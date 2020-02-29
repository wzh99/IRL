use std::cell::RefCell;
use std::collections::{BTreeSet, HashMap};
use std::hash::{Hash, Hasher};
use std::ops::Deref;

use crate::lang::func::{BlockListener, BlockRef, Func};
use crate::lang::instr::{BinOp, Instr};
use crate::lang::Program;
use crate::lang::value::{Const, SymbolRef, Type, Typed, Value};
use crate::opt::{FnPass, Pass};
use crate::opt::gvn::Gvn;

#[derive(Eq, PartialEq, Hash, Clone, Debug)]
enum Expr {
    /// Compile time constants
    Const(Const),
    /// Binary operations
    Binary(BinExpr),
    /// Temporaries that store values
    Temp(SymbolRef),
}

#[derive(Eq, Clone, Debug)]
struct BinExpr {
    op: BinOp,
    ty: Type,
    // type of operands, not of result
    fst: usize,
    snd: usize,
}

impl PartialEq for BinExpr {
    fn eq(&self, other: &Self) -> bool {
        self.op == other.op && self.fst == other.fst && self.snd == other.snd
    }
}

impl Hash for BinExpr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.op.hash(state);
        self.fst.hash(state);
        self.snd.hash(state);
    }
}

#[derive(Debug)]
struct ValueTable {
    /// Expression list for each numbered value
    tab: Vec<Vec<Expr>>,
    /// Map expressions to their corresponding value number.
    /// Note that if an expression is `Expr::Result` and the variable it holds is global, it will
    /// not be contained in this map, because the mapping is not unique.
    num: HashMap<Expr, usize>,
}

impl ValueTable {
    fn new(reserved: usize) -> ValueTable {
        ValueTable {
            tab: vec![vec![]; reserved],
            num: Default::default(),
        }
    }

    /// Add expressions that do not have a number. Return allocated number for this expression.
    fn add(&mut self, expr: Expr) -> usize {
        let num = self.tab.len();
        self.tab.push(vec![expr.clone()]);
        self.map(expr, num);
        num
    }

    /// Add expression that already has a value, this number must be less than the `reserved`
    /// argument passed to the constructor.
    fn add_num(&mut self, num: usize, expr: Expr) {
        self.tab[num].push(expr.clone());
        self.map(expr, num)
    }

    /// Map `expr` to given number, as long as it is not `Expr::Result` of a global variable.
    fn map(&mut self, expr: Expr, num: usize) {
        match expr {
            Expr::Temp(sym) if !sym.is_local_var() => {} // never map global variables
            expr => { self.num.insert(expr, num); }
        }
    }

    /// Find value number for given expression. This method also encompass operator commutation and
    /// re-association to find expressions that are not obviously available.
    fn find(&mut self, expr: &Expr) -> Option<usize> {
        self.get_num(expr).or_else(|| match expr.clone() {
            // Use operator commutativity to have another try
            Expr::Binary(BinExpr { op, ty, fst, snd }) if op.is_comm() => self.get_num(
                &Expr::Binary(BinExpr { op, ty, fst: snd, snd: fst })
            ),
            _ => None
        }).or_else(|| match expr {
            // Try to re-associate binary operations
            Expr::Binary(BinExpr { op, ty: _, fst: _, snd: _ }) if op.is_assoc() =>
                match expr.clone() {
                    // Try processing first value
                    Expr::Binary(BinExpr { op, ty: _, fst, snd })
                    if self.find_bin(fst).is_some() =>
                        self.find_bin(fst).and_then(|fst| {
                            match fst {
                                BinExpr { op: opl, ty, fst: l_fst, snd: l_snd } if op == opl =>
                                    self.get_num(&Expr::Binary(BinExpr {
                                        op,
                                        ty: ty.clone(),
                                        fst: l_snd,
                                        snd,
                                    })).and_then(|snd| self.get_num(&Expr::Binary(BinExpr {
                                        op,
                                        ty,
                                        fst: l_fst,
                                        snd,
                                    }))),
                                _ => None
                            }
                        }),
                    // Try processing second value
                    Expr::Binary(BinExpr { op, ty: _, fst, snd })
                    if self.find_bin(snd).is_some() =>
                        self.find_bin(snd).and_then(|snd| {
                            match snd {
                                BinExpr { op: opr, ty, fst: r_fst, snd: r_snd } if op == opr => {
                                    self.get_num(&Expr::Binary(BinExpr {
                                        op,
                                        ty: ty.clone(),
                                        fst,
                                        snd: r_fst,
                                    })).and_then(|fst| self.get_num(&Expr::Binary(BinExpr {
                                        op,
                                        ty,
                                        fst,
                                        snd: r_snd,
                                    })))
                                }
                                _ => None
                            }
                        }),
                    _ => None
                },
            _ => None,
        })
    }

    /// Look up value number of an expression. This method uses algebraic identities to find
    /// expressions that are not obviously available. This is different from `find` that it is more
    /// fundamental and does not dive into the structure of operand values.
    fn get_num(&mut self, expr: &Expr) -> Option<usize> {
        self.num.get(expr).copied().or_else(|| match expr.clone() {
            Expr::Binary(BinExpr { op, ref ty, fst, snd }) => {
                let fst_cn = self.find_const(fst);
                let snd_cn = self.find_const(snd);
                if let (Some(l), Some(r)) = (fst_cn, snd_cn) {
                    return Some(self.find_or_add(Expr::Const(op.eval(l, r))))
                }
                let zero = Const::zero(ty);
                let one = Const::one(ty);
                match op {
                    // 0 + x = x + 0 = x
                    BinOp::Add => match (fst_cn, snd_cn) {
                        (Some(l), _) if l == zero => Some(snd),
                        (_, Some(r)) if r == zero => Some(fst),
                        _ => None
                    }
                    // x - x = 0
                    BinOp::Sub if fst == snd =>
                        Some(self.find_or_add(Expr::Const(zero.clone()))),
                    // 0 * x = x * 0 = 0, 1 * x = x * 1 = x
                    BinOp::Mul => match (fst_cn, snd_cn) {
                        (Some(l), _) if l == zero =>
                            Some(self.find_or_add(Expr::Const(zero.clone()))),
                        (_, Some(r)) if r == zero =>
                            Some(self.find_or_add(Expr::Const(zero.clone()))),
                        (Some(l), _) if l == one => Some(snd),
                        (_, Some(r)) if r == one => Some(fst),
                        _ => None
                    }
                    // x << 0 = x, x >> 0 = x
                    BinOp::Shl | BinOp::Shr => match snd_cn {
                        r if r == Some(zero) => Some(fst),
                        _ => None
                    }
                    _ => None
                }
            }
            _ => None
        })
    }

    /// Find binary expression in the value list of given value number
    fn find_const(&self, num: usize) -> Option<Const> {
        self.tab.get(num).and_then(|list| list.iter().find(|expr| match expr {
            Expr::Const(_) => true,
            _ => false
        }).and_then(|expr| match expr {
            Expr::Const(c) => Some(c.clone()),
            _ => unreachable!()
        }))
    }

    /// Find binary expression in the value list of given value number
    fn find_bin(&self, num: usize) -> Option<BinExpr> {
        self.tab.get(num).and_then(|list| list.iter().find(|expr| match expr {
            Expr::Binary(_) => true,
            _ => false
        }).and_then(|expr| match expr {
            Expr::Binary(bin) => Some(bin.clone()),
            _ => unreachable!()
        }))
    }

    /// Possibly find indices for expression or create new number for it
    fn find_or_add(&mut self, expr: Expr) -> usize {
        self.find(&expr).unwrap_or_else(|| self.add(expr))
    }
}

/// Implement GVN-PRE proposed by Thomas.
/// See [https://www.cs.purdue.edu/homes/hosking/papers/cc04.pdf].
pub struct PreOpt {}

impl Pass for PreOpt {
    fn opt(&mut self, pro: &mut Program) { FnPass::opt(self, pro) }
}

impl FnPass for PreOpt {
    fn opt_fn(&mut self, func: &Func) {
        // Renumber the non-continuous symbols given by GVN
        let mut sym_num = Gvn::new().number(func);
        let num_set: BTreeSet<usize> = sym_num.values().copied().collect();
        let size = num_set.len();
        let num_remap: HashMap<usize, usize> = num_set.into_iter()
            .enumerate().map(|(new, old)| (old, new)).collect();
        sym_num.iter_mut().for_each(|(_, num)| *num = num_remap[num]);

        // Build sets as well as value table
        let mut builder = SetBuilder {
            sym_num,
            table: ValueTable::new(size),
            sets: Default::default(),
        };
        func.walk_dom(&mut builder);

        // Build anticipated set in reverse CFG order
        func.post_dom(|block| println!("{:?}", block));
    }
}

/// Keep record of leader sets used in PRE for each basic block
#[derive(Debug)]
struct LeaderSet {
    /// Expressions generated by this block
    expr: HashMap<usize, Expr>,
    /// Phi destinations of this block
    phi: HashMap<usize, SymbolRef>,
    /// Temporaries created in this block
    tmp: HashMap<usize, SymbolRef>,
    /// Available expressions at exit of this block
    avail_out: HashMap<usize, Expr>,
    /// Anticipated expressions at entrance and exit of this block
    antic_in: HashMap<usize, Expr>,
    antic_out: HashMap<usize, Expr>,
}

impl LeaderSet {
    fn new() -> LeaderSet {
        LeaderSet {
            expr: Default::default(),
            phi: Default::default(),
            tmp: Default::default(),
            avail_out: Default::default(),
            antic_in: Default::default(),
            antic_out: Default::default(),
        }
    }
}

struct SetBuilder {
    sym_num: HashMap<SymbolRef, usize>,
    table: ValueTable,
    sets: HashMap<BlockRef, LeaderSet>,
}

impl BlockListener for SetBuilder {
    fn on_begin(&mut self, func: &Func) {
        // Add parameters to value table and available set of entrance
        let ent = func.ent.borrow().clone();
        let avail_in: HashMap<usize, Expr> = func.param.iter().map(|p| {
            let sym = p.borrow().clone();
            let num = self.sym_num[&sym];
            self.table.add_num(num, Expr::Temp(sym.clone()));
            (num, Expr::Temp(sym.clone()))
        }).collect();
        let mut leader = LeaderSet::new();
        leader.avail_out = avail_in;
        self.sets.insert(ent, leader);
    }

    fn on_end(&mut self, _func: &Func) {}

    fn on_enter(&mut self, block: BlockRef) {
        // Register this block
        if !self.sets.contains_key(&block) { // not entrance block
            let mut leader = LeaderSet::new();
            leader.avail_out = self.sets[&block.parent().unwrap()].avail_out.clone();
            self.sets.insert(block.clone(), leader);
        }

        // Visit instructions
        block.instr.borrow().iter().for_each(|instr| {
            // Skip those whose results are not stored in local variables
            match instr.dst() {
                None => return, // this instruction does not produce a value
                Some(sym) if !sym.borrow().is_local_var() => return, // result stored to global
                _ => {}
            }

            // Process destination symbol
            macro_rules! set {
                ($name:ident) => {self.sets.get_mut(&block).unwrap().$name};
            }
            let dst = instr.dst().unwrap().borrow().clone();
            let dst_num = self.sym_num[&dst];
            let dst_expr = Expr::Temp(dst.clone());

            // Visit interested instruction
            match instr.deref() {
                Instr::Phi { src: _, dst: _ } => {
                    self.table.add_num(dst_num, dst_expr.clone());
                    Self::try_insert(&mut set!(phi), dst_num, dst);
                    Self::try_insert(&mut set!(avail_out), dst_num, dst_expr);
                }
                Instr::Mov { src, dst: _ } => {
                    let (src_num, src_expr) = self.find_src(src);
                    Self::try_insert(&mut set!(expr), src_num, src_expr);
                    self.table.add_num(dst_num, dst_expr.clone());
                    Self::try_insert(&mut set!(tmp), dst_num, dst);
                }
                Instr::Bin { op, fst, snd, dst: _ } => {
                    // Build expression for binary operation
                    let (fst_num, fst_expr) = self.find_src(fst);
                    Self::try_insert(&mut set!(expr), fst_num, fst_expr);
                    let (snd_num, snd_expr) = self.find_src(snd);
                    Self::try_insert(&mut set!(expr), snd_num, snd_expr);
                    let bin_expr = Expr::Binary(BinExpr {
                        op: *op,
                        ty: fst.borrow().get_type(),
                        fst: fst_num,
                        snd: snd_num,
                    });
                    // Find number for expression and destination
                    let dst_num = self.table.find(&bin_expr).unwrap_or(dst_num);
                    self.table.add_num(dst_num, bin_expr.clone());
                    self.table.add_num(dst_num, dst_expr);
                    Self::try_insert(&mut set!(expr), dst_num, bin_expr);
                    Self::try_insert(&mut set!(tmp), dst_num, dst);
                }
                _ => {
                    self.table.add_num(dst_num, dst_expr.clone());
                    Self::try_insert(&mut set!(tmp), dst_num, dst);
                    Self::try_insert(&mut set!(avail_out), dst_num, dst_expr);
                }
            }
        })
    }

    fn on_exit(&mut self, _block: BlockRef) {}

    fn on_enter_child(&mut self, _this: BlockRef, _child: BlockRef) {}

    fn on_exit_child(&mut self, _this: BlockRef, _child: BlockRef) {}
}

impl SetBuilder {
    fn find_src(&mut self, opd: &RefCell<Value>) -> (usize, Expr) {
        match opd.borrow().deref() {
            // Local variable must have been numbered before
            Value::Var(sym) if sym.is_local_var() => (self.sym_num[sym], Expr::Temp(sym.clone())),
            // Must allocate new number for each use of global variable
            Value::Var(sym) => {
                let expr = Expr::Temp(sym.clone());
                (self.table.add(expr.clone()), expr)
            },
            // Find number of existing constant or allocate new number for new constant
            Value::Const(c) => {
                let expr = Expr::Const(c.clone());
                (self.table.find_or_add(expr.clone()), expr)
            }
        }
    }

    fn try_insert<T>(set: &mut HashMap<usize, T>, num: usize, elem: T) {
        if !set.contains_key(&num) { set.insert(num, elem); }
    }
}

#[test]
fn test_pre() {
    use crate::compile::lex::Lexer;
    use crate::compile::parse::Parser;
    use crate::compile::build::Builder;
    use crate::lang::print::Printer;
    use std::io::stdout;
    use std::fs::File;
    use std::convert::TryFrom;
    use std::io::Read;
    use std::borrow::BorrowMut;

    let mut file = File::open("test/pre.ir").unwrap();
    let lexer = Lexer::try_from(&mut file as &mut dyn Read).unwrap();
    let parser = Parser::new(lexer);
    let tree = parser.parse().unwrap();
    let builder = Builder::new(tree);
    let mut pro = builder.build().unwrap();
    let mut opt = PreOpt {};
    Pass::opt(&mut opt, &mut pro);

    let mut out = stdout();
    let mut printer = Printer::new(out.borrow_mut());
    printer.print(&pro).unwrap();
}
