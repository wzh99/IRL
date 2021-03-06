use std::cell::RefCell;
use std::collections::{BTreeSet, HashMap};
use std::hash::{Hash, Hasher};
use std::iter::FromIterator;
use std::ops::Deref;

use crate::lang::func::{BlockRef, DomTreeListener, Fn, FnRef};
use crate::lang::inst::{BinOp, Inst};
use crate::lang::Program;
use crate::lang::util::{ExtRc, WorkList};
use crate::lang::value::{Const, SymbolGen, SymbolRef, Type, Typed, Value};
use crate::pass::{FnPass, Pass};
use crate::pass::copy::CopyProp;
use crate::pass::gvn::Gvn;

#[derive(Eq, PartialEq, Hash, Clone, Debug)]
enum Expr {
    /// Compile time constants
    Const(Const),
    /// Binary operations
    Bin(BinExpr),
    /// Pointer operations
    Ptr(PtrExpr),
    /// Temporaries that store values
    Temp(SymbolRef),
}

impl Typed for Expr {
    fn get_type(&self) -> Type {
        match self {
            Expr::Const(c) => c.get_type(),
            Expr::Bin(bin) => bin.get_type(),
            Expr::Ptr(ptr) => ptr.get_type(),
            Expr::Temp(sym) => sym.get_type()
        }
    }
}

impl Expr {
    fn opd(&self) -> Vec<usize> {
        match self {
            Expr::Bin(BinExpr { op: _, ty: _, fst, snd }) => vec![*fst, *snd],
            Expr::Ptr(PtrExpr { ty: _, base, off, idx }) =>
                vec![*base, *off, *idx].into_iter().filter(|o| *o != NONE).collect(),
            _ => vec![]
        }
    }
}

#[derive(Eq, Clone, Debug)]
struct BinExpr {
    /// Binary operator
    op: BinOp,
    /// Type of operands, not result
    ty: Type,
    /// Value number of both operands
    fst: usize,
    snd: usize,
}

impl Typed for BinExpr {
    fn get_type(&self) -> Type { self.op.res_type(&self.ty).unwrap() }
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

const NONE: usize = usize::max_value();

/// Represent pointer operation that in form of base and offset. Indices into aggregate is not
/// considered.
#[derive(Eq, Clone, Debug)]
struct PtrExpr {
    /// Type of the pointer
    ty: Type,
    /// Base pointer
    base: usize,
    /// Pointer offset
    off: usize,
    /// Single index
    idx: usize,
}

impl Typed for PtrExpr {
    fn get_type(&self) -> Type { self.ty.clone() }
}

impl PartialEq for PtrExpr {
    fn eq(&self, other: &Self) -> bool {
        self.base == other.base && self.off == other.off
    }
}

impl Hash for PtrExpr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.base.hash(state);
        self.off.hash(state);
        self.idx.hash(state);
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
            Expr::Temp(sym) if sym.is_global_var() => {} // never map global variables
            expr => { self.num.insert(expr, num); }
        }
    }

    /// Find value number for given expression. This method also encompass operator commutation and
    /// re-association to find expressions that are not obviously available.
    fn find(&mut self, expr: &Expr) -> Option<usize> {
        self.get_num(expr).or_else(|| match expr.clone() {
            // Use operator commutativity to have another try
            Expr::Bin(BinExpr { op, ty, fst, snd }) if op.is_comm() => self.get_num(
                &Expr::Bin(BinExpr { op, ty, fst: snd, snd: fst })
            ),
            _ => None
        }).or_else(|| match expr {
            // Try to re-associate binary operations
            Expr::Bin(BinExpr { op, ty: _, fst: _, snd: _ }) if op.is_assoc() =>
                match expr.clone() {
                    // Try processing first value
                    Expr::Bin(BinExpr { op, ty: _, fst, snd })
                    if self.find_bin(fst).is_some() =>
                        self.find_bin(fst).and_then(|fst| {
                            match fst {
                                BinExpr { op: opl, ty, fst: l_fst, snd: l_snd }
                                if opl.assoc_with(&op) =>
                                    self.get_num(&Expr::Bin(BinExpr {
                                        op,
                                        ty: ty.clone(),
                                        fst: l_snd,
                                        snd,
                                    })).and_then(
                                        |snd| self.get_num(&Expr::Bin(BinExpr {
                                            op: opl,
                                            ty,
                                            fst: l_fst,
                                            snd,
                                        }))
                                    ),
                                _ => None
                            }
                        }),
                    _ => None
                }.or_else(|| match expr.clone() {
                    // Try processing second value
                    Expr::Bin(BinExpr { op, ty: _, fst, snd })
                    if self.find_bin(snd).is_some() =>
                        self.find_bin(snd).and_then(|snd| {
                            match snd {
                                BinExpr { op: opr, ty, fst: r_fst, snd: r_snd }
                                if op.assoc_with(&opr) =>
                                    self.get_num(&Expr::Bin(BinExpr {
                                        op,
                                        ty: ty.clone(),
                                        fst,
                                        snd: r_fst,
                                    })).and_then(
                                        |fst| self.get_num(&Expr::Bin(BinExpr {
                                            op: opr,
                                            ty,
                                            fst,
                                            snd: r_snd,
                                        }))
                                    ),
                                _ => None
                            }
                        }),
                    _ => None
                }),
            _ => None,
        })
    }

    /// Look up value number of an expression. This method uses algebraic identities to find
    /// expressions that are not obviously available. This is different from `find` that it is more
    /// fundamental and does not dive into the structure of operand values.
    fn get_num(&mut self, expr: &Expr) -> Option<usize> {
        self.num.get(expr).copied().or_else(|| match expr.clone() {
            Expr::Bin(BinExpr { op, ref ty, fst, snd }) => {
                let fst_cn = self.find_const(fst);
                let snd_cn = self.find_const(snd);
                if let (Some(l), Some(r)) = (fst_cn, snd_cn) {
                    return Some(self.find_or_add(Expr::Const(op.eval(l, r))));
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
                    // x - x = 0, x - 0 = x
                    BinOp::Sub => match (fst_cn, snd_cn) {
                        (_, Some(r)) if r == zero => Some(fst),
                        _ if fst == snd => Some(self.find_or_add(Expr::Const(zero.clone()))),
                        _ => None
                    }
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
            Expr::Ptr(PtrExpr { ty: _, base, off, idx }) => match idx {
                NONE => match self.find_const(off) {
                    Some(Const::I64(0)) => Some(base),
                    _ => None,
                }
                _ => None
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
            Expr::Bin(_) => true,
            _ => false
        }).and_then(|expr| match expr {
            Expr::Bin(bin) => Some(bin.clone()),
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
pub struct PreOpt {
    table: ValueTable,
}

impl Pass for PreOpt {
    fn run(&mut self, pro: &mut Program) { FnPass::run(self, pro) }
}

impl FnPass for PreOpt {
    //noinspection RsTypeCheck
    fn run_on_fn(&mut self, func: &FnRef) {
        // Make sure the CFG is edge split
        func.split_edge();

        // Renumber the non-continuous symbols given by GVN
        let mut sym_num = Gvn::new().number(func);
        let num_set: BTreeSet<usize> = sym_num.values().copied().collect();
        let size = num_set.len();
        let num_remap: HashMap<usize, usize> = num_set.into_iter()
            .enumerate().map(|(new, old)| (old, new)).collect();
        sym_num.iter_mut().for_each(|(_, num)| *num = num_remap[num]);

        // Build flow sets as well as value table
        self.table = ValueTable::new(size);
        let mut builder = SetBuilder {
            sym_num,
            table: &mut self.table,
            sets: Default::default(),
        };
        func.walk_dom(&mut builder);

        // Build anticipated set in post-dominator order
        let SetBuilder { sym_num: _, table: _, mut sets } = builder;
        let mut changed = true;
        while changed {
            changed = false;
            func.post_dom(|ref block| {
                // Build anticipated set at exit of the block
                let old = sets[block].antic_in.clone();
                let mut antic_out: HashMap<usize, Expr> = HashMap::new();
                match block.succ.borrow().len() {
                    // Do nothing for exit block.
                    0 => {}
                    // This block has one successor, deal with phis in this block
                    1 => {
                        let succ = &block.succ.borrow()[0];
                        antic_out = self.phi_trans(sets[succ].antic_in.clone(), block.clone(),
                                                   succ.clone());
                    }
                    // This block has several successors, find intersection of anticipated sets
                    // of all the successors
                    _ => {
                        let all_succ = block.succ.borrow().clone();
                        let mut work = WorkList::from_iter(all_succ.into_iter());
                        let first = work.pick().unwrap();
                        antic_out = sets[&first].antic_in.clone();
                        while !work.is_empty() {
                            let succ = work.pick().unwrap();
                            antic_out.retain(|num, _| {
                                Self::find_leader(&sets[&succ].antic_in, *num).is_some()
                            })
                        }
                    }
                }

                // Build anticipated set at entrance of the block
                let other = Self::remove_tmp(&antic_out, &sets[block].tmp);
                sets.get_mut(block).unwrap().antic_in = Self::remove_tmp(&sets[block].expr,
                                                                         &sets[block].tmp);
                other.iter().for_each(|(num, expr)| {
                    if Self::find_leader(&sets[block].antic_in, *num).is_none() {
                        sets.get_mut(block).unwrap().antic_in.insert(*num, expr.clone());
                    }
                });
                Self::clean(&mut sets.get_mut(block).unwrap().antic_in);
                if old != sets[block].antic_in {
                    changed = true
                }
            })
        }

        // Hoist expressions to earlier points
        let mut new_tmp: HashMap<BlockRef, HashMap<usize, SymbolRef>> = HashMap::new();
        let mut gen = SymbolGen::new(func.scope.clone(), "t");
        let mut inserted = true;
        while inserted {
            inserted = false;
            // Traverse dominator tree
            func.iter_dom().for_each(|ref block| {
                // Inherit created temporaries from dominator
                new_tmp.insert(block.clone(), HashMap::new());
                if block.parent().is_none() { return; }
                let ref dom = block.parent().unwrap();
                new_tmp[dom].clone().into_iter().for_each(|(num, sym)| {
                    new_tmp.get_mut(block).unwrap().insert(num, sym.clone());
                    sets.get_mut(block).unwrap().avail_out.insert(num, Expr::Temp(sym));
                });

                // Insert instructions using work list algorithm
                if block.pred.borrow().len() <= 1 { return; } // only insert at merge point
                let mut work: WorkList<(usize, Expr)> = sets[block].antic_in.clone().into_iter()
                    .collect();
                while !work.is_empty() {
                    // Find insertion point
                    let (num, expr) = work.pick().unwrap();
                    let expr = if let Expr::Bin(bin) = expr { bin } else { continue; };
                    if Self::find_leader(&sets[dom].avail_out, num).is_some() { continue; }
                    let mut avail: HashMap<BlockRef, Expr> = HashMap::new();
                    let mut by_some = false;
                    let mut all_same = true;
                    let mut first_sym = None;

                    block.pred.borrow().iter().for_each(|pred| {
                        let (trans_num, trans_expr) =
                            self.phi_trans_one(num, Expr::Bin(expr.clone()), pred.clone(),
                                               block.clone());
                        match Self::find_leader(&sets[pred].avail_out, trans_num) {
                            Some(leader) => {
                                avail.insert(pred.clone(), Expr::Temp(leader.clone()));
                                by_some = true;
                                if first_sym == None {
                                    first_sym = Some(leader)
                                } else if first_sym != Some(leader) {
                                    all_same = false
                                }
                            }
                            None => {
                                avail.insert(pred.clone(), trans_expr);
                                all_same = false;
                            }
                        }
                    });

                    // Insert expression where it is not available
                    if all_same || !by_some { continue; }
                    // Operands in inserted expressions may depend on temporaries that has not yet
                    // been created. In this case, we just skip inserting phi instruction and wait
                    // for the next iteration.
                    let success = block.pred.borrow().iter().all(|pred| {
                        self.insert_expr(pred, &mut avail, &mut sets, &mut gen)
                    });
                    if !success || sets[block].phi.contains_key(&num) { continue; }
                    let dst_sym = gen.gen(&expr.get_type());
                    self.table.add_num(num, Expr::Temp(dst_sym.clone()));
                    sets.get_mut(block).unwrap().avail_out
                        .insert(num, Expr::Temp(dst_sym.clone()));
                    let phi_src = block.pred.borrow().clone().into_iter().map(|block| {
                        let sym = if let Expr::Temp(sym) = avail[&block].clone() {
                            sym
                        } else { unreachable!() };
                        (RefCell::new(block), RefCell::new(Value::Var(sym)))
                    }).collect();
                    block.push_front(ExtRc::new(Inst::Phi {
                        src: phi_src,
                        dst: RefCell::new(dst_sym.clone()),
                    }));
                    sets.get_mut(block).unwrap().phi.insert(num, dst_sym.clone());
                    new_tmp.get_mut(block).unwrap().insert(num, dst_sym);
                    inserted = true;
                }
            });
        }

        // Eliminate redundant computation
        func.iter_dom().for_each(|ref block| {
            block.inst.borrow_mut().iter_mut().for_each(|instr| {
                match instr.dst() {
                    Some(dst) if dst.borrow().is_local_var() => {
                        let dst = dst.borrow().clone();
                        let num = self.table.find(&Expr::Temp(dst.clone())).unwrap();
                        let leader = Self::find_leader(&sets[block].avail_out, num).unwrap();
                        if leader != dst.clone() {
                            *instr = ExtRc::new(Inst::Mov {
                                src: RefCell::new(Value::Var(leader)),
                                dst: RefCell::new(dst),
                            })
                        }
                    }
                    _ => {}
                }
            })
        });

        // Propagate copy
        CopyProp::new().run_on_fn(func)
    }
}

impl PreOpt {
    pub fn new() -> PreOpt {
        PreOpt { table: ValueTable::new(0) }
    }

    /// Insert corresponding instruction at given predecessor. Return whether this instruction
    /// has been successfully inserted.
    /// Insertion may fail because some operands are not available at this time.
    fn insert_expr(&mut self, pred: &BlockRef, avail: &mut HashMap<BlockRef, Expr>,
                   sets: &mut HashMap<BlockRef, LeaderSet>, gen: &mut SymbolGen) -> bool
    {
        match avail[pred].clone() {
            Expr::Bin(BinExpr { op, ty, fst, snd }) => {
                // First operand
                let fst_val =
                    if let Some(fst_val) = self.create_opd(&sets[pred].avail_out, fst) {
                        fst_val
                    } else { return false; };

                // Second operand
                let snd_val =
                    if let Some(snd_val) = self.create_opd(&sets[pred].avail_out, snd) {
                        snd_val
                    } else { return false; };

                // Insert instruction
                let dst_sym = gen.gen(&op.res_type(&ty).unwrap());
                pred.insert_before_ctrl(ExtRc::new(Inst::Bin {
                    op,
                    fst: RefCell::new(fst_val),
                    snd: RefCell::new(snd_val),
                    dst: RefCell::new(dst_sym.clone()),
                }));

                // Add to value table and leader sets
                let expr_num = self.table.find_or_add(Expr::Bin(
                    BinExpr { op, ty, fst, snd }
                ));
                self.table.add_num(expr_num, Expr::Temp(dst_sym.clone()));
                sets.get_mut(pred).unwrap().avail_out
                    .insert(expr_num, Expr::Temp(dst_sym.clone()));
                avail.insert(pred.clone(), Expr::Temp(dst_sym));

                true
            }
            Expr::Ptr(PtrExpr { ty, base, off, idx }) => {
                // Base pointer
                let base_val =
                    if let Some(base_val) = self.create_opd(&sets[pred].avail_out, base) {
                        base_val
                    } else { return false; };

                // Pointer offset
                let off_val = match self.create_opd(&sets[pred].avail_out, off) {
                    // zero pointer offset can be ignored
                    Some(Value::Const(Const::I64(0))) => None,
                    Some(val) => Some(RefCell::new(val)),
                    None => return false,
                };

                // Aggregate index
                let idx_val = match idx {
                    NONE => vec![],
                    idx => if let Some(idx_val) = self.create_opd(&sets[pred].avail_out, idx) {
                        vec![RefCell::new(idx_val)]
                    } else { return false; }
                };

                // Insert instruction
                let dst_sym = gen.gen(&ty);
                pred.insert_before_ctrl(ExtRc::new(Inst::Ptr {
                    base: RefCell::new(base_val),
                    off: off_val,
                    ind: idx_val,
                    dst: RefCell::new(dst_sym.clone()),
                }));

                // Add to value table and leader sets
                let expr_num = self.table.find_or_add(Expr::Ptr(
                    PtrExpr { ty, base, off, idx }
                ));
                self.table.add_num(expr_num, Expr::Temp(dst_sym.clone()));
                sets.get_mut(pred).unwrap().avail_out
                    .insert(expr_num, Expr::Temp(dst_sym.clone()));
                avail.insert(pred.clone(), Expr::Temp(dst_sym));

                true
            }
            // Other instructions will not be inserted
            _ => true
        }
    }

    fn phi_trans_one(&mut self, num: usize, expr: Expr, pred: BlockRef, succ: BlockRef)
                     -> (usize, Expr)
    {
        let set = HashMap::from_iter(vec![(num, expr)]);
        let res: Vec<(usize, Expr)> = self.phi_trans(set, pred, succ).into_iter().collect();
        res[0].clone()
    }

    fn phi_trans(&mut self, set: HashMap<usize, Expr>, pred: BlockRef, succ: BlockRef)
                 -> HashMap<usize, Expr>
    {
        // Build number map for all phi destinations in successor block
        let mut num_map: HashMap<usize, (usize, Expr)> = HashMap::new();
        for instr in succ.inst.borrow().iter() {
            match instr.deref() {
                Inst::Phi { src, dst } => {
                    let dst_num = self.table.find(&Expr::Temp(dst.borrow().clone())).unwrap();
                    if num_map.contains_key(&dst_num) { continue; }
                    let src_opd = &src.iter().find(|(block, _)| *block.borrow() == pred)
                        .unwrap().1;
                    num_map.insert(dst_num, self.find_value(src_opd));
                }
                _ => break
            }
        }

        // Replace expressions in the given set
        set.into_iter().map(move |(num, expr)| {
            num_map.get(&num).cloned().unwrap_or_else(|| {
                match expr {
                    // Replace operand values in binary expressions
                    Expr::Bin(BinExpr { op, ty, fst, snd }) => {
                        let fst = num_map.get(&fst).map(|(num, _)| *num).unwrap_or(fst);
                        let snd = num_map.get(&snd).map(|(num, _)| *num).unwrap_or(snd);
                        let new_expr = Expr::Bin(BinExpr { op, ty, fst, snd });
                        (self.table.find_or_add(new_expr.clone()), new_expr)
                    }
                    Expr::Ptr(PtrExpr { ty, base, off, idx }) => {
                        let base = num_map.get(&base).map(|(num, _)| *num).unwrap_or(base);
                        let off = num_map.get(&off).map(|(num, _)| *num).unwrap_or(off);
                        let idx = num_map.get(&idx).map(|(num, _)| *num).unwrap_or(idx);
                        let new_expr = Expr::Ptr(PtrExpr { ty, base, off, idx });
                        (self.table.find_or_add(new_expr.clone()), new_expr)
                    }
                    // For other expressions that cannot be translated, just return them
                    _ => (num, expr)
                }
            })
        }).collect()
    }

    /// Find leader temporary of `num` in `set` first. If a symbol is found, a local variable is
    /// created. Otherwise, a constant is returned. In this optimization, no global variable is
    /// considered, so this method is complete.
    fn create_opd(&self, set: &HashMap<usize, Expr>, num: usize) -> Option<Value> {
        match Self::find_leader(set, num) {
            Some(leader) => Some(Value::Var(leader)),
            None => self.table.find_const(num).and_then(|c| Some(Value::Const(c)))
        }
    }

    fn find_value(&mut self, val: &RefCell<Value>) -> (usize, Expr) {
        match val.borrow().deref() {
            Value::Var(sym) => {
                let expr = Expr::Temp(sym.clone());
                (self.table.find(&expr).unwrap(), expr)
            }
            Value::Const(c) => {
                let expr = Expr::Const(*c);
                (self.table.find_or_add(expr.clone()), expr)
            }
        }
    }

    fn find_leader(set: &HashMap<usize, Expr>, num: usize) -> Option<SymbolRef> {
        set.get(&num).and_then(|expr| match expr {
            Expr::Temp(sym) => Some(sym.clone()),
            _ => None
        })
    }

    fn remove_tmp(set: &HashMap<usize, Expr>, tmp: &HashMap<usize, SymbolRef>)
                  -> HashMap<usize, Expr>
    {
        let mut set = set.clone();
        set.retain(|num, expr| {
            match tmp.get(num) {
                Some(sym) => expr != &Expr::Temp(sym.clone()),
                None => true
            }
        });
        set
    }

    fn clean(set: &mut HashMap<usize, Expr>) {
        // Build dependency graph
        let mut dep: HashMap<usize, Vec<usize>> = HashMap::new();
        set.iter().for_each(|(num, expr)| {
            expr.opd().into_iter().for_each(|o| {
                match dep.get_mut(&o) {
                    Some(list) => list.push(*num),
                    None => { dep.insert(o, vec![*num]); }
                }
            });
        });

        // Eliminate killed values using work list algorithm
        let mut work: WorkList<usize> = WorkList::from_iter(set.keys().cloned());
        while !work.is_empty() {
            let ref num = work.pick().unwrap();
            let ref expr = set[num].clone();
            if !expr.opd().iter().all(|o| set.contains_key(o)) {
                set.remove(num);
                dep.get(num).map(|list| list.iter().for_each(|val| work.insert(*val)));
            }
        }
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
}

impl LeaderSet {
    fn new() -> LeaderSet {
        LeaderSet {
            expr: Default::default(),
            phi: Default::default(),
            tmp: Default::default(),
            avail_out: Default::default(),
            antic_in: Default::default(),
        }
    }
}

struct SetBuilder<'a> {
    sym_num: HashMap<SymbolRef, usize>,
    table: &'a mut ValueTable,
    sets: HashMap<BlockRef, LeaderSet>,
}

impl DomTreeListener for SetBuilder<'_> {
    fn on_begin(&mut self, func: &Fn) {
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

    fn on_end(&mut self, _func: &Fn) {}

    fn on_enter(&mut self, block: BlockRef) {
        // Register this block
        if !self.sets.contains_key(&block) { // not entrance block
            let mut leader = LeaderSet::new();
            leader.avail_out = self.sets[&block.parent().unwrap()].avail_out.clone();
            self.sets.insert(block.clone(), leader);
        }

        // Visit instructions
        block.inst.borrow().iter().for_each(|instr| {
            // Skip those whose results are not stored in local variables
            match instr.dst() {
                None => return, // this instruction does not produce a value
                Some(sym) if sym.borrow().is_global_var() => return, // result stored to global
                _ => {}
            }

            // Process destination symbol
            macro_rules! set {
                ($name:ident) => {self.sets.get_mut(&block).unwrap().$name};
            }
            let dst = instr.dst().unwrap().borrow().clone();
            let mut dst_num = self.sym_num[&dst]; // may changed later due to re-association
            let dst_expr = Expr::Temp(dst.clone());

            // Visit interested instruction
            match instr.deref() {
                Inst::Phi { src: _, dst: _ } => {
                    self.table.add_num(dst_num, dst_expr.clone());
                    Self::try_insert(&mut set!(phi), dst_num, dst);
                    Self::try_insert(&mut set!(avail_out), dst_num, dst_expr);
                }
                Inst::Mov { src, dst: _ } => {
                    if !src.borrow().is_global_var() {
                        let (src_num, src_expr) = self.find_src(src);
                        Self::try_insert(&mut set!(expr), src_num, src_expr);
                    }
                    self.table.add_num(dst_num, dst_expr.clone());
                    Self::try_insert(&mut set!(tmp), dst_num, dst);
                    Self::try_insert(&mut set!(avail_out), dst_num, dst_expr);
                }
                Inst::Bin { op, fst, snd, dst: _ } => {
                    // Once global variable appears in either operand, this expression will not be
                    // considered.
                    if !fst.borrow().is_global_var() && !snd.borrow().is_global_var() {
                        // First operand
                        let (fst_num, fst_expr) = self.find_src(fst);
                        Self::try_insert(&mut set!(expr), fst_num, fst_expr);
                        // Second operand
                        let (snd_num, snd_expr) = self.find_src(snd);
                        Self::try_insert(&mut set!(expr), snd_num, snd_expr);
                        // Create expression
                        let bin_expr = Expr::Bin(BinExpr {
                            op: *op,
                            ty: fst.borrow().get_type(),
                            fst: fst_num,
                            snd: snd_num,
                        });
                        dst_num = self.table.find(&bin_expr).unwrap_or(dst_num);
                        self.table.add_num(dst_num, bin_expr.clone());
                        Self::try_insert(&mut set!(expr), dst_num, bin_expr);
                    }
                    self.table.add_num(dst_num, dst_expr.clone());
                    Self::try_insert(&mut set!(tmp), dst_num, dst);
                    Self::try_insert(&mut set!(avail_out), dst_num, dst_expr);
                }
                // Only pointer operation with offset and without indices are considered
                Inst::Ptr { base, off, ind, dst: _ } if ind.len() <= 1 => {
                    if base.borrow().is_local_var()
                        && (off.is_none() || !off.as_ref().unwrap().borrow().is_global_var())
                        && (ind.is_empty() || !ind[0].borrow().is_global_var()) {
                        // Base pointer
                        let (base_num, base_expr) = self.find_src(base);
                        Self::try_insert(&mut set!(expr), base_num, base_expr);
                        // Pointer offset
                        let (off_num, off_expr) = match off {
                            Some(off) => self.find_src(off),
                            None => {
                                let zero = Expr::Const(Const::I64(0));
                                (self.table.find_or_add(zero.clone()), zero)
                            }
                        };
                        Self::try_insert(&mut set!(expr), off_num, off_expr);
                        // Single index
                        let idx_num = match ind.len() {
                            0 => NONE,
                            1 => {
                                let (idx_num, idx_expr) = self.find_src(&ind[0]);
                                Self::try_insert(&mut set!(expr), idx_num, idx_expr);
                                idx_num
                            }
                            _ => unreachable!()
                        };
                        // Create expression
                        let ptr_expr = Expr::Ptr(PtrExpr {
                            ty: base.borrow().get_type(),
                            base: base_num,
                            off: off_num,
                            idx: idx_num,
                        });
                        dst_num = self.table.find(&ptr_expr).unwrap_or(dst_num);
                        self.table.add_num(dst_num, ptr_expr.clone());
                        Self::try_insert(&mut set!(expr), dst_num, ptr_expr);
                    }
                    self.table.add_num(dst_num, dst_expr.clone());
                    Self::try_insert(&mut set!(tmp), dst_num, dst);
                    Self::try_insert(&mut set!(avail_out), dst_num, dst_expr);
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

impl SetBuilder<'_> {
    fn find_src(&mut self, opd: &RefCell<Value>) -> (usize, Expr) {
        match opd.borrow().deref() {
            // Local variable must have been numbered before.
            // Through algebraic simplification, the symbol may have have different number.
            Value::Var(sym) if sym.is_local_var() => {
                let sym_expr = Expr::Temp(sym.clone());
                self.table.find(&sym_expr).map(|num| (num, sym_expr.clone()))
                    .unwrap_or((self.sym_num[sym], sym_expr))
            }
            // Must allocate new number for each use of global variable
            Value::Var(sym) => {
                let expr = Expr::Temp(sym.clone());
                (self.table.add(expr.clone()), expr)
            }
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
    use crate::irc::lex::Lexer;
    use crate::irc::parse::Parser;
    use crate::irc::build::Builder;
    use crate::lang::print::Printer;
    use crate::vm::exec::Machine;
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
    let mut opt = PreOpt::new();
    Pass::run(&mut opt, &mut pro);

    let mut out = stdout();
    let mut printer = Printer::new(out.borrow_mut());
    printer.print(&pro).unwrap();

    let mut mach = Machine::new();
    mach.run(&mut pro).unwrap();
}
