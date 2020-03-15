use std::cell::RefCell;
use std::cmp::min;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use std::str::FromStr;

use crate::lang::func::{BlockRef, Func};
use crate::lang::instr::{BinOp, Instr};
use crate::lang::Program;
use crate::lang::util::ExtRc;
use crate::lang::value::{Const, Scope, SymbolGen, Typed, Value};
use crate::opt::{FnPass, Pass};
use crate::opt::graph::{GraphBuilder, SsaGraph, SsaVert, VertRef, VertTag};

pub struct OsrOpt {
    /// Reference to current function
    func: Option<Rc<Func>>,
    /// SSA graph forms the base of this algorithm
    graph: SsaGraph,
    /// Reverse post-order number of blocks
    /// Since RPO number is only used in this algorithm, it is not stored in the blocks.
    rpo: HashMap<BlockRef, usize>,
    /// Record unvisited vertices.
    /// `Worklist` is not used here, because it does not support removing a specified element.
    unvisited: HashSet<VertRef>,
    /// Stack for depth-first search in Tarjan's algorithm to find strongly-connected components
    stack: Vec<VertRef>,
    /// Record depth-first number of SSA vertices
    df_num: HashMap<VertRef, usize>,
    /// Record next depth-first number to be assigned to vertices
    next_num: usize,
    /// Record the lowest depth-first number in a yet-to-discovered SCC.
    low: HashMap<VertRef, usize>,
    /// Block of the vertices with the lowest RPO in an SCC
    header: HashMap<VertRef, BlockRef>,
    /// Hash table for reduced expressions
    expr: HashMap<Expr, VertRef>,
    /// Symbol generator
    gen: SymbolGen,
    /// Record each reduction performed by the algorithm
    red: HashMap<VertRef, Reduction>,
}

#[derive(Eq, PartialEq, Hash, Clone, Debug)]
struct Expr(String, VertRef, VertRef);

#[derive(Clone, Debug)]
struct Reduction {
    op: String,
    rc: VertRef,
    res: VertRef,
}

impl Pass for OsrOpt {
    fn opt(&mut self, pro: &mut Program) { FnPass::opt(self, pro) }
}

impl FnPass for OsrOpt {
    fn opt_fn(&mut self, func: &Rc<Func>) {
        // Set function-related members
        self.func = Some(func.clone());
        self.gen = SymbolGen::new("t", func.scope.clone());

        // Create reverse post-order number
        self.rpo = func.rpo().enumerate().map(|(i, b)| (b, i)).collect();

        // Create value graph
        let mut builder = GraphBuilder::new();
        func.walk_dom(&mut builder);
        self.graph = builder.graph;

        // Find strongly-connected components using Tarjan's algorithm
        self.next_num = 0;
        self.unvisited = self.graph.vert.iter().cloned().collect();
        while !self.unvisited.is_empty() {
            let mut vert = None;
            for v in &self.unvisited {
                vert = Some(v.clone());
                break;
            };
            self.dfs(&vert.unwrap())
        }

        // Perform linear function test replacement
        let vert = self.graph.vert.clone();
        vert.iter().for_each(|v| {
            if let VertTag::Value(op) = &v.tag {
                match BinOp::from_str(op) {
                    Ok(bin) if bin.is_cmp() => {
                        // Replace IV with last one in the chain
                        let opd = v.opd.borrow().clone();
                        if !self.red.contains_key(&opd[0]) {
                            return; // no reduction found
                        }
                        let iv = self.follow_edges(&opd[0]);
                        v.opd.borrow_mut()[0] = iv.clone();
                        v.instr.borrow().as_ref().unwrap().1.src()[0].replace(
                            Self::val_from_vert(&iv)
                        );

                        // Replace RC with result of operations in the chain
                        let rc = self.apply_edges(&opd[0], &opd[1]);
                        v.opd.borrow_mut()[0] = rc.clone();
                        v.instr.borrow().as_ref().unwrap().1.src()[1].replace(
                            Self::val_from_vert(&rc)
                        );
                    }
                    _ => {}
                }
            }
        });

        // Eliminate dead code
        func.elim_dead_code();

        // Clear records for this function
        self.low.clear();
        self.df_num.clear();
        self.header.clear();
        self.expr.clear();
        self.red.clear();
    }
}

impl OsrOpt {
    pub fn new() -> OsrOpt {
        OsrOpt {
            func: None,
            graph: SsaGraph::new(),
            rpo: Default::default(),
            unvisited: Default::default(),
            next_num: 0,
            low: Default::default(),
            stack: vec![],
            df_num: Default::default(),
            header: Default::default(),
            expr: Default::default(),
            gen: SymbolGen::new("", Rc::new(Scope::new())),
            red: Default::default(),
        }
    }

    fn dfs(&mut self, v: &VertRef) {
        // Visit this vertex
        let num = self.next_num;
        self.df_num.insert(v.clone(), num);
        self.next_num += 1;
        self.unvisited.remove(v);
        self.low.insert(v.clone(), num);
        self.stack.push(v.clone());

        // Visit all operands
        let opd = v.opd.borrow().clone();
        opd.iter().for_each(|o| {
            if self.unvisited.contains(o) {
                self.dfs(o);
                self.low.insert(v.clone(), min(self.low[v], self.low[o]));
            }
            if self.df_num.contains_key(o) && self.df_num[o] < self.df_num[v]
                && self.stack.contains(o) {
                self.low.insert(v.clone(), min(self.low[v], self.df_num[o]));
            }
        });

        // Find vertices of strongly-connected component
        if self.low[v] == self.df_num[v] {
            let mut scc = vec![];
            loop {
                let x = self.stack.pop().unwrap();
                scc.push(x.clone());
                if x == *v { break; }
            }
            self.proc_scc(scc);
        }
    }

    fn proc_scc(&mut self, scc: Vec<VertRef>) {
        // Process SCC with only one vertex
        if scc.len() == 1 {
            let v = &scc[0];
            if let Some((blk, _)) = &v.instr.borrow().clone().as_ref() {
                self.proc_vert(v, blk); // the header must be where it is defined
            }
            return;
        }

        // Find header
        let ref header = scc.iter().map(|v| v.instr.borrow().clone().unwrap().0)
            .min_by_key(|b| self.rpo[&b]).unwrap().clone();

        // Decide whether this SCC is an induction variable
        let is_iv = scc.iter().all(|v| {
            Self::is_iv_update(v) && v.opd.borrow().iter().all(|o|
                // Whether the operands are either IVs or region constants
                scc.contains(o) || Self::is_rc(o, header)
            )
        });

        // Process values according to classification result
        if is_iv {
            scc.into_iter().for_each(|v| {
                self.header.insert(v, header.clone());
            })
        } else {
            scc.iter().for_each(|v| self.proc_vert(v, header))
        }
    }

    /// Perform strength reduction if the vertex has certain form
    fn proc_vert(&mut self, v: &VertRef, header: &BlockRef) {
        // Only vertices with exactly two operands will be accepted
        if v.opd.borrow().len() != 2 {
            self.header.remove(v);
            return;
        }

        // Figure out IV and RC through pattern matching
        let (fst, snd) = (&v.opd.borrow()[0], &v.opd.borrow()[1]);
        if let VertTag::Value(op) = &v.tag {
            match op.as_str() {
                "add" | "sub" | "mul" if Self::is_iv_update(fst) && Self::is_rc(snd, header) =>
                    { self.replace(v, fst, snd); }
                "add" | "mul" | "ptr" if Self::is_rc(fst, header) && Self::is_iv_update(snd) =>
                    { self.replace(v, snd, fst); }
                _ => { self.header.remove(v); }
            }
        } else {
            self.header.remove(v);
        };
    }

    fn replace(&mut self, v: &VertRef, iv: &VertRef, rc: &VertRef) {
        // Get result of strength reduction
        let op = if let VertTag::Value(op) = &v.tag { op.as_str() } else {
            panic!("vertex {:?} is not a binary operation", v)
        };
        let res = self.reduce(op, iv, rc);
        self.header.insert(res.clone(), self.header[iv].clone());
        self.unvisited.insert(res.clone());

        // Replace use of this value with the result
        v.uses.borrow().iter().for_each(|u| {
            let pos = u.opd.borrow().iter().position(|opd| opd == v).unwrap();
            *u.opd.borrow_mut().get_mut(pos).unwrap() = res.clone();
            u.instr.borrow().as_ref().map(|(_, instr)|
                instr.src()[pos].replace(Self::val_from_vert(&res))
            );
        })
    }

    /// Inserts operation to strength reduce an induction variable and returns the result SSA
    /// vertex
    fn reduce(&mut self, op: &str, iv: &VertRef, rc: &VertRef) -> VertRef {
        // Find if there is available expression
        let expr = Expr(op.to_string(), iv.clone(), rc.clone());
        self.expr.get(&expr).cloned().unwrap_or_else(|| {
            // Invent a new symbol to store reduced variable
            let dst = self.gen.gen(&rc.get_type());

            // Create or clone the corresponding instruction
            let (blk, instr) = iv.instr.borrow().as_ref().unwrap().clone();
            let new_instr = ExtRc::new(if rc.get_type().is_ptr() && !instr.is_phi() {
                // Pointer operation should be treated differently
                Instr::Ptr {
                    base: RefCell::new(Self::val_from_vert(rc)),
                    off: Some(RefCell::new(Self::val_from_vert(iv))),
                    ind: vec![],
                    dst: RefCell::new(dst.clone()),
                }
            } else {
                let cloned = instr.as_ref().clone();
                cloned.dst().unwrap().replace(dst.clone());
                cloned
            });

            // Insert the instruction
            if instr.is_phi() {
                blk.push_front(new_instr.clone())
            } else {
                blk.insert_before_ctrl(new_instr.clone())
            }

            // Create the SSA vertex for this operation
            let res = ExtRc::new(SsaVert {
                tag: iv.tag.clone(),
                opd: iv.opd.clone(),
                uses: RefCell::new(vec![]),
                instr: RefCell::new(Some((blk, new_instr))),
                sym: RefCell::new(Some(dst.clone())),
            });
            self.header.insert(res.clone(), self.header[iv].clone());
            self.expr.insert(expr, res.clone());

            // Further reduce operands of the cloned vertex
            res.opd.borrow_mut().iter_mut().enumerate().for_each(|(i, opd)| {
                if self.header.get(opd) == self.header.get(&res) {
                    let new_opd = self.reduce(op, opd, rc);
                    *opd = new_opd.clone();
                    res.instr.borrow().as_ref().unwrap().1.src()[i].replace(
                        Self::val_from_vert(&new_opd)
                    );
                } else {
                    (match &res.tag {
                        VertTag::Phi(_) => Some(self.apply(op, opd, rc)),
                        _ if op == "mul" => Some(self.apply(op, opd, rc)),
                        // For offset operand of pointer operation, it should start from zero and
                        // accumulate along the reduction chain.
                        _ if op == "ptr" && i == 1 => {
                            let zero = ExtRc::new(SsaVert::new(
                                VertTag::Const(Const::I64(0)),
                                None,
                            ));
                            Some(self.apply("add", opd, &zero))
                        },
                        _ => None
                    }).map(|new_opd| {
                        *opd = new_opd.clone();
                        res.instr.borrow().as_ref().unwrap().1.src()[i].replace(
                            Self::val_from_vert(&new_opd)
                        )
                    });
                }
            });

            // Record this reduction
            self.red.insert(iv.clone(), Reduction {
                op: op.to_string(),
                rc: rc.clone(),
                res: res.clone(),
            });
            res.clone()
        })
    }

    /// Inserts an instruction to apply an operation with name `op` to two operands `fst` and `snd`
    /// and returns the result SSA vertex
    fn apply(&mut self, op: &str, fst: &VertRef, snd: &VertRef) -> VertRef {
        let expr = Expr(op.to_string(), fst.clone(), snd.clone());
        self.expr.get(&expr).cloned().unwrap_or_else(|| {
            if self.header.get(fst).is_some() && Self::is_rc(snd, &self.header[fst]) {
                self.reduce(op, fst, snd)
            } else if self.header.get(snd).is_some() && Self::is_rc(fst, &self.header[snd]) {
                self.reduce(op, snd, fst)
            } else {
                let vert = self.create_vert(op, fst, snd);
                self.expr.insert(expr, vert.clone());
                self.header.remove(&vert);
                vert
            }
        })
    }

    /// Follow the LFTR edges and return the SSA vertex of the last one in the chain
    fn follow_edges(&self, iv: &VertRef) -> VertRef {
        let mut last = self.red[iv].res.clone();
        loop {
            match self.red.get(&last) {
                Some(red) => last = red.res.clone(),
                None => return last
            }
        }
    }

    /// Apply the operations represented by the LFTR edges to a region constant and returns the
    /// SSA vertex of the result.
    fn apply_edges(&mut self, iv: &VertRef, rc: &VertRef) -> VertRef {
        match self.red.get(iv).cloned() {
            Some(red) => {
                let new_rc = self.apply(red.op.as_str(), rc, &red.rc);
                self.apply_edges(&red.res, &new_rc)
            }
            None => rc.clone()
        }
    }

    /// Create a new vertex with given operator and operands. Also insert the corresponding
    /// instruction at proper location.
    fn create_vert(&mut self, op: &str, fst: &VertRef, snd: &VertRef) -> VertRef {
        // Create pointer vertex if original operation is a pointer
        if fst.get_type().is_ptr() || snd.get_type().is_ptr() {
            return self.create_ptr(snd, fst)
        }

        let op = BinOp::from_str(op).unwrap();
        match (&fst.tag, &snd.tag) {
            // Do constant folding if possible
            (VertTag::Const(c1), VertTag::Const(c2)) => {
                // Create constant vertex
                let c = op.eval(*c1, *c2);
                let vert = ExtRc::new(SsaVert::new(VertTag::Const(c), None));
                self.graph.add(vert.clone(), None);
                vert
            }
            _ => {
                // Find possible block to insert
                let blk = self.block_to_insert(fst, snd);

                // Insert binary operation as instruction to block
                let fst_val = Self::val_from_vert(fst);
                let snd_val = Self::val_from_vert(snd);
                let ref dst_ty = op.res_type(&fst_val.get_type()).unwrap();
                let instr = ExtRc::new(Instr::Bin {
                    op,
                    fst: RefCell::new(fst_val),
                    snd: RefCell::new(snd_val),
                    dst: RefCell::new(self.gen.gen(dst_ty)),
                });
                blk.insert_before_ctrl(instr.clone());

                // Create value vertex for binary operation
                let vert = ExtRc::new(SsaVert::new(
                    VertTag::Value(op.to_string()),
                    Some((blk, instr)),
                ));
                vert.add_opd(fst.clone());
                vert.add_opd(snd.clone());
                self.graph.add(vert.clone(), None);
                vert
            }
        }
    }

    /// Create a new pointer operation vertex  with given base and offset. Also insert the
    /// corresponding instruction at proper location.
    fn create_ptr(&mut self, base: &VertRef, off: &VertRef) -> VertRef {
        // Find possible block to insert
        let blk = self.block_to_insert(base, off);

        // Insert pointer instruction to block
        let ptr_val = Self::val_from_vert(base);
        let dst_sym = self.gen.gen(&base.get_type());
        match &off.tag {
            // Insert just move instruction if the offset is zero
            VertTag::Const(Const::I64(0)) => {
                let instr = ExtRc::new(Instr::Mov {
                    src: RefCell::new(ptr_val),
                    dst: RefCell::new(dst_sym),
                });
                blk.insert_before_ctrl(instr);
                // return the original pointer since no new operation is introduced
                base.clone()
            }
            // Create new pointer instruction
            _ => {
                let off_val = Self::val_from_vert(off);
                let instr = ExtRc::new(Instr::Ptr {
                    base: RefCell::new(ptr_val),
                    off: Some(RefCell::new(off_val)),
                    ind: vec![],
                    dst: RefCell::new(dst_sym),
                });
                blk.insert_before_ctrl(instr.clone());

                // Create new value vertex for pointer operation
                let vert = ExtRc::new(SsaVert::new(
                    VertTag::Value("ptr".to_string()),
                    Some((blk, instr)),
                ));
                vert.add_opd(base.clone());
                vert.add_opd(off.clone());
                self.graph.add(vert.clone(), None);
                vert
            }
        }
    }

    /// Find the appropriate block to insert an instruction
    fn block_to_insert(&self, fst: &VertRef, snd: &VertRef) -> BlockRef {
        let mut blk = self.func.as_ref().unwrap().ent.borrow().clone();
        [fst, snd].iter().for_each(|v| {
            if let VertTag::Value(_) = &v.tag {
                let v_blk = v.instr.borrow().as_ref().unwrap().0.clone();
                if blk.strict_dom(&v_blk) {
                    blk = v_blk
                }
            }
        });
        blk
    }

    /// Create value from SSA vertex
    fn val_from_vert(v: &VertRef) -> Value {
        match &v.tag {
            VertTag::Const(c) => Value::Const(*c),
            VertTag::Value(_) | VertTag::Param(_) | VertTag::Phi(_) =>
                Value::Var(v.sym.borrow().as_ref().unwrap().clone()),
            _ => panic!("cannot create value from vertex {:?}", v.tag)
        }
    }

    /// Whether this value is a valid update of induction variable.
    fn is_iv_update(v: &VertRef) -> bool {
        match &v.tag {
            // Phi is always considered an IV
            VertTag::Phi(_) => true,
            // For other values, they must be updated by a region constant in each operation.
            // Only `add`, `sub` and `ptr` meet this requirement.
            VertTag::Value(op) if ["add", "sub", "ptr"].contains(&op.as_str()) => true,
            _ => false
        }
    }

    /// Whether this value is a region constant.
    fn is_rc(vert: &VertRef, header: &BlockRef) -> bool {
        match vert.tag {
            // A constant must be a region constant
            VertTag::Const(_) => true,
            // Parameters are defined in program entrance, which dominates every block
            VertTag::Param(_) => true,
            _ => match &vert.instr.borrow().as_ref() {
                // Whether the block defining this value dominates header of SCC
                Some((block, _)) => block.strict_dom(header),
                None => false
            }
        }
    }
}

#[test]
fn test_osr() {
    use crate::compile::lex::Lexer;
    use crate::compile::parse::Parser;
    use crate::compile::build::Builder;
    use crate::lang::print::Printer;
    use crate::vm::exec::Machine;

    use std::fs::File;
    use std::convert::TryFrom;
    use std::io::Read;
    use std::io::stdout;
    use std::borrow::BorrowMut;

    let mut file = File::open("test/sum.ir").unwrap();
    let lexer = Lexer::try_from(&mut file as &mut dyn Read).unwrap();
    let parser = Parser::new(lexer);
    let tree = parser.parse().unwrap();
    let builder = Builder::new(tree);
    let mut pro = builder.build().unwrap();

    let mut mach = Machine::new();
    let rcd = mach.run(&pro).unwrap();
    println!("orig: {:?}", rcd);

    let mut opt = OsrOpt::new();
    Pass::opt(&mut opt, &mut pro);

    let rcd = mach.run(&pro).unwrap();
    println!("opt: {:?}", rcd);

    let mut out = stdout();
    let mut printer = Printer::new(out.borrow_mut());
    printer.print(&pro).unwrap();
}