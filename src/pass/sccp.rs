use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::ops::Deref;

use crate::lang::func::{BlockRef, FnRef};
use crate::lang::inst::{BinOp, PhiSrc, UnOp};
use crate::lang::inst::Inst;
use crate::lang::Program;
use crate::lang::util::{ExtRc, WorkList};
use crate::lang::value::{Const, Symbol, SymbolRef, Value};
use crate::pass::{FnPass, Pass};
use crate::pass::graph::{GraphBuilder, SsaGraph, VertRef, VertTag};

/// Sparse Conditional Constant Propagation
pub struct SccpOpt {
    /// SSA value graph for the function being optimized
    graph: SsaGraph,
    /// CFG edge work list
    cfg_work: WorkList<CfgEdge>,
    /// Value graph edge work list
    ssa_work: WorkList<SsaEdge>,
    /// Map symbols to lattice values
    /// For values that are constants, lattice values are created when used, no lookup is needed.
    lat: HashMap<SymbolRef, LatVal>,
    /// Visited CFG edges
    edge_vis: HashSet<CfgEdge>,
    /// Visited instructions
    blk_vis: HashSet<BlockRef>,
}

/// Represent an edge in the control flow graph.
/// In the original SCCP algorithm, it is assumed that a basic block contains several phi
/// instructions, following by only one assignment. However, trivial edges (which only contain
/// assignment instruction) can be ignored in the implementation.
#[derive(Eq, PartialEq, Clone, Hash, Debug)]
struct CfgEdge {
    from: Option<BlockRef>,
    to: BlockRef,
}

/// Represent an edge in SSA value graph.
/// The data flow from definition point (where a value is defined) to one of its use point.
#[derive(Eq, PartialEq, Hash, Clone, Debug)]
struct SsaEdge {
    def: VertRef,
    us: VertRef, // `use` is a keyword in Rust
}

/// Lattice value for indicating 'constantness' for SSA values
#[derive(Eq, PartialEq, Copy, Clone, Debug)]
enum LatVal {
    /// Yet-undetermined value
    Top,
    /// Determined irc-time constant
    Const(Const),
    /// Not constant or cannot be determined to be constant
    Bottom,
}

impl LatVal {
    fn is_const(&self) -> bool {
        match self {
            LatVal::Const(_) => true,
            _ => false
        }
    }

    fn meet(self, rhs: Self) -> Self {
        match (self, rhs) {
            (LatVal::Top, LatVal::Top) => LatVal::Top,
            (LatVal::Top, LatVal::Const(c)) | (LatVal::Const(c), LatVal::Top) => LatVal::Const(c),
            (LatVal::Bottom, _) | (_, LatVal::Bottom) => LatVal::Bottom,
            (LatVal::Const(l), LatVal::Const(r)) =>
                if l == r { LatVal::Const(l) } else { LatVal::Bottom }
        }
    }
}

impl Pass for SccpOpt {
    fn run(&mut self, pro: &mut Program) { FnPass::run(self, pro) }
}

impl FnPass for SccpOpt {
    fn run_on_fn(&mut self, func: &FnRef) {
        // Create value graph.
        let mut builder = GraphBuilder::new();
        func.walk_dom(&mut builder);
        self.graph = builder.graph;

        // Initialize table for all interested values.
        self.lat = self.graph.map.iter().map(|(sym, vert)| {
            match &vert.tag {
                // Symbols defined by constants are sure to be constants.
                VertTag::Const(c) => (sym.clone(), LatVal::Const(c.clone())),
                // Variable and phi vertices are yet to be determined.
                VertTag::Value(_) | VertTag::Phi(_) => (sym.clone(), LatVal::Top),
                // Other kind of vertices are not in consideration, do not make any decision about
                // their constantness.
                _ => (sym.clone(), LatVal::Bottom)
            }
        }).collect();

        // Perform symbolic execution of CFG and SSA.
        self.cfg_work.insert(CfgEdge {
            from: None,
            to: func.ent.borrow().clone(),
        });
        while !self.cfg_work.is_empty() || !self.ssa_work.is_empty() {
            if !self.cfg_work.is_empty() {
                self.visit_cfg()
            }
            if !self.ssa_work.is_empty() {
                self.visit_ssa()
            }
        }

        // Apply code replacement
        func.dfs().for_each(|block| {
            block.inst.borrow_mut().retain(|instr| {
                // Remove constant definition
                match instr.dst() {
                    Some(dst) if self.lat_from_sym(dst).is_const() => { return false; }
                    _ => {}
                }
                // Possibly replace symbols with constants
                instr.src().iter().for_each(|opd| {
                    if let LatVal::Const(c) = self.lat_from_val(opd) {
                        opd.replace(Value::Const(c));
                    }
                });
                true
            });

            // Remove unreachable blocks
            match block.tail().as_ref() {
                Inst::Br { cond, tr, fls } => match self.lat_from_val(cond) {
                    LatVal::Const(Const::I1(c)) => {
                        let (tgt, rm) = if c {
                            (tr.borrow().clone(), fls.borrow().clone())
                        } else {
                            (fls.borrow().clone(), tr.borrow().clone())
                        };
                        *block.inst.borrow_mut().back_mut().unwrap() = ExtRc::new(
                            Inst::Jmp { tgt: RefCell::new(tgt) }
                        );
                        block.disconnect(&rm);
                    }
                    _ => {}
                }
                _ => {}
            }
        });
        func.remove_unreachable();

        // Rebuild dominator tree and scope, since the structure of CFG may have changed
        func.build_dom();
        func.rebuild_ssa_scope();

        // Clear all data structure for this function.
        self.lat.clear();
        self.edge_vis.clear();
        self.blk_vis.clear();
    }
}

impl SccpOpt {
    pub fn new() -> SccpOpt {
        SccpOpt {
            graph: SsaGraph::new(),
            cfg_work: WorkList::new(),
            ssa_work: WorkList::new(),
            lat: Default::default(),
            edge_vis: Default::default(),
            blk_vis: Default::default(),
        }
    }

    fn visit_cfg(&mut self) {
        // Possibly visit this edge if it has not been not visited
        let edge = self.cfg_work.pick().unwrap();
        if self.edge_vis.contains(&edge) { return; }
        self.edge_vis.insert(edge.clone());

        // Visit all instructions in this block
        let block = edge.to;
        self.blk_vis.insert(block.clone());
        for instr in block.inst.borrow().iter() {
            match instr.deref() {
                Inst::Phi { src, dst } => self.eval_phi(src, dst),
                Inst::Jmp { tgt } => self.cfg_work.insert(CfgEdge {
                    from: Some(block.clone()),
                    to: tgt.borrow().clone(),
                }),
                Inst::Br { cond, tr, fls } => self.eval_br(cond, tr, fls, &block),
                Inst::Ret { val: _ } => return,
                instr if instr.is_assign() => self.eval_assign(instr),
                _ => continue
            }
        }
    }

    fn visit_ssa(&mut self) {
        // Pick one SSA edge from work list.
        let edge = self.ssa_work.pick().unwrap();
        let (block, instr) = match edge.us.instr.borrow().clone() {
            Some(pair) => pair,
            None => return
        };
        // reject this instruction, if it is not visited in CFG
        if !self.blk_vis.contains(&block) { return; }

        match instr.deref() {
            Inst::Phi { src, dst } => self.eval_phi(src, dst),
            Inst::Br { cond, tr, fls } => self.eval_br(cond, tr, fls, &block),
            instr if instr.is_assign() => self.eval_assign(instr),
            _ => {}
        }
    }

    fn eval_phi(&mut self, src: &Vec<PhiSrc>, dst: &RefCell<SymbolRef>) {
        // Evaluate meet operation on operand lattice values
        let prev_lat = self.lat_from_sym(dst);
        let new_lat = src.iter().map(|(_, val)| self.lat_from_val(val))
            .fold(LatVal::Top, LatVal::meet);

        // Update lattice value if it has changed
        if prev_lat != new_lat {
            self.update_sym(dst, new_lat)
        }
    }

    fn eval_br(&mut self, cond: &RefCell<Value>, tr: &RefCell<BlockRef>, fls: &RefCell<BlockRef>,
               blk: &BlockRef)
    {
        let tr_edge = CfgEdge { from: Some(blk.clone()), to: tr.borrow().clone() };
        let fls_edge = CfgEdge { from: Some(blk.clone()), to: fls.borrow().clone() };
        match self.lat_from_val(cond) {
            LatVal::Const(Const::I1(cond)) =>
                self.cfg_work.insert(if cond { tr_edge } else { fls_edge }),
            _ => {
                self.cfg_work.insert(tr_edge);
                self.cfg_work.insert(fls_edge);
            }
        }
    }

    fn eval_assign(&mut self, instr: &Inst) {
        // Decide whether this instruction should be evaluated.
        let dst = instr.dst().unwrap();
        let prev_lat = self.lat_from_sym(dst);
        if prev_lat == LatVal::Bottom { return; } // no point in computing lattice value

        // Propagate constant according to instruction type.
        let new_lat = match instr {
            Inst::Un { op, opd, dst: _ } => self.eval_un(*op, self.lat_from_val(opd)),
            Inst::Bin { op, fst, snd, dst: _ } =>
                self.eval_bin(*op, self.lat_from_val(fst), self.lat_from_val(snd)),
            // Skip move instruction, since their constantness depend on the symbol moved to it.
            Inst::Mov { src: _, dst: _ } => return,
            // Cannot compute lattice values for other instructions.
            _ => LatVal::Bottom
        };

        // Update lattice value if it has changed
        if new_lat != prev_lat {
            self.update_sym(dst, new_lat)
        }
    }

    fn update_sym(&mut self, sym: &RefCell<SymbolRef>, lat: LatVal) {
        *self.lat.get_mut(sym.borrow().deref()).unwrap() = lat;
        let vert = self.graph.find(sym.borrow().deref()).unwrap();
        vert.uses.borrow().iter().for_each(
            |u| self.ssa_work.insert(SsaEdge { def: vert.clone(), us: u.clone() })
        );
    }

    fn lat_from_sym(&self, sym: &RefCell<SymbolRef>) -> LatVal {
        match sym.borrow().as_ref() {
            _ if sym.borrow().is_local_var() => *self.lat.get(sym.borrow().deref()).unwrap(),
            Symbol::Global(_) => LatVal::Bottom,
            _ => unreachable!()
        }
    }

    fn lat_from_val(&self, val: &RefCell<Value>) -> LatVal {
        match val.borrow().deref() {
            Value::Var(sym) if sym.is_local_var() => self.lat.get(sym).unwrap().clone(),
            Value::Var(_) => LatVal::Bottom,
            Value::Const(c) => LatVal::Const(c.clone())
        }
    }

    fn eval_un(&self, op: UnOp, opd: LatVal) -> LatVal {
        match opd {
            LatVal::Top | LatVal::Bottom => opd,
            LatVal::Const(c) => LatVal::Const(op.eval(c))
        }
    }

    fn eval_bin(&self, op: BinOp, lhs: LatVal, rhs: LatVal) -> LatVal {
        match (lhs, rhs) {
            // At lease one is undetermined and the other is constant, still undetermined
            (LatVal::Top, LatVal::Top) | (LatVal::Top, LatVal::Const(_))
            | (LatVal::Const(_), LatVal::Top) => LatVal::Top,
            // Two variables could only produce variables
            (LatVal::Bottom, LatVal::Bottom) => LatVal::Bottom,
            // An undetermined value with a variable could possibly produce constant, if the
            // operator support short circuit evaluation.
            // Short circuit evaluation means the result is always a constant when one of two
            // operands is a certain constant, no matter what the other value is. Since one
            // operand is `Top`, it may be lowered to `Const` and short-circuit this evaluation.
            // At present, these five cases are short-circuit evaluations:
            // 0 * x = 0, x && false = false, x & 0 = 0, x || true = true, x | -1 = -1.
            (LatVal::Top, LatVal::Bottom) | (LatVal::Bottom, LatVal::Top) => match op {
                BinOp::Mul | BinOp::And | BinOp::Or => LatVal::Top,
                _ => LatVal::Bottom
            }
            (LatVal::Const(c), LatVal::Bottom) | (LatVal::Bottom, LatVal::Const(c)) => {
                match op {
                    BinOp::Mul => match c {
                        Const::I64(0) => LatVal::Const(Const::I64(0)),
                        _ => LatVal::Bottom
                    }
                    BinOp::And => match c {
                        Const::I1(false) => LatVal::Const(Const::I1(false)),
                        Const::I64(0) => LatVal::Const(Const::I64(0)),
                        _ => LatVal::Bottom
                    }
                    BinOp::Or => match c {
                        Const::I1(true) => LatVal::Const(Const::I1(true)),
                        Const::I64(-1) => LatVal::Const(Const::I64(-1)),
                        _ => LatVal::Bottom
                    }
                    _ => LatVal::Bottom
                }
            }
            (LatVal::Const(l), LatVal::Const(r)) => LatVal::Const(op.eval(l, r))
        }
    }
}

#[test]
fn test_sccp() {
    use crate::irc::lex::Lexer;
    use crate::irc::parse::Parser;
    use crate::irc::build::Builder;
    use crate::lang::print::Printer;
    use std::io::stdout;
    use std::fs::File;
    use std::convert::TryFrom;
    use std::io::Read;
    use std::borrow::BorrowMut;

    let mut file = File::open("test/sccp.ir").unwrap();
    let lexer = Lexer::try_from(&mut file as &mut dyn Read).unwrap();
    let parser = Parser::new(lexer);
    let tree = parser.parse().unwrap();
    let builder = Builder::new(tree);
    let mut pro = builder.build().unwrap();
    let mut opt = SccpOpt::new();
    Pass::run(&mut opt, &mut pro);

    let mut out = stdout();
    let mut printer = Printer::new(out.borrow_mut());
    printer.print(&pro).unwrap();
}
