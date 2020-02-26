use std::collections::{HashMap, HashSet};
use std::ops::Deref;

use crate::lang::func::Func;
use crate::lang::instr::{BinOp, InstrRef, UnOp};
use crate::lang::Program;
use crate::lang::util::WorkList;
use crate::lang::value::Const;
use crate::opt::{FnPass, Pass};
use crate::opt::graph::{GraphBuilder, ValueGraph, VertRef, VertTag};

/// Sparse Conditional Constant Propagation
pub struct SccpOpt {
    /// SSA value graph for the function being optimized
    graph: ValueGraph,
    /// CFG edge work list
    cfg_work: WorkList<CfgEdge>,
    /// Value graph edge work list
    ssa_work: WorkList<SsaEdge>,
    /// Map value graph vertices to lattice values
    lat: HashMap<VertRef, LatVal>,
    /// Visited CFG edges
    cfg_vis: HashSet<CfgEdge>,
    /// Visited instructions
    instr_vis: HashSet<InstrRef>,
}

/// Represent an edge in the control flow graph.
/// In the original SCCP algorithm, it is assumed that a basic block contains several phi
/// instructions, following by only one assignment. However, trivial edges (which only contain
/// assignment instruction) can be ignored in the implementation.
#[derive(Eq, PartialEq, Hash, Debug)]
struct CfgEdge {
    from: Option<InstrRef>,
    to: InstrRef,
}

/// Represent an edge in SSA value graph.
/// The data flow from definition point (where a value is defined) to one of its use point.
#[derive(Eq, PartialEq, Hash, Debug)]
struct SsaEdge {
    def: VertRef,
    us: VertRef, // `use` is a keyword in Rust
}

/// Lattice value for indicating 'constantness' for SSA values
#[derive(Eq, PartialEq, Copy, Clone, Debug)]
enum LatVal {
    /// Yet-undetermined value
    Top,
    /// Determined compile-time constant
    Const(Const),
    /// Not constant or cannot be determined to be constant
    Bottom,
}

impl Pass for SccpOpt {
    fn opt(&mut self, pro: &mut Program) { FnPass::opt(self, pro) }
}

impl FnPass for SccpOpt {
    fn opt_fn(&mut self, func: &Func) {
        // Create value graph
        let mut builder = GraphBuilder::new();
        func.walk_dom(&mut builder);
        self.graph = builder.graph;

        // Mark constants in lattice value table
        let const_vert: Vec<VertRef> = self.graph.vert.iter().filter(|v| {
            if let VertTag::Const(_) = &v.tag { true } else { false }
        }).cloned().collect();
        const_vert.iter().for_each(|v| {
            if let VertTag::Const(c) = &v.tag {
                self.lat.insert(v.clone(), LatVal::Const(c.clone()));
            } else { unreachable!() }
        });

        // Perform symbolic execution with help of CFG and SSA work lists
        self.cfg_work.add(CfgEdge {
            from: None,
            to: func.ent.borrow().tail(),
        });
        while !self.cfg_work.is_empty() || !self.ssa_work.is_empty() {
            if !self.cfg_work.is_empty() {
                self.visit_cfg()
            }
            if !self.ssa_work.is_empty() {
                self.visit_ssa()
            }
        }

        // Clear all data structure for this function
        self.lat.clear();
        self.cfg_vis.clear();
        self.instr_vis.clear();
    }
}

impl SccpOpt {
    pub fn new() -> SccpOpt {
        SccpOpt {
            graph: ValueGraph::new(),
            cfg_work: WorkList::new(),
            ssa_work: WorkList::new(),
            lat: Default::default(),
            cfg_vis: Default::default(),
            instr_vis: Default::default(),
        }
    }

    fn visit_cfg(&mut self) {}

    fn visit_ssa(&mut self) {}

    fn eval_un(&self, op: UnOp, opd: LatVal) -> LatVal {
        match opd {
            LatVal::Top | LatVal::Bottom => opd,
            LatVal::Const(c) => match op {
                UnOp::Not => LatVal::Const(!c),
                UnOp::Neg => LatVal::Const(-c),
            }
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
            (LatVal::Const(l), LatVal::Const(r)) => match op {
                BinOp::Add => LatVal::Const(l + r),
                BinOp::Sub => LatVal::Const(l - r),
                BinOp::Mul => LatVal::Const(l * r),
                BinOp::Div => LatVal::Const(l / r),
                BinOp::Mod => LatVal::Const(l % r),
                BinOp::Shl => LatVal::Const(l << r),
                BinOp::Shr => LatVal::Const(l >> r),
                BinOp::And => LatVal::Const(l & r),
                BinOp::Or => LatVal::Const(l | r),
                BinOp::Xor => LatVal::Const(l ^ r),
                BinOp::Eq => LatVal::Const(l.e(r)),
                BinOp::Ne => LatVal::Const(l.n(r)),
                BinOp::Lt => LatVal::Const(l.lt(r)),
                BinOp::Le => LatVal::Const(l.le(r)),
                BinOp::Gt => LatVal::Const(l.gt(r)),
                BinOp::Ge => LatVal::Const(l.ge(r)),
            }
        }
    }
}
