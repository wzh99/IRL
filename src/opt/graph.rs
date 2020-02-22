use std::borrow::Borrow;
use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::{Debug, Error, Formatter};

use crate::lang::func::{BlockListener, BlockRef, Func};
use crate::lang::instr::{Instr, InstrRef};
use crate::lang::ssa::InstrListener;
use crate::lang::util::ExtRc;
use crate::lang::val::{Const, Symbol, SymbolRef};

#[derive(Debug)]
pub struct SsaVert {
    /// Identify category of this vertex
    pub tag: VertTag,
    /// Operands that are used to define this value (use -> def)
    pub opd: RefCell<Vec<VertRef>>,
    /// Uses of this value (def -> use)
    pub uses: RefCell<Vec<VertRef>>,
}

pub type VertRef = ExtRc<SsaVert>;

impl Debug for VertRef {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> { self.tag.fmt(f) }
}

impl VertRef {
    pub fn add_opd(&self, opd: VertRef) {
        self.opd.borrow_mut().push(opd.clone());
        opd.uses.borrow_mut().push(self.clone());
    }
}

#[derive(Debug, Eq, PartialEq)]
pub enum VertTag {
    /// This value is defined by parameter.
    Param,
    /// This is a constant.
    Const(Const),
    /// Variables that can be considered as SSA values, identified by its operation name.
    Value(String),
    /// Variable produced by phi instruction.
    /// This should be list separately from other instructions, because the incoming blocks of a
    /// phi instruction also contribute to its identity.
    Phi(Vec<Option<BlockRef>>),
    /// Memory locations that cannot be considered as SSA values, including global variables,
    /// heap-allocated memory, etc.
    Cell,
    /// Refer to instructions that use values but never produce new one, like `br`, `ret`, etc.
    /// Also identified by its name
    Consume(String),
}

pub struct SsaGraph {
    /// Keep all the vertices.
    pub vert: Vec<VertRef>,
    /// Map symbols to their vertices
    pub map: HashMap<SymbolRef, VertRef>,
}

impl SsaGraph {
    pub fn new() -> SsaGraph {
        SsaGraph {
            vert: vec![],
            map: Default::default(),
        }
    }
    pub fn add(&mut self, v: VertRef, sym: Option<SymbolRef>) {
        self.vert.push(v.clone());
        sym.map(|sym| self.map.insert(sym, v));
    }
}

pub struct GraphBuilder {
    /// Hold SSA graph
    graph: SsaGraph,
}

impl GraphBuilder {
    pub fn new() -> GraphBuilder {
        GraphBuilder {
            graph: SsaGraph::new(),
        }
    }
}

impl BlockListener for GraphBuilder {
    fn on_begin(&mut self, func: &Func) {
        // Create vertices for parameters
        func.param.iter().for_each(|param| {
            let param = param.borrow().clone();
            if let Symbol::Local { name: _, ty: _, ver: _ } = param.as_ref() {
                let vert = ExtRc::new(SsaVert {
                    tag: VertTag::Param,
                    opd: RefCell::new(vec![]),
                    uses: RefCell::new(vec![]),
                });
                self.graph.add(vert.clone(), Some(param));
            } else { unreachable!() }
        });

        InstrListener::on_begin(self, func)
    }

    fn on_end(&mut self, _: &Func) {}

    fn on_enter(&mut self, block: BlockRef) {
        InstrListener::on_enter(self, block)
    }

    fn on_exit(&mut self, _: BlockRef) {}

    fn on_enter_child(&mut self, _: BlockRef, _: BlockRef) {}

    fn on_exit_child(&mut self, _: BlockRef, _: BlockRef) {}
}

impl InstrListener for GraphBuilder {
    fn on_access(&mut self, _: BlockRef) {}

    fn on_instr(&mut self, instr: InstrRef) {
        unimplemented!()
    }

    fn on_succ_phi(&mut self, this: Option<BlockRef>, instr: InstrRef) {
        unimplemented!()
    }
}
