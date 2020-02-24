use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::{Debug, Error, Formatter};
use std::ops::Deref;

use crate::lang::func::{BlockListener, BlockRef, Func};
use crate::lang::instr::{Instr, InstrRef};
use crate::lang::ssa::InstrListener;
use crate::lang::util::ExtRc;
use crate::lang::val::{Const, Symbol, SymbolRef, Value};

#[derive(Debug)]
pub struct SsaVert {
    /// Identify category of this vertex
    pub tag: VertTag,
    /// Operands that are used to define this value (use -> def)
    pub opd: RefCell<Vec<VertRef>>,
    /// Uses of this value (def -> use)
    pub uses: RefCell<Vec<VertRef>>,
}

impl SsaVert {
    pub fn new(tag: VertTag) -> SsaVert {
        SsaVert {
            tag,
            opd: RefCell::new(vec![]),
            uses: RefCell::new(vec![]),
        }
    }
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
    Param(String),
    /// This is a constant.
    Const(Const),
    /// Variables that can be considered as SSA values, identified by its operation name.
    /// Additional information can be provided, to further identify variables.
    Var { op: String, id: Option<String> },
    /// Variable produced by phi instruction.
    /// This should be list separately from other instructions, because the incoming blocks of a
    /// phi instruction also contribute to its identity.
    Phi(Vec<Option<BlockRef>>),
    /// Variables that cannot be considered as SSA values, including global variables, values
    /// loaded from pointer, etc. The associated datum is the id of the symbol that refer to this
    ///value.
    Cell(String),
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

    /// Add vertex `v` to the graph, possibly map `sym` to `v` if it is not `None`.
    pub fn add(&mut self, v: VertRef, sym: Option<SymbolRef>) {
        self.vert.push(v.clone());
        sym.map(|sym| self.map.insert(sym, v));
    }

    /// Maps `sym` to a existing vertex `v`
    pub fn map(&mut self, sym: SymbolRef, v: VertRef) {
        self.map.insert(sym, v);
    }

    pub fn search(&self, sym: &SymbolRef) -> Option<VertRef> {
        self.map.get(sym).cloned()
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
                let vert = ExtRc::new(SsaVert::new(
                    VertTag::Param(param.id())
                ));
                self.graph.add(vert.clone(), Some(param));
            } else { unreachable!() }
        });

        InstrListener::on_begin(self, func)
    }

    fn on_end(&mut self, _: &Func) {}

    fn on_enter(&mut self, block: BlockRef) { InstrListener::on_enter(self, block) }

    fn on_exit(&mut self, _: BlockRef) {}

    fn on_enter_child(&mut self, _: BlockRef, _: BlockRef) {}

    fn on_exit_child(&mut self, _: BlockRef, _: BlockRef) {}
}

impl InstrListener for GraphBuilder {
    fn on_access(&mut self, _: BlockRef) {}

    fn on_instr(&mut self, instr: InstrRef) {
        match instr.deref() {
            Instr::Phi { src: _, dst: _ } => (), // only the ones in successors are considered
            Instr::Mov { src, dst } => {
                let src = self.build_value(src.borrow().deref(), None);
                match &src.tag {
                    // can be regarded as equivalent
                    VertTag::Var { op: _, id: _ } | VertTag::Param(_) | VertTag::Const(_)
                    | VertTag::Phi(_) | VertTag::Cell(_) =>
                        self.graph.map(dst.borrow().clone(), src),
                    // consume vertex has no symbol map
                    VertTag::Consume(_) => unreachable!(),
                }
            }
            _ => unimplemented!()
        }
    }

    fn on_succ_phi(&mut self, _: Option<BlockRef>, _: InstrRef) {
        unimplemented!()
    }
}

impl GraphBuilder {
    /// Possibly build or find SSA vertex from given `Value` argument.
    /// Name of the operation must be provided if a new variable vertex is to be created.
    fn build_value(&self, val: &Value, op: Option<String>) -> VertRef {
        match val {
            Value::Var(sym) => match sym.deref() {
                Symbol::Local { name: _, ty: _, ver: _ } => self.graph.search(sym)
                    .unwrap_or(ExtRc::new(SsaVert::new(
                        VertTag::Var { op: op.unwrap(), id: None }
                    ))),
                Symbol::Global(_) => self.graph.search(sym).unwrap_or(
                    ExtRc::new(SsaVert::new(
                        VertTag::Cell(sym.id())
                    ))
                ),
                _ => unreachable!()
            },
            Value::Const(c) => ExtRc::new(SsaVert::new(VertTag::Const(c.clone())))
        }
    }
}
