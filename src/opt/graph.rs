use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::{Debug, Error, Formatter};
use std::mem::swap;
use std::ops::Deref;

use crate::lang::func::{BlockListener, BlockRef, Func};
use crate::lang::instr::{Instr, InstrRef, PhiSrc};
use crate::lang::ssa::InstrListener;
use crate::lang::util::ExtRc;
use crate::lang::value::{Const, Symbol, SymbolRef, Value};

#[derive(Debug)]
pub struct ValueVert {
    /// Identify category of this vertex
    pub tag: VertTag,
    /// Operands that are used to define this value (use -> def)
    pub opd: RefCell<Vec<VertRef>>,
    /// Uses of this value (def -> use)
    pub uses: RefCell<Vec<VertRef>>,
    /// Instruction that define this value, along with its block
    /// This field maybe `None` if the this vertex does not have a corresponding instruction.
    pub instr: Option<(InstrRef, BlockRef)>,
}

impl ValueVert {
    pub fn new(tag: VertTag, instr: Option<(InstrRef, BlockRef)>) -> ValueVert {
        ValueVert {
            tag,
            opd: RefCell::new(vec![]),
            uses: RefCell::new(vec![]),
            instr,
        }
    }
}

pub type VertRef = ExtRc<ValueVert>;

impl Debug for VertRef {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> { self.tag.fmt(f) }
}

impl VertRef {
    pub fn add_opd(&self, opd: VertRef) {
        self.opd.borrow_mut().push(opd.clone());
        match opd.deref().tag {
            VertTag::PlaceHolder => {}
            _ => opd.uses.borrow_mut().push(self.clone())
        }
    }
}

#[derive(PartialOrd, Debug)]
pub enum VertTag {
    /// This value is defined by parameter.
    Param(String),
    /// This is a constant.
    Const(Const),
    /// Variables that can be considered as SSA values, identified by its operation name.
    /// Additional information can be provided, to further identify variables.
    Var(String),
    /// Variable produced by phi instruction.
    /// This should be list separately from other instructions, because the incoming blocks of a
    /// phi instruction also contribute to its identity.
    Phi(Vec<Option<BlockRef>>),
    /// Variables that cannot be considered as SSA values, including global variables, values
    /// loaded from pointer, etc. The associated datum is the identifier of the symbol that refer
    /// to this value.
    Cell(String),
    /// Refer to instructions that use values but never produce new one, like `br`, `ret`, etc.
    /// Also identified by its name.
    Consume(String),
    /// Placeholder for vertices.
    /// It has two uses: for padding to make corresponding operands align; for indicating
    /// temporarily unresolved vertices..
    PlaceHolder,
}

impl PartialEq for VertTag {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            // Two parameter vertices are equivalent if they are created from the same parameter.
            (VertTag::Param(s1), VertTag::Param(s2)) => s1 == s2,
            // Two constant vertices are equivalent if their values are equal.
            (VertTag::Const(c1), VertTag::Const(c2)) => c1 == c2,
            // Two variable vertices are equivalent if their operation tags are identical.
            (VertTag::Var(op1), VertTag::Var(op2)) => op1 == op2,
            // Two phi vertices are equivalent if their incoming blocks are pairwise identical.
            (VertTag::Phi(v1), VertTag::Phi(v2)) => v1 == v2,
            // For other cases, they cannot be equivalent.
            _ => false
        }
    }
}

pub struct ValueGraph {
    /// Keep all the vertices.
    pub vert: Vec<VertRef>,
    /// Map local variables to their vertices
    pub map: HashMap<SymbolRef, VertRef>,
}

impl ValueGraph {
    pub fn new() -> ValueGraph {
        ValueGraph {
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
    pub fn map(&mut self, sym: SymbolRef, v: VertRef) { self.map.insert(sym, v); }

    pub fn find(&self, sym: &SymbolRef) -> Option<VertRef> { self.map.get(sym).cloned() }
}

pub struct GraphBuilder {
    /// Hold SSA graph
    pub graph: ValueGraph,
    /// The block currently visiting
    block: Option<BlockRef>,
}

impl GraphBuilder {
    pub fn new() -> GraphBuilder {
        GraphBuilder {
            graph: ValueGraph::new(),
            block: None,
        }
    }
}

impl BlockListener for GraphBuilder {
    fn on_begin(&mut self, func: &Func) {
        // Create vertices for parameters
        func.param.iter().for_each(|param| {
            let param = param.borrow().clone();
            if let Symbol::Local { name: _, ty: _, ver: _ } = param.as_ref() {
                let vert = ExtRc::new(ValueVert::new(
                    VertTag::Param(param.id()),
                    None,
                ));
                self.graph.add(vert.clone(), Some(param));
            } else { unreachable!() }
        });

        InstrListener::on_begin(self, func)
    }

    fn on_end(&mut self, _: &Func) {}

    fn on_enter(&mut self, block: BlockRef) {
        self.block = Some(block.clone());
        InstrListener::on_enter(self, block)
    }

    fn on_exit(&mut self, _: BlockRef) {}

    fn on_enter_child(&mut self, _: BlockRef, _: BlockRef) {}

    fn on_exit_child(&mut self, _: BlockRef, _: BlockRef) {}
}

impl InstrListener for GraphBuilder {
    fn on_instr(&mut self, instr: InstrRef) {
        match instr.deref() {
            // Create vertex for phi destination if it has not been created, since it may be used
            // in following instructions.
            Instr::Phi { src, dst } =>
                if self.graph.find(dst.borrow().deref()).is_none() {
                    self.build_phi(src, dst, &instr);
                }
            Instr::Mov { src, dst } => self.build_move(src, dst),
            Instr::Un { op, opd, dst } => {
                let opd = self.get_src_vert(opd);
                let dst = self.get_dst_vert(dst, op.to_string(), Some(&instr));
                dst.add_opd(opd);
            }
            Instr::Bin { op, fst, snd, dst } => {
                let mut fst = self.get_src_vert(fst);
                let mut snd = self.get_src_vert(snd);
                // impose order of operands if the operator is commutative
                if op.is_comm() && fst.tag > snd.tag {
                    swap(&mut fst, &mut snd)
                }
                let dst = self.get_dst_vert(dst, op.to_string(), Some(&instr));
                dst.add_opd(fst);
                dst.add_opd(snd);
            }
            Instr::Call { func, arg, dst } => {
                // Function returns are not SSA value. Because a function may modify global
                // variables, and it may return different values even with the same parameters.
                let dst_vert = ExtRc::new(ValueVert::new(
                    VertTag::Cell(func.name.clone()),
                    Some((instr.clone(), self.block.clone().unwrap())),
                ));
                self.graph.add(dst_vert.clone(), dst.as_ref().map(|dst| dst.borrow().clone()));
                for a in arg {
                    let a = self.get_src_vert(a);
                    dst_vert.add_opd(a);
                }
            }
            Instr::Ret { val } => {
                let vert = ExtRc::new(ValueVert::new(
                    VertTag::Consume("ret".to_string()),
                    Some((instr.clone(), self.block.clone().unwrap())),
                ));
                val.as_ref().map(|val| {
                    let src = self.get_src_vert(val);
                    vert.add_opd(src.clone());
                });
                self.graph.add(vert, None);
            }
            Instr::Jmp { tgt: _ } => {} // nothing to do
            Instr::Br { cond, tr: _, fls: _ } => {
                let vert = ExtRc::new(ValueVert::new(
                    VertTag::Consume("br".to_string()),
                    Some((instr.clone(), self.block.clone().unwrap())),
                ));
                let cond = self.get_src_vert(cond);
                vert.add_opd(cond);
                self.graph.add(vert, None);
            }
            Instr::Alloc { dst } => {
                self.get_dst_vert(dst, format!("alloc->{}", dst.borrow().to_string()),
                                  Some(&instr));
            }
            Instr::Ptr { base, off, ind, dst } =>
                self.build_ptr(base, off, ind, dst, &instr),
            Instr::Ld { ptr, dst } => {
                let ptr = self.get_src_vert(ptr);
                let dst_vert = ExtRc::new(ValueVert::new(
                    VertTag::Cell(dst.borrow().id()),
                    Some((instr.clone(), self.block.clone().unwrap())),
                ));
                dst_vert.add_opd(ptr.clone());
                self.graph.add(dst_vert, Some(dst.borrow().clone()))
            }
            Instr::St { src, ptr } => {
                let vert = ExtRc::new(ValueVert::new(
                    VertTag::Consume("st".to_string()),
                    Some((instr.clone(), self.block.clone().unwrap())),
                ));
                let src = self.get_src_vert(src);
                vert.add_opd(src);
                let ptr = self.get_src_vert(ptr);
                vert.add_opd(ptr);
                self.graph.add(vert, None);
            }
        }
    }

    fn on_succ_phi(&mut self, this: Option<BlockRef>, instr: InstrRef) {
        // Create vertex for destination, if not created before.
        let dst = instr.dst().unwrap();
        let dst_vert = self.graph.find(&dst.borrow().deref()).unwrap_or_else(|| {
            if let Instr::Phi { src, dst: _ } = instr.deref() {
                self.build_phi(src, dst, &instr)
            } else { unreachable!() }
        });

        // Find corresponding position of current block in phi sources, replace placeholder with
        // real vertex.
        if let Instr::Phi { src, dst: _ } = instr.deref() {
            let idx = src.iter().position(|(pred, _)| *pred == this).unwrap();
            let val = &src.get(idx).unwrap().1;
            let src_vert = self.get_src_vert(val);
            *dst_vert.opd.borrow_mut().get_mut(idx).unwrap() = src_vert.clone();
            src_vert.uses.borrow_mut().push(dst_vert);
        } else { unreachable!() };
    }
}

impl GraphBuilder {
    /// Build incomplete phi vertex.
    fn build_phi(&mut self, src: &Vec<PhiSrc>, dst: &RefCell<SymbolRef>, instr: &InstrRef)
                 -> VertRef
    {
        let dst = dst.borrow().clone();
        let pred: Vec<Option<BlockRef>> = src.iter()
            .map(|(pred, _)| pred.clone()).collect();
        let vert = ExtRc::new(ValueVert::new(
            VertTag::Phi(pred.clone()),
            Some((instr.clone(), self.block.clone().unwrap())),
        ));
        for _ in 0..pred.len() { // occupy operand list with placeholders
            vert.add_opd(ExtRc::new(ValueVert::new(
                VertTag::PlaceHolder,
                None,
            )))
        }
        self.graph.add(vert.clone(), Some(dst.clone()));
        vert
    }

    /// Build graph from ptr instruction
    fn build_ptr(&mut self, base: &RefCell<Value>, off: &Option<RefCell<Value>>,
                 ind: &Vec<RefCell<Value>>, dst: &RefCell<SymbolRef>, instr: &InstrRef)
    {
        let dst = self.get_dst_vert(dst, "ptr".to_string(), Some(instr));
        let base = self.get_src_vert(base);
        dst.add_opd(base);
        match off {
            Some(off) => {
                let off = self.get_src_vert(off);
                dst.add_opd(off);
            }
            // If pointer offset does not exist, pad operand list with a placeholder, so that
            // indices operands can align.
            None => dst.add_opd(ExtRc::new(ValueVert::new(
                VertTag::PlaceHolder,
                None,
            )))
        }
        for idx in ind {
            let idx = self.get_src_vert(idx);
            dst.add_opd(idx);
        }
    }

    /// Build graph from move instruction
    fn build_move(&mut self, src: &RefCell<Value>, dst: &RefCell<SymbolRef>) {
        let src = self.get_src_vert(src);
        match &src.tag {
            // `Consume` vertex cannot have symbol map
            VertTag::Consume(_) => unreachable!(),
            // Map to existing vertex or create new one
            _ => match dst.borrow().as_ref() {
                // If destination is local variable, it can be safely mapped to source.
                Symbol::Local { name: _, ty: _, ver: _ } =>
                    self.graph.map(dst.borrow().clone(), src),
                // For global variable, it cannot be mapped to source, create new vertex for it.
                Symbol::Global(_) => {
                    let dst = self.get_dst_vert(dst, String::new(), None);
                    dst.add_opd(src);
                }
                _ => unreachable!()
            }
        }
    }

    /// Create or find source vertex with given value.
    fn get_src_vert(&mut self, val: &RefCell<Value>) -> VertRef {
        match val.borrow().deref() {
            Value::Var(sym) => match sym.deref() {
                // Local source operand must have already been created.
                Symbol::Local { name: _, ty: _, ver: _ } => self.graph.find(sym).unwrap(),
                // For global operands, their vertices cannot be connected. Just create new one.
                Symbol::Global(_) => {
                    let vert = ExtRc::new(ValueVert::new(
                        VertTag::Cell(sym.id()),
                        None,
                    ));
                    self.graph.add(vert.clone(), None);
                    vert
                }
                _ => unreachable!()
            },
            Value::Const(c) => {
                let vert = ExtRc::new(ValueVert::new(
                    VertTag::Const(c.clone()),
                    None,
                ));
                self.graph.add(vert.clone(), None);
                vert
            }
        }
    }

    /// Create or find destination vertex with given symbol.
    fn get_dst_vert(&mut self, sym: &RefCell<SymbolRef>, op: String, instr: Option<&InstrRef>)
                    -> VertRef
    {
        match sym.borrow().as_ref() {
            // For local variable, create variable vertex with given operation name. Map symbol
            // to the created vertex.
            Symbol::Local { name: _, ty: _, ver: _ } => {
                let vert = ExtRc::new(ValueVert::new(
                    VertTag::Var(op.to_string()),
                    instr.map(|instr| (instr.clone(), self.block.clone().unwrap())),
                ));
                self.graph.add(vert.clone(), Some(sym.borrow().clone()));
                vert
            }
            // For global variable, create cell vertex with the name of the symbol. Do not map
            // symbols.
            Symbol::Global(_) => {
                let vert = ExtRc::new(ValueVert::new(
                    VertTag::Cell(sym.borrow().id()),
                    instr.map(|instr| (instr.clone(), self.block.clone().unwrap())),
                ));
                self.graph.add(vert.clone(), None);
                vert
            }
            _ => unreachable!()
        }
    }
}
