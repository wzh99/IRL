use std::cell::{Cell, RefCell};
use std::collections::HashSet;
use std::ops::Deref;

use crate::lang::func::{BlockRef, DomVisitor, Func};
use crate::lang::instr::{Instr, InstrRef};
use crate::lang::val::{SymbolRef, Value};

/// Wrapper of SSA flag to make it only modifiable in this module.
#[derive(Debug)]
pub struct SsaFlag(Cell<bool>);

impl SsaFlag {
    pub fn new() -> SsaFlag { SsaFlag(Cell::new(false)) }
    pub fn get(&self) -> bool { self.0.get() }
    fn set(&self, val: bool) { self.0.set(val) }
}

/// Visitor of instructions in SSA program.
pub trait InstrVisitor<E>: DomVisitor<E> {
    fn on_begin(&mut self, func: &Func) -> Result<(), E> {
        // Visit phi instructions in the entrance block
        for instr in func.ent.borrow().instr.borrow().iter().cloned() {
            match instr.deref() {
                Instr::Phi { src: _, dst: _ } => self.on_succ_phi(None, instr)?,
                _ => break
            }
        }
        Ok(())
    }

    fn on_enter(&mut self, block: BlockRef) -> Result<(), E> {
        // Perform first-access action before visiting instructions
        self.on_access(block.clone())?;

        // Visit instructions
        for instr in block.instr.borrow().iter().cloned() {
            self.on_instr(instr)?;
        }

        // Visit phi instructions in successors
        for succ in block.succ.borrow().iter() {
            for instr in succ.instr.borrow().iter() {
                match instr.deref() {
                    Instr::Phi { src: _, dst: _ } =>
                        self.on_succ_phi(Some(block.clone()), instr.clone())?,
                    _ => break // phi instructions must be at front of each block
                }
            }
        }

        Ok(())
    }

    /// Called when `block` is accessed for the first time, before visiting instructions inside.
    fn on_access(&mut self, block: BlockRef) -> Result<(), E>;

    /// Called when visiting each instruction.
    fn on_instr(&mut self, instr: InstrRef) -> Result<(), E>;

    /// Called when visiting phi instructions in successor blocks.
    fn on_succ_phi(&mut self, this: Option<BlockRef>, instr: InstrRef) -> Result<(), E>;
}

/// Visitor of variables in SSA program.
pub trait VarVisitor<E>: InstrVisitor<E> {
    fn on_instr(&mut self, instr: InstrRef) -> Result<(), E> {
        match instr.deref() {
            Instr::Phi { src: _, dst: _ } => self.on_def(instr.dst())?, // skip phis
            _ => {
                self.on_use(instr.src())?;
                self.on_def(instr.dst())?;
            }
        }
        Ok(())
    }

    fn on_succ_phi(&mut self, this: Option<BlockRef>, instr: InstrRef) -> Result<(), E> {
        if let Instr::Phi { src, dst: _ } = instr.deref() {
            for (pred, opd) in src {
                match (&this, pred, opd) {
                    (Some(this), Some(pred), opd) if this == pred => self.on_phi_use(opd)?,
                    (None, None, opd) => self.on_phi_use(opd)?,
                    _ => ()
                }
            }
        }
        Ok(())
    }

    /// Call on possible definition of the instruction.
    fn on_def(&mut self, def: Option<&RefCell<SymbolRef>>) -> Result<(), E>;

    /// Call on operands (uses) of the instruction.
    fn on_use(&mut self, opd_list: Vec<&RefCell<Value>>) -> Result<(), E>;

    /// Call on operands of the the phi instructions in successor blocks..
    fn on_phi_use(&mut self, opd: &RefCell<Value>) -> Result<(), E>;
}

pub struct Verifier {
    // Whether a variable is found to be statically defined.
    def: HashSet<SymbolRef>,
    // Whether variables are available when reaching this block.
    // Organized as stack of frames, representing nodes on the path from root to current block
    avail: Vec<Vec<SymbolRef>>,
}

impl DomVisitor<String> for Verifier {
    fn on_begin(&mut self, func: &Func) -> Result<(), String> {
        // Add parameters as the first frame
        func.param.iter().cloned().for_each(|p| { self.def.insert(p); });
        self.avail.push(func.param.iter().cloned().collect());

        // Check phi operands in entrance block
        InstrVisitor::on_begin(self, func)?;
        Ok(())
    }

    fn on_enter(&mut self, block: BlockRef) -> Result<(), String> {
        InstrVisitor::on_enter(self, block)
    }

    fn on_exit(&mut self, _: BlockRef) -> Result<(), String> {
        self.avail.pop();
        Ok(())
    }

    fn on_end(&mut self, func: &Func) -> Result<(), String> {
        func.ssa.set(true);
        self.def.clear();
        self.avail.clear();
        Ok(())
    }

    fn on_enter_child(&mut self, _: BlockRef, _: BlockRef) -> Result<(), String> { Ok(()) }

    fn on_exit_child(&mut self, _: BlockRef, _: BlockRef) -> Result<(), String> { Ok(()) }
}

impl InstrVisitor<String> for Verifier {
    fn on_access(&mut self, block: BlockRef) -> Result<(), String> {
        // Push current frame to stack
        self.avail.push(vec![]);

        // Build predecessor list
        let mut req_pred: Vec<Option<BlockRef>> = block.pred.borrow().iter().cloned()
            .map(|p| Some(p)).collect();
        if block.parent().is_none() { // entrance block
            req_pred.push(None)
        }

        // Check correspondence of phi operands to predecessors
        for instr in block.instr.borrow().iter() {
            match instr.deref() {
                Instr::Phi { src, dst: _ } => {
                    let phi_pred: Vec<Option<BlockRef>> = src.iter()
                        .map(|(pred, _)| pred.clone()).collect();
                    for pred in &req_pred {
                        if !phi_pred.contains(pred) {
                            return Err(format!(
                                "phi operand not found for {}",
                                match pred {
                                    Some(p) => format!("predecessor {}", p.name),
                                    None => "function parameter".to_string()
                                }
                            ))
                        }
                    }
                }
                _ => break
            }
        }

        Ok(())
    }

    fn on_instr(&mut self, instr: InstrRef) -> Result<(), String> {
        VarVisitor::on_instr(self, instr)
    }

    fn on_succ_phi(&mut self, this: Option<BlockRef>, instr: InstrRef) -> Result<(), String> {
        VarVisitor::on_succ_phi(self, this, instr)
    }
}

impl VarVisitor<String> for Verifier {
    fn on_def(&mut self, def: Option<&RefCell<SymbolRef>>) -> Result<(), String> {
        match def {
            Some(sym) if sym.borrow().is_local_var() => {
                let sym = sym.borrow().clone();
                if self.def.contains(&sym) { // already statically defined
                    return Err(format!(
                        "variable {} already defined", sym.id()
                    ));
                } else {
                    self.def.insert(sym.clone()); // mark this static definition
                    // add to current frame of availability stack
                    self.avail.last_mut().unwrap().push(sym)
                }
            }
            _ => ()
        }
        Ok(())
    }

    fn on_use(&mut self, opd_list: Vec<&RefCell<Value>>) -> Result<(), String> {
        for opd in opd_list {
            match opd.borrow().deref() {
                Value::Var(sym) if sym.is_local_var() && !self.is_avail(sym) => {
                    return Err(format!(
                        "variable {} is used before defined", sym.id()
                    ));
                }
                _ => ()
            }
        }
        Ok(())
    }

    fn on_phi_use(&mut self, opd: &RefCell<Value>) -> Result<(), String> {
        match opd.borrow().deref() {
            Value::Var(sym) if sym.is_local_var() && !self.is_avail(sym) =>
                Err(format!("variable {} is used before defined", sym.id())),
            _ => Ok(())
        }
    }
}

impl Verifier {
    pub fn new() -> Verifier {
        Verifier {
            def: HashSet::new(),
            avail: vec![],
        }
    }

    fn is_avail(&self, sym: &SymbolRef) -> bool {
        self.avail.iter().any(|frame| frame.contains(sym))
    }
}

impl Func {
    pub fn to_ssa(&self) {
        if self.ssa.get() { return; } // already in SSA form
    }
}
