use std::cell::RefCell;
use std::collections::HashSet;
use std::ops::Deref;

use crate::lang::func::{BlockRef, DomVisitor, Func};
use crate::lang::instr::Instr;
use crate::lang::val::{SymbolRef, Value};

/// Abstraction of common SSA visiting pattern.
pub trait SsaVisitor<E>: DomVisitor<E> {
    /// Default method when entering a block. Normally this should override the one in
    /// `DomVisitor`
    fn on_enter(&mut self, block: BlockRef) -> Result<(), E> {
        // Perform first-access action before visiting instructions
        self.on_access(block.clone())?;

        // Visit non-phi instructions
        for instr in block.instr.borrow().iter() {
            match instr.deref() {
                Instr::Phi { src: _, dst: _ } => self.on_def(instr.def())?, // skip phis
                _ => {
                    self.on_use(instr.opd())?;
                    self.on_def(instr.def())?;
                }
            }
        }

        // Visit phi instructions in successors
        for succ in block.succ.borrow().iter() {
            for instr in succ.instr.borrow().iter() {
                match instr.deref() {
                    Instr::Phi { src, dst: _ } => for pair in src {
                        match pair {
                            (Some(pred), opd) if block == *pred => self.on_phi_use(opd)?,
                            _ => ()
                        }
                    }
                    _ => break // phi instructions must be at front of each block
                }
            }
        }

        Ok(())
    }

    /// Called when `block` is accessed for the first time.
    fn on_access(&mut self, block: BlockRef) -> Result<(), E>;

    /// Call on possible definition of the instruction.
    fn on_def(&mut self, def: Option<&RefCell<SymbolRef>>) -> Result<(), E>;

    /// Call on operands (uses) of the instruction.
    fn on_use(&mut self, opd_list: Vec<&RefCell<Value>>) -> Result<(), E>;

    /// Call on operand of the the phi instruction in successor block.
    /// This method may be called several times in each block, depending on the total number of
    /// phi instructions in successor blocks
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
        func.scope.for_each(|s| { self.def.insert(s); });
        func.param.iter().cloned().for_each(|p| { self.def.insert(p); });
        self.avail.push(func.param.iter().cloned().collect());

        // Check phi operands in entrance block
        for instr in func.ent.borrow().instr.borrow().iter() {
            match instr.deref() {
                Instr::Phi { src, dst: _ } =>
                    for (pred, opd) in src {
                        if pred.is_none() {
                            self.on_phi_use(opd)?;
                        }
                    }
                _ => break
            }
        }

        Ok(())
    }

    fn on_enter(&mut self, block: BlockRef) -> Result<(), String> {
        SsaVisitor::on_enter(self, block)
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
}

impl SsaVisitor<String> for Verifier {
    fn on_access(&mut self, _: BlockRef) -> Result<(), String> {
        self.avail.push(vec![]);
        Ok(())
    }

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
