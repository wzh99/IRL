use std::cell::RefCell;
use std::collections::HashMap;
use std::ops::Deref;

use crate::lang::func::{BlockRef, DomTreeListener, Fn, FnRef};
use crate::lang::inst::{Inst, InstRef};
use crate::lang::Program;
use crate::lang::ssa::{InstListener, ValueListener};
use crate::lang::value::{SymbolRef, Value};
use crate::pass::{FnPass, Pass};

/// Copy Propagation
pub struct CopyProp {}

impl CopyProp {
    pub fn new() -> CopyProp { CopyProp {} }
}

impl Pass for CopyProp {
    fn run(&mut self, pro: &mut Program) { FnPass::run(self, pro) }
}

impl FnPass for CopyProp {
    fn run_on_fn(&mut self, func: &FnRef) {
        func.assert_ssa();
        let mut listener = CopyListener {
            map: Default::default(),
            def: vec![],
        };
        func.walk_dom(&mut listener)
    }
}

struct CopyListener {
    map: HashMap<SymbolRef, Value>,
    def: Vec<Vec<SymbolRef>>,
}

impl DomTreeListener for CopyListener {
    fn on_begin(&mut self, _func: &Fn) {}

    fn on_end(&mut self, _func: &Fn) {}

    fn on_enter(&mut self, block: BlockRef) {
        self.def.push(vec![]);
        InstListener::on_enter(self, block.clone());
    }

    fn on_exit(&mut self, _block: BlockRef) {
        self.def.pop().unwrap().into_iter().for_each(|sym| {
            self.map.remove(&sym);
        })
    }

    fn on_enter_child(&mut self, _this: BlockRef, _child: BlockRef) {}

    fn on_exit_child(&mut self, _this: BlockRef, _child: BlockRef) {}
}

impl InstListener for CopyListener {
    fn on_instr(&mut self, instr: InstRef) {
        match instr.as_ref() {
            // Propagate copy
            Inst::Mov { src, dst } => {
                // Don't propagate global variable
                if src.borrow().is_global_var() { return; }
                if dst.borrow().is_global_var() { // treat like other instructions
                    ValueListener::on_instr(self, instr);
                    return;
                }
                match src.borrow().deref() {
                    Value::Const(_) => self.map.insert(dst.borrow().clone(), src.borrow().clone()),
                    Value::Var(sym) =>
                        self.map.insert(dst.borrow().clone(), self.map.get(sym).cloned()
                            .unwrap_or(Value::Var(sym.clone())))
                };
                self.def.last_mut().unwrap().push(dst.borrow().clone());
            }
            // Eliminate phi with only one operand
            Inst::Phi { src, dst } if src.len() == 1 => {
                let src = src[0].1.borrow().clone();
                match &src {
                    Value::Const(_) => self.map.insert(dst.borrow().clone(), src.clone()),
                    Value::Var(sym) =>
                        self.map.insert(dst.borrow().clone(), self.map.get(sym).cloned()
                            .unwrap_or(Value::Var(sym.clone())))
                };
                self.def.last_mut().unwrap().push(dst.borrow().clone());
            }
            _ => ValueListener::on_instr(self, instr)
        }
    }

    fn on_succ_phi(&mut self, this: BlockRef, instr: InstRef) {
        ValueListener::on_succ_phi(self, this, instr.clone())
    }
}

impl ValueListener for CopyListener {
    fn on_use(&mut self, _instr: InstRef, opd: &RefCell<Value>) {
        opd.replace_with(|opd| {
            match opd {
                Value::Var(ref sym) if self.map.contains_key(sym) => self.map[sym].clone(),
                _ => opd.clone()
            }
        });
    }

    fn on_def(&mut self, _instr: InstRef, _def: &RefCell<SymbolRef>) {}
}