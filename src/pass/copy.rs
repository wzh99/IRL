use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::ops::Deref;
use std::rc::Rc;

use crate::lang::func::{BlockListener, BlockRef, Func};
use crate::lang::instr::{Instr, InstrRef};
use crate::lang::Program;
use crate::lang::ssa::{InstrListener, ValueListener};
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
    fn run_on_fn(&mut self, func: &Rc<Func>) {
        let mut listener = CopyListener {
            map: Default::default(),
            def: vec![],
            rm: Default::default(),
        };
        func.walk_dom(&mut listener)
    }
}

struct CopyListener {
    map: HashMap<SymbolRef, Value>,
    def: Vec<Vec<SymbolRef>>,
    rm: HashSet<InstrRef>,
}

impl BlockListener for CopyListener {
    fn on_begin(&mut self, _func: &Func) {}

    fn on_end(&mut self, _func: &Func) {}

    fn on_enter(&mut self, block: BlockRef) {
        self.def.push(vec![]);
        InstrListener::on_enter(self, block.clone());
        block.instr.borrow_mut().retain(|instr| {
            !self.rm.contains(instr)
        })
    }

    fn on_exit(&mut self, _block: BlockRef) {
        self.def.pop().unwrap().into_iter().for_each(|sym| {
            self.map.remove(&sym);
        })
    }

    fn on_enter_child(&mut self, _this: BlockRef, _child: BlockRef) {}

    fn on_exit_child(&mut self, _this: BlockRef, _child: BlockRef) {}
}

impl InstrListener for CopyListener {
    fn on_instr(&mut self, instr: InstrRef) {
        if let Instr::Mov { src, dst } = instr.as_ref() {
            if src.borrow().is_global_var() || dst.borrow().is_global_var() {
                return; // don't propagate global variable
            }
            match src.borrow().deref() {
                Value::Const(_) => self.map.insert(dst.borrow().clone(), src.borrow().clone()),
                Value::Var(sym) =>
                    self.map.insert(dst.borrow().clone(), self.map.get(sym).cloned()
                        .unwrap_or(Value::Var(sym.clone())))
            };
            self.def.last_mut().unwrap().push(dst.borrow().clone());
            self.rm.insert(instr);
        } else {
            ValueListener::on_instr(self, instr)
        }
    }

    fn on_succ_phi(&mut self, this: Option<BlockRef>, instr: InstrRef) {
        ValueListener::on_succ_phi(self, this, instr)
    }
}

impl ValueListener for CopyListener {
    fn on_use(&mut self, _instr: InstrRef, opd: &RefCell<Value>) {
        opd.replace_with(|opd| {
            match opd {
                Value::Var(ref sym) if self.map.contains_key(sym) => self.map[sym].clone(),
                _ => opd.clone()
            }
        });
    }

    fn on_def(&mut self, _instr: InstrRef, _def: &RefCell<SymbolRef>) {}
}