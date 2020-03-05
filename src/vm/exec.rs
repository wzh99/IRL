use std::collections::HashMap;
use std::fmt::{Debug, Error, Formatter};
use std::rc::Rc;

use crate::lang::func::Func;
use crate::lang::Program;
use crate::lang::value::GlobalVarRef;
use crate::vm::mem::{FrameRef, Reg, Stack};

pub struct Interpreter {
    global: HashMap<GlobalVarRef, Reg>,
    stack: Stack,
    count: Counter,
}

impl Interpreter {
    pub fn new() -> Self {
        Interpreter {
            global: Default::default(),
            stack: Stack::new(),
            count: Counter::new(),
        }
    }

    pub fn run(&mut self, pro: &Program) -> Result<VmState, RuntimeErr> {
        // Initialize global variable
        pro.vars.iter().for_each(|var| {
            let mut reg = Reg::from(&var.ty);
            var.init.map(|c| reg.set(c));
            self.global.insert(var.clone(), reg);
        });

        // Find program entrance and run that function
        match pro.func.iter().find(|func| &func.name == "main") {
            Some(main) => { self.call(main, vec![])?; }
            None => self.err(format!("cannot find program entrance"))?
        }

        // Collect final global variables
        let mut global: Vec<_> = self.global.iter()
            .map(|(v, r)| (v.clone(), r.clone())).collect();
        global.sort_by_cached_key(|(v, _)| v.name.clone());

        // Clear machine state for this program
        self.global.clear();
        self.stack.clear();
        self.count.reset();

        Ok(VmState { global })
    }

    fn call(&mut self, func: &Rc<Func>, arg: Vec<Reg>) -> Result<Option<Reg>, RuntimeErr> {
        // Initialize parameters
        Ok(None)
    }

    fn err(&self, msg: String) -> Result<(), RuntimeErr> {
        Err(RuntimeErr { msg, frame: self.stack.unwind() })
    }
}

pub struct VmState {
    pub global: Vec<(GlobalVarRef, Reg)>
}

pub struct RuntimeErr {
    msg: String,
    frame: Vec<FrameRef>,
}

impl Debug for RuntimeErr {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        write!(f, "runtime error: {}", self.msg)
    }
}

struct Counter {
    /// Number of instructions executed
    num: usize,
    /// Time consumed in executing this program
    time: usize,
}

impl Counter {
    fn new() -> Self { Counter { num: 0, time: 0 } }

    fn reset(&mut self) {
        self.num = 0;
        self.time = 0;
    }
}
