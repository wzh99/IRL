use std::ops::Deref;
use std::rc::Rc;

use crate::lang::func::Func;
use crate::lang::Program;

pub mod simple;

/// Program optimizer trait
pub trait Opt {
    fn opt(&mut self, pro: &mut Program);
}

/// Global (function-level) optimizer trait
pub trait GlobalOpt: Opt {
    fn opt(&mut self, pro: &mut Program) {
        for func in &pro.funcs {
            self.opt_fn(func.deref())
        }
    }

    fn opt_fn(&mut self, func: &Func);
}