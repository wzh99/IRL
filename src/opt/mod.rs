use std::ops::Deref;

use crate::lang::func::Func;
use crate::lang::Program;

pub mod simple;
pub mod graph;
pub mod gvn;
pub mod pre;
pub mod sccp;

/// Program optimization pass trait
pub trait Pass {
    fn opt(&mut self, pro: &mut Program);
}

/// Global (function-level) optimizer trait
pub trait FnPass: Pass {
    fn opt(&mut self, pro: &mut Program) {
        for func in &pro.func {
            self.opt_fn(func.deref())
        }
    }

    fn opt_fn(&mut self, func: &Func);
}