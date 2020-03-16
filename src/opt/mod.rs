use std::rc::Rc;

use crate::lang::func::Func;
use crate::lang::Program;

pub mod simple;
pub mod graph;
pub mod gvn;
pub mod pre;
pub mod sccp;
pub mod osr;
pub mod adce;

/// Program optimization pass trait
pub trait Pass {
    fn opt(&mut self, pro: &mut Program);
}

/// Global (function-level) optimizer trait
pub trait FnPass: Pass {
    fn opt(&mut self, pro: &mut Program) {
        pro.func.iter().for_each(|func| self.opt_fn(func));
    }

    fn opt_fn(&mut self, func: &Rc<Func>);
}