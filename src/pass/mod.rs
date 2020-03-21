use crate::lang::func::FnRef;
use crate::lang::Program;

pub mod util;
pub mod graph;
pub mod gvn;
pub mod pre;
pub mod sccp;
pub mod licm;
pub mod osr;
pub mod adce;
pub mod copy;

/// Program pass trait
pub trait Pass {
    fn run(&mut self, pro: &mut Program);
}

/// Function-level pass trait
pub trait FnPass: Pass {
    fn run(&mut self, pro: &mut Program) {
        pro.func.iter().for_each(|func| self.run_on_fn(func));
    }

    fn run_on_fn(&mut self, f: &FnRef);
}