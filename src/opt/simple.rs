use crate::lang::func::Func;
use crate::lang::Program;
use crate::opt::{FnPass, Pass};

/// Wrapper for dead code elimination
pub struct DceOpt();

impl Pass for DceOpt {
    fn opt(&mut self, pro: &mut Program) { FnPass::opt(self, pro) }
}

impl FnPass for DceOpt {
    fn opt_fn(&mut self, func: &Func) { func.elim_dead_code() }
}