use crate::lang::func::Func;
use crate::lang::Program;
use crate::opt::{FuncPass, Pass};

/// Wrapper for dead code elimination
pub struct DceOpt();

impl Pass for DceOpt {
    fn opt(&mut self, pro: &mut Program) { FuncPass::opt(self, pro) }
}

impl FuncPass for DceOpt {
    fn opt_fn(&mut self, func: &Func) { func.elim_dead_code() }
}