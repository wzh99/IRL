use crate::lang::func::Func;
use crate::lang::Program;
use crate::opt::{GlobalOpt, Opt};

/// Wrapper for dead code elimination
pub struct DceOpt();

impl Opt for DceOpt {
    fn opt(&mut self, pro: &mut Program) { GlobalOpt::opt(self, pro) }
}

impl GlobalOpt for DceOpt {
    fn opt_fn(&mut self, func: &Func) { func.elim_dead_code() }
}