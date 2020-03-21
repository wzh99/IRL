use std::rc::Rc;

use crate::lang::func::FnRef;
use crate::lang::value::{GlobalVarRef, Scope};

pub mod util;
pub mod value;
pub mod inst;
pub mod func;
pub mod ssa;
pub mod print;
pub mod graph;

/// Top level program structure
pub struct Program {
    /// Global variable list
    pub vars: Vec<GlobalVarRef>,
    /// Function list
    pub func: Vec<FnRef>,
    /// Scope for global symbols
    pub global: Rc<Scope>,
}
