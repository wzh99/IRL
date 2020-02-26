use std::fmt::Debug;
use std::rc::Rc;

use crate::lang::func::Func;
use crate::lang::value::{GlobalVar, Scope};

pub mod util;
pub mod value;
pub mod instr;
pub mod func;
pub mod ssa;
pub mod print;
pub mod graph;

/// Top level program structure
#[derive(Debug)]
pub struct Program {
    /// Global variable list
    pub vars: Vec<Rc<GlobalVar>>,
    /// Function list
    pub funcs: Vec<Rc<Func>>,
    /// Scope for global symbols
    pub global: Rc<Scope>,
}
