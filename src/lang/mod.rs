use std::fmt::Debug;
use std::hash::{Hash, Hasher};
use std::ops::Deref;
use std::rc::Rc;

use crate::lang::func::Func;
use crate::lang::val::{GlobalVar, Scope};

pub mod val;
pub mod instr;
pub mod func;
pub mod print;

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

/// A auxiliary structure to make `Rc` act like pointer.
/// The extended behavior include pointer-equality testing, comparison and hash.
pub struct ExtRc<T>(pub Rc<T>);

impl<T> ExtRc<T> {
    pub fn new(e: T) -> Self { ExtRc(Rc::new(e)) }
}

impl<T> From<Rc<T>> for ExtRc<T> {
    fn from(rc: Rc<T>) -> Self { ExtRc(rc) }
}

impl<T> PartialEq for ExtRc<T> {
    fn eq(&self, other: &Self) -> bool { Rc::ptr_eq(&self.0, &other.0) }
}

impl<T> Eq for ExtRc<T> {}

impl<T> Hash for ExtRc<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (self.0.as_ref() as *const T).hash(state)
    }
}

impl<T> AsRef<T> for ExtRc<T> {
    fn as_ref(&self) -> &T { self.0.as_ref() }
}

impl<T> Deref for ExtRc<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target { self.0.deref() }
}

impl<T> Clone for ExtRc<T> {
    fn clone(&self) -> Self { ExtRc(self.0.clone()) }
}
