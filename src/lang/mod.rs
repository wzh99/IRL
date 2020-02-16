pub mod val;
pub mod instr;
pub mod bb;

use crate::lang::val::{Func, Scope};
use std::rc::Rc;
use std::cmp::Ordering;
use std::hash::{Hash, Hasher};
use std::ops::Deref;

/// Top level program structure
#[derive(Debug)]
pub struct Program {
    /// Map function name to its entity
    pub fn_list: Vec<Rc<Func>>,
    /// Scope for global symbols
    pub global: Rc<Scope>
}

/// A auxiliary structure to make `Rc` act like pointer.
/// The extended behavior include pointer-equality testing, comparison and hash.
pub struct ExtRc<T>(pub Rc<T>);

impl <T> From<Rc<T>> for ExtRc<T> {
    fn from(rc: Rc<T>) -> Self { ExtRc(rc) }
}

impl <T> PartialEq for ExtRc<T> {
    fn eq(&self, other: &Self) -> bool { Rc::ptr_eq(&self.0, &other.0) }
}

impl <T> Eq for ExtRc<T> {}

impl <T> Ord for ExtRc<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        (self.0.as_ref() as *const T).cmp(&(other.0.as_ref() as *const T))
    }
}

impl <T> PartialOrd for ExtRc<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        (self.0.as_ref() as *const T).partial_cmp(&(other.0.as_ref() as *const T))
    }
}

impl <T> Hash for ExtRc<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (self.0.as_ref() as *const T).hash(state)
    }
}

impl <T> AsRef<T> for ExtRc<T> {
    fn as_ref(&self) -> &T { self.0.as_ref() }
}

impl <T> Deref for ExtRc<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target { self.0.deref() }
}

impl <T> Clone for ExtRc<T> {
    fn clone(&self) -> Self { ExtRc(self.0.clone()) }
}
