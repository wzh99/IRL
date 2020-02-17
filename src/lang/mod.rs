use std::cell::{Ref, RefCell, RefMut};
use std::cmp::Ordering;
use std::fmt::Debug;
use std::hash::{Hash, Hasher};
use std::ops::Deref;
use std::rc::Rc;

use crate::lang::val::{Func, GlobalVar, Scope};

pub mod val;
pub mod instr;
pub mod bb;

/// Top level program structure
#[derive(Debug)]
pub struct Program {
    /// Global variable list
    pub vars: Vec<Rc<GlobalVar>>,
    /// Function list
    pub funcs: Vec<Rc<Func>>,
    /// Scope for global symbols
    pub global: Scope,
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

impl<T> Ord for ExtRc<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        (self.0.as_ref() as *const T).cmp(&(other.0.as_ref() as *const T))
    }
}

impl<T> PartialOrd for ExtRc<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        (self.0.as_ref() as *const T).partial_cmp(&(other.0.as_ref() as *const T))
    }
}

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

/// Enhanced reference counter with interior mutability
pub struct MutRc<T>(pub ExtRc<RefCell<T>>);

impl<T> MutRc<T> {
    pub fn new(e: T) -> MutRc<T> { MutRc(ExtRc::new(RefCell::new(e))) }

    pub fn borrow(&self) -> Ref<T> { self.0.deref().borrow() }

    pub fn borrow_mut(&self) -> RefMut<T> { self.0.deref().borrow_mut() }
}

impl<T> From<RefCell<T>> for MutRc<T> {
    fn from(c: RefCell<T>) -> Self { MutRc(ExtRc::new(c)) }
}

impl<T> PartialEq for MutRc<T> {
    fn eq(&self, other: &Self) -> bool { self.0.eq(&other.0) }
}

impl<T> Eq for MutRc<T> {}

impl<T> Ord for MutRc<T> {
    fn cmp(&self, other: &Self) -> Ordering { self.0.cmp(&other.0) }
}

impl<T> PartialOrd for MutRc<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> { self.0.partial_cmp(&other.0) }
}

impl<T> Hash for MutRc<T> {
    fn hash<H: Hasher>(&self, state: &mut H) { self.0.hash(state) }
}

impl<T> Clone for MutRc<T> {
    fn clone(&self) -> Self { MutRc(self.0.clone()) }
}
