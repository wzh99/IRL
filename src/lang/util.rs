use std::cell::{Ref, RefCell, RefMut};
use std::cmp::Ordering;
use std::hash::{Hash, Hasher};
use std::iter::FromIterator;
use std::ops::Deref;
use std::rc::Rc;

/// A auxiliary structure to make `Rc` act like pointer.
/// The extended behavior include pointer-equality testing and hash.
pub struct ExtRc<T>(pub Rc<T>);

impl<T> ExtRc<T> {
    pub fn new(e: T) -> Self { ExtRc(Rc::new(e)) }
}

impl<T> PartialEq for ExtRc<T> {
    fn eq(&self, other: &Self) -> bool { Rc::ptr_eq(&self.0, &other.0) }
}

impl<T> Eq for ExtRc<T> {}

impl<T> PartialOrd for ExtRc<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        (self.0.as_ref() as *const T).partial_cmp(&(other.as_ref() as *const T))
    }
}

impl<T> Ord for ExtRc<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        (self.0.as_ref() as *const T).cmp(&(other.as_ref() as *const T))
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

/// Extended reference counting with interior mutability
pub struct MutRc<T>(pub Rc<RefCell<T>>);

impl<T> MutRc<T> {
    pub fn new(e: T) -> Self { MutRc(Rc::new(RefCell::new(e))) }
}

impl<T> PartialEq for MutRc<T> {
    fn eq(&self, other: &Self) -> bool { Rc::ptr_eq(&self.0, &other.0) }
}

impl<T> Eq for MutRc<T> {}

impl<T> PartialOrd for MutRc<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        (self.borrow().deref() as *const T).partial_cmp(&(other.borrow().deref() as *const T))
    }
}

impl<T> Ord for MutRc<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        (self.borrow().deref() as *const T).cmp(&(other.borrow().deref() as *const T))
    }
}

impl<T> Hash for MutRc<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (self.0.as_ref() as *const RefCell<T>).hash(state)
    }
}

impl<T> Clone for MutRc<T> {
    fn clone(&self) -> Self { MutRc(self.0.clone()) }
}

impl<T> MutRc<T> {
    pub fn borrow(&self) -> Ref<T> { self.0.deref().borrow() }

    pub fn borrow_mut(&self) -> RefMut<T> { self.0.deref().borrow_mut() }
}

/// Encapsulation of `HashSet` to aid work list algorithms
/// A work list must allow quick testing of membership and quick extraction of an element,
/// regardless of which element is moved.
#[derive(Debug)]
pub struct WorkList<T> where T: PartialEq {
    list: Vec<T>
}

impl<T> FromIterator<T> for WorkList<T> where T: PartialEq {
    fn from_iter<I>(iter: I) -> Self where I: IntoIterator<Item=T> {
        WorkList { list: Vec::from_iter(iter) }
    }
}

impl<T> WorkList<T> where T: PartialEq {
    pub fn new() -> WorkList<T> {
        WorkList { list: vec![] }
    }

    pub fn add(&mut self, item: T) {
        if !self.list.contains(&item) {
            self.list.push(item)
        }
    }

    pub fn pick(&mut self) -> Option<T> { self.list.pop() }

    pub fn is_empty(&self) -> bool { self.list.is_empty() }
}
