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
