use std::cell::RefCell;
use std::collections::{HashMap, HashSet, VecDeque};
use std::iter::FromIterator;
use std::rc::Rc;

use crate::lang::bb::{BasicBlock, BlockRef};
use crate::lang::ExtRc;
use crate::lang::val::{SymbolRef, Type, Typed};

#[derive(Debug)]
pub struct Func {
    /// Name of this function
    pub name: String,
    /// Scope of this function
    pub scope: Rc<Scope>,
    /// Parameter list
    pub param: Vec<SymbolRef>,
    /// Return type
    pub ret: Type,
    /// Entrance block of this function
    pub ent: RefCell<ExtRc<BasicBlock>>,
    /// Set of exit blocks of this function
    pub exit: RefCell<HashSet<ExtRc<BasicBlock>>>,
}

impl PartialEq for Func {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name && self.get_type() == other.get_type()
    }
}

impl Eq for Func {}

impl Typed for Func {
    fn get_type(&self) -> Type {
        Type::Fn {
            param: self.param.iter().map(|p| p.get_type()).collect(),
            ret: Box::new(self.ret.clone()),
        }
    }
}

impl Func {
    /// Return an iterator to breadth-first search the CFG
    pub fn bfs(&self) -> BfsIter {
        let ent = self.ent.borrow().clone();
        BfsIter {
            queue: VecDeque::from_iter(vec![ent.clone()]),
            visited: HashSet::from_iter(vec![ent]),
        }
    }

    pub fn dfs(&self) -> DfsIter {
        let ent = self.ent.borrow().clone();
        DfsIter {
            stack: vec![ent.clone()],
            visited: HashSet::from_iter(vec![ent]),
        }
    }
}

/// Breadth-first iterator
pub struct BfsIter {
    queue: VecDeque<BlockRef>,
    visited: HashSet<BlockRef>,
}

impl Iterator for BfsIter {
    type Item = BlockRef;

    fn next(&mut self) -> Option<Self::Item> {
        self.queue.pop_front().map(|next| {
            for succ in next.succ.borrow().iter() {
                if !self.visited.contains(succ) {
                    self.queue.push_back(succ.clone());
                    self.visited.insert(succ.clone());
                }
            }
            next
        })
    }
}

/// Depth-first iterator
pub struct DfsIter {
    stack: Vec<BlockRef>,
    visited: HashSet<BlockRef>,
}

impl Iterator for DfsIter {
    type Item = BlockRef;

    fn next(&mut self) -> Option<Self::Item> {
        self.stack.pop().map(|next| {
            for succ in next.succ.borrow().iter() {
                if !self.visited.contains(succ) {
                    self.stack.push(succ.clone());
                    self.visited.insert(succ.clone());
                }
            }
            next
        })
    }
}

#[derive(Debug)]
pub struct Scope {
    /// Maps variable identifier to symbol
    /// For local variable, its identifier is `{$name}(.{$ver})?`
    sym: RefCell<HashMap<String, SymbolRef>>,
}

impl Scope {
    /// Create a new scope.
    /// If `parent` is `Some(p)`, a function scope with parent pointer `p` will be created.
    /// Otherwise, a global scope will be created.
    pub fn new() -> Scope {
        Scope {
            sym: RefCell::new(HashMap::new())
        }
    }

    /// Add a symbol to the scope.
    /// `Ok` if the symbol is successfully added to scope.
    /// `Err` if the symbol with the same name is already in scope.
    pub fn add(&self, sym: SymbolRef) -> Result<(), String> {
        let id = sym.id();
        if self.sym.borrow().contains_key(&id) {
            return Err(format!("symbol of identifier \"{}\" is already in scope", id));
        }
        self.sym.borrow_mut().insert(id, sym);
        Ok(())
    }

    /// Lookup a symbol with given `id`.
    pub fn find(&self, id: &str) -> Option<SymbolRef> {
        self.sym.borrow_mut().get(id).cloned()
    }

    /// Remove symbol with `name` from scope.
    pub fn remove(&self, name: &String) { self.sym.borrow_mut().remove(name); }

    /// Return vector containing all the symbols in the scope.
    pub fn collect(&self) -> Vec<SymbolRef> {
        self.sym.borrow().values().cloned().collect()
    }
}
