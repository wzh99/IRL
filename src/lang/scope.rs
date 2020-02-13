use crate::lang::ty::{Type, Typed};
use crate::lang::val::Func;
use std::collections::HashMap;
use std::rc::Rc;
use std::cell::RefCell;

#[derive(Clone)]
pub struct Symbol {
    /// Name of this symbol
    name: String,
    /// Type of this symbol
    ty: Type,
    /// If this symbol is in global scope
    global: bool,
    /// The entity of this symbol
    entity: Entity
}

impl Typed for Symbol {
    fn get_type(&self) -> Type {
        match &self.entity {
            Entity::Var {ty, ver: _} => ty.clone(),
            Entity::Fn(func) => func.get_type()
        }
    }
}

#[derive(Clone)]
pub enum Entity {
    /// The entity of the symbol is a variable.
    /// `ver` is `Some(i)` if it is the `i`th version of the variable in SSA form.
    /// `None` if the IR is not in SSA form.
    Var{
        ty: Type,
        ver: Option<isize>
    },
    /// The entity of the symbol is a function.
    /// Holds pointer to the function
    Fn(Rc<Func>),
}

pub struct Scope {
    /// `Some(g)` if is function scope with `g` as global one,
    /// `None` if this scope itself is global scope.
    pub parent: Option<Rc<RefCell<Scope>>>,
    /// Maps names to symbol pointers
    symbols: HashMap<String, Rc<Symbol>>,
}

impl Scope {
    /// Create a new scope.
    /// If `parent` is `Some(p)`, a function scope with parent pointer `p` will be created.
    /// Otherwise, a global scope will be created.
    pub fn new(parent: Option<Rc<RefCell<Scope>>>) -> Scope {
        Scope{
            parent,
            symbols: HashMap::new()
        }
    }

    /// Decide whether this scope is global
    pub fn is_global(&self) -> bool { self.parent.is_none() }

    /// Add a symbol to a shared reference cell of scope.
    pub fn add(&mut self, mut sym: Symbol) -> Result<(), String> {
        if self.symbols.contains_key(&sym.name) {
            return Err(format!("symbol '{}' is already in scope", &sym.name))
        }
        sym.global = self.is_global();
        self.symbols.insert(sym.name.clone(), Rc::new(sym));
        Ok(())
    }

    /// Find a symbol with given `name`.
    /// If the symbol cannot be found in current scope, it will try to look for it in global
    /// scope.
    pub fn find(&self, name: &String) -> Option<Rc<Symbol>> {
        self.symbols.get(name).cloned().or(
             match &self.parent {
                Some(p) => p.borrow().find(name),
                None => None,
            })
    }

    /// Remove symbol with `name` from scope.
    pub fn remove(&mut self, name: &String) { self.symbols.remove(name); }
}