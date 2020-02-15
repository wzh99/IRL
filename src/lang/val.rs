use crate::lang::bb::BlockRef;
use std::rc::Rc;
use std::fmt::{Display, Formatter, Error};
use std::collections::{HashSet, HashMap};
use std::cell::RefCell;

#[derive(Clone, PartialEq)]
pub enum Type {
    /// Void type, only used in function return type
    Void,
    /// 1-bit integer, usually serves as booleans
    I1,
    /// 64-bit integer
    I64,
    /// Function (pointer) with `param` as parameter type(s) and `ret` as return type
    Fn{param: Vec<Type>, ret: Box<Type>}
}

pub trait Typed {
    fn get_type(&self) -> Type;
}

pub enum Value {
    /// A variable holding reference to corresponding symbol
    Var(Rc<Symbol>),
    /// A constant with its specific value
    Const(ConstVal)
}

impl Typed for Value {
    fn get_type(&self) -> Type {
        match self {
            Value::Var(sym) => sym.get_type(),
            Value::Const(c) => c.get_type()
        }
    }
}

pub enum ConstVal {
    I1(bool),
    I64(i64),
}

impl Typed for ConstVal {
    fn get_type(&self) -> Type {
        match self {
            ConstVal::I1(_) => Type::I1,
            ConstVal::I64(_) => Type::I64,
        }
    }
}

impl Display for ConstVal {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        match self {
            ConstVal::I1(v) => if *v { f.write_str("1") } else { f.write_str("0") }
            ConstVal::I64(v) => write!(f, "{}", v),
        }
    }
}

pub struct Func {
    /// Name of this function
    name: String,
    /// Scope of this function
    scope: Rc<Scope>,
    /// Entrance block of this function
    ent: BlockRef,
    /// Set of exit blocks of this function
    exit: HashSet<BlockRef>,
    /// Parameter list
    param: Vec<Rc<Symbol>>,
    /// Return type
    ret: Type,
}

impl Typed for Func {
    fn get_type(&self) -> Type {
        Type::Fn {
            param: self.param.iter().map(|p| p.get_type()).collect(),
            ret: Box::new(self.ret.clone())
        }
    }
}

#[derive(Clone)]
pub struct Symbol {
    /// Name of this symbol
    name: String,
    /// If this symbol is in global scope
    global: bool,
    /// Type of this symbol
    ty: Type,
    /// `Some(i)` if it is the `i`th version of the variable in SSA form.
    /// `None` if the IR is not in SSA form.
    ver: Option<isize>
}

impl Typed for Symbol {
    fn get_type(&self) -> Type { self.ty.clone() }
}

pub struct Scope {
    /// Maps names to symbol pointers
    symbols: RefCell<HashMap<String, Rc<Symbol>>>,
}

impl Scope {
    /// Create a new scope.
    /// If `parent` is `Some(p)`, a function scope with parent pointer `p` will be created.
    /// Otherwise, a global scope will be created.
    pub fn new() -> Scope {
        Scope{
            symbols: RefCell::new(HashMap::new())
        }
    }

    /// Add a symbol to a shared reference cell of scope.
    pub fn add(&self, sym: Symbol) -> Result<(), String> {
        if self.symbols.borrow().contains_key(&sym.name) {
            return Err(format!("symbol '{}' is already in scope", &sym.name))
        }
        self.symbols.borrow_mut().insert(sym.name.clone(), Rc::new(sym));
        Ok(())
    }

    /// Find a symbol with given `name`.
    /// If the symbol cannot be found in current scope, it will try to look for it in global
    /// scope.
    pub fn find(&self, name: &String) -> Option<Rc<Symbol>> {
        self.symbols.borrow_mut().get(name).cloned()
    }

    /// Remove symbol with `name` from scope.
    pub fn remove(&mut self, name: &String) { self.symbols.borrow_mut().remove(name); }
}
