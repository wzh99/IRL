use std::rc::Rc;
use std::fmt::{Display, Formatter, Error, Debug};
use std::collections::{HashSet, HashMap};
use std::cell::RefCell;
use std::str::FromStr;
use crate::lang::{ExtRc, MutRc};
use crate::lang::bb::BasicBlock;
use std::ops::Deref;

#[derive(Clone, PartialEq, Debug)]
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

impl FromStr for Type {
    type Err = String;

    /// Currently, this method only recognize primitive type.
    /// Function type and void will not be accepted, since they will not appear in source code.
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "i1" => Ok(Type::I1),
            "i64" => Ok(Type::I64),
            _ => Err("unknown type".to_string())
        }
    }
}

pub trait Typed {
    fn get_type(&self) -> Type;
}

pub enum Value {
    /// A variable holding reference to corresponding symbol
    Var(Rc<Symbol>),
    /// A constant with its specific value
    Const(Const)
}

impl Typed for Value {
    fn get_type(&self) -> Type {
        match self {
            Value::Var(sym) => sym.get_type(),
            Value::Const(c) => c.get_type()
        }
    }
}

#[derive(Clone, Debug)]
pub enum Const {
    I1(bool),
    I64(i64),
}

impl Typed for Const {
    fn get_type(&self) -> Type {
        match self {
            Const::I1(_) => Type::I1,
            Const::I64(_) => Type::I64,
        }
    }
}

impl Display for Const {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        match self {
            Const::I1(v) => if *v { f.write_str("1") } else { f.write_str("0") }
            Const::I64(v) => write!(f, "{}", v),
        }
    }
}

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
    /// If this function is in SSA form
    pub ssa: bool
}

impl Typed for Func {
    fn get_type(&self) -> Type {
        Type::Fn {
            param: self.param.iter().map(|p| p.borrow().get_type()).collect(),
            ret: Box::new(self.ret.clone())
        }
    }
}

#[derive(Clone, Debug)]
pub enum Symbol {
    Local {
        name: String,
        ty: Type,
        ver: Option<usize>,
    },
    Global(Rc<GlobalVar>),
    Func(Rc<Func>)
}

pub type SymbolRef = MutRc<Symbol>;

#[derive(Clone, Debug)]
pub struct GlobalVar {
    pub name: String,
    pub ty: Type,
    pub init: Option<Const>
}

impl Typed for GlobalVar {
    fn get_type(&self) -> Type { return self.ty.clone() }
}

impl Typed for Symbol {
    fn get_type(&self) -> Type {
        match self {
            Symbol::Local { name:_, ty, ver:_ } => ty.clone(),
            Symbol::Global(v) => v.ty.clone(),
            Symbol::Func(f) => f.get_type()
        }
    }
}

impl Debug for SymbolRef {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> { Debug::fmt(&self.0.deref(), f) }
}

impl Symbol {
    /// Get name of this symbol.
    /// For local variable, only its name part is extracted
    pub fn name(&self) -> &str {
        match self {
            Symbol::Local { name, ty:_, ver:_ } => name,
            Symbol::Global(v) => &v.name,
            Symbol::Func(f) => &f.name
        }
    }

    /// Get identifier of symbol without tag `@` or `%`
    /// For local variable, its name, possibly connected with its version by `.` is returned.
    /// (`{$name}(.{$ver})?`)
    pub fn id(&self) -> String {
        if let Symbol::Local { name, ty:_, ver } = self {
            match ver {
                Some(v) => format!("{}.{}", name, v),
                None => name.to_string()
            }
        } else { self.name().to_string() }
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
        Scope{
            sym: RefCell::new(HashMap::new())
        }
    }

    /// Add a symbol to the scope.
    /// `Ok` if the symbol is successfully added to scope.
    /// `Err` if the symbol with the same name is already in scope.
    pub fn add(&self, sym: SymbolRef) -> Result<(), String> {
        if self.sym.borrow().contains_key(&sym.borrow().id()) {
            return Err(format!("symbol '{}' is already in scope", sym.borrow().name()))
        }
        let key = sym.borrow().id();
        self.sym.borrow_mut().insert(key, sym);
        Ok(())
    }

    /// Lookup a symbol with given `id`.
    pub fn find(&self, id: &str) -> Option<SymbolRef> {
        self.sym.borrow_mut().get(id).cloned()
    }

    /// Remove symbol with `name` from scope.
    pub fn remove(&mut self, name: &String) { self.sym.borrow_mut().remove(name); }
}
