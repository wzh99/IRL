use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::{Debug, Error, Formatter};
use std::ops::Deref;
use std::rc::Rc;
use std::str::FromStr;

use crate::lang::func::Func;
use crate::lang::util::ExtRc;

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum Type {
    /// Void type, which does not represent any value and has no size.
    Void,
    /// 1-bit integer, usually serves as booleans.
    I1,
    /// 64-bit integer.
    I64,
    /// Function (pointer) with `param` as parameter type(s) and `ret` as return type.
    Fn { param: Vec<Type>, ret: Box<Type> },
    /// Pointer type
    Ptr(Box<Type>),
    /// Array type, whose length should be specified at compile time
    Array { elem: Box<Type>, len: usize },
    /// Structure type
    Struct { field: Vec<Type> },
    /// Type alias
    /// Nominal typing is used to decide equivalence for alias types, which means two alias types
    /// with different names are not equivalent, and an alias type is not equivalent to any non-
    /// alias type.
    Alias(SymbolRef),
}

impl FromStr for Type {
    type Err = String;

    /// Currently, this method only recognize primitive type.
    /// Other type should be resolved by compiler, instead of this method.
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "i1" => Ok(Type::I1),
            "i64" => Ok(Type::I64),
            _ => Err("unknown type".to_string())
        }
    }
}

impl ToString for Type {
    fn to_string(&self) -> String {
        match self {
            Type::Void => "void".to_string(),
            Type::I1 => "i1".to_string(),
            Type::I64 => "i64".to_string(),
            Type::Fn { param, ret } => {
                let p_str = Self::vec_to_string(param);
                let r_str = match ret.deref() {
                    Type::Void => "".to_string(),
                    r => format!(" -> {}", r.to_string()),
                };
                format!("fn({}){}", p_str, r_str)
            }
            Type::Ptr(tgt) => "*".to_owned() + &tgt.to_string(),
            Type::Array { elem, len } => format!("[{}]{}", len, elem.to_string()),
            Type::Struct { field } =>
                format!("{{ {} }}", Self::vec_to_string(field)),
            Type::Alias(def) => "@".to_owned() + def.name()
        }
    }
}

impl Type {
    /// Get original type for this type. This method is mainly for alias types.
    pub fn orig(&self) -> Type {
        let mut orig = self.clone();
        loop {
            if let Type::Alias(sym) = orig {
                orig = sym.get_type();
            } else { break }
        }
        orig
    }

    fn vec_to_string(vec: &Vec<Type>) -> String {
        let str_list: Vec<String> = vec.iter().map(|p| p.to_string()).collect();
        str_list.join(", ")
    }
}

pub trait Typed {
    fn get_type(&self) -> Type;
}

#[derive(Eq, PartialEq, Clone, Debug)]
pub enum Value {
    /// A variable holding reference to corresponding symbol
    Var(SymbolRef),
    /// A constant with its specific value
    Const(Const),
}

impl Typed for Value {
    fn get_type(&self) -> Type {
        match self {
            Value::Var(sym) => sym.get_type(),
            Value::Const(c) => c.get_type()
        }
    }
}

impl ToString for Value {
    fn to_string(&self) -> String {
        match self {
            Value::Var(sym) => sym.to_string(),
            Value::Const(c) => c.to_string()
        }
    }
}

impl Value {
    /// Whether this value is variable, including global and local.
    pub fn is_var(&self) -> bool {
        match self {
            Value::Var(_) => true,
            _ => false
        }
    }

    /// Whether this value is constant.
    pub fn is_const(&self) -> bool {
        match self {
            Value::Const(_) => true,
            _ => false
        }
    }

    /// Whether this value is local variable
    pub fn is_local_var(&self) -> bool {
        match self {
            Value::Var(sym) if sym.is_local_var() => true,
            _ => false
        }
    }
}

#[derive(Eq, PartialEq, Clone, Debug)]
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

impl ToString for Const {
    fn to_string(&self) -> String {
        match self {
            Const::I1(v) => if *v { "1".to_string() } else { "0".to_string() }
            Const::I64(v) => format!("{}", v),
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
    Type {
        name: String,
        ty: RefCell<Type>,
    },
    Func(Rc<Func>),
}

pub type SymbolRef = ExtRc<Symbol>;

impl Typed for Symbol {
    fn get_type(&self) -> Type {
        match self {
            Symbol::Local { name: _, ty, ver: _ } => ty.clone(),
            Symbol::Global(v) => v.ty.clone(),
            Symbol::Func(f) => f.get_type(),
            Symbol::Type { name: _, ty } => ty.borrow().clone()
        }
    }
}

impl ToString for Symbol {
    fn to_string(&self) -> String {
        match self {
            Symbol::Local { name: _, ty: _, ver: _ } => format!("${}", self.id()),
            _ => format!("@{}", self.name())
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
            Symbol::Local { name, ty: _, ver: _ } => name,
            Symbol::Global(v) => &v.name,
            Symbol::Type { name, ty: _ } => name,
            Symbol::Func(f) => &f.name
        }
    }

    /// Get identifier of symbol without tag `@` or `%`
    /// For local variable, its name, possibly connected with its version by `.` is returned.
    /// (`{$name}(.{$ver})?`)
    pub fn id(&self) -> String {
        if let Symbol::Local { name, ty: _, ver } = self {
            match ver {
                Some(v) => format!("{}.{}", name, v),
                None => name.to_string()
            }
        } else { self.name().to_string() }
    }

    /// Whether this symbol refers to local variable.
    pub fn is_local_var(&self) -> bool {
        match self {
            Symbol::Local { name: _, ty: _, ver: _ } => true,
            _ => false
        }
    }
}

#[derive(Eq, PartialEq, Clone, Debug)]
pub struct GlobalVar {
    pub name: String,
    pub ty: Type,
    pub init: Option<Const>,
}

impl Typed for GlobalVar {
    fn get_type(&self) -> Type { return self.ty.clone(); }
}

#[derive(Debug)]
/// Encapsulation of hash map to provide common operations to scope.
/// Internal mutability is utilized, so be careful not to violate the borrowing rules.
pub struct Scope {
    /// Maps variable identifier to symbol
    /// For local variable, its identifier is `{$name}(.{$ver})?`
    map: RefCell<HashMap<String, SymbolRef>>,
}

impl Scope {
    /// Create a new scope.
    /// If `parent` is `Some(p)`, a function scope with parent pointer `p` will be created.
    /// Otherwise, a global scope will be created.
    pub fn new() -> Scope {
        Scope {
            map: RefCell::new(HashMap::new())
        }
    }

    /// Add a symbol to the scope, and return if this symbol was successfully added.
    pub fn add(&self, sym: SymbolRef) -> bool {
        let id = sym.id();
        self.map.borrow_mut().insert(id, sym).is_none()
    }

    /// Append a collection of symbols to Scope
    pub fn append<I>(&self, iter: I) where I: Iterator<Item=SymbolRef> {
        iter.for_each(|sym| { self.add(sym); })
    }

    /// Lookup a symbol with given `id`.
    pub fn find(&self, id: &str) -> Option<SymbolRef> {
        self.map.borrow_mut().get(id).cloned()
    }

    /// Remove symbol with `name` from scope.
    pub fn remove(&self, name: &str) { self.map.borrow_mut().remove(name); }

    /// Clear all the symbols in the scope
    pub fn clear(&self) { self.map.borrow_mut().clear() }

    /// Return vector containing all the symbols in the scope.
    pub fn collect(&self) -> Vec<SymbolRef> {
        self.map.borrow().values().cloned().collect()
    }

    /// Run the given function on each symbol in this scope
    pub fn for_each<F>(&self, f: F) where F: FnMut(SymbolRef) {
        self.map.borrow().values().cloned().for_each(f)
    }
}
