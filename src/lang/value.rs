use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::{Debug, Error, Formatter};
use std::ops::*;
use std::rc::Rc;
use std::str::FromStr;

use crate::lang::func::Func;
use crate::lang::util::ExtRc;

#[derive(Clone, Eq, Debug)]
pub enum Type {
    /// Void type, which does not represent any value and has no size.
    Void,
    /// Integers, could be 1, 8, 16, 32 or 64 bits
    I(u8),
    /// Function (pointer) with `param` as parameter type(s) and `ret` as return type.
    Fn { param: Vec<Type>, ret: Box<Type> },
    /// Pointer type
    Ptr(Box<Type>),
    /// Array type, whose length should be specified at compile time
    Array { elem: Box<Type>, len: usize },
    /// Structure type
    Struct { field: Vec<Type> },
    /// Type alias
    Alias(SymbolRef),
}

impl PartialEq for Type {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Type::Void, Type::Void) => true,
            (Type::I(b1), Type::I(b2)) => b1 == b2,
            (Type::Fn { param: p1, ret: r1 }, Type::Fn { param: p2, ret: r2 }) =>
                p1 == p2 && r1 == r2,
            (Type::Ptr(p1), Type::Ptr(p2)) => p1 == p2,
            (Type::Array { elem: e1, len: l1 }, Type::Array { elem: e2, len: l2 }) =>
                l1 == l2 && e1 == e2,
            (Type::Struct { field: f1 }, Type::Struct { field: f2 }) => f1 == f2,
            // Nominal typing is used to decide equivalence for alias types, which means two alias
            // types with different names are not equivalent. However, an alias type can be equal
            // to its original type.
            (Type::Alias(a1), Type::Alias(a2)) => a1 == a2,
            (Type::Alias(_), _) => self.orig() == *other,
            (_, Type::Alias(_)) => *self == other.orig(),
            _ => false
        }
    }
}

impl FromStr for Type {
    type Err = String;

    /// Currently, this method only recognize primitive type.
    /// Other type should be resolved by compiler, instead of this method.
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "i1" => Ok(Type::I(1)),
            "i8" => Ok(Type::I(8)),
            "i16" => Ok(Type::I(16)),
            "i32" => Ok(Type::I(32)),
            "i64" => Ok(Type::I(64)),
            _ => Err("unknown type".to_string())
        }
    }
}

impl ToString for Type {
    fn to_string(&self) -> String {
        match self {
            Type::Void => "void".to_string(),
            Type::I(b) => format!("i{}", b),
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
            } else { break; }
        }
        orig
    }

    fn vec_to_string(vec: &Vec<Type>) -> String {
        let str_list: Vec<String> = vec.iter().map(|p| p.to_string()).collect();
        str_list.join(", ")
    }

    /// Whether this type is alias type
    pub fn is_alias(&self) -> bool {
        match self {
            Type::Alias(_) => true,
            _ => false
        }
    }

    /// Whether values of this type could be stored in virtual registers
    pub fn is_reg(&self) -> bool {
        match self.orig() {
            Type::I(_) | Type::Ptr(_) => true,
            _ => false
        }
    }

    /// Get target type for pointer types
    pub fn tgt_type(&self) -> Type {
        if let Type::Ptr(t) = self { t.deref().clone() } else {
            panic!("cannot get target type of non-pointer type")
        }
    }
}

pub trait Typed {
    fn get_type(&self) -> Type;
}

#[derive(Clone, Debug)]
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

    /// Whether this value is global variable
    pub fn is_global_var(&self) -> bool {
        match self {
            Value::Var(sym) if sym.is_global_var() => true,
            _ => false
        }
    }
}

#[derive(Clone)]
pub enum Symbol {
    Local {
        name: String,
        ty: Type,
        ver: Option<usize>,
    },
    Global(GlobalVarRef),
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

impl Debug for Symbol {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        write!(f, "{}", self.to_string())
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

    /// Whether this symbol is a local variable.
    pub fn is_local_var(&self) -> bool {
        match self {
            Symbol::Local { name: _, ty: _, ver: _ } => true,
            _ => false
        }
    }

    /// Whether this symbol refers to a global variable.
    pub fn is_global_var(&self) -> bool {
        match self {
            Symbol::Global(_) => true,
            _ => false
        }
    }
}

#[derive(Clone, Debug)]
pub struct GlobalVar {
    pub name: String,
    pub ty: Type,
    pub init: Option<Const>,
}

impl Typed for GlobalVar {
    fn get_type(&self) -> Type { return self.ty.clone(); }
}

pub type GlobalVarRef = ExtRc<GlobalVar>;

impl Debug for GlobalVarRef {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        write!(f, "@{}", self.name)
    }
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
    pub fn insert(&self, sym: SymbolRef) -> bool {
        let id = sym.id();
        self.map.borrow_mut().insert(id, sym).is_none()
    }

    /// Append a collection of symbols to Scope
    pub fn append<I>(&self, iter: I) where I: Iterator<Item=SymbolRef> {
        iter.for_each(|sym| { self.insert(sym); })
    }

    /// Lookup a symbol with given `id`.
    pub fn find(&self, id: &str) -> Option<SymbolRef> {
        self.map.borrow_mut().get(id).cloned()
    }

    /// Remove symbol with `id` from scope.
    pub fn remove(&self, id: &str) { self.map.borrow_mut().remove(id); }

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

/// Procedural symbol generator
pub struct SymbolGen {
    pre: String,
    num: usize,
    scope: Rc<Scope>,
}

impl SymbolGen {
    pub fn new(pre: &str, scope: Rc<Scope>) -> SymbolGen {
        SymbolGen {
            pre: pre.to_string(),
            num: 0,
            scope,
        }
    }

    pub fn gen(&mut self, ty: &Type) -> SymbolRef {
        loop {
            let name = format!("{}{}", self.pre, self.num);
            self.num += 1;
            if self.scope.find(&name).is_some() { continue; }
            let sym = ExtRc::new(Symbol::Local {
                name,
                ty: ty.clone(),
                ver: None,
            });
            self.scope.insert(sym.clone());
            return sym
        }
    }
}

/// A compile-time constant.
/// Note that `Ord` and `PartialOrd` trait is just for comparing two `Const` objects, not for
/// evaluating the constants at compile time. To achieve this, use the `eval` associative method
/// in operator's implementation.
#[derive(Ord, PartialOrd, Eq, PartialEq, Copy, Clone, Hash, Debug)]
pub enum Const {
    I1(bool),
    I8(i8),
    I16(i16),
    I32(i32),
    I64(i64),
}

impl Const {
    /// Create constant `s` of type `ty`. Return `None` if the constant cannot be created.
    pub fn from_str(s: &str, ty: &Type) -> Option<Const> {
        let d: i64 = s.parse().ok()?;
        match ty {
            Type::I(1) => match d {
                0 => Some(Const::I1(false)),
                1 => Some(Const::I1(true)),
                _ => None
            },
            Type::I(8) => Some(Const::I8(d as i8)),
            Type::I(16) => Some(Const::I16(d as i16)),
            Type::I(32) => Some(Const::I32(d as i32)),
            Type::I(64) => Some(Const::I64(d as i64)),
            _ => unreachable!()
        }
    }

    pub fn zero(ty: &Type) -> Const {
        match ty {
            Type::I(1) => Const::I1(false),
            Type::I(8) => Const::I8(0),
            Type::I(16) => Const::I16(0),
            Type::I(32) => Const::I32(0),
            Type::I(64) => Const::I64(0),
            _ => unreachable!()
        }
    }

    pub fn one(ty: &Type) -> Const {
        match ty {
            Type::I(1) => Const::I1(true),
            Type::I(8) => Const::I8(1),
            Type::I(16) => Const::I16(1),
            Type::I(32) => Const::I32(1),
            Type::I(64) => Const::I64(1),
            _ => unreachable!()
        }
    }
}

impl Typed for Const {
    fn get_type(&self) -> Type {
        match self {
            Const::I1(_) => Type::I(1),
            Const::I8(_) => Type::I(8),
            Const::I16(_) => Type::I(16),
            Const::I32(_) => Type::I(32),
            Const::I64(_) => Type::I(64),
        }
    }
}

impl ToString for Const {
    fn to_string(&self) -> String {
        match self {
            Const::I1(v) => if *v { "1".to_string() } else { "0".to_string() }
            Const::I8(v) => format!("{}", v),
            Const::I16(v) => format!("{}", v),
            Const::I32(v) => format!("{}", v),
            Const::I64(v) => format!("{}", v),
        }
    }
}

impl Not for Const {
    type Output = Self;

    fn not(self) -> Self::Output {
        match self {
            Const::I1(v) => Const::I1(!v),
            Const::I8(v) => Const::I8(!v),
            Const::I16(v) => Const::I16(!v),
            Const::I32(v) => Const::I32(!v),
            Const::I64(v) => Const::I64(!v),
        }
    }
}

impl Neg for Const {
    type Output = Self;

    fn neg(self) -> Self::Output {
        match self {
            Const::I8(v) => Const::I8(-v),
            Const::I16(v) => Const::I16(-v),
            Const::I32(v) => Const::I32(-v),
            Const::I64(v) => Const::I64(-v),
            _ => unreachable!()
        }
    }
}

macro_rules! bin_arith_impl {
    ($trait:ty, $func:ident, $op:tt) => {
        impl $trait for Const {
            type Output = Self;
            fn $func(self, rhs: Self) -> Self::Output {
                match (self, rhs) {
                    (Const::I8(l), Const::I8(r)) => Const::I8(l $op r),
                    (Const::I16(l), Const::I16(r)) => Const::I16(l $op r),
                    (Const::I32(l), Const::I32(r)) => Const::I32(l $op r),
                    (Const::I64(l), Const::I64(r)) => Const::I64(l $op r),
                    _ => unreachable!()
                }
            }
        }
    };
}

bin_arith_impl!(Add, add, +);
bin_arith_impl!(Sub, sub, -);
bin_arith_impl!(Mul, mul, *);
bin_arith_impl!(Div, div, /);
bin_arith_impl!(Shl, shl, <<);
bin_arith_impl!(Shr, shr, >>);
bin_arith_impl!(Rem, rem, %);

macro_rules! bin_bitwise_impl {
    ($trait:ty, $func:ident, $op:tt) => {
        impl $trait for Const {
            type Output = Self;

            fn $func(self, rhs: Self) -> Self::Output {
                match (self, rhs) {
                    (Const::I1(l), Const::I1(r)) => Const::I1(l $op r),
                    (Const::I8(l), Const::I8(r)) => Const::I8(l $op r),
                    (Const::I16(l), Const::I16(r)) => Const::I16(l $op r),
                    (Const::I32(l), Const::I32(r)) => Const::I32(l $op r),
                    (Const::I64(l), Const::I64(r)) => Const::I64(l $op r),
                    _ => unreachable!()
                }
            }
        }
    };
}

bin_bitwise_impl!(BitAnd, bitand, &);
bin_bitwise_impl!(BitOr, bitor, |);
bin_bitwise_impl!(BitXor, bitxor, ^);

macro_rules! cmp_ord_impl {
    ($func:ident, $op:tt) => {
        impl Const {
            pub fn $func(self, rhs: Self) -> Self {
                match (self, rhs) {
                    (Const::I8(l), Const::I8(r)) => Const::I1(l $op r),
                    (Const::I16(l), Const::I16(r)) => Const::I1(l $op r),
                    (Const::I32(l), Const::I32(r)) => Const::I1(l $op r),
                    (Const::I64(l), Const::I64(r)) => Const::I1(l $op r),
                    _ => unreachable!()
                }
            }
        }
    };
}

cmp_ord_impl!(less_than, <);
cmp_ord_impl!(less_eq, <=);
cmp_ord_impl!(greater_than, >);
cmp_ord_impl!(greater_eq, >=);

// Note that the result is `Const::I1`, not bool
macro_rules! cmp_eq_impl {
    ($func:ident, $op:tt) => {
        impl Const {
            pub fn $func(self, rhs: Self) -> Self {
                match (self, rhs) {
                    (Const::I1(l), Const::I1(r)) => Const::I1(l $op r),
                    (Const::I8(l), Const::I8(r)) => Const::I1(l $op r),
                    (Const::I16(l), Const::I16(r)) => Const::I1(l $op r),
                    (Const::I32(l), Const::I32(r)) => Const::I1(l $op r),
                    (Const::I64(l), Const::I64(r)) => Const::I1(l $op r),
                    _ => unreachable!()
                }
            }
        }
    };
}

// TO avoid colliding with library trait `Eq` and `Ne`, its method name is `e` and `n`.
cmp_eq_impl!(equal, ==);
cmp_eq_impl!(not_eq, !=);
