use crate::lang::scope::{Symbol, Scope};
use crate::lang::ty::{Type, Typed};
use crate::lang::bb::BasicBlock;
use std::rc::Rc;
use std::cell::{RefCell};
use std::fmt::{Display, Formatter, Error};
use std::collections::HashSet;

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
    /// Scope of this function
    scope: Rc<RefCell<Scope>>,
    /// Entrance block of this function
    ent: Rc<RefCell<BasicBlock>>,
    /// Set of exit blocks of this function
    exit: HashSet<Rc<RefCell<BasicBlock>>>,
    /// Parameter list
    param: Vec<Rc<Symbol>>,
    /// Return type
    ret: Type,
}

impl Typed for Func {
    fn get_type(&self) -> Type {
        let param_ty = self.param.iter().map(|p| p.get_type()).collect();
        Type::Fn {param: param_ty, ret: Box::new(self.ret.clone()) }
    }
}
