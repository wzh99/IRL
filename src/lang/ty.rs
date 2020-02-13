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