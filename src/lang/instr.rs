use crate::lang::val::Value;

pub enum Instr {
    /// Move (copy) data from one virtual register to another
    Mov{src: Value, dst: Value},
    /// Unary operations
    Un{op: UnOp, opd: Value, res: Value},
    /// Binary operations
    Bin{op: BinOp, left: Value, right: Value, res: Value},
    /// Jump to label
    Jmp,
    /// Conditional branch to labels
    Br,
    /// Procedure call
    Call,
    /// Return computation results
    Ret{val: Value},
    /// Phi instructions in SSA
    Phi
}

#[derive(Debug)]
pub enum UnOp {
    /// 2's complement of signed number
    Neg,
    /// Bitwise-NOT of bits
    Not
}

impl ToString for UnOp {
    fn to_string(&self) -> String {
        format!("{:?}", self).to_lowercase()
    }
}

#[derive(Debug)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    And,
    Or,
    Xor,
    SHL,
    SHR,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge
}

impl ToString for BinOp {
    fn to_string(&self) -> String {
        format!("{:?}", self).to_lowercase()
    }
}
