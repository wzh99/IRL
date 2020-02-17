use std::str::FromStr;

use crate::lang::MutRc;
use crate::lang::bb::BlockRef;
use crate::lang::val::Value;

pub enum Instr {
    /// Move (copy) data from one virtual register to another
    Mov { src: Value, dst: Value },
    /// Unary operations
    Un { op: UnOp, opd: Value, res: Value },
    /// Binary operations
    Bin { op: BinOp, left: Value, right: Value, res: Value },
    /// Jump to another basic block
    Jmp { tgt: BlockRef },
    /// Conditional branch to labels
    /// If `cond` evaluates to true, branch to `tr` block, otherwise to `fls` block
    Br { cond: Value, tr: BlockRef, fls: BlockRef },
    /// Procedure call
    Call { func: Value },
    /// Return computation results, or `None` if return type is `Void`.
    Ret { val: Option<Value> },
    /// Phi instructions in SSA
    /// A phi instruction hold a list of block-value pairs. The blocks are all predecessors of
    /// current block (where this instruction is defined). The values are different versions of
    /// of a certain variable.
    Phi { pair: Vec<(BlockRef, Value)> },
}

/// Reference to `Instr` that support both enhanced reference counting and interior mutability.
pub type InstrRef = MutRc<Instr>;

impl Instr {
    /// Decide if this instruction is a control flow instruction
    /// Currently, only `Br`, `Call` and `Ret`are control flow instructions.
    pub fn is_ctrl(&self) -> bool {
        match self {
            Instr::Br { cond: _, tr: _, fls: _ } | Instr::Call { func: _ } | Instr::Ret { val: _ } => true,
            _ => false
        }
    }
}

#[derive(Debug)]
pub enum UnOp {
    /// 2's complement of signed number
    Neg,
    /// Bitwise-NOT of bits
    Not,
}

impl FromStr for UnOp {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "neg" => Ok(UnOp::Neg),
            "not" => Ok(UnOp::Not),
            _ => Err("not unary operation".to_string())
        }
    }
}

impl ToString for UnOp {
    fn to_string(&self) -> String {
        format!("{:?}", self).to_lowercase()
    }
}

#[derive(Debug)]
pub enum BinOp {
    /// Addition
    Add,
    /// Subtraction
    Sub,
    /// Multiplication
    Mul,
    /// Division
    Div,
    /// Modulo
    Mod,
    /// Bitwise-AND
    And,
    /// Bitwise-OR
    Or,
    /// Bitwise-XOR
    Xor,
    /// Left shift
    Shl,
    /// Right shift
    Shr,
    /// Equal
    Eq,
    /// Not equal
    Ne,
    /// Less than
    Lt,
    /// Less equal
    Le,
    /// Greater than
    Gt,
    /// Greater equal
    Ge,
}

impl FromStr for BinOp {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "add" => Ok(BinOp::Add),
            "sub" => Ok(BinOp::Sub),
            "mul" => Ok(BinOp::Mul),
            "div" => Ok(BinOp::Div),
            "mod" => Ok(BinOp::Mod),
            "and" => Ok(BinOp::And),
            "or" => Ok(BinOp::Or),
            "xor" => Ok(BinOp::Xor),
            "shl" => Ok(BinOp::Shl),
            "shr" => Ok(BinOp::Shr),
            "eq" => Ok(BinOp::Eq),
            "ne" => Ok(BinOp::Ne),
            "lt" => Ok(BinOp::Lt),
            "le" => Ok(BinOp::Le),
            "gt" => Ok(BinOp::Gt),
            "ge" => Ok(BinOp::Ge),
            _ => Err("not binary operation".to_string())
        }
    }
}

impl ToString for BinOp {
    fn to_string(&self) -> String { format!("{:?}", self).to_lowercase() }
}
