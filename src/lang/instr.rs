use crate::lang::val::Value;
use std::rc::Rc;
use crate::lang::bb::BasicBlock;

pub enum Instr {
    /// Move (copy) data from one virtual register to another
    Mov{src: Value, dst: Value},
    /// Unary operations
    Un{op: UnOp, opd: Value, res: Value},
    /// Binary operations
    Bin{op: BinOp, left: Value, right: Value, res: Value},
    /// Jump to another basic block
    Jmp{tgt: Rc<BasicBlock>},
    /// Conditional branch to labels
    /// If `cond` evaluates to true, branch to `tr` block, otherwise to `fls` block
    Br{cond: Value, tr: Rc<BasicBlock>, fls: Rc<BasicBlock>},
    /// Procedure call
    Call{func: Value},
    /// Return computation results, or `None` if return type is `Void`.
    Ret{val: Option<Value>},
    /// Phi instructions in SSA
    /// A phi instruction hold a list of block-value pairs. The blocks are all predecessors of
    /// current block (where this instruction is defined). The values are different versions of
    /// of a certain variable.
    Phi{pair: Vec<(Rc<BasicBlock>, Value)>}
}

impl Instr {
    /// Decide if this instruction is a control flow instruction
    /// Currently, only `Br`, `Call` and `Ret`are control flow instructions.
    pub fn is_ctrl(&self) -> bool {
        match self {
            Instr::Br{cond: _, tr: _, fls: _} | Instr::Call{func: _} | Instr::Ret{val: _} => true,
            _ => false
        }
    }
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

impl ToString for BinOp {
    fn to_string(&self) -> String { format!("{:?}", self).to_lowercase() }
}
