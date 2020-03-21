use std::ops::{Add, Deref};

use crate::lang::instr::{BinOp, Inst};
use crate::lang::value::{Type, Typed, Value};

#[derive(Copy, Clone, Debug)]
pub struct Counter {
    /// Number of instructions executed
    pub num: usize,
    /// Time consumed in executing this program
    pub time: usize,
}

impl Counter {
    pub fn new() -> Self { Counter { num: 0, time: 0 } }

    pub fn reset(&mut self) {
        self.num = 0;
        self.time = 0;
    }

    pub fn count(&mut self, instr: &Inst) {
        self.num += 1;
        let mut time = match instr {
            Inst::Mov { src: _, dst: _ } => MOV,
            Inst::Un { op: _, opd: _, dst: _ } => UN_OP,
            Inst::Bin { op, fst, snd: _, dst: _ } => {
                let ty = fst.borrow().get_type();
                match op {
                    op if op.is_bitwise() | op.is_cmp() | op.is_shift() => FAST_BIN,
                    BinOp::Add | BinOp::Sub => FAST_BIN,
                    BinOp::Mul => IMUL,
                    BinOp::Div => match ty {
                        Type::I(64) => I64_DIV,
                        Type::I(_) => IDIV,
                        _ => unreachable!()
                    }
                    _ => unreachable!()
                }
            }
            Inst::Call { func: _, arg, dst: _ } => CALL + arg.len() * MOV,
            Inst::Ret { val: _ } => RET,
            Inst::Jmp { tgt: _ } | Inst::Br { cond: _, tr: _, fls: _ } => JMP,
            Inst::Phi { src: _, dst: _ } => MOV,
            Inst::Alloc { dst: _ } => MOV,
            Inst::New { dst: _, len: _ } => NEW,
            Inst::Ptr { base: _, off, ind, dst: _ } => {
                let mut opd: Vec<_> = ind.iter().collect();
                off.as_ref().map(|off| opd.push(off));
                opd.iter().map(|opd| {
                    match opd.borrow().deref() {
                        // all constant offset can be computed at irc time
                        Value::Const(_) => 0,
                        // variable offset require one multiplication and one addition
                        Value::Var(_) => IMUL + FAST_BIN
                    }
                }).fold(1, Add::add)
            }
            Inst::Ld { ptr: _, dst: _ } | Inst::St { src: _, ptr: _ } => MEM,
        };
        instr.dst().map(|dst| if !dst.borrow().is_local_var() { time += GLB_PEN });
        self.time += time;
    }
}

/// Weights for all basic operations
/// These values are based on number if clock cycles to do the corresponding computation in modern
/// processors. They can be changed to suit your need.
/// See [https://www.agner.org/optimize/]

/// Move between registers
const MOV: usize = 1;
/// If the instruction writes to global variable, add this additional penalty.
const GLB_PEN: usize = 1;
/// Unary operations
const UN_OP: usize = 1;
/// Binary operations that can be done fast
const FAST_BIN: usize = 1;
/// Multiplication of integers
const IMUL: usize = 2;
/// Division of integers
const IDIV: usize = 10;
const I64_DIV: usize = 40;
/// Call a function
const CALL: usize = 3;
/// Pop stack pointer
const RET: usize = 1;
/// Jump
const JMP: usize = 1;
/// Allocate memory on heap
const NEW: usize = 10;
/// Memory access
const MEM: usize = 2;
