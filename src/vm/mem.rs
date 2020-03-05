use std::fmt::{Debug, Error, Formatter};
use std::rc::Rc;

use crate::lang::func::{BlockRef, Func};
use crate::lang::util::MutRc;
use crate::lang::value::{Const, Type};

/// Represent base address of memory space
#[derive(Clone, Debug)]
pub enum MemSpace {
    Stack(usize),
    Heap(HeapSpace),
}

/// Use reference counting to manage heap memory
pub type HeapSpace = MutRc<Vec<u8>>;

impl Debug for HeapSpace {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        write!(f, "{:?}", self.0.as_ptr())
    }
}

/// Function call stack
pub struct Stack {
    /// Frames of called functions
    frame: Vec<FrameRef>,
    /// All allocated spaces
    alloc: Vec<Vec<u8>>,
}

impl Stack {
    pub fn new() -> Stack { Stack { frame: vec![], alloc: vec![] } }

    pub fn unwind(&self) -> Vec<FrameRef> { self.frame.clone() }

    /// Push a new frame to stack with the given function.
    pub fn push_frame(&mut self, func: Rc<Func>) {
        let frame = Frame {
            func,
            block: None,
            instr: 0,
            count: 0,
        };
        self.frame.push(MutRc::new(frame));
    }

    /// Pop a frame from stack.
    pub fn pop_frame(&mut self) {
        self.frame.pop().map(|frame| {
            for _ in 0..frame.borrow().count {
                self.alloc.pop();
            }
        });
    }

    pub fn top(&mut self) -> FrameRef { self.frame.last().unwrap().clone() }

    pub fn clear(&mut self) {
        self.frame.clear();
        self.alloc.clear();
    }
}

/// A frame on call stack
#[derive(Clone, Debug)]
pub struct Frame {
    /// The function called on this frame
    pub func: Rc<Func>,
    /// The block being executed
    pub block: Option<BlockRef>,
    /// The index of instruction in this block being executed
    pub instr: usize,
    /// Count of allocated memory spaces
    count: usize,
}

/// Frames must be held as references instead of values, because previous function calls will hold
/// reference to their frames, which prevent the stack from growing.
pub type FrameRef = MutRc<Frame>;

/// Register that holds a primitive or pointer value
#[derive(Clone, Debug)]
pub enum Reg {
    Val(Const),
    Ptr { base: Option<MemSpace>, off: usize },
}

impl From<&Type> for Reg {
    fn from(ty: &Type) -> Self {
        match ty {
            Type::I(_) => Reg::Val(Const::zero(ty)),
            Type::Ptr(_) => Reg::Ptr { base: None, off: 0 },
            _ => panic!("cannot create register for type that is neither primitive nor pointer")
        }
    }
}

impl Reg {
    pub fn is_val(&self) -> bool {
        match self {
            Reg::Val(_) => true,
            Reg::Ptr { base: _, off: _ } => false
        }
    }

    pub fn is_ptr(&self) -> bool {
        match self {
            Reg::Ptr { base: _, off: _ } => true,
            Reg::Val(_) => false
        }
    }

    pub fn get(&self) -> Const {
        match self {
            Reg::Val(v) => *v,
            Reg::Ptr { base: _, off: _ } => panic!("cannot get value of pointer")
        }
    }

    pub fn set(&mut self, new: Const) {
        match self {
            Reg::Val(c) => *c = new,
            Reg::Ptr { base: _, off: _ } => panic!("cannot set value to pointer")
        }
    }
}
