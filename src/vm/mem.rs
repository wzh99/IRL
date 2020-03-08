use std::collections::HashMap;
use std::fmt::{Debug, Error, Formatter};
use std::mem::size_of;
use std::ops::Add;
use std::rc::Rc;

use crate::lang::func::{BlockRef, Func};
use crate::lang::util::MutRc;
use crate::lang::value::{Const, SymbolRef, Type};

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

    pub fn len(&self) -> usize { self.frame.len() }

    /// Push a new frame to stack with the given function.
    pub fn push_frame(&mut self, func: &Rc<Func>) {
        let frame = Frame {
            func: func.clone(),
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

    pub fn alloc(&mut self, size: usize) -> Reg {
        let addr = self.alloc.len();
        self.alloc.push(vec![0; size]);
        self.top().borrow_mut().count += 1;
        Reg::Ptr { base: Some(MemSpace::Stack(addr)), off: 0 }
    }

    pub fn get_mem(&self, addr: usize) -> Option<&Vec<u8>> { self.alloc.get(addr) }

    pub fn get_mem_mut(&mut self, addr: usize) -> Option<&mut Vec<u8>> {
        self.alloc.get_mut(addr)
    }

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

pub type RegFile = HashMap<SymbolRef, Reg>;

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
    pub fn zero(ty: &Type) -> Reg {
        match ty {
            Type::I(_) => Reg::Val(Const::zero(ty)),
            Type::Ptr(_) => Reg::Ptr { base: None, off: 0 },
            _ => panic!("cannot create zero value for type {:?}", ty)
        }
    }

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

    pub fn get_const(&self) -> Const {
        match self {
            Reg::Val(v) => *v,
            Reg::Ptr { base: _, off: _ } => panic!("cannot get value of pointer")
        }
    }

    pub fn set_const(&mut self, new: Const) {
        match self {
            Reg::Val(c) => *c = new,
            Reg::Ptr { base: _, off: _ } => panic!("cannot set value to pointer")
        }
    }

    pub fn get_off(&self) -> usize {
        match self {
            Reg::Ptr { base: _, off } => *off,
            Reg::Val(_) => panic!("cannot get offset of value")
        }
    }

    pub fn set_off(&mut self, new: usize) {
        match self {
            Reg::Ptr { base: _, off } => *off = new,
            Reg::Val(_) => panic!("cannot set offset to value")
        }
    }
}

impl Type {
    /// Indicate runtime size of types in this VM
    pub fn size(&self) -> usize {
        match self {
            Type::Void => 0,
            Type::I(1) => size_of::<bool>(),
            Type::I(b) => *b as usize / 8,
            Type::Ptr(_) => size_of::<Reg>(),
            Type::Array { elem, len } => elem.size() * *len,
            Type::Struct { field } => field.iter().map(|f| f.size()).fold(0, Add::add),
            Type::Fn { param: _, ret: _ } => size_of::<Rc<Func>>(),
            Type::Alias(_) => self.orig().size(),
        }
    }
}
