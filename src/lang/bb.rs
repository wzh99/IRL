use crate::lang::instr::{Instr, InstrRef};
use std::collections::{VecDeque, HashSet};
use std::cell::RefCell;
use std::fmt::{Debug, Formatter, Error};
use crate::lang::{ExtRc, MutRc};
use std::ops::Deref;

pub struct BasicBlock {
    /// Name of this basic block
    pub name: String,
    /// Linked list of all instructions in this block
    pub instr: RefCell<VecDeque<InstrRef>>,
    /// Inside a function, the basic blocks form a control flow graph. For each basic block, it
    /// has predecessor and successor sets, depending on the control flow instructions in the
    /// block.
    /// Predecessor blocks
    pub pred: RefCell<HashSet<BlockRef>>,
    /// Successor blocks
    pub succ: RefCell<HashSet<BlockRef>>,
}

pub type BlockRef = ExtRc<BasicBlock>;

impl Debug for BlockRef {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        write!(f, "{}", self.name)
    }
}

impl Default for BasicBlock {
    fn default() -> Self { BasicBlock::new("".to_string()) }
}

impl BasicBlock {
    pub fn new(name: String) -> BasicBlock {
        BasicBlock{
            name,
            instr: RefCell::new(VecDeque::new()),
            pred: RefCell::new(HashSet::new()),
            succ: RefCell::new(HashSet::new())
        }
    }

    /// A basic block is complete iff. it ends with control instructions.
    pub fn is_complete(&self) -> bool {
        match self.instr.borrow().back() {
            Some(back) => back.deref().borrow().is_ctrl(),
            None => false
        }
    }

    /// Push instruction to the front of the instruction list
    pub fn push_front(&self, ins: Instr) {
        self.instr.borrow_mut().push_front(MutRc::new(ins))
    }

    /// Push instruction to the back of the instruction list
    pub fn push_back(&self, ins: Instr) {
        self.instr.borrow_mut().push_back(MutRc::new(ins))
    }

    /// If the tail of the instruction list is a control flow instruction, push `ins` before
    /// it. Otherwise, push to the back of the list.
    pub fn push_before_ctrl(&self, ins: Instr) {
        if self.is_complete() {
            let idx = self.instr.borrow().len() - 1;
            self.instr.borrow_mut().insert(idx, MutRc::new(ins))
        } else {
           self.push_back(ins)
        }
    }
}
