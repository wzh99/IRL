use crate::lang::instr::Instr;
use crate::lang::val::Func;
use std::rc::Rc;
use std::collections::{VecDeque, HashSet};
use std::hash::{Hash, Hasher};
use std::cell::RefCell;
use std::ops::Deref;

pub struct BasicBlock {
    /// Name of this basic block
    name: String,
    /// The function that this basic block lies in
    func: Rc<Func>,
    /// Linked list of all instructions in this block
    instr: RefCell<VecDeque<Instr>>,
    /// Inside a function, the basic blocks form a control flow graph. For each basic block, it
    /// has predecessor and successor sets, depending on the control flow instructions in the
    /// block.
    /// Predecessor blocks
    pred: RefCell<HashSet<BlockRef>>,
    /// Successor blocks
    succ: RefCell<HashSet<BlockRef>>,
}

/// A auxiliary structure to assist reference equality for basic blocks
pub struct BlockRef(Rc<BasicBlock>);

impl Eq for BlockRef {}

impl PartialEq for BlockRef {
    fn eq(&self, other: &Self) -> bool { Rc::ptr_eq(&self.0, &other.0) }
}

impl Hash for BlockRef {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (self.0.as_ref() as *const BasicBlock).hash(state)
    }
}

impl Deref for BlockRef {
    type Target = BasicBlock;
    fn deref(&self) -> &Self::Target { self.0.deref() }
}

impl BasicBlock {
    fn new(name: String, func: Rc<Func>) -> BasicBlock {
        BasicBlock{
            name,
            func,
            instr: RefCell::new(VecDeque::new()),
            pred: RefCell::new(HashSet::new()),
            succ: RefCell::new(HashSet::new())
        }
    }

    /// A basic block is complete iff. it ends with control instructions.
    pub fn is_complete(&self) -> bool {
        match self.instr.borrow().back() {
            Some(back) => back.is_ctrl(),
            None => false
        }
    }

    /// Push instruction to the front of the instruction list
    pub fn push_front(&self, ins: Instr) { self.instr.borrow_mut().push_front(ins) }

    /// Push instruction to the back of the instruction list
    pub fn push_back(&self, ins: Instr) { self.instr.borrow_mut().push_back(ins) }

    /// If the tail of the instruction list is a control flow instruction, push `ins` before
    /// it. Otherwise, push to the back of the list.
    pub fn insert_before_ctrl(&self, ins: Instr) {
        if self.is_complete() {
            let idx = self.instr.borrow().len() - 1;
            self.instr.borrow_mut().insert(idx, ins)
        } else {
           self.push_back(ins)
        }
    }
}
