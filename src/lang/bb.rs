use crate::lang::instr::Instr;
use crate::lang::val::Func;
use std::rc::Rc;
use std::collections::{LinkedList, HashSet};
use std::cell::RefCell;

pub struct BasicBlock {
    /// Name of this basic block
    name: String,
    /// The function that this basic block lies in
    func: Rc<Func>,
    /// Linked list of all instructions in this block
    instr: LinkedList<Instr>,
    /// Inside a function, the basic blocks form a control flow graph. For each basic block, it
    /// has predecessor and successor sets, depending on the control flow instructions in the
    /// block.
    pred: HashSet<Rc<RefCell<BasicBlock>>>, // predecessors
    succ: HashSet<Rc<RefCell<BasicBlock>>>, // successors
}
