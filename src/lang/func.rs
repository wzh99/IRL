use std::cell::{Cell, RefCell};
use std::cmp::Ordering;
use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt::{Debug, Error, Formatter};
use std::iter::FromIterator;
use std::ops::Deref;
use std::rc::Rc;

use crate::lang::ExtRc;
use crate::lang::instr::{Instr, InstrRef};
use crate::lang::val::{Scope, SymbolRef, Type, Typed};

#[derive(Debug)]
pub struct Func {
    /// Name of this function
    pub name: String,
    /// Scope of this function
    pub scope: Rc<Scope>,
    /// Parameter list
    pub param: Vec<SymbolRef>,
    /// Return type
    pub ret: Type,
    /// Entrance block of this function
    pub ent: RefCell<BlockRef>,
    /// Set of exit blocks of this function
    pub exit: RefCell<HashSet<BlockRef>>,
    /// Whether this program is verified to be in SSA form.
    ssa: RefCell<bool>,
}

impl PartialEq for Func {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name && self.get_type() == other.get_type()
    }
}

impl Eq for Func {}

impl Typed for Func {
    fn get_type(&self) -> Type {
        Type::Fn {
            param: self.param.iter().map(|p| p.get_type()).collect(),
            ret: Box::new(self.ret.clone()),
        }
    }
}

impl Func {
    pub fn new(name: String, scope: Scope, param: Vec<SymbolRef>, ret: Type, ent: BasicBlock)
               -> Func
    {
        Func {
            name,
            scope: Rc::new(scope),
            param,
            ret,
            ent: RefCell::new(ExtRc::new(ent)),
            exit: RefCell::new(HashSet::new()),
            ssa: RefCell::new(false),
        }
    }

    /// Return an iterator to breadth-first search the CFG.
    pub fn bfs(&self) -> BfsIter {
        let ent = self.ent.borrow().clone();
        BfsIter {
            queue: VecDeque::from_iter(vec![ent.clone()]),
            visited: HashSet::from_iter(vec![ent]),
        }
    }

    /// Return an iterator to depth-first search the CFG.
    pub fn dfs(&self) -> DfsIter {
        let ent = self.ent.borrow().clone();
        DfsIter {
            stack: vec![ent.clone()],
            visited: HashSet::from_iter(vec![ent]),
        }
    }
}

/// Breadth-first iterator of blocks
pub struct BfsIter {
    queue: VecDeque<BlockRef>,
    visited: HashSet<BlockRef>,
}

impl Iterator for BfsIter {
    type Item = BlockRef;

    fn next(&mut self) -> Option<Self::Item> {
        self.queue.pop_front().map(|next| {
            for succ in next.succ.borrow().iter() {
                if !self.visited.contains(succ) {
                    self.queue.push_back(succ.clone());
                    self.visited.insert(succ.clone());
                }
            }
            next
        })
    }
}

/// Depth-first iterator of blocks
pub struct DfsIter {
    stack: Vec<BlockRef>,
    visited: HashSet<BlockRef>,
}

impl Iterator for DfsIter {
    type Item = BlockRef;

    fn next(&mut self) -> Option<Self::Item> {
        self.stack.pop().map(|next| {
            for succ in next.succ.borrow().iter().rev() {
                if !self.visited.contains(succ) {
                    self.stack.push(succ.clone());
                    self.visited.insert(succ.clone());
                }
            }
            next
        })
    }
}

#[derive(Debug)]
pub struct BasicBlock {
    /// Name of this basic block
    pub name: String,
    /// Linked list of all instructions in this block
    pub instr: RefCell<VecDeque<InstrRef>>,
    /// Inside a function, the basic blocks form a control flow graph. For each basic block,
    /// it has predecessor and successor sets, depending on the control flow instructions in
    /// the block. `Vec` is actually used here because we want to keep the insertion order of
    /// blocks.
    /// Predecessor blocks
    pub pred: RefCell<Vec<BlockRef>>,
    /// Successor blocks
    pub succ: RefCell<Vec<BlockRef>>,
    /// Parent of this block in the dominator tree
    /// This and `child` is dependent on the structure of the CFG. They can only be modified by
    /// the method of `Func` and granted read-only access by the public method.
    parent: RefCell<Option<BlockRef>>,
    /// Children of this block in the dominator tree
    child: RefCell<Vec<BlockRef>>,
}

pub type BlockRef = ExtRc<BasicBlock>;

impl Debug for BlockRef {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        write!(f, "{}", self.name)
    }
}

impl Ord for BlockRef {
    fn cmp(&self, other: &Self) -> Ordering { self.name.cmp(&other.name) }
}

impl PartialOrd for BlockRef {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.name.partial_cmp(&other.name)
    }
}

impl Default for BasicBlock {
    fn default() -> Self { BasicBlock::new("".to_string()) }
}

impl BasicBlock {
    pub fn new(name: String) -> BasicBlock {
        BasicBlock {
            name,
            instr: RefCell::new(VecDeque::new()),
            pred: RefCell::new(vec![]),
            succ: RefCell::new(vec![]),
            parent: RefCell::new(None),
            child: RefCell::new(Vec::new()),
        }
    }

    /// Get parent of this block in the dominator tree.
    pub fn parent(&self) -> Option<BlockRef> { self.parent.borrow().clone() }

    /// Get children of this block in the dominator tree.
    pub fn children(&self) -> Vec<BlockRef> { self.child.borrow().clone() }

    /// A basic block is complete iff. it ends with control instructions.
    pub fn is_complete(&self) -> bool {
        match self.instr.borrow().back() {
            Some(back) => back.deref().is_ctrl(),
            None => false
        }
    }

    /// Push instruction to the front of the instruction list.
    pub fn push_front(&self, ins: Instr) {
        self.instr.borrow_mut().push_front(ExtRc::new(ins))
    }

    /// Push instruction to the back of the instruction list.
    pub fn push_back(&self, ins: Instr) {
        self.instr.borrow_mut().push_back(ExtRc::new(ins))
    }

    /// If the tail of the instruction list is a control flow instruction, push `ins` before
    /// it. Otherwise, push to the back of the list.
    pub fn push_before_ctrl(&self, ins: Instr) {
        if self.is_complete() {
            let idx = self.instr.borrow().len() - 1;
            self.instr.borrow_mut().insert(idx, ExtRc::new(ins))
        } else {
            self.push_back(ins)
        }
    }

    /// Visit each instruction in this block
    pub fn for_each<F>(&self, f: F) where F: FnMut(&InstrRef) {
        self.instr.borrow().iter().for_each(f)
    }
}

impl BlockRef {
    /// Add a directed edge from this block to another.
    /// This method add `to` to the successor set of this block and add this block to the
    /// predecessor set of `to` block.
    pub fn connect(&self, to: BlockRef) {
        if to.pred.borrow().iter().find(|b| *b == self).is_none() {
            to.pred.borrow_mut().push(self.clone())
        }
        if self.succ.borrow().iter().find(|b| *b == &to).is_none() {
            self.succ.borrow_mut().push(to)
        }
    }

    /// Remove a directed edge from this block to another.
    /// If there was an edge before, this is the inverse operation of `connect`. Otherwise,
    /// nothing will be actually done.
    pub fn disconnect(&self, to: BlockRef) {
        to.pred.borrow().iter().position(|b| b == self)
            .map(|i| to.pred.borrow_mut().remove(i));
        self.succ.borrow().iter().position(|b| b == &to)
            .map(|i| self.succ.borrow_mut().remove(i));
    }
}

/// Node in a depth-first spanning tree
#[derive(Debug)]
struct DfNode {
    /// Point back to the actual block
    block: BlockRef,
    /// Parent of this node in the tree
    parent: Cell<usize>,
    /// Semidominator of this node
    semi: Cell<usize>,
    /// Set of nodes whose semidominator is this node
    bucket: RefCell<HashSet<usize>>,
    /// Intermediate dominator
    dom: Cell<usize>,
    /// Tree root in the forest
    ancestor: Cell<usize>,
    /// Record intermediate evaluation result
    label: Cell<usize>,
    /// Size of subtree with current node as root
    size: Cell<usize>,
    /// Child of current node
    child: Cell<usize>,
}

const NONE: usize = usize::max_value();

impl Func {
    /// Build dominator tree according to current CFG using Lengauer-Tarjan algorithm.
    /// Only after calling this method can `parent` and `children` methods of `BasicBlock`
    /// return valid results.
    pub fn build_dom(&self) {
        // Perform depth-first search on the CFG
        let mut nodes = Vec::new();
        let mut block_num = HashMap::new(); // map block to number
        self.dfs().enumerate().for_each(|(i, block)| {
            block_num.insert(block.clone(), i);
            nodes.push(DfNode { // store nodes as the order of traversal
                block,
                parent: Cell::new(NONE),
                semi: Cell::new(NONE),
                bucket: RefCell::new(HashSet::new()),
                dom: Cell::new(NONE),
                ancestor: Cell::new(NONE),
                label: Cell::new(i),
                size: Cell::new(0),
                child: Cell::new(NONE),
            })
        });

        let semi = |v: usize| nodes[v].semi.get();
        let parent = |v_num: usize| nodes[v_num].parent.get();

        if nodes.len() <= 1 { return; } // no point in building dominator tree
        for (v_num, v_node) in nodes.iter().enumerate() { // find parent for each node
            v_node.semi.replace(v_num);
            for w_block in v_node.block.succ.borrow().iter() {
                let w_num = block_num.get(w_block).copied().unwrap();
                let w_node = &nodes[w_num];
                if w_node.semi.get() == NONE {
                    w_node.parent.replace(v_num);
                }
            }
        }

        for w_num in (1..nodes.len()).rev() {
            // Compute semidominator of each vertex
            let w_node = &nodes[w_num];
            for v_block in w_node.block.pred.borrow().iter() {
                let v_num = block_num.get(v_block).copied().unwrap();
                let u_num = self.eval(&nodes, v_num);
                if semi(u_num) < semi(w_num) {
                    w_node.semi.replace(semi(u_num));
                }
                nodes[w_node.semi.get()].bucket.borrow_mut().insert(w_num);
                self.link(&nodes, parent(w_num), w_num);
            }
        }
    }

    /// Find ancestor of node `v` with smallest semidominator.
    fn eval(&self, nodes: &Vec<DfNode>, v: usize) -> usize {
        let label = |v: usize| nodes[v].label.get();
        let ancestor = |v: usize| nodes[v].ancestor.get();
        let semi = |v: usize| nodes[v].semi.get();

        if ancestor(v) == NONE { label(v) } else {
            self.compress(nodes, v);
            if semi(label(ancestor(v))) >= semi(label(v)) {
                label(v)
            } else {
                label(ancestor(v))
            }
        }
    }

    /// Compress path to ancestor
    fn compress(&self, nodes: &Vec<DfNode>, v: usize) {
        let label = |v: usize| nodes[v].label.get();
        let ancestor = |v: usize| nodes[v].ancestor.get();
        let semi = |v: usize| nodes[v].semi.get();

        if ancestor(ancestor(v)) == NONE { return; } // cannot compress
        self.compress(nodes, ancestor(v));
        if semi(label(ancestor(v))) < semi(label(v)) {
            nodes[v].label.replace(label(ancestor(v)));
        }
        nodes[v].ancestor.replace(ancestor(ancestor(v)));
    }

    /// Add edge `(v, w)` to the forest
    fn link(&self, nodes: &Vec<DfNode>, v: usize, w: usize) {
        let size = |v: usize| if v == NONE { 0 } else { nodes[v].size.get() };
        let label = |v: usize| if v == NONE { NONE } else { nodes[v].label.get() };
        let semi = |v: usize| if v == NONE { NONE } else { nodes[v].semi.get() };
        let child = |v: usize| nodes[v].child.get();
        let parent = |v: usize| nodes[v].parent.get();

        let mut s = w;
        while semi(label(w)) < semi(label(child(s))) {
            if size(s) + size(child(child(s))) >= 2 * size(child(s)) {
                nodes[child(s)].parent.replace(s);
                nodes[s].child.replace(child(child(s)));
            } else {
                nodes[child(s)].size.replace(size(s));
                nodes[s].parent.replace(child(s));
                s = parent(s);
            }
        }
        nodes[s].label.replace(label(w));
        nodes[v].size.replace(size(v) + size(w));
        if size(v) < 2 * size(w) {
            let tmp = child(v);
            nodes[v].child.replace(s);
            s = tmp;
        }
        while s != NONE {
            nodes[s].parent.replace(v);
            s = child(s)
        }
    }
}
