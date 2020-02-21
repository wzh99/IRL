use std::cell::{Cell, RefCell};
use std::cmp::Ordering;
use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt::{Debug, Error, Formatter};
use std::iter::FromIterator;
use std::ops::Deref;
use std::rc::Rc;

use crate::lang::ExtRc;
use crate::lang::instr::{Instr, InstrRef};
use crate::lang::ssa::SsaFlag;
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
    /// Whether this function is in SSA form.
    /// This tag should only be set by verification and transformation function.
    pub ssa: SsaFlag
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
            ssa: SsaFlag::new()
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

impl Func {
    /// Return an iterator to breadth-first search the CFG.
    pub fn bfs(&self) -> BfsIter {
        let ent = self.ent.borrow().clone();
        BfsIter {
            queue: VecDeque::from_iter(vec![ent.clone()]),
            visited: HashSet::from_iter(vec![ent]),
        }
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

impl Func {
    /// Return an iterator to depth-first search the CFG.
    pub fn dfs(&self) -> DfsIter {
        let ent = self.ent.borrow().clone();
        DfsIter {
            stack: vec![ent.clone()],
            visited: HashSet::from_iter(vec![ent]),
        }
    }
}

/// Visitor trait of dominance tree
pub trait DomVisitor<E> {
    /// Called on the very beginning of visiting.
    fn on_begin(&mut self, func: &Func) -> Result<(), E>;

    /// Called when the visiting is finished.
    fn on_end(&mut self, func: &Func) -> Result<(), E>;

    /// Called when the subtree whose root is current block is entered.
    fn on_enter(&mut self, block: BlockRef) -> Result<(), E>;

    /// Called when the offspring of this block have already been visited, and ready to leave
    /// this subtree.
    fn on_exit(&mut self, block: BlockRef) -> Result<(), E>;

    /// Called when a child subtree is entered.
    fn on_enter_child(&mut self, this: BlockRef, child: BlockRef) -> Result<(), E>;

    /// Called when leaving a child subtree
    fn on_exit_child(&mut self, this: BlockRef, child: BlockRef) -> Result<(), E>;
}

impl Func {
    /// Visit the dominator tree of this function with given visitor trait object
    pub fn visit_dom<E, V>(&self, visitor: &mut V) -> Result<(), E>
        where V: DomVisitor<E>
    {
        visitor.on_begin(self)?;
        self.visit_block(self.ent.borrow().clone(), visitor)?;
        visitor.on_end(self)?;
        Ok(())
    }

    fn visit_block<E, V>(&self, block: BlockRef, visitor: &mut V) -> Result<(), E>
        where V: DomVisitor<E>
    {
        visitor.on_enter(block.clone())?;
        for child in block.child.borrow().iter() {
            visitor.on_enter_child(block.clone(), child.clone())?;
            self.visit_block(child.clone(), visitor)?;
            visitor.on_exit_child(block.clone(), child.clone())?;
        }
        visitor.on_exit(block)?;
        Ok(())
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
        let pos = to.pred.borrow().iter().position(|b| b == self);
        pos.map(|i| to.pred.borrow_mut().remove(i));
        let pos = self.succ.borrow().iter().position(|b| b == &to);
        pos.map(|i| self.succ.borrow_mut().remove(i));
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
    best: Cell<usize>,
    /// Size of subtree with current node as root
    size: Cell<usize>,
    /// Child of current node
    child: Cell<usize>,
}

const NONE: usize = usize::max_value();

impl Func {
    /// Remove unreachable blocks in this function. This is necessary for algorithms that rely
    /// on predecessors of blocks.
    pub fn remove_unreachable(&self) {
        // Mark all reachable blocks
        let mut marked = HashSet::new();
        self.dfs().for_each(|block| { marked.insert(block); });

        // Sweep unmarked blocks
        self.dfs().for_each(|block| {
            let pred_list: Vec<BlockRef> = block.pred.borrow().clone();
            for pred in pred_list {
                if !marked.contains(&pred) {
                    pred.disconnect(block.clone())
                }
            }
        })
    }

    /// Build dominator tree according to current CFG using Lengauer-Tarjan algorithm.
    /// Only after calling this method can `parent` and `children` methods of `BasicBlock`
    /// return valid results.
    /// See [https://www.cl.cam.ac.uk/~mr10/lengtarj.pdf].
    pub fn build_dom(&self) {
        // Remove unreachable blocks
        self.remove_unreachable();

        // Perform depth-first search on the CFG
        let mut nodes = Vec::new();
        let mut block_num = HashMap::new(); // map block to number
        for (i, block) in self.dfs().enumerate() {
            block_num.insert(block.clone(), i);
            nodes.push(DfNode { // store nodes as the order of traversal
                block,
                parent: Cell::new(NONE),
                semi: Cell::new(NONE),
                bucket: RefCell::new(HashSet::new()),
                dom: Cell::new(NONE),
                ancestor: Cell::new(NONE),
                best: Cell::new(i),
                size: Cell::new(0),
                child: Cell::new(NONE),
            })
        }
        if nodes.len() <= 1 { return; } // no point in building dominator tree

        let semi = |v: usize| nodes[v].semi.get();
        let parent = |v: usize| nodes[v].parent.get();
        let dom = |v: usize| nodes[v].dom.get();

        for (v_num, v_node) in nodes.iter().enumerate() { // find parent for each node
            v_node.semi.replace(v_num);
            for w_block in v_node.block.succ.borrow().iter() {
                let w_num = block_num.get(w_block).copied().unwrap();
                let w_node = &nodes[w_num];
                if w_node.semi.get() == NONE {
                    w_node.parent.set(v_num);
                }
            }
        }

        for w in (1..nodes.len()).rev() {
            // Compute semidominator of each vertex
            let p = parent(w);
            for v_block in nodes[w].block.pred.borrow().iter() {
                let v = block_num.get(v_block).copied().unwrap();
                let u = self.eval(&nodes, v);
                if semi(w) > semi(u) {
                    nodes[w].semi.set(semi(u))
                }
            }
            nodes[semi(w)].bucket.borrow_mut().insert(w);
            self.link(&nodes, p, w);

            // Implicitly define immediate dominator
            for v in nodes[p].bucket.borrow().iter().copied() {
                let u = self.eval(&nodes, v);
                nodes[v].dom.set(if semi(u) < semi(v) { u } else { p });
            }
            nodes[p].bucket.replace(HashSet::new());
        }

        // Explicitly define immediate dominator
        for w in 1..nodes.len() {
            if dom(w) != semi(w) {
                nodes[w].dom.set(dom(dom(w)));
            }
            let d = dom(w);
            nodes[w].block.parent.borrow_mut().replace(nodes[d].block.clone());
            nodes[d].block.child.borrow_mut().push(nodes[w].block.clone())
        }
    }

    /// Find ancestor of node `v` with smallest semidominator.
    fn eval(&self, nodes: &Vec<DfNode>, v: usize) -> usize {
        let best = |v: usize| nodes[v].best.get();
        let ancestor = |v: usize| nodes[v].ancestor.get();
        let semi = |v: usize| nodes[v].semi.get();

        if ancestor(v) == NONE { v } else {
            self.compress(nodes, v);
            if semi(best(ancestor(v))) >= semi(best(v)) {
                best(v)
            } else {
                best(ancestor(v))
            }
        }
    }

    fn compress(&self, nodes: &Vec<DfNode>, v: usize) {
        let best = |v: usize| nodes[v].best.get();
        let ancestor = |v: usize| nodes[v].ancestor.get();
        let semi = |v: usize| nodes[v].semi.get();

        if ancestor(ancestor(v)) == NONE { return; }
        self.compress(nodes, ancestor(v));
        if semi(best(ancestor(v))) < semi(best(v)) {
            nodes[v].best.set(best(ancestor(v)))
        }
        nodes[v].ancestor.set(ancestor(ancestor(v)))
    }

    /// Add edge `(v, w)` to the forest
    fn link(&self, nodes: &Vec<DfNode>, v: usize, w: usize) {
        let size = |v: usize| if v == NONE { 0 } else { nodes[v].size.get() };
        let best = |v: usize| if v == NONE { NONE } else { nodes[v].best.get() };
        let semi = |v: usize| if v == NONE { NONE } else { nodes[v].semi.get() };
        let child = |v: usize| if v == NONE { NONE } else { nodes[v].child.get() };

        let mut s = w;
        while child(s) != NONE && semi(best(w)) < semi(best(child(s))) {
            // Combine the first two trees in the child chain, making the larger one the
            // combined root.
            if size(s) + size(child(child(s))) >= 2 * size(child(s)) {
                nodes[child(s)].ancestor.replace(s);
                nodes[s].child.replace(child(child(s)));
            } else {
                nodes[child(s)].size.replace(size(s));
                nodes[s].ancestor.replace(child(s));
                s = child(s);
            }
        }

        // Now combine the two forests giving the combination the child chain of the smaller
        // forest. The other child chain is then collapsed, giving all its trees ancestor
        // links to v.
        nodes[s].best.replace(best(w));
        if size(v) < size(w) {
            let tmp = child(v);
            nodes[v].child.replace(s);
            s = tmp
        }
        nodes[v].size.replace(size(v) + size(w));
        while s != NONE {
            nodes[s].ancestor.replace(v);
            s = child(s)
        }
    }
}

impl Func {
    /// Compute dominance frontiers for all basic blocks.
    /// This should be called after dominator tree is built.
    pub fn compute_df(&self) -> HashMap<BlockRef, HashSet<BlockRef>> {
        Default::default()
    }
}

#[test]
fn test_dom() {
    use crate::compile::lex::Lexer;
    use crate::compile::parse::Parser;
    use crate::compile::build::Builder;
    use std::fs::File;
    use std::convert::TryFrom;
    use std::io::Read;

    let mut file = File::open("test/dom.ir").unwrap();
    let lexer = Lexer::try_from(&mut file as &mut dyn Read).unwrap();
    let parser = Parser::new(lexer);
    let tree = parser.parse().unwrap();
    let builder = Builder::new(tree);
    println!("{:?}", builder.build());
}
