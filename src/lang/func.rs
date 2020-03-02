use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt::{Debug, Error, Formatter};
use std::hash::{Hash, Hasher};
use std::iter::FromIterator;
use std::ops::Deref;
use std::rc::Rc;

use crate::lang::graph::{BfsIter, DfsIter, Vertex};
use crate::lang::graph::dom;
use crate::lang::instr::{Instr, InstrRef};
use crate::lang::ssa::SsaFlag;
use crate::lang::util::ExtRc;
use crate::lang::value::{Scope, SymbolRef, Type, Typed};

#[derive(Debug)]
pub struct Func {
    /// Name of this function
    pub name: String,
    /// Scope of this function
    pub scope: Rc<Scope>,
    /// Parameter list
    pub param: Vec<RefCell<SymbolRef>>,
    /// Return type
    pub ret: Type,
    /// Entrance block of this function
    pub ent: RefCell<BlockRef>,
    /// Set of exit blocks of this function
    pub exit: RefCell<HashSet<BlockRef>>,
    /// Whether this function is in SSA form.
    /// This tag should only be set by verification and transformation function.
    pub ssa: SsaFlag,
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
            param: self.param.iter().map(|p| p.borrow().get_type()).collect(),
            ret: Box::new(self.ret.clone()),
        }
    }
}

impl Func {
    pub fn new(name: String, scope: Scope, param: Vec<RefCell<SymbolRef>>, ret: Type,
               ent: BasicBlock) -> Func
    {
        Func {
            name,
            scope: Rc::new(scope),
            param,
            ret,
            ent: RefCell::new(ExtRc::new(ent)),
            exit: RefCell::new(HashSet::new()),
            ssa: SsaFlag::new(),
        }
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

    /// Whether this block is entrance of the function.
    /// This replies on the correct computation of dominator tree.
    pub fn is_entrance(&self) -> bool { self.parent.borrow().is_none() }

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

    /// Get first instruction of this block
    pub fn head(&self) -> InstrRef {
        self.instr.borrow().front().unwrap().clone()
    }

    /// Get last instruction of this block
    pub fn tail(&self) -> InstrRef {
        self.instr.borrow().back().unwrap().clone()
    }

    /// Possibly get the instruction before given one
    pub fn before(&self, instr: &InstrRef) -> Option<InstrRef> {
        self.instr.borrow().iter().position(|i| i == instr)
            .and_then(|idx| self.instr.borrow().get(idx - 1).cloned())
    }

    /// Possibly get the instruction after given one
    pub fn after(&self, instr: &InstrRef) -> Option<InstrRef> {
        self.instr.borrow().iter().position(|i| i == instr)
            .and_then(|idx| self.instr.borrow().get(idx + 1).cloned())
    }

    /// If the tail of the instruction list is a control flow instruction, insert `ins` before
    /// it. Otherwise, push to the back of the list.
    pub fn insert_before_ctrl(&self, ins: Instr) {
        if self.is_complete() {
            let idx = self.instr.borrow().len() - 1;
            self.instr.borrow_mut().insert(idx, ExtRc::new(ins))
        } else {
            self.push_back(ins)
        }
    }

    /// Generate predecessor list from for phi instructions.
    /// The difference is that this allows one predecessor to be `None` if it is the entrance
    /// block.
    pub fn phi_pred(&self) -> Vec<Option<BlockRef>> {
        let mut pred: Vec<Option<BlockRef>> = self.pred.borrow().iter().cloned()
            .map(|p| Some(p)).collect();
        if self.is_entrance() { // entrance block
            pred.push(None)
        }
        pred
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

    /// Decide if this block dominates the given block.
    /// This method has logarithm time complexity. Though a linear time algorithm is possible,
    /// it requires keeping extra data in the block structure.
    pub fn dominates(&self, other: BlockRef) -> bool {
        let mut cur = Some(other);
        loop {
            match cur {
                Some(block) if *self == block => return true,
                None => return false,
                _ => cur = cur.unwrap().parent.borrow().clone()
            }
        }
    }
}

impl Vertex<BlockRef> for BlockRef {
    fn this(&self) -> BlockRef { self.clone() }
    fn pred(&self) -> Vec<BlockRef> { self.pred.borrow().deref().clone() }
    fn succ(&self) -> Vec<BlockRef> { self.succ.borrow().deref().clone() }
}

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

    /// Build dominator tree according to current CFG.
    /// This method is just a wrapper for the generic graph algorithm.
    pub fn build_dom(&self) {
        // Remove unreachable blocks
        self.remove_unreachable();
        // Clear previously computed dominator
        self.dfs().for_each(|block| {
            block.parent.replace(None);
            block.child.borrow_mut().clear();
        });
        // Run the Lengauer-Tarjan algorithm
        let result = dom::build(self.ent.borrow().clone());
        for (block, dom) in result {
            block.parent.replace(Some(dom.clone()));
            dom.child.borrow_mut().push(block);
        }
    }
}

impl Func {
    /// Return an iterator to breadth-first search the CFG.
    pub fn bfs(&self) -> BfsIter<BlockRef> {
        Vertex::bfs(self.ent.borrow().deref())
    }

    /// Return an iterator to depth-first search the CFG.
    pub fn dfs(&self) -> DfsIter<BlockRef> {
        Vertex::dfs(self.ent.borrow().deref())
    }
}

/// Visitor trait of dominance tree
pub trait BlockListener {
    /// Called on the very beginning of visiting.
    fn on_begin(&mut self, func: &Func);

    /// Called when the visiting is finished.
    fn on_end(&mut self, func: &Func);

    /// Called when the subtree whose root is current block is entered, before visiting its
    /// children.
    fn on_enter(&mut self, block: BlockRef);

    /// Called when the offspring of this block have already been visited, and ready to leave
    /// this subtree.
    fn on_exit(&mut self, block: BlockRef);

    /// Called when a child subtree is entered.
    fn on_enter_child(&mut self, this: BlockRef, child: BlockRef);

    /// Called when leaving a child subtree
    fn on_exit_child(&mut self, this: BlockRef, child: BlockRef);
}

impl Func {
    /// Walk the dominator tree of this function with given listener trait object
    pub fn walk_dom<L>(&self, listener: &mut L) where L: BlockListener {
        listener.on_begin(self);
        self.visit_block(self.ent.borrow().clone(), listener);
        listener.on_end(self);
    }

    fn visit_block<L>(&self, block: BlockRef, listener: &mut L) where L: BlockListener {
        listener.on_enter(block.clone());
        for child in block.child.borrow().iter() {
            listener.on_enter_child(block.clone(), child.clone());
            self.visit_block(child.clone(), listener);
            listener.on_exit_child(block.clone(), child.clone());
        }
        listener.on_exit(block);
    }

    /// Iterate blocks in dominator tree order.
    /// This provide a simpler interface for procedures that only want to visit each block.\
    pub fn iter_dom<F>(&self, mut f: F) where F: FnMut(BlockRef) {
        let mut stack = vec![self.ent.borrow().clone()];
        loop {
            match stack.pop() {
                Some(block) => {
                    block.child.borrow().iter().cloned().for_each(|c| stack.push(c));
                    f(block)
                }
                None => break
            }
        }
    }
}

/// Represent an vertex in the reverse CFG
#[derive(Eq, Clone, Debug)]
enum RevVert<'a> {
    Block(BlockRef, &'a Func),
    Exit(&'a Func),
}

impl PartialEq for RevVert<'_> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            // Only the block pointers need to be compared.
            (RevVert::Block(b1, _), RevVert::Block(b2, _)) => b1.eq(b2),
            // There is no chance that two blocks from different function are compared.
            (RevVert::Exit(_), RevVert::Exit(_)) => true,
            _ => false
        }
    }
}

impl Hash for RevVert<'_> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            RevVert::Block(block, _) => block.hash(state),
            RevVert::Exit(func) => (*func as *const Func).hash(state)
        }
    }
}

impl<'a> Vertex<RevVert<'a>> for RevVert<'a> {
    fn this(&self) -> RevVert<'a> { self.clone() }

    fn pred(&self) -> Vec<RevVert<'a>> {
        match self {
            // Predecessors of a block in the reverse CFG are successors of that block in the
            // forward CFG. For exit blocks of the function, its predecessor should be the
            // `Exit` vertex, since it is not included in the original forward CFG
            RevVert::Block(block, func) => if func.exit.borrow().contains(&block) {
                vec![RevVert::Exit(func)]
            } else {
                block.succ.borrow().iter().cloned()
                    .map(|succ| RevVert::Block(succ, func)).collect()
            }
            // Function exit has no predecessors in the reverse CFG, since it has no successors in
            // the forward CFG.
            RevVert::Exit(_) => vec![]
        }
    }

    fn succ(&self) -> Vec<RevVert<'a>> {
        match self {
            // Successors of a block in the reverse CFG are predecessors of that block in the
            // forward CFG.
            RevVert::Block(block, func) => block.pred.borrow().iter().cloned()
                .map(|pred| RevVert::Block(pred, func)).collect(),
            // Successors of function exit in the reverse CFG are exit blocks, since its
            // predecessors are these blocks in the forward CFG
            RevVert::Exit(func) => func.exit.borrow().iter().cloned()
                .map(|exit| RevVert::Block(exit, func)).collect()
        }
    }
}

impl Func {
    // Visit CFG in order of post-dominator tree
    pub fn post_dom<F>(&self, mut f: F) where F: FnMut(BlockRef) {
        // Build dominator tree for reverse CFG
        let root = RevVert::Exit(self);
        let nodes: Vec<_> = root.dfs().collect();
        let parent = dom::build(root.clone());
        let mut child: HashMap<RevVert, Vec<RevVert>> = nodes.iter().cloned()
            .map(|v| (v, vec![])).collect();
        parent.into_iter().for_each(|(c, p)| child.get_mut(&p).unwrap().push(c));

        // Traverse post-dominator tree
        let mut stack: Vec<RevVert> = child[&root].iter().cloned().collect();
        loop {
            match stack.pop() {
                Some(node) => {
                    child[&node].iter().cloned().for_each(|v| stack.push(v));
                    if let RevVert::Block(block, _) = node { f(block) } else { unreachable!() }
                }
                None => break
            }
        }
    }
}

/// Builder of dominance frontier
struct DfBuilder {
    stack: Vec<HashSet<BlockRef>>,
    df: HashMap<BlockRef, Vec<BlockRef>>,
}

impl BlockListener for DfBuilder {
    fn on_begin(&mut self, _: &Func) {}

    fn on_end(&mut self, _: &Func) {}

    fn on_enter(&mut self, block: BlockRef) {
        self.stack.push(HashSet::new());
        for succ in block.succ.borrow().iter() {
            if *succ.parent.borrow() != Some(block.clone()) {
                self.stack.last_mut().unwrap().insert(succ.clone());
            }
        }
    }

    fn on_exit(&mut self, block: BlockRef) {
        let df_set = Vec::from_iter(self.stack.pop().unwrap().into_iter());
        self.df.insert(block, df_set);
    }

    fn on_enter_child(&mut self, _: BlockRef, _: BlockRef) {}

    fn on_exit_child(&mut self, this: BlockRef, child: BlockRef) {
        for w in self.df.get(&child).cloned().unwrap() {
            if !this.dominates(w.clone()) || this == w { // this does not strictly dominates w
                self.stack.last_mut().unwrap().insert(w);
            }
        }
    }
}

impl Func {
    /// Compute dominance frontiers for all basic blocks.
    /// This should be called after dominator tree is built.
    pub fn compute_df(&self) -> HashMap<BlockRef, Vec<BlockRef>> {
        let mut builder = DfBuilder {
            stack: vec![],
            df: HashMap::new(),
        };
        self.walk_dom(&mut builder);
        builder.df
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
