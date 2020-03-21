use std::cell::{Cell, RefCell};
use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt::{Debug, Error, Formatter};
use std::hash::Hash;
use std::iter::FromIterator;
use std::ops::Deref;

use crate::lang::func::{BlockRef, Fn, FnRef};

/// Generic data structure of vertex in a graph.
/// Implement this trait if some algorithms provided here are needed.
pub trait Vertex<T> where T: Vertex<T> + Eq + Clone + Hash {
    /// Give a clone of this object.
    /// This work cannot be done by the default method. Trait `Vertex<T>` it not equivalent to
    /// `T`. Therefore, the trait bound of `T` does not applies to `Vertex<T>`. If this method is
    /// implemented, the trait bound of `T` can be transferred to `Vertex<T>`
    fn this(&self) -> T;
    fn pred(&self) -> Vec<T>;
    fn succ(&self) -> Vec<T>;

    fn dfs(&self) -> DfsIter<T> {
        DfsIter {
            stack: vec![self.this()],
            visited: HashSet::from_iter(vec![self.this()]),
        }
    }

    fn bfs(&self) -> BfsIter<T> {
        BfsIter {
            queue: VecDeque::from_iter(vec![self.this()]),
            visited: HashSet::from_iter(vec![self.this()]),
        }
    }

    fn po(&self) -> PostOrd<T> {
        PostOrd {
            stack: vec![(self.this(), false)],
            visited: HashSet::from_iter(vec![self.this()]),
        }
    }

    fn rpo(&self) -> RevPostOrd<T> {
        RevPostOrd { post: self.po().collect() }
    }
}

/// Depth-first iterator for graph
pub struct DfsIter<T> where T: Vertex<T> + Eq + Clone + Hash {
    stack: Vec<T>,
    visited: HashSet<T>,
}

impl<T> Iterator for DfsIter<T> where T: Vertex<T> + Eq + Clone + Hash {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.stack.pop().map(|next| {
            for succ in next.succ().iter() {
                if !self.visited.contains(succ) {
                    self.stack.push(succ.clone());
                    self.visited.insert(succ.clone());
                }
            }
            next
        })
    }
}

/// Breadth-first iterator of blocks
pub struct BfsIter<T> where T: Vertex<T> + Eq + Clone + Hash {
    queue: VecDeque<T>,
    visited: HashSet<T>,
}

impl<T> Iterator for BfsIter<T> where T: Vertex<T> + Eq + Clone + Hash {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.queue.pop_front().map(|next| {
            for succ in next.succ().iter() {
                if !self.visited.contains(succ) {
                    self.queue.push_back(succ.clone());
                    self.visited.insert(succ.clone());
                }
            }
            next
        })
    }
}

pub struct PostOrd<T> where T: Vertex<T> + Eq + Clone + Hash {
    // An element will be returned only if it is visited twice
    stack: Vec<(T, bool)>,
    visited: HashSet<T>,
}

impl<T> Iterator for PostOrd<T> where T: Vertex<T> + Eq + Clone + Hash {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.stack.pop() {
                // This vertex is visited twice before, can return this time
                Some((next, true)) => return Some(next),
                // This vertex is visited only once, mark it as twice, push its successors to stack
                Some((next, false)) => {
                    self.stack.push((next.clone(), true));
                    let unvisited: Vec<T> = next.succ().into_iter()
                        .filter(|succ| !self.visited.contains(&succ)).collect();
                    unvisited.into_iter().for_each(|succ| {
                        self.visited.insert(succ.clone());
                        self.stack.push((succ, false))
                    });
                }
                // Stack is empty, no more vertices to process
                None => return None
            }
        }
    }
}

pub struct RevPostOrd<T> where T: Vertex<T> + Eq + Clone + Hash {
    post: Vec<T>
}

impl<T> Iterator for RevPostOrd<T> where T: Vertex<T> + Eq + Clone + Hash {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> { self.post.pop() }
}

/// Node in a depth-first spanning tree
#[derive(Debug)]
struct DfTreeNode<T> where T: Vertex<T> + Eq + Clone + Hash {
    /// Point back to the actual block
    vert: T,
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

pub struct DomBuilder<T> where T: Vertex<T> + Eq + Clone + Hash {
    nodes: Vec<DfTreeNode<T>>,
    block_num: HashMap<T, usize>,
}

impl<T> DomBuilder<T> where T: Vertex<T> + Eq + Clone + Hash {
    pub fn new(root: T) -> DomBuilder<T> {
        // Find all nodes by depth-first search
        let mut nodes = Vec::new();
        let mut block_num = HashMap::new(); // map block to number
        for (i, vert) in root.dfs().enumerate() {
            block_num.insert(vert.clone(), i);
            nodes.push(DfTreeNode { // store nodes as the order of traversal
                vert,
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
        DomBuilder { nodes, block_num }
    }

    /// Build dominator tree with given vertex as root using Lengauer-Tarjan algorithm.
    /// See [https://www.cl.cam.ac.uk/~mr10/lengtarj.pdf].
    /// The returned `HashMap` does not contain the root itself, as it must be `None`.
    pub fn build(self) -> HashMap<T, T> {
        // Return if the graph is too trivial
        if self.nodes.len() <= 1 { return HashMap::default(); }

        let semi = |v: usize| self.nodes[v].semi.get();
        let parent = |v: usize| self.nodes[v].parent.get();
        let dom = |v: usize| self.nodes[v].dom.get();

        for (v_num, v_node) in self.nodes.iter().enumerate() { // find parent for each node
            v_node.semi.replace(v_num);
            for ref w_block in v_node.vert.succ() {
                let w_num = self.block_num.get(w_block).copied().unwrap();
                let w_node = &self.nodes[w_num];
                if w_node.semi.get() == NONE {
                    w_node.parent.set(v_num);
                }
            }
        }

        for w in (1..self.nodes.len()).rev() {
            // Compute semidominator of each vertex
            let p = parent(w);
            for ref v_block in self.nodes[w].vert.pred() {
                let v = self.block_num.get(v_block).copied().unwrap();
                let u = self.eval(v);
                if semi(w) > semi(u) {
                    self.nodes[w].semi.set(semi(u))
                }
            }
            self.nodes[semi(w)].bucket.borrow_mut().insert(w);
            self.link(p, w);

            // Implicitly define immediate dominator
            for v in self.nodes[p].bucket.borrow().iter().copied() {
                let u = self.eval(v);
                self.nodes[v].dom.set(if semi(u) < semi(v) { u } else { p });
            }
            self.nodes[p].bucket.replace(HashSet::new());
        }

        // Explicitly define immediate dominator
        let mut result = HashMap::new();
        for w in 1..self.nodes.len() {
            if dom(w) != semi(w) {
                self.nodes[w].dom.set(dom(dom(w)));
            }
            let d = dom(w);
            result.insert(self.nodes[w].vert.clone(), self.nodes[d].vert.clone());
        }

        result
    }

    /// Find ancestor of node `v` with smallest semidominator.
    fn eval(&self, v: usize) -> usize {
        let best = |v: usize| self.nodes[v].best.get();
        let ancestor = |v: usize| self.nodes[v].ancestor.get();
        let semi = |v: usize| self.nodes[v].semi.get();

        if ancestor(v) == NONE { v } else {
            self.compress(v);
            if semi(best(ancestor(v))) >= semi(best(v)) {
                best(v)
            } else {
                best(ancestor(v))
            }
        }
    }

    fn compress(&self, v: usize) {
        let best = |v: usize| self.nodes[v].best.get();
        let ancestor = |v: usize| self.nodes[v].ancestor.get();
        let semi = |v: usize| self.nodes[v].semi.get();

        if ancestor(ancestor(v)) == NONE { return; }
        self.compress(ancestor(v));
        if semi(best(ancestor(v))) < semi(best(v)) {
            self.nodes[v].best.set(best(ancestor(v)))
        }
        self.nodes[v].ancestor.set(ancestor(ancestor(v)))
    }

    /// Add edge `(v, w)` to the forest
    fn link(&self, v: usize, w: usize) {
        let size = |v: usize| if v == NONE { 0 } else { self.nodes[v].size.get() };
        let best = |v: usize| if v == NONE { NONE } else { self.nodes[v].best.get() };
        let semi = |v: usize| if v == NONE { NONE } else { self.nodes[v].semi.get() };
        let child = |v: usize| if v == NONE { NONE } else { self.nodes[v].child.get() };

        let mut s = w;
        while child(s) != NONE && semi(best(w)) < semi(best(child(s))) {
            // Combine the first two trees in the child chain, making the larger one the combined
            // root.
            if size(s) + size(child(child(s))) >= 2 * size(child(s)) {
                self.nodes[child(s)].ancestor.replace(s);
                self.nodes[s].child.replace(child(child(s)));
            } else {
                self.nodes[child(s)].size.replace(size(s));
                self.nodes[s].ancestor.replace(child(s));
                s = child(s);
            }
        }

        // Now combine the two forests giving the combination the child chain of the smaller
        // forest. The other child chain is then collapsed, giving all its trees ancestor links
        // to v.
        self.nodes[s].best.replace(best(w));
        if size(v) < size(w) {
            let tmp = child(v);
            self.nodes[v].child.replace(s);
            s = tmp
        }
        self.nodes[v].size.replace(size(v) + size(w));
        while s != NONE {
            self.nodes[s].ancestor.replace(v);
            s = child(s)
        }
    }
}

/// Represent an vertex in the forward CFG
impl Vertex<BlockRef> for BlockRef {
    fn this(&self) -> BlockRef { self.clone() }
    fn pred(&self) -> Vec<BlockRef> { self.pred.borrow().deref().clone() }
    fn succ(&self) -> Vec<BlockRef> { self.succ.borrow().deref().clone() }
}

impl Fn {
    /// Return an iterator to breadth-first search the CFG.
    pub fn bfs(&self) -> BfsIter<BlockRef> { self.ent.borrow().bfs() }

    /// Return an iterator to depth-first search the CFG.
    pub fn dfs(&self) -> DfsIter<BlockRef> { self.ent.borrow().dfs() }

    /// Return an iterator for reverse post-order traversal.
    pub fn rpo(&self) -> RevPostOrd<BlockRef> { self.ent.borrow().rpo() }
}

/// Represent an vertex in the reverse CFG
#[derive(Eq, Hash, Clone)]
pub enum RevVert {
    /// Entrance of the function, this does not represent the entrance block in the original CFG.
    Enter(FnRef),
    /// Represent a block in the CFG.
    Block(BlockRef, FnRef),
    /// Exit of the function, the common predecessor of all exit blocks in reverse CFG.
    Exit(FnRef),
}

impl PartialEq for RevVert {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            // Only the block pointers need to be compared.
            (RevVert::Block(b1, _), RevVert::Block(b2, _)) => b1 == b2,
            // There is no chance that two blocks from different function are compared.
            (RevVert::Exit(_), RevVert::Exit(_)) => true,
            (RevVert::Enter(_), RevVert::Enter(_)) => true,
            _ => false
        }
    }
}

impl Debug for RevVert {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        match self {
            RevVert::Enter(_) => write!(f, "Enter"),
            RevVert::Exit(_) => write!(f, "Exit"),
            RevVert::Block(block, _) => write!(f, "Block({})", block.name)
        }
    }
}

impl Vertex<RevVert> for RevVert {
    fn this(&self) -> RevVert { self.clone() }

    fn pred(&self) -> Vec<RevVert> {
        match self {
            // Predecessors of a block in the reverse CFG are successors of that block in the
            // forward CFG. For exit blocks of the function, its predecessor should be the
            // `Exit` vertex, since it is not included in the original forward CFG
            RevVert::Block(block, f) => if f.exit.borrow().contains(&block) {
                vec![RevVert::Exit(f.clone())]
            } else {
                block.succ.borrow().iter().cloned()
                    .map(|succ| RevVert::Block(succ, f.clone())).collect()
            }
            // Function entrance has both entrance block in the original CFG and function exit as
            // predecessors.
            RevVert::Enter(f) => vec![
                RevVert::Block(f.ent.borrow().clone(), f.clone()),
                RevVert::Exit(f.clone())
            ],
            // Function exit has no predecessors in the reverse CFG, since it has no successors in
            // the forward CFG.
            RevVert::Exit(_) => vec![]
        }
    }

    fn succ(&self) -> Vec<RevVert> {
        match self {
            // Successors of a block in the reverse CFG are predecessors of that block in the
            // forward CFG. For entrance blocks of the function, its predecessor should be the
            // `Enter` vertex, since it is not included in the original forward CFG.
            RevVert::Block(block, f) => if f.ent.borrow().deref() == block {
                vec![RevVert::Enter(f.clone())]
            } else {
                block.pred.borrow().iter().cloned()
                    .map(|pred| RevVert::Block(pred, f.clone())).collect()
            }
            // Function entrance has no successor in the reverse CFG, since it has no predecessor
            // in the forward CFG.
            RevVert::Enter(_) => vec![],
            // Successors of function exit in the reverse CFG are exit blocks, since its
            // predecessors are these blocks in the forward CFG. Also, it has successor as function
            // entrance as successor.
            RevVert::Exit(f) => {
                let mut succ: Vec<_> = f.exit.borrow().iter().cloned()
                    .map(|exit| RevVert::Block(exit, f.clone())).collect();
                succ.push(RevVert::Enter(f.clone()));
                succ
            }
        }
    }
}

impl FnRef {
    /// Visit CFG in order of post-dominator tree
    pub fn post_dom<F>(&self, mut f: F) where F: FnMut(BlockRef) {
        // Build dominator tree for reverse CFG
        let root = RevVert::Exit(self.clone());
        let nodes: Vec<_> = root.dfs().collect();
        let parent = DomBuilder::new(root.clone()).build();
        let mut child: HashMap<RevVert, Vec<RevVert>> = nodes.iter().cloned()
            .map(|v| (v, vec![])).collect();
        parent.into_iter().for_each(|(c, p)| child.get_mut(&p).unwrap().push(c));

        // Traverse post-dominator tree
        let mut stack: Vec<RevVert> = child[&root].iter().cloned().collect();
        loop {
            match stack.pop() {
                Some(node) => {
                    child[&node].iter().cloned().for_each(|v| stack.push(v));
                    if let RevVert::Block(block, _) = node { f(block) } else {}
                }
                None => break
            }
        }
    }
}
