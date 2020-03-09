use std::collections::{HashSet, VecDeque};
use std::hash::Hash;
use std::iter::FromIterator;

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

    fn post_ord(&self) -> PostOrd<T> {
        PostOrd {
            stack: vec![(self.this(), false)],
            visited: HashSet::from_iter(vec![self.this()]),
        }
    }

    fn rpo(&self) -> RevPostOrd<T> {
        RevPostOrd { post: self.post_ord().collect() }
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

/// Implement Lengauer-Tarjan algorithm for building dominator tree
pub mod dom {
    use std::cell::{Cell, RefCell};
    use std::collections::{HashMap, HashSet};
    use std::hash::Hash;

    use crate::lang::graph::Vertex;

    /// Node in a depth-first spanning tree
    #[derive(Debug)]
    struct DfNode<T> where T: Vertex<T> + Eq + Clone + Hash {
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

    /// Build dominator tree with given vertex as root using Lengauer-Tarjan algorithm.
    /// See [https://www.cl.cam.ac.uk/~mr10/lengtarj.pdf].
    /// The returned `HashMap` does not contain the root itself, as it must be `None`.
    pub fn build<T>(root: T) -> HashMap<T, T> where T: Vertex<T> + Eq + Clone + Hash {
        // Perform depth-first search on the CFG
        let mut nodes = Vec::new();
        let mut block_num = HashMap::new(); // map block to number
        for (i, vert) in root.dfs().enumerate() {
            block_num.insert(vert.clone(), i);
            nodes.push(DfNode { // store nodes as the order of traversal
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

        // Return if the graph is too trivial
        if nodes.len() <= 1 { return HashMap::default(); }

        let semi = |v: usize| nodes[v].semi.get();
        let parent = |v: usize| nodes[v].parent.get();
        let dom = |v: usize| nodes[v].dom.get();

        for (v_num, v_node) in nodes.iter().enumerate() { // find parent for each node
            v_node.semi.replace(v_num);
            for ref w_block in v_node.vert.succ() {
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
            for ref v_block in nodes[w].vert.pred() {
                let v = block_num.get(v_block).copied().unwrap();
                let u = eval(&nodes, v);
                if semi(w) > semi(u) {
                    nodes[w].semi.set(semi(u))
                }
            }
            nodes[semi(w)].bucket.borrow_mut().insert(w);
            link(&nodes, p, w);

            // Implicitly define immediate dominator
            for v in nodes[p].bucket.borrow().iter().copied() {
                let u = eval(&nodes, v);
                nodes[v].dom.set(if semi(u) < semi(v) { u } else { p });
            }
            nodes[p].bucket.replace(HashSet::new());
        }

        // Explicitly define immediate dominator
        let mut result = HashMap::new();
        for w in 1..nodes.len() {
            if dom(w) != semi(w) {
                nodes[w].dom.set(dom(dom(w)));
            }
            let d = dom(w);
            result.insert(nodes[w].vert.clone(), nodes[d].vert.clone());
        }
        result
    }

    /// Find ancestor of node `v` with smallest semidominator.
    fn eval<T>(nodes: &Vec<DfNode<T>>, v: usize) -> usize
        where T: Vertex<T> + Eq + Clone + Hash
    {
        let best = |v: usize| nodes[v].best.get();
        let ancestor = |v: usize| nodes[v].ancestor.get();
        let semi = |v: usize| nodes[v].semi.get();

        if ancestor(v) == NONE { v } else {
            compress(nodes, v);
            if semi(best(ancestor(v))) >= semi(best(v)) {
                best(v)
            } else {
                best(ancestor(v))
            }
        }
    }

    fn compress<T>(nodes: &Vec<DfNode<T>>, v: usize)
        where T: Vertex<T> + Eq + Clone + Hash
    {
        let best = |v: usize| nodes[v].best.get();
        let ancestor = |v: usize| nodes[v].ancestor.get();
        let semi = |v: usize| nodes[v].semi.get();

        if ancestor(ancestor(v)) == NONE { return; }
        compress(nodes, ancestor(v));
        if semi(best(ancestor(v))) < semi(best(v)) {
            nodes[v].best.set(best(ancestor(v)))
        }
        nodes[v].ancestor.set(ancestor(ancestor(v)))
    }

    /// Add edge `(v, w)` to the forest
    fn link<T>(nodes: &Vec<DfNode<T>>, v: usize, w: usize)
        where T: Vertex<T> + Eq + Clone + Hash
    {
        let size = |v: usize| if v == NONE { 0 } else { nodes[v].size.get() };
        let best = |v: usize| if v == NONE { NONE } else { nodes[v].best.get() };
        let semi = |v: usize| if v == NONE { NONE } else { nodes[v].semi.get() };
        let child = |v: usize| if v == NONE { NONE } else { nodes[v].child.get() };

        let mut s = w;
        while child(s) != NONE && semi(best(w)) < semi(best(child(s))) {
            // Combine the first two trees in the child chain, making the larger one the combined
            // root.
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
        // forest. The other child chain is then collapsed, giving all its trees ancestor links
        // to v.
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
