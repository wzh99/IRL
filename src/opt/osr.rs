use std::cmp::min;
use std::collections::{HashMap, HashSet};

use crate::lang::func::{BlockRef, Func};
use crate::lang::Program;
use crate::opt::{FnPass, Pass};
use crate::opt::graph::{GraphBuilder, SsaGraph, VertRef, VertTag};

pub struct OsrOpt {
    /// SSA graph forms the base of this algorithm
    graph: SsaGraph,
    /// Reverse post-order number of blocks
    /// Since RPO number is only used in this algorithm, it is not stored in the blocks.
    rpo: HashMap<BlockRef, usize>,
    /// Record unvisited vertices.
    /// `Worklist` is not used here, because it does not support removing a specified element.
    unvisited: HashSet<VertRef>,
    /// Stack for depth-first search in Tarjan's algorithm to find strongly-connected components
    stack: Vec<VertRef>,
    /// Record depth-first number of SSA vertices
    df_num: HashMap<VertRef, usize>,
    /// Record next depth-first number to be assigned to vertices
    next_num: usize,
    /// Record the lowest depth-first number in a yet-to-discovered SCC.
    low: HashMap<VertRef, usize>,
    /// Block of the vertices with the lowest RPO in an SCC
    header: HashMap<VertRef, Option<BlockRef>>,
}

impl Pass for OsrOpt {
    fn opt(&mut self, pro: &mut Program) { FnPass::opt(self, pro) }
}

impl FnPass for OsrOpt {
    fn opt_fn(&mut self, func: &Func) {
        // Create reverse post-order number
        self.rpo = func.rpo().enumerate().map(|(i, b)| (b, i)).collect();

        // Create value graph
        let mut builder = GraphBuilder::new();
        func.walk_dom(&mut builder);
        self.graph = builder.graph;

        // Find strongly-connected components using Tarjan's algorithm
        self.next_num = 0;
        self.unvisited = self.graph.vert.iter().cloned().collect();
        while !self.unvisited.is_empty() {
            let mut vert = None;
            for v in &self.unvisited {
                vert = Some(v.clone());
                break;
            };
            self.dfs(&vert.unwrap())
        }

        // Clear records for this function
        self.rpo.clear();
        self.low.clear();
        self.df_num.clear();
        self.header.clear();
    }
}

impl OsrOpt {
    pub fn new() -> OsrOpt {
        OsrOpt {
            graph: SsaGraph::new(),
            rpo: Default::default(),
            unvisited: Default::default(),
            next_num: 0,
            low: Default::default(),
            stack: vec![],
            df_num: Default::default(),
            header: Default::default(),
        }
    }

    fn dfs(&mut self, v: &VertRef) {
        // Visit this vertex
        let num = self.next_num;
        self.df_num.insert(v.clone(), num);
        self.next_num += 1;
        self.unvisited.remove(v);
        self.low.insert(v.clone(), num);
        self.stack.push(v.clone());

        // Visit all operands
        v.opd.borrow().iter().for_each(|o| {
            if self.unvisited.contains(o) {
                self.dfs(o);
                *self.low.get_mut(v).unwrap() = min(self.low[v], self.low[o]);
            }
            if self.df_num[o] < self.df_num[v] && self.stack.contains(o) {
                *self.low.get_mut(v).unwrap() = min(self.low[v], self.df_num[o]);
            }
        });

        // Find vertices of strongly-connected component
        if self.low[v] == self.df_num[v] {
            let mut scc = vec![];
            loop {
                let x = self.stack.pop().unwrap();
                scc.push(x.clone());
                if x == *v { break; }
            }
            self.proc_scc(scc);
        }
    }

    fn proc_scc(&mut self, scc: Vec<VertRef>) {
        // Process SCC with only one vertex
        if scc.len() == 1 {
            let v = &scc[0];
            if let Some((blk, _)) = &v.instr {
                self.proc_vert(v, blk);
            }
            return;
        }

        // Find header
        let ref header = scc.iter().map(|v| &v.instr.as_ref().unwrap().0)
            .min_by_key(|b| self.rpo[b]).unwrap().clone();

        // Decide whether this SCC is an induction variable
        let is_iv = scc.iter().all(|v| {
            Self::is_iv_update(v) && v.opd.borrow().iter().all(|o|
                // Whether the operands are either IVs or region constants
                scc.contains(o) || Self::is_rc(o, header)
            )
        });

        // Process values according to classification result
        if is_iv {
            scc.iter().for_each(|v| {
                self.header.insert(v.clone(), Some(header.clone()));
            })
        } else {
            scc.iter().for_each(|v| self.proc_vert(v, header))
        }
    }

    /// Perform strength reduction if the vertex has certain form
    fn proc_vert(&mut self, v: &VertRef, header: &BlockRef) {
        // Only vertices with exactly two operands will be accepted
        if v.opd.borrow().len() != 2 {
            self.header.insert(v.clone(), None);
            return;
        }

        // Figure out IV and RC through pattern matching
        let (fst, snd) = (&v.opd.borrow()[0], &v.opd.borrow()[1]);
        if let VertTag::Value(op) = &v.tag {
            match op.as_str() {
                "add" if Self::is_iv_update(fst) && Self::is_rc(snd, header) =>
                    self.replace(v, fst, snd),
                "add" if Self::is_rc(fst, header) && Self::is_iv_update(snd) =>
                    self.replace(v, snd, fst),
                "sub" if Self::is_iv_update(fst) && Self::is_rc(snd, header) =>
                    self.replace(v, fst, snd),
                "mul" if Self::is_iv_update(fst) && Self::is_rc(snd, header) =>
                    self.replace(v, fst, snd),
                "mul" if Self::is_rc(fst, header) && Self::is_iv_update(snd) =>
                    self.replace(v, snd, fst),
                "ptr" if Self::is_rc(fst, header) && Self::is_iv_update(snd) =>
                    self.replace(v, snd, fst),
                _ => { self.header.insert(v.clone(), None); }
            }
        } else {
            self.header.insert(v.clone(), None);
        }
    }

    fn replace(&mut self, v: &VertRef, iv: &VertRef, rc: &VertRef) {
        println!("{:?} {:?} {:?}", v.sym, iv.sym, rc.sym);
    }

    /// Whether this value is a valid update of induction variable.
    fn is_iv_update(v: &VertRef) -> bool {
        match &v.tag {
            // Phi is always considered an IV
            VertTag::Phi(_) => true,
            // For other values, they must be updated by a region constant in each operation.
            // Only `add`, `sub` and `ptr` meet this requirement.
            VertTag::Value(op) if ["add", "sub", "ptr"].contains(&op.as_str()) => true,
            _ => false
        }
    }

    /// Whether this value is a region constant.
    fn is_rc(vert: &VertRef, header: &BlockRef) -> bool {
        match vert.tag {
            // A constant must be a region constant
            VertTag::Const(_) => true,
            // Parameters are defined in program entrance, which dominates every block
            VertTag::Param(_) => true,
            _ => match &vert.instr {
                // Whether the block defining this value dominates header of SCC
                Some((block, _)) => block.dominates(header),
                None => false
            }
        }
    }
}

#[test]
fn test_osr() {
    use crate::compile::lex::Lexer;
    use crate::compile::parse::Parser;
    use crate::compile::build::Builder;
    use std::fs::File;
    use std::convert::TryFrom;
    use std::io::Read;

    let mut file = File::open("test/sum.ir").unwrap();
    let lexer = Lexer::try_from(&mut file as &mut dyn Read).unwrap();
    let parser = Parser::new(lexer);
    let tree = parser.parse().unwrap();
    let builder = Builder::new(tree);
    let mut pro = builder.build().unwrap();
    let mut opt = OsrOpt::new();
    Pass::opt(&mut opt, &mut pro);
}