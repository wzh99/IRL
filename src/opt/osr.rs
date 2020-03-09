use std::cmp::min;
use std::collections::{HashMap, HashSet};

use crate::lang::func::{BlockRef, Func};
use crate::lang::Program;
use crate::opt::{FnPass, Pass};
use crate::opt::graph::{GraphBuilder, SsaGraph, VertRef};

pub struct OsrOpt {
    graph: SsaGraph,
    rpo: HashMap<BlockRef, usize>,
    unvisited: HashSet<VertRef>,
    stack: Vec<VertRef>,
    num: HashMap<VertRef, usize>,
    next_num: usize,
    low: HashMap<VertRef, usize>,
    header: HashMap<VertRef, Option<VertRef>>,
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
        self.num.clear();
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
            num: Default::default(),
            header: Default::default(),
        }
    }

    fn dfs(&mut self, v: &VertRef) {
        // Visit this vertex
        let num = self.next_num;
        self.num.insert(v.clone(), num);
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
            if self.num[o] < self.num[v] && self.stack.contains(o) {
                *self.low.get_mut(v).unwrap() = min(self.low[v], self.num[o]);
            }
        });

        // Find vertices of strongly-connected component
        if self.low[v] == self.num[v] {
            let mut scc = vec![];
            loop {
                let x = self.stack.pop().unwrap();
                scc.push(x.clone());
                if x == *v { break; }
            }
            println!("{:?}", scc);
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