use std::cell::RefCell;
use std::collections::HashMap;
use std::ops::Deref;

use crate::lang::func::{BlockRef, DomTreeListener, Fn, FnRef};
use crate::lang::inst::Inst;
use crate::lang::Program;
use crate::lang::util::{ExtRc, WorkList};
use crate::lang::value::{SymbolRef, Value};
use crate::pass::{FnPass, Pass};
use crate::pass::copy::CopyProp;
use crate::pass::graph::{GraphBuilder, VertRef};

pub struct Gvn {
    vert_num: HashMap<VertRef, usize>
}

impl Gvn {
    pub fn new() -> Gvn {
        Gvn { vert_num: Default::default() }
    }

    pub fn number(mut self, func: &Fn) -> HashMap<SymbolRef, usize> {
        // Build value graph for this function.
        let mut builder = GraphBuilder::new();
        func.walk_dom(&mut builder);
        let graph = builder.graph;

        // Create initial vertex partition.
        let mut part: Vec<Vec<VertRef>> = vec![];
        let mut work: WorkList<usize> = WorkList::new();
        // Here we consider all the vertices. Though at last only two local variables will possibly
        // be given the same value, their congruence depend on their operands vertices, which could
        // possibly not be local variables.
        for v in &graph.vert {
            // Create the first partition.
            if part.is_empty() {
                part.push(vec![v.clone()]);
                self.vert_num.insert(v.clone(), 0);
                continue;
            }
            // Check if this vertex is equivalent to vertices in any partition.
            let pos = part.iter().position(|set| set.first().unwrap().tag == v.tag);
            let num = match pos {
                Some(num) => {
                    part.get_mut(num).unwrap().push(v.clone());
                    if !v.opd.borrow().is_empty() { // congruence rely on operands
                        work.insert(num);
                    }
                    num
                }
                None => {
                    let num = part.len();
                    part.push(vec![v.clone()]);
                    num
                }
            };
            self.vert_num.insert(v.clone(), num);
        }

        // Further partition the vertices until a fixed point is reached.
        while !work.is_empty() {
            // Find vertices whose operands are not equivalent to standard one.
            let idx = work.pick().unwrap();
            let std = part[idx][0].clone();
            let new_set: Vec<VertRef> = part[idx].iter()
                .filter(|v| !self.opd_cong(&std, v)).cloned().collect();

            // Make another cut in this set
            if new_set.is_empty() { continue; }
            part[idx].retain(|v| !new_set.contains(v));
            let new_num = part.len(); // acquire new number for this partition
            new_set.iter().for_each(|v| {
                // Map vertices in the new set to new number
                *self.vert_num.get_mut(v).unwrap() = new_num;
                // Add uses of vertices in the new set to the work list
                // The numbers of their uses depend on the ones of them. Since the numbers of
                // themselves have already changed, their uses may also change.
                v.uses.borrow().iter().for_each(|u| work.insert(*self.vert_num.get(u).unwrap()))
            });
            if part[idx].len() > 1 {
                work.insert(idx)
            }
            if new_set.len() > 1 {
                work.insert(new_num)
            }
            part.push(new_set);
        }

        graph.map.iter().map(|(sym, vert)| {
            (sym.clone(), *self.vert_num.get(vert).unwrap())
        }).collect()
    }

    fn opd_cong(&self, v1: &VertRef, v2: &VertRef) -> bool {
        if v1.opd.borrow().len() != v2.opd.borrow().len() { return false; }
        // Here we allow a vertex to be not found in the mapping, and it must be a placeholder.
        v1.opd.borrow().iter().zip(v2.opd.borrow().iter())
            .all(|(o1, o2)| self.vert_num.get(o1) == self.vert_num.get(o2))
    }
}

pub struct GvnOpt {}

impl Pass for GvnOpt {
    fn run(&mut self, pro: &mut Program) { FnPass::run(self, pro) }
}

impl FnPass for GvnOpt {
    fn run_on_fn(&mut self, func: &FnRef) {
        // Number values
        let sym_num = Gvn::new().number(func);

        // Perform code replacement
        let mut listener = GvnListener::new(sym_num);
        func.walk_dom(&mut listener);

        // Clean code
        CopyProp::new().run_on_fn(func);
        func.elim_dead_code()
    }
}

struct GvnListener {
    /// Contain symbol numbers for local variables
    num: HashMap<SymbolRef, usize>,
    /// Record available symbol for each value number
    def: HashMap<usize, SymbolRef>,
    /// Defined symbol number stack
    stack: Vec<Vec<usize>>,
}

impl GvnListener {
    fn new(map: HashMap<SymbolRef, usize>) -> GvnListener {
        GvnListener {
            num: map,
            def: Default::default(),
            stack: vec![],
        }
    }
}

impl DomTreeListener for GvnListener {
    fn on_begin(&mut self, func: &Fn) {
        self.stack.push(func.param.iter().map(|p| self.num[p.borrow().deref()]).collect());
    }

    fn on_end(&mut self, _func: &Fn) {}

    fn on_enter(&mut self, block: BlockRef) {
        self.stack.push(vec![]);
        block.inst.borrow_mut().iter_mut().for_each(|inst| {
            // Process destination symbol
            inst.dst().cloned().map(|dst| {
                let dst = dst.borrow().clone();
                if dst.is_global_var() { return; }
                let num = self.num[&dst];
                match self.def.get(&num).cloned() {
                    // A symbol of the same value has been defined, this value is fully redundant
                    Some(rep) => {
                        *inst = ExtRc::new(Inst::Mov {
                            src: RefCell::new(Value::Var(rep)),
                            dst: RefCell::new(dst),
                        })
                    }
                    // This could serve as representative symbol
                    None => {
                        self.def.insert(num, dst);
                        self.stack.last_mut().unwrap().push(num);
                    }
                }
            });
        });
        self.stack.pop().unwrap().into_iter().for_each(|num| {
            self.def.remove(&num);
        });
    }

    fn on_exit(&mut self, _block: BlockRef) {}

    fn on_enter_child(&mut self, _this: BlockRef, _child: BlockRef) {}

    fn on_exit_child(&mut self, _this: BlockRef, _child: BlockRef) {}
}

#[test]
fn test_gvn() {
    use crate::irc::lex::Lexer;
    use crate::irc::parse::Parser;
    use crate::irc::build::Builder;
    use crate::lang::print::Printer;
    use std::io::stdout;
    use std::fs::File;
    use std::convert::TryFrom;
    use std::io::Read;
    use std::borrow::BorrowMut;

    let mut file = File::open("test/gvn.ir").unwrap();
    let lexer = Lexer::try_from(&mut file as &mut dyn Read).unwrap();
    let parser = Parser::new(lexer);
    let tree = parser.parse().unwrap();
    let builder = Builder::new(tree);
    let mut pro = builder.build().unwrap();
    let mut opt = GvnOpt {};
    Pass::run(&mut opt, &mut pro);

    let mut out = stdout();
    let mut printer = Printer::new(out.borrow_mut());
    printer.print(&pro).unwrap();
}
