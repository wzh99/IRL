use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use crate::lang::func::{BlockListener, BlockRef, Func};
use crate::lang::instr::InstrRef;
use crate::lang::Program;
use crate::lang::ssa::{InstrListener, ValueListener};
use crate::lang::util::WorkList;
use crate::lang::value::{SymbolRef, Value};
use crate::opt::{FnPass, Pass};
use crate::opt::graph::{GraphBuilder, VertRef};

pub struct Gvn {
    vert_num: HashMap<VertRef, usize>
}

impl Gvn {
    pub fn new() -> Gvn {
        Gvn { vert_num: Default::default() }
    }

    pub fn number(mut self, func: &Func) -> HashMap<SymbolRef, usize> {
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
    fn opt(&mut self, pro: &mut Program) { FnPass::opt(self, pro) }
}

impl FnPass for GvnOpt {
    fn opt_fn(&mut self, func: &Rc<Func>) {
        // Number values
        let sym_num = Gvn::new().number(func);

        // Build symbol mapping
        // Here we first gather symbols of different partitions, choose the symbol with 'smallest'
        // identifier, and then build the actual mapping. A more efficient algorithm may directly
        // build this mapping, but in that way the transformed code is less readable.
        // Hash map is used here because the numbers are not continuous, due to existence of non-
        // variable vertices. Linear vector is not beneficial in this scenario.
        let mut rep: HashMap<usize, SymbolRef> = HashMap::new();
        sym_num.iter().for_each(|(sym, num)| {
            if !rep.contains_key(num) || sym.name() < rep[num].name() {
                rep.insert(*num, sym.clone());
            }
        });
        let map: HashMap<SymbolRef, SymbolRef> = sym_num.iter().map(|(sym, num)| {
            (sym.clone(), rep[num].clone())
        }).collect();

        // Perform code replacement
        let mut listener = GvnListener::new(map);
        func.walk_dom(&mut listener);
    }
}

struct GvnListener {
    /// Contain symbol mapping
    map: HashMap<SymbolRef, SymbolRef>,
    /// Defined symbols stack
    def: Vec<Vec<SymbolRef>>,
    /// Instructions to be eliminated in current block
    dup: HashSet<InstrRef>,
}

impl GvnListener {
    fn new(map: HashMap<SymbolRef, SymbolRef>) -> GvnListener {
        GvnListener {
            map,
            def: vec![],
            dup: Default::default(),
        }
    }
}

impl BlockListener for GvnListener {
    fn on_begin(&mut self, func: &Func) {
        self.def.push(func.param.iter().map(|p| p.borrow().clone()).collect());
        InstrListener::on_begin(self, func)
    }

    fn on_end(&mut self, _func: &Func) {}

    fn on_enter(&mut self, block: BlockRef) {
        // Replace congruent symbols
        self.def.push(vec![]);
        InstrListener::on_enter(self, block.clone());

        // Clear instructions defining congruent symbols
        block.instr.borrow_mut().retain(|instr| {
            !self.dup.contains(instr)
        });
        self.def.pop();
    }

    fn on_exit(&mut self, _block: BlockRef) {}

    fn on_enter_child(&mut self, _this: BlockRef, _child: BlockRef) {}

    fn on_exit_child(&mut self, _this: BlockRef, _child: BlockRef) {}
}

impl InstrListener for GvnListener {
    fn on_instr(&mut self, instr: InstrRef) {
        ValueListener::on_instr(self, instr)
    }

    fn on_succ_phi(&mut self, this: Option<BlockRef>, instr: InstrRef) {
        ValueListener::on_succ_phi(self, this, instr)
    }
}

impl ValueListener for GvnListener {
    fn on_use(&mut self, _instr: InstrRef, opd: &RefCell<Value>) {
        opd.replace_with(|val| {
            match val {
                Value::Var(sym) if sym.is_local_var() => {
                    Value::Var(self.map.get(sym).unwrap().clone())
                }
                _ => val.clone()
            }
        });
    }

    fn on_def(&mut self, instr: InstrRef, def: &RefCell<SymbolRef>) {
        def.replace_with(|sym| {
            match sym {
                sym if sym.is_local_var() => {
                    let rep = &self.map[&sym];
                    if self.def.iter().any(|frame| frame.contains(rep)) { // fully redundant
                        self.dup.insert(instr);
                    } else {
                        self.def.last_mut().unwrap().push(rep.clone())
                    }
                    rep.clone()
                }
                _ => sym.clone()
            }
        });
    }
}

#[test]
fn test_gvn() {
    use crate::compile::lex::Lexer;
    use crate::compile::parse::Parser;
    use crate::compile::build::Builder;
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
    Pass::opt(&mut opt, &mut pro);

    let mut out = stdout();
    let mut printer = Printer::new(out.borrow_mut());
    printer.print(&pro).unwrap();
}
