use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use crate::lang::func::{BlockListener, BlockRef, Func};
use crate::lang::instr::InstrRef;
use crate::lang::Program;
use crate::lang::ssa::{InstrListener, ValueListener};
use crate::lang::util::WorkList;
use crate::lang::value::{Scope, Symbol, SymbolRef, Value};
use crate::opt::{FnPass, Pass};
use crate::opt::graph::{GraphBuilder, VertRef};

pub struct GvnOpt {}

impl Pass for GvnOpt {
    fn opt(&mut self, pro: &mut Program) { FnPass::opt(self, pro) }
}

impl FnPass for GvnOpt {
    fn opt_fn(&mut self, func: &Func) {
        // Build value graph for this function.
        let mut builder = GraphBuilder::new();
        func.walk_dom(&mut builder);
        let graph = builder.graph;

        // Create initial vertex partition.
        let mut part: Vec<Vec<VertRef>> = vec![];
        let mut vert_num: HashMap<VertRef, usize> = HashMap::new();
        let mut work: WorkList<usize> = WorkList::new();
        for v in &graph.vert {
            // Create the first partition.
            if part.is_empty() {
                part.push(vec![v.clone()]);
                vert_num.insert(v.clone(), 0);
                continue;
            }
            // Check if this vertex is equivalent to vertices in any partition.
            let pos = part.iter().position(|set| set.first().unwrap().tag == v.tag);
            let num = match pos {
                Some(num) => {
                    part.get_mut(num).unwrap().push(v.clone());
                    if !v.opd.borrow().is_empty() { // congruence rely on operands
                        work.add(num);
                    }
                    num
                }
                None => {
                    let num = part.len();
                    part.push(vec![v.clone()]);
                    num
                }
            };
            vert_num.insert(v.clone(), num);
        }

        // Further partition the vertices until a fixed point is reached.
        while !work.is_empty() {
            // Find vertices whose operands are not equivalent to standard one.
            let idx = work.pick().unwrap();
            let std = part[idx][0].clone();
            let new_set: Vec<VertRef> = part[idx].iter()
                .filter(|v| !self.opd_cong(&vert_num, &std, v)).cloned().collect();

            // Make another cut in this set
            if new_set.is_empty() { continue; }
            part.get_mut(idx).unwrap().retain(|v| !new_set.contains(v));
            let new_num = part.len(); // acquire new number for this partition
            new_set.iter().for_each(|v| {
                // Map vertices in the new set to new number
                *vert_num.get_mut(v).unwrap() = new_num;
                // Add uses of vertices in the new set to the work list
                // The numbers of their uses depend on the ones of them. Since the numbers of
                // themselves have already changed, their uses may also change.
                v.uses.borrow().iter().for_each(|u| work.add(*vert_num.get(u).unwrap()))
            });
            if part[idx].len() > 1 {
                work.add(idx)
            }
            if new_set.len() > 1 {
                work.add(new_num)
            }
            part.push(new_set);
        }

        // Build symbol mapping
        // Here we first gather symbols of different partitions, choose the symbol with 'smallest'
        // identifier. And then build the actual mapping.
        // A more efficient algorithm may directly build this mapping, but in that way the
        // transformed code is less readable.
        let mut rep: Vec<Option<SymbolRef>> = part.iter().map(|_| None).collect();
        graph.map.iter().for_each(|(sym, vert)| {
            let num = *vert_num.get(vert).unwrap();
            if rep[num].is_none() || sym.id() < rep[num].as_ref().unwrap().id() {
                *rep.get_mut(num).unwrap() = Some(sym.clone());
            }
        });
        let mut map: HashMap<SymbolRef, SymbolRef> = HashMap::new();
        graph.map.iter().for_each(|(sym, vert)| {
            let num = *vert_num.get(vert).unwrap();
            map.insert(sym.clone(), rep[num].as_ref().unwrap().clone());
        });

        // Perform code motion
        let mut motion = GvnMotion::new(map);
        func.walk_dom(&mut motion);
    }
}

struct GvnMotion {
    /// Contain symbol mapping
    map: HashMap<SymbolRef, SymbolRef>,
    /// Instructions to be eliminated in current block
    dup: HashSet<InstrRef>,
    /// Scope of current function
    scope: Option<Rc<Scope>>,
}

impl BlockListener for GvnMotion {
    fn on_begin(&mut self, func: &Func) {
        self.scope = Some(func.scope.clone());
        InstrListener::on_begin(self, func)
    }

    fn on_end(&mut self, _func: &Func) {}

    fn on_enter(&mut self, block: BlockRef) {
        // Replace congruent symbols
        InstrListener::on_enter(self, block.clone());

        // Clear instructions defining congruent symbols
        block.instr.borrow_mut().retain(|instr| {
            !self.dup.contains(instr)
        });
        self.dup.clear();
    }

    fn on_exit(&mut self, _block: BlockRef) {}

    fn on_enter_child(&mut self, _this: BlockRef, _child: BlockRef) {}

    fn on_exit_child(&mut self, _this: BlockRef, _child: BlockRef) {}
}

impl InstrListener for GvnMotion {
    fn on_instr(&mut self, instr: InstrRef) {
        ValueListener::on_instr(self, instr)
    }

    fn on_succ_phi(&mut self, this: Option<BlockRef>, instr: InstrRef) {
        ValueListener::on_succ_phi(self, this, instr)
    }
}

impl ValueListener for GvnMotion {
    fn on_use(&mut self, _instr: InstrRef, opd: &RefCell<Value>) {
        opd.replace_with(|val| {
            match val {
                Value::Var(sym) if sym.is_local_var() && self.map.contains_key(sym) => {
                    Value::Var(self.map.get(sym).unwrap().clone())
                }
                _ => val.clone()
            }
        });
    }

    fn on_def(&mut self, instr: InstrRef, def: &RefCell<SymbolRef>) {
        def.replace_with(|sym| {
            match sym.as_ref() {
                Symbol::Local { name: _, ty: _, ver: _ } if self.map.contains_key(sym) => {
                    let rep = self.map.get(sym).unwrap();
                    if sym != rep { // a congruent symbol already defined
                        self.scope.as_ref().unwrap().remove(sym.id().as_str());
                        self.dup.insert(instr); // mark this instruction as duplicated
                    }
                    rep.clone()
                }
                _ => sym.clone()
            }
        });
    }
}

impl GvnMotion {
    fn new(map: HashMap<SymbolRef, SymbolRef>) -> GvnMotion {
        GvnMotion {
            map,
            dup: Default::default(),
            scope: None,
        }
    }
}

impl GvnOpt {
    /// Decide whether operands of two vertices are pairwise congruent.
    fn opd_cong(&self, vert_num: &HashMap<VertRef, usize>, v1: &VertRef, v2: &VertRef) -> bool {
        if v1.opd.borrow().len() != v2.opd.borrow().len() { return false; }
        v1.opd.borrow().iter().zip(v2.opd.borrow().iter())
            .all(|(o1, o2)| vert_num.get(o1).unwrap() == vert_num.get(o2).unwrap())
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
