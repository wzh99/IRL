use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::ops::Deref;
use std::rc::Rc;

use crate::lang::func::{BlockRef, Func};
use crate::lang::instr::{Instr, InstrRef};
use crate::lang::Program;
use crate::lang::ssa::{DefPos, DefUse};
use crate::lang::util::{ExtRc, WorkList};
use crate::lang::value::{SymbolRef, Value};
use crate::opt::{FnPass, Pass};

pub struct AdceOpt {
    rev_df: HashMap<BlockRef, Vec<BlockRef>>,
    def_use: HashMap<SymbolRef, DefUse>,
    blk: HashSet<BlockRef>,
    instr: HashSet<InstrRef>,
    work: WorkList<(BlockRef, InstrRef)>,
}

impl Pass for AdceOpt {
    fn opt(&mut self, pro: &mut Program) { FnPass::opt(self, pro) }
}

impl FnPass for AdceOpt {
    fn opt_fn(&mut self, func: &Rc<Func>) {
        // Build control dependence graph
        self.rev_df = func.rev_df();

        // Get def-use information for this function
        self.def_use = func.def_use();

        // Mark all instructions that are sure to be active
        func.iter_dom(|block| {
            block.for_each(|instr| {
                match instr.as_ref() {
                    // Mark instructions that are returns or have side effect
                    active if active.is_ret() || active.has_side_effect() =>
                        self.mark(block.clone(), instr),
                    _ => {}
                }
            })
        });

        // Use work list algorithm to mark more active instructions
        loop {
            match self.work.pick() {
                Some((blk, instr)) => self.mark(blk, instr),
                None => break
            }
        }

        func.iter_dom(|blk| {
            // Remove unmarked instruction
            blk.instr.borrow_mut().retain(|instr| {
                match instr.as_ref() {
                    // Keep all control flow instructions
                    ctrl if ctrl.is_ctrl() => true,
                    // For other instructions, keep what are marked
                    _ => self.instr.contains(&instr)
                }
            });

            // Deal with conditional branch
            if let Instr::Br { cond: _, tr, fls } = blk.tail().as_ref() {
                let mut tgt = vec![tr.borrow().clone(), fls.borrow().clone()];
                tgt.retain(|blk| self.blk.contains(blk));
                match tgt.len() {
                    // Two blocks all active
                    2 => {}
                    // Only one is active, modify the control flow in this block.
                    1 => {
                        let succ = tgt[0].clone();
                        let jmp = ExtRc::new(Instr::Jmp {
                            tgt: RefCell::new(succ.clone())
                        });
                        *blk.instr.borrow_mut().back_mut().unwrap() = jmp;
                        blk.succ.replace(vec![succ]);
                    }
                    _ => unreachable!()
                }
            }
        });

        // Remove unreachable blocks
        func.remove_unreachable();

        // Clear data structure for this function
        self.instr.clear();
        self.blk.clear();
    }
}

impl AdceOpt {
    pub fn new() -> AdceOpt {
        AdceOpt {
            rev_df: Default::default(),
            def_use: Default::default(),
            blk: Default::default(),
            instr: Default::default(),
            work: WorkList::new(),
        }
    }

    fn mark(&mut self, blk: BlockRef, instr: InstrRef) {
        // Mark block and instruction
        if self.instr.contains(&instr) { return; }
        self.blk.insert(blk.clone());
        self.instr.insert(instr.clone());

        // Add conditional branch upon which this block is control-dependent on
        self.rev_df.get(&blk).cloned().map(|list| {
            list.iter().for_each(|dep| {
                let tail = dep.tail();
                if let Instr::Br { cond: _, tr: _, fls: _ } = tail.deref() {
                    self.work.insert((dep.clone(), tail))
                }
            })
        });

        // Add the definition points of its operands to work list
        instr.src().iter().for_each(|src| {
            let src = src.borrow().clone();
            match src {
                Value::Var(sym) if sym.is_local_var() => {
                    if let DefPos::Instr(blk, instr) = &self.def_use[&sym].def {
                        self.work.insert((blk.clone(), instr.clone()))
                    }
                }
                _ => {}
            }
        });
    }
}

#[test]
fn test_adce() {
    use crate::compile::lex::Lexer;
    use crate::compile::parse::Parser;
    use crate::compile::build::Builder;
    use crate::lang::print::Printer;
    use std::io::stdout;
    use std::fs::File;
    use std::convert::TryFrom;
    use std::io::Read;
    use std::borrow::BorrowMut;

    let mut file = File::open("test/adce.ir").unwrap();
    let lexer = Lexer::try_from(&mut file as &mut dyn Read).unwrap();
    let parser = Parser::new(lexer);
    let tree = parser.parse().unwrap();
    let builder = Builder::new(tree);
    let mut pro = builder.build().unwrap();
    FnPass::opt(&mut AdceOpt::new(), &mut pro);

    let mut out = stdout();
    let mut printer = Printer::new(out.borrow_mut());
    printer.print(&pro).unwrap();
}