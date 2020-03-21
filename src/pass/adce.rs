use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::ops::Deref;

use crate::lang::func::{BlockRef, FnRef};
use crate::lang::graph::{DomBuilder, RevVert, Vertex};
use crate::lang::inst::{Inst, InstRef};
use crate::lang::Program;
use crate::lang::ssa::{DefPos, DefUse};
use crate::lang::util::{ExtRc, WorkList};
use crate::lang::value::{SymbolRef, Value};
use crate::pass::{FnPass, Pass};

pub struct AdceOpt {
    rev_df: HashMap<BlockRef, Vec<BlockRef>>,
    def_use: HashMap<SymbolRef, DefUse>,
    blk: HashSet<BlockRef>,
    instr: HashSet<InstRef>,
    work: WorkList<(BlockRef, InstRef)>,
}

impl Pass for AdceOpt {
    fn run(&mut self, pro: &mut Program) { FnPass::run(self, pro) }
}

impl FnPass for AdceOpt {
    fn run_on_fn(&mut self, f: &FnRef) {
        // Build control dependence graph
        self.rev_df = Self::rev_df(f);

        // Get def-use information for this function
        self.def_use = f.def_use();

        // Mark all instructions that are sure to be active
        f.iter_dom(|block| {
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

        f.iter_dom(|blk| {
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
            if let Inst::Br { cond: _, tr, fls } = blk.tail().as_ref() {
                let mut tgt = vec![tr.borrow().clone(), fls.borrow().clone()];
                tgt.retain(|blk| self.blk.contains(blk));
                match tgt.len() {
                    // Two blocks all active
                    2 => {}
                    // Only one is active, modify the control flow in this block.
                    1 => {
                        let succ = tgt[0].clone();
                        let jmp = ExtRc::new(Inst::Jmp {
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
        f.remove_unreachable();

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

    fn mark(&mut self, blk: BlockRef, instr: InstRef) {
        // Mark block and instruction
        if self.instr.contains(&instr) { return; }
        self.blk.insert(blk.clone());
        self.instr.insert(instr.clone());

        // Add conditional branch upon which this block is control-dependent on
        self.rev_df.get(&blk).cloned().map(|list| {
            list.iter().for_each(|dep| {
                let tail = dep.tail();
                if let Inst::Br { cond: _, tr: _, fls: _ } = tail.deref() {
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

    /// Compute reverse dominance frontier for a given function
    fn rev_df(f: &FnRef) -> HashMap<BlockRef, Vec<BlockRef>> {
        // Build post-dominator tree
        let root = RevVert::Exit(f.clone());
        let parent = DomBuilder::new(root.clone()).build();
        let mut child: HashMap<_, Vec<_>> = HashMap::new();
        parent.iter().for_each(|(c, p)| {
            match child.get_mut(p) {
                Some(list) => list.push(c.clone()),
                None => { child.insert(p.clone(), vec![c.clone()]); }
            }
        });

        // Build post-dominance frontier
        let mut builder = RevDfBuilder {
            parent,
            child,
            df: Default::default(),
        };
        builder.build(root);

        // Convert to block map
        let mut blk_df: HashMap<BlockRef, Vec<BlockRef>> = HashMap::new();
        builder.df.into_iter().for_each(|(b, list)| {
            if let RevVert::Block(b, _) = b {
                list.into_iter().for_each(|df| {
                    if let RevVert::Block(df, _) = df {
                        match blk_df.get_mut(&b) {
                            Some(list) => list.push(df),
                            None => { blk_df.insert(b.clone(), vec![df]); }
                        }
                    }
                })
            }
        });
        blk_df
    }
}

/// Dominance frontier construction for reverse CFG.
/// To make the generic graph algorithm efficient, the vertices in reverse CFG cannot have much
/// bookkeeping, so the listener pattern cannot be adopted here. So the implementation is different
/// from the original CFG, although the algorithm is the same.
struct RevDfBuilder {
    parent: HashMap<RevVert, RevVert>,
    child: HashMap<RevVert, Vec<RevVert>>,
    df: HashMap<RevVert, Vec<RevVert>>,
}

impl RevDfBuilder {
    fn build(&mut self, vert: RevVert) {
        let mut set = HashSet::new();
        vert.succ().iter().for_each(|succ| {
            if self.parent.get(succ) != Some(&vert) {
                set.insert(succ.clone());
            }
        });
        self.child.get(&vert).cloned().map(|list| {
            list.iter().for_each(|child| {
                self.build(child.clone());
                self.df[&child].clone().iter().for_each(|df| {
                    if !self.dominates(&vert, df) || vert == *df {
                        set.insert(df.clone());
                    }
                });
            });
        });
        self.df.insert(vert.clone(), set.into_iter().collect());
    }

    fn dominates(&self, parent: &RevVert, child: &RevVert) -> bool {
        let mut cur = Some(child.clone());
        loop {
            match cur {
                Some(ref block) if parent == block => return true,
                None => return false,
                _ => cur = self.parent.get(&cur.unwrap()).cloned()
            }
        }
    }
}

#[test]
fn test_adce() {
    use crate::irc::lex::Lexer;
    use crate::irc::parse::Parser;
    use crate::irc::build::Builder;
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
    FnPass::run(&mut AdceOpt::new(), &mut pro);

    let mut out = stdout();
    let mut printer = Printer::new(out.borrow_mut());
    printer.print(&pro).unwrap();
}