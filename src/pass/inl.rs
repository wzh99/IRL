use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::ops::Deref;

use crate::lang::func::{BlockGen, BlockRef, FnAttrib, FnRef};
use crate::lang::inst::Inst;
use crate::lang::Program;
use crate::lang::util::ExtRc;
use crate::lang::value::{SymbolGen, SymbolRef, Typed, Value};
use crate::pass::Pass;

pub struct Inliner {
    /// Functions to be inlined
    tgt: HashSet<FnRef>,
    /// Map blocks in callee to new blocks in caller
    blk_map: HashMap<BlockRef, BlockRef>,
    /// Map symbols in callee to values in caller
    sym_map: HashMap<SymbolRef, SymbolRef>,
    /// Stack of nested inlined functions
    /// It may happen that a inlined function calls another function that could be inlined. This
    /// allows for multiple levels of inline expansion.
    nested: Vec<FnRef>,
    /// Stack of exit blocks
    /// During inline expansion, exit blocks of some inlined functions may change. This record
    /// the latest exit blocks of inlined functions. This stack is always one element fewer than
    /// function stack.
    exit: Vec<Vec<BlockRef>>,
    /// Block generator for current function
    blk_gen: Option<BlockGen>,
    /// Symbol generator for current function
    sym_gen: SymbolGen,
}

impl Pass for Inliner {
    fn run(&mut self, pro: &mut Program) {
        // Make sure all functions is in SSA form
        // Actually, inlining does not rely on SSA property. However, an SSA function may call
        // a non-SSA function and the SSA property no longer holds. On the other hand, a non-SSA
        // function may call an SSA function and introduce phi instruction for itself. It will
        // cause a problem if that non-SSA function is later converted to SSA form.
        // The safe approach is to ensure all functions are in SSA form.
        pro.func.iter().for_each(|f| f.assert_ssa());

        // Find target for inlining
        self.tgt = pro.func.iter()
            .filter(|f| Self::can_inl(f)).cloned().collect();

        // Process blocks
        let tgt: Vec<_> = pro.func.iter()
            .filter(|f| !self.tgt.contains(f)).cloned().collect();
        tgt.iter().for_each(|f| {
            f.assert_ssa();

            // Push this function to nested stack
            self.nested.push(f.clone());

            // Initialize block generator for this function
            self.blk_gen = Some(BlockGen::new(f.as_ref(), ""));
            self.sym_gen = SymbolGen::new(f.scope.clone(), "t");

            // Process blocks in this function
            f.iter_dom().for_each(|b| self.proc_blk(f, b));

            // Rebuild dominator tree
            f.build_dom();

            // Clear records for this function
            self.blk_map.clear();
            self.sym_map.clear();
            self.nested.clear();
        });
    }
}

impl Inliner {
    pub fn new() -> Inliner {
        Inliner {
            tgt: Default::default(),
            blk_map: Default::default(),
            sym_map: Default::default(),
            nested: vec![],
            exit: vec![],
            blk_gen: None,
            sym_gen: SymbolGen::new(Default::default(), ""),
        }
    }

    fn can_inl(f: &FnRef) -> bool { f.has_attrib(FnAttrib::Inline) }

    fn proc_blk(&mut self, caller: &FnRef, mut blk: BlockRef) {
        loop {
            // Find the first call instruction
            let pos = blk.inst.borrow().iter().position(|inst| match inst.as_ref() {
                // Inline this function if it could be inlined, and it is not on the nested stack.
                // If this function is on the nested stack, it is a recursive call. Inlining
                // recursive call will lead to infinite recursion in inliner.
                Inst::Call { func, arg: _, dst: _ }
                if self.tgt.contains(func) && !self.nested.contains(func) => true,
                _ => false
            });
            let pos = if let Some(pos) = pos { pos } else { return; };

            // Inline the called function
            let call = blk.inst.borrow()[pos].clone();
            let (callee, arg, dst) = if let Inst::Call { func, arg, dst } = call.as_ref() {
                (func, arg, dst)
            } else { unreachable!() };
            let (ent, exit) = self.inl_fn(caller, callee, arg);

            // Split the block separated by call instruction
            let blk_split = self.blk_gen.as_mut().unwrap().rename(&blk);
            blk_split.succ.replace(blk.succ.borrow().clone());
            let inst_split = blk.inst.borrow_mut().split_off(pos);
            blk_split.inst.replace(inst_split);

            // Insert blocks of callee into caller block
            blk.succ.replace(vec![ent.clone()]); // connect to entry block
            blk.push_back(ExtRc::new(Inst::Jmp { tgt: RefCell::new(ent.clone()) }));
            ent.pred.replace(vec![blk.clone()]);
            blk_split.pred.replace(exit.iter().map(|exit| { // connect to exit blocks
                exit.succ.replace(vec![blk_split.clone()]); // connect to the split block
                exit
            }).cloned().collect());

            // Collect return result
            blk_split.inst.borrow_mut().pop_front(); // remove the call instruction
            dst.as_ref().map(|dst| {
                // Create phi source operands
                let phi_src: Vec<_> = exit.clone().into_iter().map(|exit| {
                    let val = exit.inst.borrow().back().unwrap().src()[0].clone();
                    let ret_sym = self.sym_gen.gen(&val.borrow().get_type());
                    exit.insert_before_ctrl(ExtRc::new(Inst::Mov {
                        src: val,
                        dst: RefCell::new(ret_sym.clone()),
                    }));
                    (RefCell::new(exit), RefCell::new(Value::Var(ret_sym)))
                }).collect();

                // Assign returned result to destination
                let ref dst_ty = dst.borrow().get_type();
                let collect_sym = self.sym_gen.gen(dst_ty);
                blk_split.push_front(ExtRc::new(Inst::Mov {
                    src: RefCell::new(Value::Var(collect_sym.clone())),
                    dst: dst.clone(),
                }));
                blk_split.push_front(ExtRc::new(Inst::Phi { // add phi in front of split block
                    src: phi_src,
                    dst: RefCell::new(collect_sym),
                }));
            });

            // Connect exit blocks to split block of caller function
            exit.iter().for_each(|exit| {
                *exit.inst.borrow_mut().back_mut().unwrap() = ExtRc::new(Inst::Jmp {
                    tgt: RefCell::new(blk_split.clone())
                })
            });

            // Update exit blocks of current function
            let replace = |exit: &mut BlockRef| if exit == &blk { *exit = blk_split.clone() };
            match self.exit.last_mut() {
                Some(exit) => exit.iter_mut().for_each(replace),
                None => caller.exit.borrow_mut().iter_mut().for_each(replace)
            }

            // Visit the rest instructions
            blk = blk_split
        }
    }

    /// Inline function with given arguments. Return entry block and exit blocks of inlined
    /// function.
    fn inl_fn(&mut self, caller: &FnRef, callee: &FnRef, arg: &Vec<RefCell<Value>>)
              -> (BlockRef, Vec<BlockRef>)
    {
        // Push this function to nested stack
        self.nested.push(callee.clone());

        // Create corresponding blocks of callee
        callee.iter_dom().for_each(|ref b| {
            self.blk_map.insert(b.clone(), self.blk_gen.as_mut().unwrap().rename(b));
        });
        self.blk_map.iter().for_each(|(prev, new)| {
            new.pred.replace(prev.pred.borrow().iter()
                .map(|p| self.blk_map[p].clone()).collect()
            );
            new.succ.replace(prev.succ.borrow().iter()
                .map(|s| self.blk_map[s].clone()).collect()
            );
        });

        // Push current version of function exits to stack
        self.exit.push(callee.exit.borrow().iter().map(|b| self.blk_map[b].clone()).collect());

        // Map symbols
        callee.scope.collect().into_iter().for_each(|ref s| {
            self.sym_map.insert(s.clone(), self.sym_gen.rename(s));
        });

        // Transfer instructions to new block
        self.blk_map.clone().iter().for_each(|(prev, new)| self.trans_inst(caller, prev, new));

        // Assign arguments to parameters
        let ent = self.blk_map[callee.ent.borrow().deref()].clone();
        callee.param.iter().zip(arg).for_each(|(p, a)| {
            ent.push_front(ExtRc::new(Inst::Mov {
                src: a.clone(),
                dst: RefCell::new(self.sym_map[p.borrow().deref()].clone()),
            }));
        });

        // Pop this function from nested stack
        self.nested.pop();

        // Return entry and exit blocks of inlined function
        (ent, self.exit.pop().unwrap())
    }

    /// Transfer instructions from one block to another. Possibly inline functions in the new block
    /// if some instruction calls another function that could be inlined.
    fn trans_inst(&mut self, caller: &FnRef, from: &BlockRef, to: &BlockRef) {
        // Transfer instructions to new block
        to.inst.replace(from.inst.borrow().iter().map(|inst| {
            // Clone the original instruction
            let inst = ExtRc::new(inst.as_ref().clone());

            // Map symbols
            inst.src().iter().for_each(|src| {
                src.replace_with(|v| {
                    match v {
                        Value::Var(sym) if sym.is_local_var() =>
                            Value::Var(self.sym_map[&sym].clone()),
                        _ => v.clone()
                    }
                });
            });
            inst.dst().map(|dst| {
                if dst.borrow().is_global_var() { return; }
                let ref sym = dst.borrow().clone();
                dst.replace(self.sym_map[sym].clone());
            });

            // Map blocks
            inst.blk().iter().for_each(|blk| {
                let ref b = blk.borrow().clone();
                blk.replace(self.blk_map[b].clone());
            });

            inst
        }).collect());

        // Do nested inline expansion in the new block
        self.proc_blk(caller, to.clone());
    }
}

#[test]
fn test_inl() {
    use crate::irc::lex::Lexer;
    use crate::irc::parse::Parser;
    use crate::irc::build::Builder;
    use crate::lang::print::Printer;
    use crate::vm::exec::Machine;
    use std::io::stdout;
    use std::fs::File;
    use std::convert::TryFrom;
    use std::io::Read;
    use std::borrow::BorrowMut;

    let mut file = File::open("test/example.ir").unwrap();
    let lexer = Lexer::try_from(&mut file as &mut dyn Read).unwrap();
    let parser = Parser::new(lexer);
    let tree = parser.parse().unwrap();
    let builder = Builder::new(tree);
    let mut pro = builder.build().unwrap();
    Pass::run(&mut Inliner::new(), &mut pro);

    let mut out = stdout();
    let mut printer = Printer::new(out.borrow_mut());
    printer.print(&pro).unwrap();

    let mut mach = Machine::new();
    let rcd = mach.run(&mut pro).unwrap();
    println!("{:?}", rcd);
}
