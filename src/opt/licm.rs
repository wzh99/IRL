use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::ops::Deref;
use std::rc::Rc;

use crate::lang::func::{BlockRef, Func};
use crate::lang::instr::InstrRef;
use crate::lang::Program;
use crate::lang::ssa::{DefPos, DefUseMap};
use crate::lang::util::WorkList;
use crate::lang::value::{SymbolRef, Value};
use crate::opt::{FnPass, Pass};
use crate::opt::util::LoopNodeRef;

pub struct LicmOpt {}

impl Pass for LicmOpt {
    fn opt(&mut self, pro: &mut Program) { FnPass::opt(self, pro) }
}

impl FnPass for LicmOpt {
    fn opt_fn(&mut self, func: &Rc<Func>) {
        // Build loop-nest trees
        let trees = func.analyze_loop();

        // Hoist code in post order of loop-nest tree
        let mut stack: Vec<_> = trees.into_iter().map(|node| (node, false)).collect();
        loop {
            match stack.pop() {
                Some((node, true)) => self.opt_loop(func, node),
                Some((node, false)) => {
                    stack.push((node.clone(), true));
                    node.borrow().nested.clone().into_iter()
                        .for_each(|blk| stack.push((blk, false)));
                }
                None => break
            }
        }
    }
}

impl LicmOpt {
    pub fn new() -> LicmOpt { LicmOpt {} }

    fn opt_loop(&self, func: &Rc<Func>, node: LoopNodeRef) {
        // Get define-use information
        // This should be computed in each loop, because the definition point of a value may have
        // changed when processing the previous loop.
        let ref def_use = func.def_use();

        // Build instruction work list
        let mut instr_list: HashSet<InstrRef> = HashSet::new();
        let level = node.borrow().level_blocks();
        level.iter().for_each(|blk| {
            blk.instr.borrow().iter().for_each(|instr| { instr_list.insert(instr.clone()); })
        });
        let mut work: WorkList<_> = instr_list.clone().into_iter().collect();

        // Iteratively find all loop invariants and hoist them
        let ref header = node.borrow().header.clone();
        let ref mut hoist: HashMap<SymbolRef, BlockRef> = HashMap::new();
        let ref mut removed: HashSet<InstrRef> = HashSet::new();
        loop {
            match work.pick() {
                Some(instr) => {
                    // Check destination of this instruction
                    let dst = instr.dst();
                    if dst.is_none() || dst.unwrap().borrow().is_global_var() {
                        continue;
                    }
                    let ref dst = dst.unwrap().borrow().clone();

                    // Check whether this instruction has side effects
                    if instr.has_side_effect() { continue; }

                    // Check whether all operands are loop invariant
                    let src = instr.src();
                    if !src.iter().all(|o| Self::is_invariant(o, header, def_use, hoist)) {
                        continue;
                    }

                    // Hoist to an appropriate location
                    let blk = src.iter().map(|o| Self::def_block(o, func, def_use, hoist))
                        .fold(func.ent.borrow().clone(), |a, b| {
                            if a.strict_dom(&b) { b } else { a }
                        });
                    blk.insert_before_ctrl(instr.clone());
                    hoist.insert(dst.clone(), blk);
                    removed.insert(instr);

                    // Add uses of destination symbol to worklist
                    def_use[dst].uses.iter().for_each(|u| {
                        if instr_list.contains(u) { work.insert(u.clone()) }
                    })
                }
                None => break
            }
        }

        // Remove instruction in their original block
        level.iter().for_each(|blk| {
            blk.instr.borrow_mut().retain(|instr| !removed.contains(instr))
        })
    }

    fn is_invariant(val: &RefCell<Value>, header: &BlockRef, def_use: &DefUseMap,
                    hoist: &HashMap<SymbolRef, BlockRef>) -> bool
    {
        match val.borrow().deref() {
            Value::Const(_) => true,
            Value::Var(sym) if sym.is_local_var() => match &def_use[sym].def {
                DefPos::Param => true,
                DefPos::Instr(blk, _) => blk.strict_dom(header) || hoist.contains_key(sym),
                DefPos::None => unreachable!()
            }
            _ => false
        }
    }

    fn def_block(val: &RefCell<Value>, func: &Rc<Func>, def_use: &DefUseMap,
                 hoist: &HashMap<SymbolRef, BlockRef>) -> BlockRef
    {
        let ent = func.ent.borrow().clone();
        match val.borrow().deref() {
            Value::Const(_) => ent,
            Value::Var(sym) => match &def_use[sym].def {
                DefPos::Param => ent,
                DefPos::Instr(blk, _) => match hoist.get(sym) {
                    Some(new_blk) => new_blk.clone(),
                    None => blk.clone()
                }
                DefPos::None => unreachable!()
            }
        }
    }
}

#[test]
fn test_licm() {
    use crate::compile::lex::Lexer;
    use crate::compile::parse::Parser;
    use crate::compile::build::Builder;
    use crate::lang::print::Printer;
    use crate::opt::osr::OsrOpt;
    use crate::opt::pre::PreOpt;
    use crate::opt::util::PtrExp;
    use crate::vm::exec::Machine;

    use std::fs::File;
    use std::convert::TryFrom;
    use std::io::Read;
    use std::io::stdout;
    use std::borrow::BorrowMut;

    let mut file = File::open("test/mat.ir").unwrap();
    let lexer = Lexer::try_from(&mut file as &mut dyn Read).unwrap();
    let parser = Parser::new(lexer);
    let tree = parser.parse().unwrap();
    let builder = Builder::new(tree);
    let mut pro = builder.build().unwrap();

    let mut mach = Machine::new();
    println!("orig: {:?}", mach.run(&pro).unwrap());
    FnPass::opt(&mut PtrExp::new(), &mut pro);
    // println!("ptr: {:?}", mach.run(&pro).unwrap());
    FnPass::opt(&mut PreOpt::new(), &mut pro);
    // println!("pre: {:?}", mach.run(&pro).unwrap());
    FnPass::opt(&mut LicmOpt::new(), &mut pro);
    // println!("licm: {:?}", mach.run(&pro).unwrap());
    FnPass::opt(&mut OsrOpt::new(), &mut pro);
    println!("osr: {:?}", mach.run(&pro).unwrap());

    let mut out = stdout();
    let mut printer = Printer::new(out.borrow_mut());
    printer.print(&pro).unwrap();
}