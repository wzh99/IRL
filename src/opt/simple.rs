use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::ops::Deref;
use std::rc::Rc;

use crate::lang::func::{BlockListener, BlockRef, Func};
use crate::lang::instr::{Instr, InstrRef};
use crate::lang::Program;
use crate::lang::ssa::{InstrListener, ValueListener};
use crate::lang::util::ExtRc;
use crate::lang::value::{Const, SymbolGen, SymbolRef, Type, Typed, Value};
use crate::opt::{FnPass, Pass};

/// Copy Propagation
pub struct CopyProp {}

impl CopyProp {
    pub fn new() -> CopyProp { CopyProp {} }
}

impl Pass for CopyProp {
    fn opt(&mut self, pro: &mut Program) { FnPass::opt(self, pro) }
}

impl FnPass for CopyProp {
    fn opt_fn(&mut self, func: &Rc<Func>) {
        let mut listener = CopyListener {
            map: Default::default(),
            def: vec![],
            rm: Default::default(),
        };
        func.walk_dom(&mut listener)
    }
}

struct CopyListener {
    map: HashMap<SymbolRef, Value>,
    def: Vec<Vec<SymbolRef>>,
    rm: HashSet<InstrRef>,
}

impl BlockListener for CopyListener {
    fn on_begin(&mut self, _func: &Func) {}

    fn on_end(&mut self, _func: &Func) {}

    fn on_enter(&mut self, block: BlockRef) {
        self.def.push(vec![]);
        InstrListener::on_enter(self, block.clone());
        block.instr.borrow_mut().retain(|instr| {
            !self.rm.contains(instr)
        })
    }

    fn on_exit(&mut self, _block: BlockRef) {
        self.def.pop().unwrap().into_iter().for_each(|sym| {
            self.map.remove(&sym);
        })
    }

    fn on_enter_child(&mut self, _this: BlockRef, _child: BlockRef) {}

    fn on_exit_child(&mut self, _this: BlockRef, _child: BlockRef) {}
}

impl InstrListener for CopyListener {
    fn on_instr(&mut self, instr: InstrRef) {
        if let Instr::Mov { src, dst } = instr.as_ref() {
            if src.borrow().is_global_var() || dst.borrow().is_global_var() {
                return; // don't propagate global variable
            }
            match src.borrow().deref() {
                Value::Const(_) => self.map.insert(dst.borrow().clone(), src.borrow().clone()),
                Value::Var(sym) =>
                    self.map.insert(dst.borrow().clone(), self.map.get(sym).cloned()
                        .unwrap_or(Value::Var(sym.clone())))
            };
            self.def.last_mut().unwrap().push(dst.borrow().clone());
            self.rm.insert(instr);
        } else {
            ValueListener::on_instr(self, instr)
        }
    }

    fn on_succ_phi(&mut self, this: Option<BlockRef>, instr: InstrRef) {
        ValueListener::on_succ_phi(self, this, instr)
    }
}

impl ValueListener for CopyListener {
    fn on_use(&mut self, _instr: InstrRef, opd: &RefCell<Value>) {
        opd.replace_with(|opd| {
            match opd {
                Value::Var(ref sym) if self.map.contains_key(sym) => self.map[sym].clone(),
                _ => opd.clone()
            }
        });
    }

    fn on_def(&mut self, _instr: InstrRef, _def: &RefCell<SymbolRef>) {}
}

/// Pointer operation expansion
/// Note that this transformation does not directly improve runtime efficiency, but provide
/// opportunities for later optimizations.
pub struct PtrExp {}

impl PtrExp {
    pub fn new() -> PtrExp { PtrExp {} }
}

impl Pass for PtrExp {
    fn opt(&mut self, pro: &mut Program) { FnPass::opt(self, pro) }
}

impl FnPass for PtrExp {
    fn opt_fn(&mut self, func: &Rc<Func>) {
        func.iter_dom(|block| {
            // Find pointer instruction with indices
            let ptr_list: Vec<InstrRef> = block.instr.borrow().iter().filter(|instr| {
                if let Instr::Ptr { base: _, off: _, ind, dst: _ } = instr.as_ref() {
                    !ind.is_empty()
                } else { false }
            }).cloned().collect();

            // Expand pointer operation
            let mut gen = SymbolGen::new("t", func.scope.clone());
            ptr_list.into_iter().for_each(|ref ptr| {
                if let Instr::Ptr { base, off, ind, dst } = ptr.as_ref() {
                    // Extract the base pointer
                    let mut expand = vec![];
                    let mut cur_ptr = gen.gen(&base.borrow().get_type());
                    let base_instr = ExtRc::new(Instr::Ptr {
                        base: base.clone(),
                        off: off.clone(),
                        ind: vec![],
                        dst: RefCell::new(cur_ptr.clone()),
                    });
                    expand.push(base_instr);

                    // Convert indices to offsets
                    let mut cur_ty = cur_ptr.get_type().tgt_type();
                    ind.iter().enumerate().for_each(|(i, idx_val)| {
                        match cur_ty.clone() {
                            Type::Array { elem, len: _ } => {
                                // Point to the first element
                                let ref elem_ptr_ty = Type::Ptr(elem.clone());
                                cur_ty = elem.deref().clone();
                                let head_ptr = gen.gen(elem_ptr_ty);
                                let head_instr = ExtRc::new(Instr::Ptr {
                                    base: RefCell::new(Value::Var(cur_ptr.clone())),
                                    off: None,
                                    ind: vec![RefCell::new(Value::Const(Const::I64(0)))],
                                    dst: RefCell::new(head_ptr.clone()),
                                });
                                expand.push(head_instr);

                                // Offset to specified location
                                let elem_ptr = if i == ind.len() - 1 {
                                    dst.borrow().clone()
                                } else { gen.gen(elem_ptr_ty) };
                                let elem_instr = ExtRc::new(Instr::Ptr {
                                    base: RefCell::new(Value::Var(head_ptr.clone())),
                                    off: Some(idx_val.clone()),
                                    ind: vec![],
                                    dst: RefCell::new(elem_ptr.clone()),
                                });
                                expand.push(elem_instr);
                                cur_ptr = elem_ptr;
                            }
                            // For structure type, the only way to access its member is through
                            // constant index. Therefore, it cannot be converted to offset.
                            Type::Struct { field } => {
                                let idx =
                                    if let Value::Const(Const::I64(i)) = idx_val.borrow().deref() {
                                        *i
                                    } else { unreachable!() };
                                let cur_ty = field[idx as usize].clone();
                                let ref elem_ptr_ty = Type::Ptr(Box::new(cur_ty.clone()));
                                let elem_ptr = if i == ind.len() - 1 {
                                    dst.borrow().clone()
                                } else { gen.gen(elem_ptr_ty) };
                                let elem_instr = ExtRc::new(Instr::Ptr {
                                    base: RefCell::new(Value::Var(elem_ptr.clone())),
                                    off: None,
                                    ind: vec![idx_val.clone()],
                                    dst: RefCell::new(elem_ptr.clone()),
                                });
                                expand.push(elem_instr);
                                cur_ptr = elem_ptr;
                            }
                            _ => unreachable!()
                        }
                    });

                    // Insert the expanded instructions to block
                    let pos = block.instr.borrow().iter().position(|instr| instr == ptr).unwrap();
                    block.instr.borrow_mut().remove(pos);
                    expand.into_iter().rev().for_each(|instr| {
                        block.instr.borrow_mut().insert(pos, instr)
                    })
                } else { unreachable!() }
            })
        })
    }
}

#[test]
fn test_ptr_exp() {
    use crate::compile::lex::Lexer;
    use crate::compile::parse::Parser;
    use crate::compile::build::Builder;
    use crate::lang::print::Printer;
    use crate::opt::osr::OsrOpt;
    use crate::opt::pre::PreOpt;

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

    FnPass::opt(&mut PtrExp::new(), &mut pro);
    FnPass::opt(&mut PreOpt::new(), &mut pro);
    // FnPass::opt(&mut OsrOpt::new(), &mut pro);

    let mut out = stdout();
    let mut printer = Printer::new(out.borrow_mut());
    printer.print(&pro).unwrap();
}

