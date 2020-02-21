use std::cell::{Cell, RefCell};
use std::collections::{HashMap, HashSet};
use std::ops::Deref;

use crate::lang::func::{BlockRef, DomVisitor, Func};
use crate::lang::instr::{Instr, InstrRef, PhiSrc};
use crate::lang::util::{ExtRc, WorkList};
use crate::lang::val::{Symbol, SymbolRef, Typed, Value};

/// Wrapper of SSA flag to make it only modifiable in this module.
#[derive(Debug)]
pub struct SsaFlag(Cell<bool>);

impl SsaFlag {
    pub fn new() -> SsaFlag { SsaFlag(Cell::new(false)) }
    pub fn get(&self) -> bool { self.0.get() }
    fn set(&self, val: bool) { self.0.set(val) }
}

/// Visitor of instructions in SSA program.
pub trait InstrVisitor<E>: DomVisitor<E> {
    fn on_begin(&mut self, func: &Func) -> Result<(), E> {
        // Visit phi instructions in the entrance block
        for instr in func.ent.borrow().instr.borrow().iter().cloned() {
            match instr.deref() {
                Instr::Phi { src: _, dst: _ } => self.on_succ_phi(None, instr)?,
                _ => break
            }
        }
        Ok(())
    }

    fn on_enter(&mut self, block: BlockRef) -> Result<(), E> {
        // Perform first-access action before visiting instructions
        self.on_access(block.clone())?;

        // Visit instructions
        for instr in block.instr.borrow().iter().cloned() {
            self.on_instr(instr)?;
        }

        // Visit phi instructions in successors
        for succ in block.succ.borrow().iter() {
            for instr in succ.instr.borrow().iter() {
                match instr.deref() {
                    Instr::Phi { src: _, dst: _ } =>
                        self.on_succ_phi(Some(block.clone()), instr.clone())?,
                    _ => break // phi instructions must be at front of each block
                }
            }
        }

        Ok(())
    }

    /// Called when `block` is accessed for the first time, before visiting instructions inside.
    fn on_access(&mut self, block: BlockRef) -> Result<(), E>;

    /// Called when visiting each instruction.
    fn on_instr(&mut self, instr: InstrRef) -> Result<(), E>;

    /// Called when visiting phi instructions in successor blocks.
    fn on_succ_phi(&mut self, this: Option<BlockRef>, instr: InstrRef) -> Result<(), E>;
}

/// Visitor of variables in SSA program.
pub trait VarVisitor<E>: InstrVisitor<E> {
    fn on_instr(&mut self, instr: InstrRef) -> Result<(), E> {
        match instr.deref() {
            Instr::Phi { src: _, dst: _ } => if let Some(dst) = instr.dst() {
                self.on_def(dst)?;
            }
            _ => {
                for opd in instr.src() {
                    self.on_use(opd)?;
                }
                if let Some(dst) = instr.dst() {
                    self.on_def(dst)?;
                }
            }
        }
        Ok(())
    }

    fn on_succ_phi(&mut self, this: Option<BlockRef>, instr: InstrRef) -> Result<(), E> {
        if let Instr::Phi { src, dst: _ } = instr.deref() {
            for (pred, opd) in src {
                match (&this, pred, opd) {
                    (Some(this), Some(pred), opd) if this == pred => self.on_use(opd)?,
                    (None, None, opd) => self.on_use(opd)?,
                    _ => ()
                }
            }
        }
        Ok(())
    }

    /// Call on operands (uses) of the instruction.
    fn on_use(&mut self, opd_list: &RefCell<Value>) -> Result<(), E>;

    /// Call on possible definition of the instruction.
    fn on_def(&mut self, def: &RefCell<SymbolRef>) -> Result<(), E>;
}

pub struct Verifier {
    // Whether a variable is found to be statically defined.
    def: HashSet<SymbolRef>,
    // Whether variables are available when reaching this block.
    // Organized as stack of frames, representing nodes on the path from root to current block
    avail: Vec<Vec<SymbolRef>>,
}

impl DomVisitor<String> for Verifier {
    fn on_begin(&mut self, func: &Func) -> Result<(), String> {
        // Add parameters as the first frame
        func.param.iter().for_each(|p| { self.def.insert(p.borrow().clone()); });
        self.avail.push(func.param.iter().map(|p| p.borrow().clone()).collect());

        // Check phi operands in entrance block
        InstrVisitor::on_begin(self, func)?;
        Ok(())
    }

    fn on_end(&mut self, func: &Func) -> Result<(), String> {
        func.ssa.set(true);
        self.def.clear();
        self.avail.clear();
        Ok(())
    }

    fn on_enter(&mut self, block: BlockRef) -> Result<(), String> {
        InstrVisitor::on_enter(self, block)
    }

    fn on_exit(&mut self, _: BlockRef) -> Result<(), String> {
        self.avail.pop();
        Ok(())
    }

    fn on_enter_child(&mut self, _: BlockRef, _: BlockRef) -> Result<(), String> { Ok(()) }

    fn on_exit_child(&mut self, _: BlockRef, _: BlockRef) -> Result<(), String> { Ok(()) }
}

impl InstrVisitor<String> for Verifier {
    fn on_access(&mut self, block: BlockRef) -> Result<(), String> {
        // Push current frame to stack
        self.avail.push(vec![]);

        // Build predecessor list
        let req_pred = block.phi_pred();

        // Check correspondence of phi operands to predecessors
        for instr in block.instr.borrow().iter() {
            match instr.deref() {
                Instr::Phi { src, dst: _ } => {
                    let phi_pred: Vec<Option<BlockRef>> = src.iter()
                        .map(|(pred, _)| pred.clone()).collect();
                    for pred in &req_pred {
                        if !phi_pred.contains(pred) {
                            return Err(format!(
                                "phi operand not found for {}",
                                match pred {
                                    Some(p) => format!("predecessor {}", p.name),
                                    None => "function parameter".to_string()
                                }
                            ));
                        }
                    }
                }
                _ => break
            }
        }

        Ok(())
    }

    fn on_instr(&mut self, instr: InstrRef) -> Result<(), String> {
        VarVisitor::on_instr(self, instr)
    }

    fn on_succ_phi(&mut self, this: Option<BlockRef>, instr: InstrRef) -> Result<(), String> {
        VarVisitor::on_succ_phi(self, this, instr)
    }
}

impl VarVisitor<String> for Verifier {
    fn on_use(&mut self, opd: &RefCell<Value>) -> Result<(), String> {
        match opd.borrow().deref() {
            Value::Var(sym) if sym.is_local_var() && !self.is_avail(sym) => {
                return Err(format!(
                    "variable {} is used before defined", sym.id()
                ));
            }
            _ => ()
        }
        Ok(())
    }

    fn on_def(&mut self, def: &RefCell<SymbolRef>) -> Result<(), String> {
        if def.borrow().is_local_var() {
            let sym = def.borrow().clone();
            if self.def.contains(&sym) { // already statically defined
                return Err(format!(
                    "variable {} already defined", sym.id()
                ));
            } else {
                self.def.insert(sym.clone()); // mark this static definition
                // add to current frame of availability stack
                self.avail.last_mut().unwrap().push(sym)
            }
        }
        Ok(())
    }
}

impl Verifier {
    pub fn new() -> Verifier {
        Verifier {
            def: HashSet::new(),
            avail: vec![],
        }
    }

    fn is_avail(&self, sym: &SymbolRef) -> bool {
        self.avail.iter().any(|frame| frame.contains(sym))
    }
}

impl Func {
    pub fn to_ssa(&self) {
        // Compute dominance frontiers of blocks
        if self.ssa.get() { return; } // already in SSA form
        let df = self.compute_df();
        // Insert phi instructions
        self.insert_phi(&df);
        // Rename variables
        self.rename()
    }

    fn insert_phi(&self, df: &HashMap<BlockRef, Vec<BlockRef>>) {
        // Keep records for blocks and symbols
        // set of symbols the phi's of whom are inserted
        let mut ins_phi: HashMap<BlockRef, HashSet<SymbolRef>> = HashMap::new();
        // set of symbols defined in a block
        let mut orig: HashMap<BlockRef, HashSet<SymbolRef>> = HashMap::new();
        // set of block where a symbol is defined
        let mut def_site: HashMap<SymbolRef, HashSet<BlockRef>> = HashMap::new();

        // Build these records
        self.scope.for_each(|sym| { def_site.insert(sym, HashSet::new()); });
        self.dfs().for_each(|block| {
            ins_phi.insert(block.clone(), HashSet::new());
            let def = self.defined_sym(&block);
            def.iter().for_each(|sym| {
                def_site.get_mut(sym).unwrap().insert(block.clone());
            });
            orig.insert(block, def);
        });

        // Insert phi instructions using worklist algorithm
        self.scope.for_each(|sym| {
            let mut work: WorkList<BlockRef> = def_site.get(&sym).unwrap().iter()
                .cloned().collect();
            while !work.is_empty() {
                let block = work.pick().unwrap();
                for tgt in df.get(&block).unwrap() {
                    // Insert phi instruction for this symbol
                    if ins_phi.get(tgt).unwrap().contains(&sym) { continue; }
                    let src: Vec<PhiSrc> = tgt.phi_pred().into_iter().map(|pred| {
                        (pred, RefCell::new(Value::Var(sym.clone())))
                    }).collect();
                    tgt.push_front(Instr::Phi { src, dst: RefCell::new(sym.clone()) });

                    // Update records
                    ins_phi.get_mut(tgt).unwrap().insert(sym.clone());
                    if !orig.get(&tgt).unwrap().contains(&sym) {
                        work.add(tgt.clone());
                    }
                }
            }
        })
    }

    fn rename(&self) {
        let mut visitor = RenameVisitor {
            sym: HashMap::new(),
            def: vec![],
        };
        self.visit_dom(&mut visitor).unwrap();
    }

    fn defined_sym(&self, block: &BlockRef) -> HashSet<SymbolRef> {
        let mut def: HashSet<SymbolRef> = HashSet::new();
        for instr in block.instr.borrow().iter() {
            instr.dst().map(|sym| { def.insert(sym.borrow().clone()); });
        }
        def
    }
}

struct RenamedSym {
    /// How many versions are defined now
    count: usize,
    /// Stack of versioned variables
    stack: Vec<SymbolRef>,
}

impl RenamedSym {
    fn latest(&self) -> SymbolRef { self.stack.last().unwrap().clone() }

    fn pop(&mut self) { self.stack.pop(); }

    fn rename(&mut self) -> SymbolRef {
        self.count += 1;
        let new_sym =
            if let Symbol::Local { name, ty, ver: Some(_) } = self.latest().deref() {
                ExtRc::new(Symbol::Local {
                    name: name.clone(),
                    ty: ty.clone(),
                    ver: Some(self.count),
                })
            } else { unreachable!() };
        self.stack.push(new_sym.clone());
        new_sym
    }
}

struct RenameVisitor {
    /// Map symbol name to its renaming status
    sym: HashMap<String, RenamedSym>,
    /// Stack of frames for defined symbols in each block
    def: Vec<Vec<String>>,
}

impl DomVisitor<()> for RenameVisitor {
    fn on_begin(&mut self, func: &Func) -> Result<(), ()> {
        // Initialize renaming stack
        func.scope.for_each(|sym| {
            self.sym.insert(sym.name().to_string(), RenamedSym {
                count: 0,
                stack: vec![
                    ExtRc::new(Symbol::Local {
                        name: sym.name().to_string(),
                        ty: sym.get_type(),
                        ver: Some(0),
                    })
                ],
            });
        });

        // Replace function parameters
        func.param.iter().for_each(|param| {
            let new_sym = self.sym.get(param.borrow().name()).unwrap()
                .stack.last().unwrap().clone();
            param.replace(new_sym);
        });

        InstrVisitor::on_begin(self, func)
    }

    fn on_end(&mut self, _: &Func) -> Result<(), ()> {
        self.sym.clear();
        self.def.clear();
        Ok(())
    }

    fn on_enter(&mut self, block: BlockRef) -> Result<(), ()> {
        self.def.push(vec![]);
        InstrVisitor::on_enter(self, block)
    }

    fn on_exit(&mut self, _: BlockRef) -> Result<(), ()> {
        for name in self.def.last().unwrap() {
            self.sym.get_mut(name).unwrap().pop();
        }
        self.def.pop();
        Ok(())
    }

    fn on_enter_child(&mut self, _: BlockRef, _: BlockRef) -> Result<(), ()> { Ok(()) }

    fn on_exit_child(&mut self, _: BlockRef, _: BlockRef) -> Result<(), ()> { Ok(()) }
}

impl InstrVisitor<()> for RenameVisitor {
    fn on_access(&mut self, _: BlockRef) -> Result<(), ()> { Ok(()) }

    fn on_instr(&mut self, instr: InstrRef) -> Result<(), ()> {
        VarVisitor::on_instr(self, instr)
    }

    fn on_succ_phi(&mut self, this: Option<BlockRef>, instr: InstrRef) -> Result<(), ()> {
        VarVisitor::on_succ_phi(self, this, instr)
    }
}

impl VarVisitor<()> for RenameVisitor {
    fn on_use(&mut self, opd: &RefCell<Value>) -> Result<(), ()> {
        opd.replace_with(|opd| {
            if let Value::Var(sym) = opd.deref() {
                let latest = self.sym.get(sym.name()).unwrap().latest();
                Value::Var(latest)
            } else { opd.clone() }
        });
        Ok(())
    }

    fn on_def(&mut self, def: &RefCell<SymbolRef>) -> Result<(), ()> {
        def.replace_with(|sym| {
            let new_sym = self.sym.get_mut(sym.name()).unwrap().rename();
            self.def.last_mut().unwrap().push(new_sym.name().to_string());
            new_sym
        });
        Ok(())
    }
}

#[test]
fn test_ssa() {
    use crate::compile::lex::Lexer;
    use crate::compile::parse::Parser;
    use crate::compile::build::Builder;
    use crate::lang::print::Printer;
    use std::io::stdout;
    use std::fs::File;
    use std::convert::TryFrom;
    use std::io::Read;
    use std::borrow::BorrowMut;

    let mut file = File::open("test/ssa.ir").unwrap();
    let lexer = Lexer::try_from(&mut file as &mut dyn Read).unwrap();
    let parser = Parser::new(lexer);
    let tree = parser.parse().unwrap();
    let builder = Builder::new(tree);
    let pro = builder.build().unwrap();
    for func in &pro.funcs {
        func.to_ssa();
    }
    let mut out = stdout();
    let mut printer = Printer::new(out.borrow_mut());
    printer.print(&pro).unwrap();
}
