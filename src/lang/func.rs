use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt::{Debug, Error, Formatter};
use std::iter::FromIterator;
use std::ops::Deref;
use std::rc::Rc;
use std::str::FromStr;

use crate::lang::graph::DomBuilder;
use crate::lang::inst::{Inst, InstRef};
use crate::lang::ssa::SsaFlag;
use crate::lang::util::ExtRc;
use crate::lang::value::{Scope, SymbolRef, Type, Typed};

#[derive(Debug)]
pub struct Fn {
    /// Name of this function
    pub name: String,
    /// Scope of this function
    pub scope: Rc<Scope>,
    /// Attribute list
    pub attrib: Vec<FnAttrib>,
    /// Parameter list
    pub param: Vec<RefCell<SymbolRef>>,
    /// Return type
    pub ret: Type,
    /// Entrance block of this function
    pub ent: RefCell<BlockRef>,
    /// Set of exit blocks of this function
    pub exit: RefCell<Vec<BlockRef>>,
    /// Whether this function is in SSA form.
    /// This tag should only be set by verification and transformation function.
    pub ssa: SsaFlag,
}

impl PartialEq for Fn {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name && self.get_type() == other.get_type()
    }
}

impl Eq for Fn {}

impl Typed for Fn {
    fn get_type(&self) -> Type {
        Type::Fn {
            param: self.param.iter().map(|p| p.borrow().get_type()).collect(),
            ret: Box::new(self.ret.clone()),
        }
    }
}

pub type FnRef = ExtRc<Fn>;

impl Debug for FnRef {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        write!(f, "@{}", self.name)
    }
}

impl Fn {
    pub fn new(name: String, scope: Scope, attrib: Vec<FnAttrib>, param: Vec<RefCell<SymbolRef>>,
               ret: Type, ent: BasicBlock) -> Fn
    {
        Fn {
            name,
            scope: Rc::new(scope),
            attrib,
            param,
            ret,
            ent: RefCell::new(ExtRc::new(ent)),
            exit: RefCell::new(Default::default()),
            ssa: SsaFlag::new(),
        }
    }

    pub fn has_attrib(&self, attrib: FnAttrib) -> bool { self.attrib.contains(&attrib) }
}

#[derive(Eq, PartialEq, Copy, Clone, Debug)]
pub enum FnAttrib {
    Inline,
    NoInline,
    ReadOnly,
    Ssa
}

impl ToString for FnAttrib {
    fn to_string(&self) -> String { format!("{:?}", self).to_lowercase() }
}

impl FromStr for FnAttrib {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "inline" => Ok(FnAttrib::Inline),
            "noinline" => Ok(FnAttrib::NoInline),
            "readonly" => Ok(FnAttrib::ReadOnly),
            "ssa" => Ok(FnAttrib::Ssa),
            _ => Err(())
        }
    }
}

#[derive(Eq)]
pub struct BasicBlock {
    /// Name of this basic block
    pub name: String,
    /// Linked list of all instructions in this block
    pub inst: RefCell<VecDeque<InstRef>>,
    /// Inside a function, the basic blocks form a control flow graph. For each basic block,
    /// it has predecessor and successor sets, depending on the control flow instructions in
    /// the block. `Vec` is actually used here because we want to keep the insertion order of
    /// blocks.
    /// Predecessor blocks
    pub pred: RefCell<Vec<BlockRef>>,
    /// Successor blocks
    pub succ: RefCell<Vec<BlockRef>>,
    /// Parent of this block in the dominator tree
    /// This and `child` is dependent on the structure of the CFG. They can only be modified by
    /// the method of `Func` and granted read-only access by the public method.
    parent: RefCell<Option<BlockRef>>,
    /// Children of this block in the dominator tree
    child: RefCell<Vec<BlockRef>>,
}

pub type BlockRef = ExtRc<BasicBlock>;

impl Debug for BlockRef {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        write!(f, "{}", self.name)
    }
}

impl PartialEq for BasicBlock {
    fn eq(&self, other: &Self) -> bool { self.name == other.name }
}

impl Ord for BasicBlock {
    fn cmp(&self, other: &Self) -> Ordering { self.name.cmp(&other.name) }
}

impl PartialOrd for BasicBlock {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.name.partial_cmp(&other.name)
    }
}

impl Default for BasicBlock {
    fn default() -> Self { BasicBlock::new("".to_string()) }
}

impl BasicBlock {
    pub fn new(name: String) -> BasicBlock {
        BasicBlock {
            name,
            inst: RefCell::new(VecDeque::new()),
            pred: RefCell::new(vec![]),
            succ: RefCell::new(vec![]),
            parent: RefCell::new(None),
            child: RefCell::new(Vec::new()),
        }
    }

    /// Get parent of this block in the dominator tree.
    pub fn parent(&self) -> Option<BlockRef> { self.parent.borrow().clone() }

    /// Get children of this block in the dominator tree.
    pub fn children(&self) -> Vec<BlockRef> { self.child.borrow().clone() }

    /// Whether this block is entrance of the function.
    /// This replies on the correct computation of dominator tree.
    pub fn is_entrance(&self) -> bool { self.parent.borrow().is_none() }

    /// A basic block is complete iff. it ends with control instructions.
    pub fn is_complete(&self) -> bool {
        match self.inst.borrow().back() {
            Some(back) => back.deref().is_ctrl(),
            None => false
        }
    }

    /// Visit each instruction in this block
    pub fn for_each<F>(&self, f: F) where F: FnMut(InstRef) {
        self.inst.borrow().iter().cloned().for_each(f)
    }

    /// Push instruction to the front of the instruction list.
    pub fn push_front(&self, ins: InstRef) {
        self.inst.borrow_mut().push_front(ins)
    }

    /// Push instruction to the back of the instruction list.
    pub fn push_back(&self, ins: InstRef) {
        self.inst.borrow_mut().push_back(ins)
    }

    /// Get first instruction of this block
    pub fn head(&self) -> InstRef {
        self.inst.borrow().front().unwrap().clone()
    }

    /// Get last instruction of this block
    pub fn tail(&self) -> InstRef {
        self.inst.borrow().back().unwrap().clone()
    }

    /// Possibly get the instruction before given one
    pub fn before(&self, instr: &InstRef) -> Option<InstRef> {
        self.inst.borrow().iter().position(|i| i == instr)
            .and_then(|idx| self.inst.borrow().get(idx - 1).cloned())
    }

    /// Possibly get the instruction after given one
    pub fn after(&self, instr: &InstRef) -> Option<InstRef> {
        self.inst.borrow().iter().position(|i| i == instr)
            .and_then(|idx| self.inst.borrow().get(idx + 1).cloned())
    }

    /// If the tail of the instruction list is a control flow instruction, insert `ins` before
    /// it. Otherwise, push to the back of the list.
    pub fn insert_before_ctrl(&self, instr: InstRef) {
        if self.is_complete() {
            let idx = self.inst.borrow().len() - 1;
            self.inst.borrow_mut().insert(idx, instr)
        } else {
            self.push_back(instr)
        }
    }
}

impl BlockRef {
    /// Add a directed edge from this block to another.
    /// This method add `to` to the successor set of this block and add this block to the
    /// predecessor set of `to` block. It also modifies target of jump and branch instruction.
    pub fn connect(&self, to: BlockRef) {
        // Modify predecessor and successor list
        if to.pred.borrow().iter().find(|b| *b == self).is_none() {
            to.pred.borrow_mut().push(self.clone())
        }
        if self.succ.borrow().iter().find(|b| *b == &to).is_none() {
            self.succ.borrow_mut().push(to.clone())
        }
    }

    /// Remove a directed edge from this block to another.
    /// If there was an edge before, this is the inverse operation of `connect`. Otherwise,
    /// nothing will be actually done.
    pub fn disconnect(&self, to: &BlockRef) {
        let pos = to.pred.borrow().iter().position(|b| b == self);
        pos.map(|i| to.pred.borrow_mut().remove(i));
        let pos = self.succ.borrow().iter().position(|b| b == to);
        pos.map(|i| self.succ.borrow_mut().remove(i));
    }

    /// Switch an edge from a block to another
    /// This method modifies the predecessor and successors list, and alters target in control flow
    /// instructions.
    pub fn switch_to(&self, from: &BlockRef, to: BlockRef) {
        // Modify edges
        self.disconnect(from);
        self.connect(to.clone());

        // Modify target in control flow instructions
        match self.inst.borrow().back().unwrap().as_ref() {
            Inst::Jmp { tgt } => { tgt.replace(to.clone()); }
            Inst::Br { cond: _, tr, fls } => {
                if tr.borrow().deref() == from { tr.replace(to.clone()); }
                if fls.borrow().deref() == from { fls.replace(to.clone()); }
            }
            _ => {}
        }
    }

    /// Decide if this block dominates the given block.
    /// This method has logarithm time complexity. Though a linear time algorithm is possible,
    /// it requires keeping extra data in the block structure.
    pub fn dominates(&self, other: &BlockRef) -> bool {
        let mut cur = Some(other.clone());
        loop {
            match cur {
                Some(block) if *self == block => return true,
                None => return false,
                _ => cur = cur.unwrap().parent.borrow().clone()
            }
        }
    }

    /// Decide if this block strictly dominates the given block.
    pub fn strict_dom(&self, other: &BlockRef) -> bool {
        self.dominates(other) && self != other
    }
}

/// Generate block that has unique name in a function.
pub struct BlockGen {
    name: HashSet<String>,
    pre: String,
    count: usize,
}

impl BlockGen {
    pub fn new(func: &Fn, pre: &str) -> BlockGen {
        let mut name = HashSet::new();
        func.iter_dom().for_each(|block| { name.insert(block.name.clone()); });
        BlockGen {
            name,
            pre: pre.to_string(),
            count: 0,
        }
    }

    /// Generate a new block with fixed name format.
    pub fn gen(&mut self) -> BlockRef {
        loop {
            let name = format!("{}{}", self.pre, self.count);
            self.count += 1;
            if self.name.contains(&name) { continue; }
            return ExtRc::new(BasicBlock::new(name));
        }
    }

    /// Generate a new block based on the name of a given block
    pub fn rename(&mut self, blk: &BlockRef) -> BlockRef {
        let pre = blk.name.as_str().split('_').collect::<Vec<&str>>()[0];
        let mut i = 0usize;
        loop {
            let name = format!("{}_{}", pre, i);
            i += 1;
            if self.name.contains(&name) { continue; }
            self.name.insert(name.clone());
            return ExtRc::new(BasicBlock::new(name));
        }
    }
}

impl Fn {
    /// Split critical edge in the CFG. A critical edge is an CFG edge that whose predecessor has
    /// several successors, and whose successor has several predecessors.
    pub fn split_edge(&self) {
        let mut blk_gen = BlockGen::new(self, "B");
        self.iter_dom().for_each(|ref block| {
            // Decide whether there are any critical edges
            if block.succ.borrow().len() <= 1 { return; }
            let to_split: Vec<_> = block.succ.borrow().iter().cloned().filter(|succ| {
                succ.pred.borrow().len() > 1
            }).collect();

            // Split edges
            to_split.iter().for_each(|succ| {
                // Reconnect edges
                let mid = blk_gen.gen();
                mid.push_back(ExtRc::new(Inst::Jmp {
                    tgt: RefCell::new(succ.clone())
                }));
                mid.connect(succ.clone());
                block.switch_to(&succ, mid.clone());

                // Replace phi source in the split successor
                succ.inst.borrow_mut().iter_mut().for_each(|instr| {
                    if let Inst::Phi { src, dst } = instr.as_ref().clone() {
                        let mut src = src.clone();
                        src.iter_mut().filter(|(pred, _)| pred.borrow().deref() == block)
                            .for_each(|(pred, _)| *pred = RefCell::new(mid.clone()));
                        *instr = ExtRc::new(Inst::Phi { src, dst })
                    }
                })
            })
        });
        self.build_dom()
    }

    /// Remove unreachable blocks in this function. This is necessary for algorithms that rely
    /// on predecessors of blocks. This procedure will rebuild phi instructions in blocks.
    pub fn remove_unreachable(&self) {
        // Mark all reachable blocks
        let mut marked = HashSet::new();
        self.dfs().for_each(|block| { marked.insert(block); });

        // Sweep unmarked blocks in predecessors
        self.dfs().for_each(|block| {
            let pred_list: Vec<BlockRef> = block.pred.borrow().clone();
            pred_list.iter().for_each(|pred| {
                // Disconnect this predecessor
                if marked.contains(pred) { return; }
                pred.disconnect(&block);
            });

            // Rebuild phi instruction of this block
            block.inst.borrow_mut().iter_mut().for_each(|instr| {
                if let Inst::Phi { src, dst } = instr.as_ref() {
                    let prev_src = src.clone();
                    let new_src: Vec<_> = block.pred.borrow().iter().map(|pred| {
                        prev_src.iter().find(|(p, _)| p.borrow().deref() == pred).unwrap().clone()
                    }).collect();
                    *instr = ExtRc::new(Inst::Phi {
                        src: new_src,
                        dst: dst.clone(),
                    })
                }
            }); // end for each inst
        }) // end for each block
    }
}

impl Fn {
    /// Build dominator tree according to current CFG.
    /// This method is just a wrapper for the generic graph algorithm.
    pub fn build_dom(&self) {
        // Remove unreachable blocks
        self.remove_unreachable();
        // Clear previously computed dominator
        self.dfs().for_each(|block| {
            block.parent.replace(None);
            block.child.borrow_mut().clear();
        });
        // Run the Lengauer-Tarjan algorithm
        let result = DomBuilder::new(self.ent.borrow().clone()).build();
        for (block, dom) in result {
            block.parent.replace(Some(dom.clone()));
            dom.child.borrow_mut().push(block);
        }
    }
}

pub struct DomIter {
    stack: Vec<BlockRef>
}

impl Iterator for DomIter {
    type Item = BlockRef;

    fn next(&mut self) -> Option<Self::Item> {
        self.stack.pop().map(|blk| {
            self.stack.append(&mut blk.child.borrow().clone());
            blk
        })
    }
}

impl Fn {
    /// Iterate blocks in dominator tree order.
/// This provide a simpler interface for procedures that only want to visit each block.
    pub fn iter_dom(&self) -> DomIter {
        DomIter { stack: vec![self.ent.borrow().clone()] }
    }
}

/// Visitor trait of dominance tree
pub trait DomTreeListener {
    /// Called on the very beginning of visiting.
    fn on_begin(&mut self, func: &Fn);

    /// Called when the visiting is finished.
    fn on_end(&mut self, func: &Fn);

    /// Called when the subtree whose root is current block is entered, before visiting its
    /// children.
    fn on_enter(&mut self, block: BlockRef);

    /// Called when the offspring of this block have already been visited, and ready to leave
    /// this subtree.
    fn on_exit(&mut self, block: BlockRef);

    /// Called when a child subtree is entered.
    fn on_enter_child(&mut self, this: BlockRef, child: BlockRef);

    /// Called when leaving a child subtree
    fn on_exit_child(&mut self, this: BlockRef, child: BlockRef);
}

impl Fn {
    /// Walk the dominator tree of this function with given listener trait object
    pub fn walk_dom<L>(&self, listener: &mut L) where L: DomTreeListener {
        listener.on_begin(self);
        self.visit_block(self.ent.borrow().clone(), listener);
        listener.on_end(self);
    }

    fn visit_block<L>(&self, block: BlockRef, listener: &mut L) where L: DomTreeListener {
        listener.on_enter(block.clone());
        for child in block.child.borrow().iter() {
            listener.on_enter_child(block.clone(), child.clone());
            self.visit_block(child.clone(), listener);
            listener.on_exit_child(block.clone(), child.clone());
        }
        listener.on_exit(block);
    }
}

impl Fn {
    /// Compute dominance frontiers for all basic blocks.
    /// This should be called after dominator tree is built.
    pub fn compute_df(&self) -> HashMap<BlockRef, Vec<BlockRef>> {
        let mut builder = DfBuilder {
            stack: vec![],
            df: HashMap::new(),
        };
        self.walk_dom(&mut builder);
        builder.df
    }
}

/// Builder of dominance frontier
struct DfBuilder {
    stack: Vec<HashSet<BlockRef>>,
    df: HashMap<BlockRef, Vec<BlockRef>>,
}

impl DomTreeListener for DfBuilder {
    fn on_begin(&mut self, _: &Fn) {}

    fn on_end(&mut self, _: &Fn) {}

    fn on_enter(&mut self, block: BlockRef) {
        self.stack.push(HashSet::new());
        for succ in block.succ.borrow().iter() {
            if *succ.parent.borrow() != Some(block.clone()) {
                self.stack.last_mut().unwrap().insert(succ.clone());
            }
        }
    }

    fn on_exit(&mut self, block: BlockRef) {
        let df_set = Vec::from_iter(self.stack.pop().unwrap().into_iter());
        self.df.insert(block, df_set);
    }

    fn on_enter_child(&mut self, _: BlockRef, _: BlockRef) {}

    fn on_exit_child(&mut self, this: BlockRef, child: BlockRef) {
        for w in self.df.get(&child).unwrap() {
            if !this.dominates(w) || this == *w { // this does not strictly dominates w
                self.stack.last_mut().unwrap().insert(w.clone());
            }
        }
    }
}
