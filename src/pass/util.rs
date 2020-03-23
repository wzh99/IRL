use std::cell::RefCell;
use std::collections::HashSet;
use std::fmt::{Debug, Error, Formatter};
use std::ops::Deref;

use crate::lang::func::{BlockRef, Fn, FnRef};
use crate::lang::inst::{Inst, InstRef};
use crate::lang::Program;
use crate::lang::util::{ExtRc, MutRc};
use crate::lang::value::{Const, SymbolGen, Type, Typed, Value};
use crate::pass::{FnPass, Pass};

#[derive(Clone, Debug)]
pub struct LoopNode {
    /// Header of this loop
    pub header: BlockRef,
    /// Blocks in first level of this loop, excluding header and ones in nested loops
    pub level: Vec<BlockRef>,
    /// Nested loops of this loop
    pub nested: Vec<LoopNodeRef>,
}

impl LoopNode {
    /// Return blocks in first level of this loop, including header.
    pub fn level_blocks(&self) -> Vec<BlockRef> {
        let mut blk = self.level.clone();
        blk.push(self.header.clone());
        blk
    }

    /// Return blocks in all levels of this loop, including ones in nested loops.
    pub fn all_blocks(&self) -> Vec<BlockRef> {
        let mut blk = self.level_blocks();
        self.nested.iter().for_each(|c| blk.append(&mut c.borrow().all_blocks()));
        blk
    }
}

pub type LoopNodeRef = MutRc<LoopNode>;

impl Debug for LoopNodeRef {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> { self.borrow().header.fmt(f) }
}

impl Fn {
    /// Detect all loops in the function and return as loop-nest forest
    pub fn analyze_loop(&self) -> Vec<LoopNodeRef> {
        // Find all natural loops
        let mut trees = vec![];
        self.iter_dom().for_each(|ref blk| {
            blk.succ.borrow().iter()
                .filter(|succ| succ.dominates(blk))
                .for_each(|header| trees.push(Self::create_natural(blk, header)));
        });

        // Combine natural loops to create loop-nest tree
        let mut i = 0;
        while i < trees.len() {
            // Look for node with the same header
            let node = trees[i].clone();
            trees.iter()
                .position(|n| *n != node && n.borrow().header == node.borrow().header)
                .map(|pos| {
                    // Merge two nodes
                    let other = trees.remove(pos);
                    node.borrow_mut().level.append(&mut other.borrow_mut().level);
                    node.borrow_mut().nested.append(&mut other.borrow_mut().nested);
                });

            // Look for node that could be parent of this node
            trees.iter()
                .position(|n| n.borrow().level.contains(&node.borrow().header))
                .map(|pos| {
                    // Add this to nested list of that node
                    let parent = trees[pos].clone();
                    parent.borrow_mut().nested.push(node.clone());
                    let all_blk = node.borrow().all_blocks();
                    parent.borrow_mut().level.retain(|b| !all_blk.contains(b));

                    // Modify tree list according to relative position of nodes in the list
                    if i < pos { // child is in front of parent
                        trees.remove(pos);
                        trees[i] = parent; // move parent to position of child
                        i += 1; // move to next node
                    } else { // child is at back of parent
                        trees.remove(i); // clear this child
                        // no need to increment i because it already points to next node
                    }
                }).or_else(|| {
                i += 1; // no parent found, move to next node
                Some(())
            });
        }

        // trees.iter().for_each(|n| println!("{:?}", n.borrow().deref()));
        trees
    }

    /// Create natural loop of a back edge
    fn create_natural(blk: &BlockRef, header: &BlockRef) -> LoopNodeRef {
        // Perform DFS on reversed CFG with header block as boundary
        let mut visited = HashSet::new();
        let mut stack = vec![blk.clone()];
        visited.insert(header.clone());
        loop {
            match stack.pop() {
                Some(v) => {
                    visited.insert(v.clone());
                    stack.append(&mut v.pred.borrow().iter()
                        .filter(|blk| !visited.contains(blk)).cloned().collect()
                    )
                }
                None => break,
            }
        }

        // Collect all visited blocks, except header
        MutRc::new(LoopNode {
            header: header.clone(),
            level: visited.iter().cloned().filter(|blk| blk != header).collect(),
            nested: vec![],
        })
    }
}

/// Pointer operation expansion
/// This transformation could provide opportunities for later optimizations.
pub struct PtrExp {}

impl PtrExp {
    pub fn new() -> PtrExp { PtrExp {} }
}

impl Pass for PtrExp {
    fn run(&mut self, pro: &mut Program) { FnPass::run(self, pro) }
}

impl FnPass for PtrExp {
    fn run_on_fn(&mut self, func: &FnRef) {
        func.iter_dom().for_each(|block| {
            // Find pointer instruction with indices
            let ptr_list: Vec<InstRef> = block.inst.borrow().iter().filter(|instr| {
                if let Inst::Ptr { base: _, off: _, ind, dst: _ } = instr.as_ref() {
                    !ind.is_empty()
                } else { false }
            }).cloned().collect();

            // Expand pointer operation
            let mut gen = SymbolGen::new(func.scope.clone(), "t");
            ptr_list.into_iter().for_each(|ref ptr| {
                if let Inst::Ptr { base, off, ind, dst } = ptr.as_ref() {
                    // Extract the base pointer
                    let mut expand = vec![];
                    let mut cur_ptr = gen.gen(&base.borrow().get_type());
                    let base_instr = ExtRc::new(Inst::Ptr {
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
                                let head_instr = ExtRc::new(Inst::Ptr {
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
                                let elem_instr = ExtRc::new(Inst::Ptr {
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
                                let elem_instr = ExtRc::new(Inst::Ptr {
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
                    let pos = block.inst.borrow().iter().position(|instr| instr == ptr).unwrap();
                    block.inst.borrow_mut().remove(pos);
                    expand.into_iter().rev().for_each(|instr| {
                        block.inst.borrow_mut().insert(pos, instr)
                    })
                } else { unreachable!() }
            })
        })
    }
}
