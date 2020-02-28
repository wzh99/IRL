use std::collections::HashMap;
use std::hash::{Hash, Hasher};

use crate::lang::func::Func;
use crate::lang::instr::{BinOp, UnOp};
use crate::lang::Program;
use crate::lang::value::{Const, SymbolRef, Type};
use crate::opt::{FnPass, Pass};

#[derive(Eq, PartialEq, Hash, Clone, Debug)]
enum Expr {
    /// Compile time constants
    Const(Const),
    /// Unary operations
    Unary(UnExpr),
    /// Binary operations
    Binary(BinExpr),
    /// Temporaries that store values
    Temp(SymbolRef),
    /// Any operation not in consideration for this optimization, including global variables and
    /// results of neither unary or binary operations. Pointer arithmetic is also in this category,
    /// since its has arbitrary operands.
    Result(SymbolRef),
}

#[derive(Eq, Clone, Debug)]
struct UnExpr {
    op: UnOp,
    ty: Type,
    opd: usize, // value number
}

impl PartialEq for UnExpr {
    fn eq(&self, other: &Self) -> bool {
        self.op == other.op && self.opd == other.opd
    }
}

impl Hash for UnExpr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.op.hash(state);
        self.opd.hash(state);
    }
}

#[derive(Eq, Clone, Debug)]
struct BinExpr {
    op: BinOp,
    ty: Type,
    // type of operands, not of result
    fst: usize,
    snd: usize,
}

impl PartialEq for BinExpr {
    fn eq(&self, other: &Self) -> bool {
        self.op == other.op && self.fst == other.fst && self.snd == other.snd
    }
}

impl Hash for BinExpr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.op.hash(state);
        self.fst.hash(state);
        self.snd.hash(state);
    }
}

struct ValueTable {
    /// Expression list for each numbered value
    tab: Vec<Vec<Expr>>,
    /// Map expressions to their corresponding value number.
    /// Note that instances of `Expr::Result` should not be keys of this map, because it could
    /// correspond to several values.
    num: HashMap<Expr, usize>,
    /// Record next possible available value number.
    /// Since value numbers produced by GVN implementation are not continuous, it may lead to
    /// inefficient use of value table. This field help to make sure all the numbers are fully used
    /// before allocating larger numbers. It is not equal to `tab.len()` until all the current
    /// value numbers are fully used.
    next: usize,
}

impl ValueTable {
    fn new() -> ValueTable {
        ValueTable {
            tab: vec![],
            num: Default::default(),
            next: 0,
        }
    }

    /// Add expressions that are already known to have a number.
    fn add_num(&mut self, expr: Expr, num: usize) {
        self.extend(num);
        self.tab[num].push(expr.clone());
        self.map(expr, num);
    }

    /// Add expressions that do not have a number. Return allocated number for this expression.
    fn add_not_num(&mut self, expr: Expr) -> usize {
        // empty list, or not allocated number
        while self.tab.get(self.next).is_some() && !self.tab[self.next].is_empty() {
            self.next += 1; // this list has something, try next number
        }
        let num = self.next;
        self.extend(num);
        self.tab[self.next].push(expr.clone());
        self.map(expr, num);
        num
    }

    /// Map `expr` to given number, as long as it is not `Expr::Result`
    fn map(&mut self, expr: Expr, num: usize) {
        match expr {
            Expr::Result(_) => {} // mapping is not unique
            expr => { self.num.insert(expr, num); }
        }
    }

    /// Find value number for given expression
    fn find(&mut self, expr: &Expr) -> Option<usize> {
        self.get_num(expr).or_else(|| match expr.clone() {
            // Use operator commutativity to have another try
            Expr::Binary(BinExpr { op, ty, fst, snd }) if op.is_comm() => self.get_num(
                &Expr::Binary(BinExpr { op, ty, fst: snd, snd: fst })
            ),
            _ => None
        }).or_else(|| match expr.clone() {
            // Try to re-associate binary operations
            Expr::Binary(BinExpr { op, ty, fst, snd }) if op.is_assoc() =>
                match expr.clone() {
                    // Try processing first value
                    Expr::Binary(BinExpr { op, ty, fst, snd }) if self.find_bin(fst).is_some() =>
                        self.find_bin(fst).and_then(|fst| {
                            match fst {
                                BinExpr { op: opl, ty, fst: l_fst, snd: l_snd } if op == opl =>
                                    self.get_num(&Expr::Binary(BinExpr {
                                        op,
                                        ty: ty.clone(),
                                        fst: l_snd,
                                        snd,
                                    })).and_then(|snd| self.get_num(&Expr::Binary(BinExpr {
                                        op,
                                        ty,
                                        fst: l_fst,
                                        snd,
                                    }))),
                                _ => None
                            }
                        }),
                    // Try processing second value
                    Expr::Binary(BinExpr { op, ty, fst, snd }) if self.find_bin(snd).is_some() =>
                        self.find_bin(snd).and_then(|snd| {
                            match snd {
                                BinExpr { op: opr, ty, fst: r_fst, snd: r_snd } if op == opr => {
                                    self.get_num(&Expr::Binary(BinExpr {
                                        op,
                                        ty: ty.clone(),
                                        fst,
                                        snd: r_fst,
                                    })).and_then(|fst| self.get_num(&Expr::Binary(BinExpr {
                                        op,
                                        ty,
                                        fst,
                                        snd: r_snd,
                                    })))
                                }
                                _ => None
                            }
                        }),
                    _ => None
                },
            _ => None,
        })
    }

    fn get_num(&mut self, expr: &Expr) -> Option<usize> {
        self.num.get(expr).copied().or_else(|| match expr.clone() {
            Expr::Binary(BinExpr { op, ref ty, fst, snd }) => {
                let fst_cn = self.find_const(fst);
                let snd_cn = self.find_const(snd);
                let zero = Const::zero(ty);
                let one = Const::one(ty);
                match op {
                    // 0 + x = x + 0 = x
                    BinOp::Add => match (fst_cn, snd_cn) {
                        (Some(l), _) if l == zero => Some(snd),
                        (_, Some(r)) if r == zero => Some(fst),
                        _ => None
                    }
                    // x - x = 0
                    BinOp::Sub if fst == snd =>
                        Some(self.find_or_add(&Expr::Const(zero.clone()))),
                    // 0 * x = x * 0 = 0, 1 * x = x * 1 = x
                    BinOp::Mul => match (fst_cn, snd_cn) {
                        (Some(l), _) if l == zero =>
                            Some(self.find_or_add(&Expr::Const(zero.clone()))),
                        (_, Some(r)) if r == zero =>
                            Some(self.find_or_add(&Expr::Const(zero.clone()))),
                        (Some(l), _) if l == one => Some(snd),
                        (_, Some(r)) if r == one => Some(fst),
                        _ => None
                    }
                    // x << 0 = x, x >> 0 = x
                    BinOp::Shl | BinOp::Shr => match snd_cn {
                        r if r == Some(zero) => Some(fst),
                        _ => None
                    }
                    _ => None
                }
            }
            _ => None
        })
    }

    fn find_const(&self, num: usize) -> Option<Const> {
        self.tab.get(num).and_then(|list| list.iter().find(|expr| match expr {
            Expr::Const(c) => true,
            _ => false
        }).and_then(|expr| match expr {
            Expr::Const(c) => Some(c.clone()),
            _ => unreachable!()
        }))
    }

    /// Find binary expression in the value list of given value number
    fn find_bin(&self, num: usize) -> Option<BinExpr> {
        self.tab.get(num).and_then(|list| list.iter().find(|expr| match expr {
            Expr::Binary(bin) => true,
            _ => false
        }).and_then(|expr| match expr {
            Expr::Binary(bin) => Some(bin.clone()),
            _ => unreachable!()
        }))
    }

    /// Possibly find indices for expression or create new number for it
    fn find_or_add(&mut self, expr: &Expr) -> usize {
        self.find(expr).unwrap_or_else(|| self.add_not_num(expr.clone()))
    }

    /// Extend value table so that it is long enough to have an element indexed by `to`.
    fn extend(&mut self, to: usize) {
        if self.tab.len() <= to {
            let more = to - self.tab.len() + 1;
            self.tab.append(&mut vec![vec![]; more]);
        }
    }
}

/// Implement GVN-PRE proposed by Thomas and Antony.
/// See [https://www.cs.purdue.edu/homes/hosking/papers/cc04.pdf].
pub struct PreOpt {}

impl Pass for PreOpt {
    fn opt(&mut self, pro: &mut Program) { FnPass::opt(self, pro) }
}

impl FnPass for PreOpt {
    fn opt_fn(&mut self, _func: &Func) {
        unimplemented!()
    }
}
