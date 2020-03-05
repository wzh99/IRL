use std::cell::RefCell;
use std::io::{Error, Write};
use std::ops::Deref;

use crate::lang::func::{BlockRef, Func};
use crate::lang::instr::{Instr, InstrRef};
use crate::lang::Program;
use crate::lang::value::{GlobalVar, Symbol, Type, Typed, Value};

pub struct Printer<'a> {
    writer: &'a mut dyn Write,
}

macro_rules! fmt_val { ($v:ident) => {$v.borrow().to_string()}; }
macro_rules! fmt_ty { ($v:ident) => {$v.borrow().get_type().to_string()}; }

impl Printer<'_> {
    pub fn new(writer: &mut dyn Write) -> Printer {
        Printer { writer }
    }

    pub fn print(&mut self, pro: &Program) -> Result<(), Error> {
        // Print type aliases
        self.print_type_alias(pro)?;
        // Print global variables
        for g in &pro.vars {
            self.print_global_var(g)?;
        }
        writeln!(self.writer, "")?;
        // Print functions
        for f in &pro.func {
            self.print_fn(f.deref())?;
            writeln!(self.writer, "")?;
        }
        Ok(())
    }

    fn print_type_alias(&mut self, pro: &Program) -> Result<(), Error> {
        for sym in pro.global.collect() {
            match sym.deref() {
                Symbol::Type { name, ty } => {
                    writeln!(self.writer, "type @{} = {}", name, ty.borrow().to_string())?;
                }
                _ => continue,
            }
        }
        writeln!(self.writer, "")?;
        Ok(())
    }

    fn print_global_var(&mut self, g: &GlobalVar) -> Result<(), Error> {
        let mut s = format!("@{}: {}", g.name, g.ty.to_string());
        g.init.as_ref().map(|v| s += format!(" <- {}", v.to_string()).as_str());
        writeln!(self.writer, "{};", s)
    }

    pub fn print_fn(&mut self, func: &Func) -> Result<(), Error> {
        // Print signature
        let mut s = format!("fn @{}(", func.name);
        let params: Vec<String> = func.param.iter().map(|s| {
            format!("${}: {}", s.borrow().id(), s.borrow().get_type().to_string())
        }).collect();
        s += &params.join(", ");
        s += ")";
        if let Type::Void = func.ret {} else {
            s += format!(" -> {}", func.ret.to_string()).as_str()
        }
        s += " {";
        writeln!(self.writer, "{}", s)?;

        // Print blocks
        for ref b in func.bfs() {
            self.print_block(b)?;
        }

        writeln!(self.writer, "{}", '}')?;
        Ok(())
    }

    fn print_block(&mut self, block: &BlockRef) -> Result<(), Error> {
        writeln!(self.writer, "%{}:", block.name)?;
        for instr in block.instr.borrow().iter() {
            self.print_instr(instr)?;
        }
        Ok(())
    }

    fn print_instr(&mut self, instr: &InstrRef) -> Result<(), Error> {
        let s = match instr.deref() {
            Instr::Mov { src, dst } =>
                format!("{} <- mov {} {}", fmt_val!(dst), fmt_ty!(dst), fmt_val!(src)),
            Instr::Un { op, opd, dst } =>
                format!("{} <- {} {} {}", fmt_val!(dst), op.to_string(), fmt_ty!(dst),
                        fmt_val!(opd)),
            Instr::Bin { op, fst, snd, dst } => {
                let opd_ty = if op.is_cmp() {
                    fst.borrow().get_type()
                } else {
                    dst.borrow().get_type()
                };
                format!("{} <- {} {} {}, {}", fmt_val!(dst), op.to_string(), opd_ty.to_string(),
                        fmt_val!(fst), fmt_val!(snd))
            }
            Instr::Call { func, arg, dst } => {
                let ty = if let Type::Void = func.ret { "".to_string() } else {
                    func.ret.to_string() + " "
                };
                let mut s = format!("call {}@{}({})", ty, func.name, self.fmt_opd_list(arg));
                dst.as_ref().map(|dst| s = format!("{} <- ", fmt_val!(dst)) + s.as_str());
                s
            }
            Instr::Phi { src, dst } =>
                format!("{} <- phi {} {}", fmt_val!(dst), fmt_ty!(dst), self.fmt_phi_list(src)),
            Instr::Ret { val } => {
                let mut s = "ret".to_string();
                val.as_ref().map(|v| s += format!(" {}", fmt_val!(v)).as_str());
                s
            }
            Instr::Jmp { tgt } => format!("jmp %{}", tgt.borrow().name),
            Instr::Br { cond, tr, fls } =>
                format!("br {} ? %{} : %{}", fmt_val!(cond), tr.borrow().name, fls.borrow().name),
            Instr::Alloc { dst } => {
                let dst_ty = dst.borrow().get_type();
                let elem_ty = if let Type::Ptr(elem) = dst_ty {
                    elem.deref().clone()
                } else { unreachable!() };
                format!("{} <- alloc {}", fmt_val!(dst), elem_ty.to_string())
            }
            Instr::New { dst } => {
                let dst_ty = dst.borrow().get_type();
                let elem_ty = if let Type::Ptr(elem) = dst_ty {
                    elem.deref().clone()
                } else { unreachable!() };
                format!("{} <- new {}", fmt_val!(dst), elem_ty.to_string())
            }
            Instr::Ptr { base, off, ind, dst } => {
                let mut s = format!("{} <- ptr {} {}", fmt_val!(dst), fmt_ty!(dst),
                                    fmt_val!(base));
                off.as_ref().map(|off| s += format!(", {}", fmt_val!(off)).as_str());
                if !ind.is_empty() {
                    s += format!(" [{}]", self.fmt_opd_list(ind)).as_str()
                }
                s
            }
            Instr::Ld { ptr, dst } =>
                format!("{} <- ld {} {}", fmt_val!(dst), fmt_ty!(dst), fmt_val!(ptr)),
            Instr::St { src, ptr } =>
                format!("st {} {} -> {}", fmt_ty!(src), fmt_val!(src), fmt_val!(ptr))
        };

        writeln!(self.writer, "    {};", s)?;
        Ok(())
    }

    fn fmt_opd_list(&self, opd: &Vec<RefCell<Value>>) -> String {
        let vec: Vec<String> = opd.iter().map(|v| v.borrow().to_string()).collect();
        vec.join(", ")
    }

    fn fmt_phi_list(&self, list: &Vec<(Option<BlockRef>, RefCell<Value>)>) -> String {
        let vec: Vec<String> = list.iter().map(|(b, v)| {
            let mut s = fmt_val!(v);
            b.as_ref().map(|b| s = format!("%{}: ", b.name) + &s);
            format!("[{}]", s)
        }).collect();
        vec.join(" ")
    }
}

#[test]
fn test_print() {
    use crate::compile::build::Builder;
    use crate::compile::lex::Lexer;
    use crate::compile::parse::Parser;
    use std::fs::File;
    use std::io::{Read, stdout};
    use std::convert::TryFrom;

    // Build program from source
    let mut file = File::open("test/example.ir").unwrap();
    let lexer = Lexer::try_from(&mut file as &mut dyn Read).unwrap();
    let parser = Parser::new(lexer);
    let tree = parser.parse().unwrap();
    let builder = Builder::new(tree);
    let pro = builder.build().unwrap();

    // Print program
    let mut output = stdout();
    let mut printer = Printer::new(&mut output);
    printer.print(&pro).unwrap();
}

