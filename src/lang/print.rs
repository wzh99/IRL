use std::cell::RefCell;
use std::io::{Error, Write};
use std::ops::Deref;
use std::rc::Rc;

use crate::lang::bb::BlockRef;
use crate::lang::func::Func;
use crate::lang::instr::{Instr, InstrRef};
use crate::lang::Program;
use crate::lang::val::{GlobalVar, Type, Typed, Value};

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
        // Print global variables
        for g in &pro.vars {
            self.print_global_var(g)?;
        }
        writeln!(self.writer, "")?;
        // Print functions
        for f in &pro.funcs {
            self.print_fn(f)?;
            writeln!(self.writer, "")?;
        }
        Ok(())
    }

    fn print_global_var(&mut self, g: &GlobalVar) -> Result<(), Error> {
        let mut s = format!("@{}", g.name);
        g.init.as_ref().map(|v| s += format!(" <- {}", v.to_string()).as_str());
        s += format!(": {}", g.ty.to_string()).as_str();
        writeln!(self.writer, "{};", s)
    }

    fn print_fn(&mut self, func: &Rc<Func>) -> Result<(), Error> {
        // Print signature
        let mut s = format!("fn @{}(", func.name);
        let params: Vec<String> = func.param.iter().map(|s| {
            format!("${}: {}", s.id(), s.get_type().to_string())
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
            Instr::Bin { op, fst, snd, dst } =>
                format!("{} <- {} {} {}, {}", fmt_val!(dst), op.to_string(), fmt_ty!(dst),
                        fmt_val!(fst), fmt_val!(snd)),
            Instr::Call { func, arg, dst } => {
                let mut s = format!("call {} @{}({})", func.ret.to_string(), func.name,
                                    self.fmt_opd_list(arg));
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
                format!("br {} ? %{} : %{}", fmt_val!(cond), tr.borrow().name, fls.borrow().name)
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
    use std::io::stdout;

    // Build program from source
    let mut file = File::open("test/parse.ir").unwrap();
    let lexer = Lexer::from_read(&mut file).unwrap();
    let parser = Parser::new(lexer);
    let tree = parser.parse().unwrap();
    let builder = Builder::new(tree);
    let pro = builder.build().unwrap();

    // Print program
    let mut output = stdout();
    let mut printer = Printer::new(&mut output);
    printer.print(&pro).unwrap();
}

