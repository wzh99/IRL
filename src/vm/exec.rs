use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::{Debug, Error, Formatter};
use std::ops::{Add, Deref, DerefMut};
use std::rc::Rc;

use crate::lang::func::Func;
use crate::lang::instr::Instr;
use crate::lang::Program;
use crate::lang::util::MutRc;
use crate::lang::value::{Const, GlobalVarRef, Symbol, SymbolRef, Type, Typed, Value};
use crate::vm::mem::{FrameRef, MemSpace, Reg, RegFile, Stack};
use crate::vm::stat::Counter;

pub struct Machine {
    global: HashMap<GlobalVarRef, Reg>,
    stack: Stack,
    count: Counter,
}

impl Machine {
    pub fn new() -> Self {
        Machine {
            global: Default::default(),
            stack: Stack::new(),
            count: Counter::new(),
        }
    }

    pub fn run(&mut self, pro: &Program) -> Result<VmRcd, RuntimeErr> {
        // Initialize global variable
        pro.vars.iter().for_each(|var| {
            let mut reg = Reg::from(&var.ty);
            var.init.map(|init| reg.set_const(init));
            self.global.insert(var.clone(), reg);
        });

        // Find program entrance and run that function
        match pro.func.iter().find(|func| &func.name == "main") {
            Some(main) => { self.call(main, vec![])?; }
            None => self.err(format!("cannot find program entrance"))?
        }

        // Collect machine statistics
        let mut global: Vec<_> = self.global.iter()
            .map(|(v, r)| (v.clone(), r.clone())).collect();
        global.sort_by_cached_key(|(v, _)| v.name.clone());
        let count = self.count;

        // Clear machine state for this program
        self.global.clear();
        self.stack.clear();
        self.count.reset();

        Ok(VmRcd { global, count })
    }

    fn call(&mut self, func: &Rc<Func>, arg: Vec<Reg>) -> Result<Option<Reg>, RuntimeErr> {
        // Pass arguments to parameters
        let ref mut file: RegFile = func.param.iter().zip(arg.into_iter())
            .map(|(p, r)| { (p.borrow().clone(), r) }).collect();

        // Push a new frame to stack
        if self.stack.len() >= 256 {
            self.err(format!("stack overflow"))?
        }
        self.stack.push_frame(func);
        let frame = self.stack.top();

        // Walk the CFG
        let mut next_blk = func.ent.borrow().clone();
        loop {
            // Assign values to phi destinations
            for phi in next_blk.instr.borrow().iter() {
                match phi.as_ref() {
                    Instr::Phi { src, dst } => {
                        let src = &src.iter().find(|(b, _)| b == &frame.borrow().block).unwrap().1;
                        let val = match src.borrow().deref() {
                            Value::Var(sym) => file[sym].clone(),
                            Value::Const(c) => Reg::Val(*c)
                        };
                        file.insert(dst.borrow().clone(), val);
                    }
                    _ => break
                }
            }

            // Transfer to the new block and execute the remaining instructions
            let cur_blk = next_blk.clone();
            frame.borrow_mut().block = Some(cur_blk.clone());
            for instr in cur_blk.instr.borrow().iter() {
                self.count.count(instr.as_ref());
                match instr.as_ref() {
                    Instr::Phi { src: _, dst: _ } => {}
                    Instr::Mov { src, dst } => {
                        let reg = self.reg_from_src(src, file);
                        self.reg_to_dst(reg, dst, file);
                    }
                    Instr::Un { op, opd, dst } => {
                        let opd = self.reg_from_src(opd, file).get_const();
                        let res = Reg::Val(op.eval(opd));
                        self.reg_to_dst(res, dst, file);
                    }
                    Instr::Bin { op, fst, snd, dst } => {
                        let fst = self.reg_from_src(fst, file).get_const();
                        let snd = self.reg_from_src(snd, file).get_const();
                        let res = Reg::Val(op.eval(fst, snd));
                        self.reg_to_dst(res, dst, file);
                    }
                    Instr::Call { func, arg, dst } => {
                        let arg: Vec<_> = arg.iter().map(|a| self.reg_from_src(a, file)).collect();
                        let res = self.call(func, arg)?;
                        dst.as_ref().map(|dst| self.reg_to_dst(res.unwrap(), dst, file));
                    }
                    Instr::Ret { val } => {
                        let res = val.as_ref().map(|val| self.reg_from_src(val, file));
                        self.stack.pop_frame();
                        return Ok(res);
                    }
                    Instr::Jmp { tgt } => {
                        next_blk = tgt.borrow().clone();
                        frame.borrow_mut().instr = 0;
                        break;
                    }
                    Instr::Br { cond, tr, fls } => {
                        let cond = self.reg_from_src(cond, file).get_const();
                        let cond = if let Const::I1(b) = cond { b } else { unreachable!() };
                        next_blk = if cond { tr.borrow().clone() } else { fls.borrow().clone() };
                        frame.borrow_mut().instr = 0;
                        break;
                    }
                    Instr::Alloc { dst } => {
                        let ptr = self.stack.alloc(dst.borrow().get_type().tgt_type().size());
                        self.reg_to_dst(ptr, dst, file);
                    }
                    Instr::New { dst, len } => self.exec_new(dst, len, file),
                    Instr::Ptr { base, off, ind, dst } =>
                        self.exec_ptr(base, off, ind, dst, file)?,
                    Instr::Ld { ptr, dst } => self.exec_ld(ptr, dst, file)?,
                    Instr::St { src, ptr } => self.exec_st(src, ptr, file)?
                }
                frame.borrow_mut().instr += 1;
            }
        }
    }

    fn exec_st(&mut self, src: &RefCell<Value>, ptr: &RefCell<Value>, file: &RegFile)
               -> Result<(), RuntimeErr>
    {
        let ptr_reg = self.reg_from_src(ptr, file);
        let src_ty = src.borrow().get_type();
        let src = self.reg_from_src(src, file);
        match ptr_reg {
            Reg::Ptr { base, off } => {
                let mem_end = off + src_ty.size();
                match base.as_ref() {
                    None => self.err(format!("dereference of null pointer"))?,
                    Some(MemSpace::Stack(addr)) => match self.stack.get_mem_mut(*addr) {
                        Some(mem) if mem_end <= mem.len() => Self::write_by_type(mem, off, src),
                        Some(_) => self.err(format!("memory access out of bound"))?,
                        None => self.err(format!("stack space does not exist"))?
                    }
                    Some(MemSpace::Heap(mem)) => {
                        if mem_end <= mem.borrow().len() {
                            Self::write_by_type(mem.borrow_mut().deref_mut(), off, src)
                        } else {
                            self.err(format!("memory access out of bound"))?
                        }
                    }
                }
            }
            Reg::Val(_) => unreachable!()
        }
        Ok(())
    }

    fn write_by_type(mem: &mut Vec<u8>, addr: usize, src: Reg) {
        match src {
            Reg::Val(Const::I1(c)) => Self::write(mem, addr, c),
            Reg::Val(Const::I8(c)) => Self::write(mem, addr, c),
            Reg::Val(Const::I16(c)) => Self::write(mem, addr, c),
            Reg::Val(Const::I32(c)) => Self::write(mem, addr, c),
            Reg::Val(Const::I64(c)) => Self::write(mem, addr, c),
            ptr if ptr.is_ptr() => Self::write(mem, addr, ptr),
            _ => unreachable!()
        }
    }

    fn write<T>(mem: &mut Vec<u8>, addr: usize, val: T) {
        let ptr = &mut mem[addr] as *mut u8 as *mut T;
        unsafe { *ptr = val }
    }

    fn exec_ld(&mut self, ptr: &RefCell<Value>, dst: &RefCell<SymbolRef>, file: &mut RegFile)
               -> Result<(), RuntimeErr>
    {
        let ptr_reg = self.reg_from_src(ptr, file);
        let ref dst_ty = dst.borrow().get_type();
        match ptr_reg {
            Reg::Ptr { base, off } => {
                let mem_end = off + dst_ty.size();
                match base.as_ref() {
                    None => self.err(format!("dereference of null pointer"))?,
                    Some(MemSpace::Stack(addr)) => match self.stack.get_mem(*addr) {
                        Some(mem) if mem_end <= mem.len() => {
                            let reg = Self::read_by_type(mem, off, dst_ty);
                            self.reg_to_dst(reg, dst, file);
                        }
                        Some(_) => self.err(format!("memory access out of bound"))?,
                        None => self.err(format!("stack space does not exist"))?
                    }
                    Some(MemSpace::Heap(mem)) => {
                        if mem_end <= mem.borrow().len() {
                            let reg = Self::read_by_type(mem.borrow().deref(), off, dst_ty);
                            self.reg_to_dst(reg, dst, file);
                        } else {
                            self.err(format!("memory access out of bound"))?
                        }
                    }
                }
            }
            Reg::Val(_) => unreachable!()
        }
        Ok(())
    }

    fn read_by_type(mem: &Vec<u8>, addr: usize, ty: &Type) -> Reg {
        match ty {
            Type::I(1) => Reg::Val(Const::I1(Self::read::<bool>(mem, addr))),
            Type::I(8) => Reg::Val(Const::I8(Self::read::<i8>(mem, addr))),
            Type::I(16) => Reg::Val(Const::I16(Self::read::<i16>(mem, addr))),
            Type::I(32) => Reg::Val(Const::I32(Self::read::<i32>(mem, addr))),
            Type::I(64) => Reg::Val(Const::I64(Self::read::<i64>(mem, addr))),
            Type::Ptr(_) => Self::read::<Reg>(mem, addr),
            _ => unreachable!()
        }
    }

    fn read<T: Clone>(mem: &Vec<u8>, addr: usize) -> T {
        let ptr = &mem[addr] as *const u8 as *const T;
        unsafe { (*ptr).clone() }
    }

    fn exec_new(&mut self, dst: &RefCell<SymbolRef>, len: &Option<RefCell<Value>>,
                file: &mut RegFile)
    {
        // Compute size of heap space to be dynamically allocated
        let mut size = dst.borrow().get_type().tgt_type().size();
        len.as_ref().map(|len| {
            let len = self.reg_from_src(len, file).get_const();
            let len = if let Const::I64(c) = len { c } else { unreachable!() };
            size *= len as usize;
        });

        // Allocate heap space
        // This space will be handled by the mutable reference counter. No garbage collector is
        // needed in this VM.
        let space = MutRc::new(vec![0; size]);
        let ptr = Reg::Ptr {
            base: Some(MemSpace::Heap(space)),
            off: 0,
        };
        self.reg_to_dst(ptr, dst, file);
    }

    fn exec_ptr(&mut self, base: &RefCell<Value>, off: &Option<RefCell<Value>>,
                ind: &Vec<RefCell<Value>>, dst: &RefCell<SymbolRef>, file: &mut RegFile)
                -> Result<(), RuntimeErr>
    {
        // Compute pointer offset outside target value
        let mut tgt_ty = base.borrow().get_type().tgt_type();
        let mut size_off = 0;
        off.as_ref().map(|off| {
            let off = self.reg_from_src(off, file).get_const();
            let off = if let Const::I64(c) = off { c } else { unreachable!() };
            size_off += off as usize * tgt_ty.size();
        });

        // Compute element offset inside aggregate
        for idx in ind {
            let idx = self.reg_from_src(idx, file).get_const();
            let idx = if let Const::I64(c) = idx { c as usize } else { unreachable!() };
            match tgt_ty.clone() {
                Type::Array { elem, len } => {
                    if idx >= len {
                        self.err(format!("index {} out of bound {}", idx, len))?
                    }
                    size_off += elem.size() * idx;
                    tgt_ty = elem.deref().clone();
                }
                Type::Struct { field } => {
                    // indices into struct are checked at compile time, impossible to be out of
                    // bound
                    size_off += field[..idx].iter().map(|f| f.size()).fold(0, Add::add);
                    tgt_ty = field[idx].clone();
                }
                _ => unreachable!()
            }
        }

        // Store the new address
        let mut addr = self.reg_from_src(base, file);
        addr.set_off(addr.get_off() + size_off);
        self.reg_to_dst(addr, dst, file);
        Ok(())
    }

    fn reg_from_src(&mut self, src: &RefCell<Value>, file: &RegFile) -> Reg {
        match src.borrow().deref() {
            Value::Var(sym) if sym.is_local_var() => file[sym].clone(),
            Value::Var(sym) => if let Symbol::Global(g) = sym.as_ref() {
                self.global[g].clone()
            } else { unreachable!() }
            Value::Const(c) => Reg::Val(*c)
        }
    }

    fn reg_to_dst(&mut self, reg: Reg, dst: &RefCell<SymbolRef>, file: &mut RegFile) {
        match dst.borrow().as_ref() {
            sym if sym.is_local_var() => { file.insert(dst.borrow().clone(), reg); }
            Symbol::Global(g) => { *self.global.get_mut(g).unwrap() = reg; }
            _ => unreachable!()
        }
    }

    fn err(&self, msg: String) -> Result<(), RuntimeErr> {
        Err(RuntimeErr { msg, frame: self.stack.unwind() })
    }
}

/// Record of VM when executing this program
#[derive(Debug)]
pub struct VmRcd {
    pub global: Vec<(GlobalVarRef, Reg)>,
    pub count: Counter,
}

pub struct RuntimeErr {
    msg: String,
    frame: Vec<FrameRef>,
}

impl Debug for RuntimeErr {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        writeln!(f, "runtime error: {}", self.msg)?;
        writeln!(f, "call stack: ")?;
        for (i, frame) in self.frame.iter().rev().enumerate() {
            writeln!(f, "{} @{}, %{:?}, #{}", i, frame.borrow().func.name,
                     frame.borrow().block.as_ref().unwrap(), frame.borrow().instr)?;
        }
        Ok(())
    }
}

#[test]
fn test_exec() {
    use crate::compile::lex::Lexer;
    use crate::compile::parse::Parser;
    use crate::compile::build::Builder;
    use crate::vm::exec::Machine;
    use std::fs::File;
    use std::convert::TryFrom;
    use std::io::Read;

    let mut file = File::open("test/example.ir").unwrap();
    let lexer = Lexer::try_from(&mut file as &mut dyn Read).unwrap();
    let parser = Parser::new(lexer);
    let tree = parser.parse().unwrap();
    let builder = Builder::new(tree);
    let mut pro = builder.build().unwrap();

    let mut mach = Machine::new();
    let rcd = mach.run(&mut pro).unwrap();
    println!("{:?}", rcd);
}
