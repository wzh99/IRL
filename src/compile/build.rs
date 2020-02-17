use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::ops::Deref;
use std::rc::Rc;
use std::str::FromStr;

use crate::compile::{CompileErr, Loc};
use crate::compile::syntax::{Term, Token};
use crate::compile::syntax::Term::PhiOpd;
use crate::lang::{ExtRc, Program};
use crate::lang::bb::{BasicBlock, BlockRef};
use crate::lang::instr::Instr;
use crate::lang::val::{Const, Func, GlobalVar, Scope, Symbol, SymbolRef, Type, Typed, Value};

pub struct Builder {
    root: Term,
}

struct Context {
    global: Rc<Scope>,
    func: Rc<Func>,
    labels: HashMap<String, BlockRef>,
}

impl Builder {
    pub fn new(root: Term) -> Builder { Builder { root } }

    /// Build program from passed syntax tree. Semantic analysis is also performed.
    pub fn build(self) -> Result<Program, CompileErr> {
        // Build top level scope
        let mut pro = Program {
            vars: vec![],
            funcs: vec![],
            global: Rc::new(Scope::new()),
        };
        let mut bodies = Vec::new();
        if let Term::Program { def } = &self.root {
            for t in def {
                match t {
                    // Create global variable, possibly with initial value
                    Term::VarDef { loc, id, init, ty } => {
                        let var = Rc::new(self.build_global_var(id, ty, init, loc)?);
                        pro.vars.push(var.clone());
                        let sym = ExtRc::new(Symbol::Global(var));
                        pro.global.add(sym).map_err(|e| CompileErr { loc: loc.clone(), msg: e })?;
                    }
                    // Create signature part for function, while its body are left empty for a
                    // later pass.
                    Term::FnDef { loc: _, sig, body } => {
                        pro.funcs.push(Rc::new(self.build_fn_sig(sig)?));
                        bodies.push(body.deref())
                    }
                    _ => unreachable!()
                }
            }
        } else { unreachable!() }

        // Build basic blocks in each function
        for i in 0..pro.funcs.len() {
            let blocks = match bodies[i] {
                Term::FnBody { loc: _, bb } => bb,
                _ => unreachable!()
            };
            self.build_body(blocks, pro.funcs[i].clone(), pro.global.clone())?;
        }

        Ok(pro)
    }

    fn build_global_var(&self, id: &Token, ty: &Term, init: &Option<Token>, loc: &Loc)
                        -> Result<GlobalVar, CompileErr>
    {
        let ty = self.create_type(ty)?;
        let init = match init {
            Some(c) => Some(self.create_const(c, &ty, loc)?),
            None => None
        };
        let name = if let Token::GlobalId(s) = id { self.trim_tag(s) } else { unreachable!() };
        Ok(GlobalVar { name: name.to_string(), ty, init })
    }

    fn build_fn_sig(&self, term: &Term) -> Result<Func, CompileErr> {
        if let Term::FnSig { loc: _, id, param, ret } = term {
            // Extract function name
            let name = if let Token::GlobalId(s) = id {
                self.trim_tag(s) // trim global tag
            } else { unreachable!() };

            // Build parameter list, also add parameter to function scope
            let mut plist: Vec<SymbolRef> = Vec::new();
            let scope = Scope::new();
            if let Term::ParamList { loc: _, list } = param.as_ref() {
                for p in list {
                    if let Term::ParamDef { loc, id: Token::LocalId(s), ty } = p {
                        let sym = ExtRc::new(self.create_local(s, self.create_type(ty)?)?);
                        plist.push(sym.clone());
                        scope.add(sym).map_err(|e| CompileErr { loc: loc.clone(), msg: e })?
                    } else { unreachable!() }
                }
            } else { unreachable!() }

            // Build return type
            let ret = match ret {
                Some(r) => if let Term::FnRet { loc: _, ty } = r.deref() {
                    self.create_type(ty)?
                } else { unreachable!() }
                None => Type::Void,
            };

            // Return incomplete function object
            Ok(Func {
                name: name.to_string(),
                scope: Rc::new(scope),
                param: plist,
                ret,
                ent: RefCell::new(ExtRc::new(BasicBlock::default())),
                exit: RefCell::new(HashSet::new()),
                ssa: RefCell::new(false),
            })
        } else { unreachable!() }
    }

    fn build_body(&self, terms: &Vec<Term>, func: Rc<Func>, global: Rc<Scope>)
                  -> Result<(), CompileErr>
    {
        // Build block labels
        let mut labels: HashMap<String, BlockRef> = HashMap::new();
        let mut blocks: Vec<(BlockRef, &Vec<Term>)> = vec![];
        for i in 0..terms.len() {
            if let Term::BlockDef { loc: _, id, instr } = &terms[i] {
                let name = if let Token::Label(s) = id {
                    self.trim_tag(s).to_string()
                } else { unreachable!() };
                let block = ExtRc::new(BasicBlock::new(name.clone()));
                labels.insert(name, block.clone());
                blocks.push((block.clone(), instr));
                if i == 0 { func.ent.replace(block); } // replace dummy entrance with real one
            } else { unreachable!() };
        }

        // Build instructions inside each block
        let ctx = Context { global, func, labels };
        for (b, terms) in blocks {
            for t in terms {
                let instr = self.build_instr(t, &ctx)?;
                b.push_back(instr);
            }
        }

        Ok(())
    }

    fn build_instr(&self, term: &Term, ctx: &Context) -> Result<Instr, CompileErr> {
        match term {
            Term::AssignInstr { loc: _, id, rhs } => self.build_assign(id, rhs, ctx),
            Term::CtrlInstr { loc: _, name: Token::Reserved(s), tgt } =>
                self.build_ctrl(s, tgt, ctx),
            _ => unreachable!()
        }
    }

    fn build_assign(&self, dst: &Token, rhs: &Term, ctx: &Context) -> Result<Instr, CompileErr> {
        if let Term::AssignRhs { loc, name: Token::Reserved(op), ty, opd } = rhs {
            // Create symbols for destination
            let rhs_loc = loc;
            let ref ty = self.create_type(ty)?;
            let dst = self.build_symbol(dst, &ty, ctx, loc)?;

            // Deal with operands
            match opd.deref() {
                Term::OpdList { loc, list } => {
                    let opd = self.build_opd_list(ty, list, ctx)?;
                    self.build_arith(&ty, dst.clone(), op.as_str(), list, ctx, rhs_loc)
                }
                Term::FnCall { loc, func, arg } => {
                    let fn_sym = self.build_symbol(func, ty, ctx, loc)?;
                    let arg = if let Term::OpdList { loc: _, list } = arg.deref() {
                        list
                    } else { unreachable!() };
                    if let Symbol::Func(func) = fn_sym.deref() {
                        self.build_fn_call(func, ty, arg, Some(dst.clone()), ctx, loc)
                    } else {
                        Err(CompileErr {
                            loc: loc.clone(),
                            msg: format!("symbol {} is not a function", fn_sym.name()),
                        })
                    }
                }
                Term::PhiList { loc, list } => {
                    let mut pairs: Vec<(Option<BlockRef>, RefCell<Value>)> = Vec::new();
                    for t in list {
                        if let Term::PhiOpd { loc, bb, opd } = t {
                            let block = match bb {
                                Some(Token::Label(s)) => ctx.labels.get(s).cloned(),
                                None => None,
                                _ => { unreachable!() }
                            };
                            let val = self.build_value(opd, ty, ctx)?;
                            pairs.push((block, RefCell::new(val)));
                        } else { unreachable!() }
                    }
                    Ok(Instr::Phi { src: pairs, dst: RefCell::new(dst) })
                }
                _ => unreachable!()
            }
        } else { unreachable!() }
    }

    fn build_arith(&self, ty: &Type, dst: SymbolRef, op: &str, opd: &Vec<Token>, ctx: &Context,
                   loc: &Loc) -> Result<Instr, CompileErr>
    {
        unimplemented!()
    }

    fn build_fn_call(&self, func: &Rc<Func>, ty: &Type, arg: &Vec<Token>, dst: Option<SymbolRef>,
                     ctx: &Context, loc: &Loc) -> Result<Instr, CompileErr>
    {
        unimplemented!()
    }

    fn build_opd_list(&self, ty: &Type, opd: &Vec<Token>, ctx: &Context)
                      -> Result<Vec<SymbolRef>, CompileErr>
    {
        unimplemented!()
    }

    fn build_ctrl(&self, name: &str, tgt: &Term, ctx: &Context) -> Result<Instr, CompileErr> {
        unimplemented!()
    }

    fn build_value(&self, tok: &Token, ty: &Type, ctx: &Context) -> Result<Value, CompileErr> {
        unimplemented!()
    }

    fn build_symbol(&self, tok: &Token, ty: &Type, ctx: &Context, loc: &Loc)
                    -> Result<SymbolRef, CompileErr>
    {
        match tok {
            Token::GlobalId(s) => match ctx.global.find(self.trim_tag(s)) {
                Some(sym) => {
                    self.check_type(sym.deref(), &ty, loc)?;
                    Ok(sym)
                }
                None => Err(CompileErr {
                    loc: loc.clone(),
                    msg: format!("identifier {} not found in global scope", s),
                })
            }
            Token::LocalId(s) => match ctx.func.scope.find(s) {
                Some(sym) => Ok(sym),
                None => {
                    let sym = ExtRc::new(self.create_local(s, ty.clone())?);
                    let _ = ctx.func.scope.add(sym.clone());
                    Ok(sym)
                }
            }
            _ => unreachable!()
        }
    }

    fn check_type(&self, sym: &Symbol, ty: &Type, loc: &Loc) -> Result<(), CompileErr> {
        let sym_ty = sym.get_type();
        if ty != &sym_ty {
            Err(CompileErr {
                loc: loc.clone(),
                msg: format!("expect symbol of type {}, found {}", ty.to_string(),
                             sym_ty.to_string()),
            })
        } else { Ok(()) }
    }

    fn create_const(&self, tok: &Token, ty: &Type, loc: &Loc) -> Result<Const, CompileErr> {
        if let Token::Integer(i) = tok {
            match ty {
                Type::I1 => match i.as_str() {
                    "0" => Ok(Const::I1(false)),
                    "1" => Ok(Const::I1(true)),
                    _ => Err(CompileErr {
                        loc: loc.clone(),
                        msg: format!("cannot create constant {} of type i1", i),
                    })
                }
                Type::I64 => Ok(Const::I64(i.parse().unwrap())),
                _ => unreachable!()
            }
        } else { unreachable!() }
    }

    fn create_local(&self, s: &str, ty: Type) -> Result<Symbol, CompileErr> {
        let mut name = self.trim_tag(s); // trim local tag
        let ver = match name.find(".") {
            Some(_) => {
                let split: Vec<&str> = name.split('.').collect();
                name = split[0];
                Some(usize::from_str(split[1]).unwrap())
            }
            None => None
        };
        Ok(Symbol::Local { name: name.to_string(), ty, ver })
    }

    fn create_type(&self, term: &Term) -> Result<Type, CompileErr> {
        if let Term::TypeDecl { loc, ty: Token::Reserved(s) } = term {
            Type::from_str(s).map_err(|e| CompileErr { loc: loc.clone(), msg: e })
        } else { unreachable!() }
    }

    fn trim_tag<'a>(&self, s: &'a str) -> &'a str {
        match s.split_at(1).0 {
            "@" | "$" => s.split_at(1).1,
            _ => s
        }
    }
}

#[test]
fn test_build() {
    use crate::compile::lex::Lexer;
    use crate::compile::parse::Parser;
    use std::fs::File;
    let mut file = File::open("test/parse.ir").unwrap();
    let lexer = Lexer::from_read(&mut file).unwrap();
    let parser = Parser::new(lexer);
    let tree = parser.parse().unwrap();
    let builder = Builder::new(tree);
    println!("{:?}", builder.build());
}
