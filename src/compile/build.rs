use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::ops::Deref;
use std::rc::Rc;
use std::str::FromStr;

use crate::compile::{CompileErr, Loc};
use crate::compile::syntax::{Term, Token};
use crate::lang::{ExtRc, MutRc, Program};
use crate::lang::bb::{BasicBlock, BlockRef};
use crate::lang::instr::Instr;
use crate::lang::val::{Const, Func, GlobalVar, Scope, Symbol, SymbolRef, Type};

pub struct Builder {
    root: Term,
}

type LabelMap = HashMap<String, BlockRef>;

impl Builder {
    pub fn new(root: Term) -> Builder { Builder { root } }

    /// Build program from passed syntax tree. Semantic analysis is also performed.
    pub fn build(self) -> Result<Program, CompileErr> {
        // Build top level scope
        let mut pro = Program {
            vars: vec![],
            funcs: vec![],
            global: Scope::new(),
        };
        let mut bodies = Vec::new();
        if let Term::Program { def } = &self.root {
            for t in def {
                match t {
                    // Create global variable, possibly with initial value
                    Term::VarDef { loc, id, init, ty } => {
                        let var = Rc::new(self.build_global_var(id, ty, init, loc)?);
                        pro.vars.push(var.clone());
                        let sym = MutRc::new(Symbol::Global(var));
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
            self.build_body(blocks, &pro.funcs[i], &pro.global)?;
        }

        Ok(pro)
    }

    fn build_global_var(&self, id: &Token, ty: &Term, init: &Option<Token>, loc: &Loc)
                        -> Result<GlobalVar, CompileErr> {
        let ty = self.build_type(ty)?;
        let init = match init {
            Some(c) => Some(self.parse_const(c, &ty, loc)?),
            None => None
        };
        let name = if let Token::GlobalId(s) = id { s.split_at(1).1 } else { unreachable!() };
        Ok(GlobalVar { name: name.to_string(), ty, init })
    }

    fn build_fn_sig(&self, term: &Term) -> Result<Func, CompileErr> {
        if let Term::FnSig { loc: _, id, param, ret } = term {
            // Extract function name
            let name = if let Token::GlobalId(s) = id {
                s.split_at(1).1 // trim global tag
            } else { unreachable!() };

            // Build parameter list, also add parameter to function scope
            let mut plist: Vec<SymbolRef> = Vec::new();
            let scope = Scope::new();
            if let Term::ParamList { loc: _, list } = param.as_ref() {
                for p in list {
                    if let Term::ParamDef { loc, id: Token::LocalId(s), ty } = p {
                        let sym = MutRc::new(self.parse_local(s, self.build_type(ty)?)?);
                        plist.push(sym.clone());
                        scope.add(sym).map_err(|e| CompileErr { loc: loc.clone(), msg: e })?
                    } else { unreachable!() }
                }
            } else { unreachable!() }

            // Build return type
            let ret = match ret {
                Some(r) => if let Term::FnRet { loc: _, ty } = r.deref() {
                    self.build_type(ty)?
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

    fn build_body(&self, terms: &Vec<Term>, func: &Rc<Func>, global: &Scope)
                  -> Result<(), CompileErr> {
        // Build block labels
        let mut labels = HashMap::new();
        let mut blocks = vec![];
        for i in 0..terms.len() {
            if let Term::BlockDef { loc, id, instr } = &terms[i] {
                let name = self.parse_label(id, loc)?;
                let block = ExtRc::new(BasicBlock::new(name.clone()));
                labels.insert(name, block.clone());
                blocks.push((block.clone(), instr));
                if i == 0 { func.ent.replace(block); } // replace dummy entrance with real one
            } else { unreachable!() };
        }

        // Build instructions inside each block
        for (b, terms) in blocks {
            for t in terms {
                let instr = self.build_instr(t, &labels, global)?;
                b.push_back(instr);
            }
        }

        Ok(())
    }

    fn build_instr(&self, term: &Term, labels: &LabelMap, global: &Scope)
                   -> Result<Instr, CompileErr> {
        match term {
            Term::AssignInstr { loc: _, id, rhs } => self.build_assign(id, rhs, labels, global),
            Term::CtrlInstr { loc: _, name: Token::Reserved(s), tgt } =>
                self.build_ctrl(s, tgt, labels, global),
            _ => unreachable!()
        }
    }

    fn build_assign(&self, dst: &Token, rhs: &Term, labels: &LabelMap, global: &Scope)
                    -> Result<Instr, CompileErr> {
        unimplemented!()
    }

    fn build_ctrl(&self, name: &str, tgt: &Term, labels: &LabelMap, global: &Scope)
                  -> Result<Instr, CompileErr> {
        unimplemented!()
    }

    fn parse_const(&self, tok: &Token, ty: &Type, loc: &Loc) -> Result<Const, CompileErr> {
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
                Type::I64 => Ok(Const::I64(i64::from_str(i.as_str()).unwrap())),
                _ => unreachable!()
            }
        } else { unreachable!() }
    }

    fn parse_local(&self, s: &str, ty: Type) -> Result<Symbol, CompileErr> {
        let mut name = s.split_at(1).1; // trim local tag
        let ver: Option<usize>;
        match name.find(".") {
            Some(_) => {
                let split: Vec<&str> = name.split('.').collect();
                name = split[0];
                ver = Some(usize::from_str(split[1]).unwrap())
            }
            None => { ver = None; }
        }
        Ok(Symbol::Local { name: name.to_string(), ty, ver })
    }

    fn build_type(&self, term: &Term) -> Result<Type, CompileErr> {
        if let Term::TypeDecl { loc, ty: Token::Reserved(s) } = term {
            Type::from_str(s).map_err(|e| CompileErr { loc: loc.clone(), msg: e })
        } else { unreachable!() }
    }

    fn parse_label(&self, id: &Token, loc: &Loc) -> Result<String, CompileErr> {
        if let Token::Label(s) = id {
            let label = s.split_at(1).1;
            Ok(label.to_string())
        } else { unreachable!() }
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
