use crate::compile::{ParseErr, Loc};
use crate::compile::syntax::{Term, Token};
use crate::lang::{Program, ExtRc};
use crate::lang::val::{Scope, Type, Const, Symbol, Func};
use std::rc::Rc;
use std::str::FromStr;
use std::ops::Deref;
use std::cell::RefCell;
use crate::lang::bb::BasicBlock;

pub struct Builder {
    root: Term,
}

impl Builder {
    pub fn new(root: Term) -> Builder { Builder{root} }

    /// Build program from passed syntax tree. Semantic analysis is also performed.
    pub fn build(&mut self) -> Result<Program, ParseErr> {
        // Build top level scope
        let mut pro = Program{
            fn_list: vec![],
            global: Rc::new(Scope::new())
        };
        if let Term::Program { def } = &self.root {
            for t in def {
                match t {
                    // Create global variable, possibly with initial value
                    Term::VarDef { loc, id, init, ty } => {
                        let sym = Rc::new(self.build_global_var(id, ty, init, loc)?);
                        pro.global.add(sym).map_err(|e| ParseErr{ loc: loc.clone(), msg: e })?;
                    }
                    // Create signature part for function, while its body are left empty for a
                    // later pass.
                    Term::FnDef { loc: _, sig, body:_ } =>
                        pro.fn_list.push(Rc::new(self.build_fn_sig(sig)?)),
                    _ => unreachable!()
                }
            }
        } else { unreachable!() }
        unimplemented!()
    }

    fn build_global_var(&self, id: &Token, ty: &Term, init: &Option<Token>, loc: &Loc)
        -> Result<Symbol, ParseErr> {
        let ty = self.build_type(ty)?;
        let init = match init {
            Some(c) => Some(self.build_const(c, &ty, loc)?),
            None => None
        };
        let name = if let Token::GlobalId(s) = id { s } else { unreachable!() };
        Ok(Symbol::GlobalVar { name: name.clone(), ty, init })
    }

    fn build_fn_sig(&self, term: &Term) -> Result<Func, ParseErr> {
        if let Term::FnSig { loc:_, id, param, ret } = term {
            // Extract function name
            let name = if let Token::GlobalId(s) = id {
                s.split_at(1).1 // trim global tag
            } else { unreachable!() };

            // Build parameter list, also add parameter to function scope
            let mut param_list: Vec<Rc<Symbol>> = Vec::new();
            let scope = Scope::new();
            if let Term::ParamList { loc:_, list } = param.as_ref() {
                for p in list {
                    if let Term::ParamDef { loc, id: Token::LocalId(s), ty } = p {
                        let sym = Rc::new(self.build_local(s, self.build_type(ty)?)?);
                        param_list.push(sym.clone());
                        scope.add(sym).map_err(|e| ParseErr{ loc: loc.clone(), msg: e })?
                    } else { unreachable!() }
                }
            } else { unreachable!() }

            // Build return type
            let ret = match ret {
                Some(r) => if let Term::FnRet { loc:_, ty } = r.deref() {
                    self.build_type(ty)?
                } else { unreachable!() }
                None => Type::Void,
            };

            // Return incomplete function object
            Ok(Func{
                name: name.to_string(),
                scope: Rc::new(scope),
                param: param_list,
                ret,
                ent: RefCell::new(ExtRc(Rc::new(BasicBlock::new("".to_string())))),
                exit: RefCell::new(Default::default())
            })
        } else { unreachable!() }
    }

    fn build_type(&self, term: &Term) -> Result<Type, ParseErr> {
        if let Term::TypeDecl { loc, ty: Token::Reserved(s) } = term {
            Type::from_str(s).map_err(|e| ParseErr{ loc: loc.clone(), msg: e })
        } else { unreachable!() }
    }

    fn build_const(&self, tok: &Token, ty: &Type, loc: &Loc) -> Result<Const, ParseErr> {
        if let Token::Integer(i) = tok {
            match ty {
                Type::I1 => match i.as_str() {
                    "0" => Ok(Const::I1(false)),
                    "1" => Ok(Const::I1(true)),
                    _ => Err(ParseErr{
                        loc: loc.clone(),
                        msg: format!("cannot create constant {} of type i1", i)
                    })
                }
                Type::I64 => Ok(Const::I64(i64::from_str(i.as_str()).unwrap())),
                _ => unreachable!()
            }
        } else { unreachable!() }
    }

    fn build_local(&self, s: &str, ty: Type) -> Result<Symbol, ParseErr> {
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
}

#[test]
fn test_build() {
    use crate::compile::lex::Lexer;
    use crate::compile::parse::Parser;
    use std::fs::File;
    let mut file = File::open("test/compile.ir").unwrap();
    let lexer = Lexer::from_read(&mut file).unwrap();
    let mut parser = Parser::new(lexer);
    let tree = parser.parse().unwrap();
    let mut builder = Builder::new(tree);
    println!("{:#?}", builder.build());
}
