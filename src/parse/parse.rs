use crate::parse::lex::{Lexer, Lexeme};
use crate::parse::{ParseErr, Loc};
use crate::parse::syntax::{Term, Token};
use std::collections::VecDeque;
use crate::parse::syntax::Term::AssignInstr;

pub struct Parser {
    lexer: Lexer,
    buf: VecDeque<Lexeme>,
    loc: Loc,
}

type ParseResult = Result<Term, ParseErr>;

macro_rules! check_op {
    ($parser:ident, $tok:ident, $term: ident) => {
        if let Token::$term = $tok {} else {
            return $parser.err(vec![&Token::$term.to_string()], $tok)
        }
    };
}

impl Parser {
    /// Construct parser from lexer object
    pub fn new(lexer: Lexer) -> Parser {
        Parser{
            lexer,
            buf: VecDeque::new(),
            loc: Loc{ line: 0, col: 0 }
        }
    }

    /// Parse the source file from token stream.
    /// `Ok(t)` if the source is successfully parsed, or `Err(e)` if some syntax error is found.
    pub fn parse(&mut self) -> Result<Term, ParseErr> {
        let mut def = Vec::new();
        loop {
            let tok = self.peek(0)?;
            let term = match tok {
                Token::GlobalId(_) => self.var_def()?,
                Token::Reserved(k) if &k == "fn" => self.fn_def()?,
                Token::Eof => break,
                _ => self.err(vec!["GlobalId", "Reserved", "Eof"], tok)?
            };
            def.push(term);
        }
        Ok(Term::Program{def})
    }

    fn var_def(&mut self) -> ParseResult {
        let loc = self.loc.clone();
        let id = self.consume()?; // GlobalId
        if let Token::GlobalId(_) = id {} else {
            return self.err(vec!["GlobalId"], id)
        }
        let col = self.consume()?; // `:`
        check_op!(self, col, Colon);
        let ty = self.type_decl()?; // TypeDecl
        let semi = self.consume()?;  // `;`
        check_op!(self, semi, Semicolon);
        Ok(Term::VarDef { loc, id, ty: Box::new(ty) })
    }

    fn fn_def(&mut self) -> ParseResult {
        let loc = self.loc.clone();
        let fn_kw = self.consume()?; // `fn`
        match &fn_kw {
            Token::Reserved(k) if k == "fn" => (),
            _ => return self.err(vec!["fn"], fn_kw)
        }
        let sig = self.fn_sig()?; // FnSig
        let body = self.fn_body()?; // FnBody
        Ok(Term::FnDef { loc, sig: Box::new(sig), body: Box::new(body) })
    }

    fn fn_sig(&mut self) -> ParseResult {
        let loc = self.loc.clone();
        let id = self.consume()?; // GlobalId
        if let Token::GlobalId(_) = id {} else {
            return self.err(vec!["GlobalId"], id);
        }
        let left_par = self.consume()?; // `(`
        check_op!(self, left_par, LeftParent);
        let param = self.param_list()?; // ParamList
        let right_par = self.consume()?; // `)`
        check_op!(self, right_par, RightParent);
        let ret: Option<Term>;
        let next = self.peek(0)?;
        match next { // FnRet?
            Token::RightArrow => ret = Some(self.fn_ret()?),
            Token::LeftCurly => ret = None,
            _ => return self.err(vec!["->", "{"], next)
        }
        Ok(Term::FnSig {
            loc, id,
            param: Box::new(param),
            ret: ret.map(|r| Box::new(r))
        })
    }

    fn param_list(&mut self) -> ParseResult {
        let loc = self.loc.clone();
        let mut list = Vec::new();
        loop {
            let tok = self.peek(0)?;
            match tok {
                Token::LocalId(_) => list.push(self.param_def()?), // ParamDef
                Token::Comma => { // (`,` ParamDef)*
                    self.consume()?;
                    list.push(self.param_def()?)
                }
                Token::RightParent => break,
                _ => return self.err(vec!["LocalId", "RightParent"], tok)
            }
        }
        Ok(Term::ParamList { loc, list })
    }

    fn param_def(&mut self) -> ParseResult {
        let loc = self.loc.clone();
        let id = self.consume()?; // LocalId
        if let Token::LocalId(_) = id {} else {
            return self.err(vec!["LocalId"], id);
        }
        let col = self.consume()?; // `:`
        check_op!(self, col, Colon);
        let ty = self.type_decl()?; // TypeDecl
        Ok(Term::ParamDef { loc, id, ty: Box::new(ty) })
    }

    fn fn_ret(&mut self) -> ParseResult {
        let loc = self.loc.clone();
        let right_arr = self.consume()?; // `->`
        check_op!(self, right_arr, RightArrow);
        let ty = self.type_decl()?;
        Ok(Term::FnRet { loc, ty: Box::new(ty) })
    }

    fn fn_body(&mut self) -> ParseResult {
        let loc = self.loc.clone();
        let left_cur = self.consume()?; // `{`
        check_op!(self, left_cur, LeftCurly);
        let mut bb = Vec::new();
        loop {
            let tok = self.peek(0)?;
            match tok { // BlockDef+
                // Until at least a basic block is parsed, `}` cannot be accepted.
                Token::LocalId(_) => bb.push(self.block_def()?),
                Token::RightCurly if !bb.is_empty() => break,
                _ => {
                    let mut expect = vec!["LocalId"];
                    if !bb.is_empty() { expect.push("}") }
                    return self.err(expect, tok)
                }
            }
        }
        Ok(Term::FnBody { loc, bb })
    }

    fn block_def(&mut self) -> ParseResult {
        let loc = self.loc.clone();
        let id = self.consume()?; // LocalId
        if let Token::LocalId(_) = id {} else {
            return self.err(vec!["LocalId"], id)
        }
        let col = self.consume()?; // `:`
        check_op!(self, col, Colon);
        let mut instr = Vec::new();
        loop {
            let next_two = (self.peek(0)?, self.peek(1)?);
            match next_two {
                (id, Token::LeftArrow) if id.is_id() => { // AssignInstr
                    instr.push(self.instr_def()?)
                }
                (Token::Reserved(_), _) => instr.push(self.instr_def()?), // CtrlInstr
                (id, Token::Colon) if id.is_id() && !instr.is_empty() => break,
                (Token::RightCurly, _) if !instr.is_empty() => break,
                _ => {
                    let mut expect = vec!["Id", "Reserved"];
                    if !instr.is_empty() { expect.push("}") }
                    return self.err(expect, next_two.0)
                }
            }
        }
        Ok(Term::BlockDef { loc, id, instr })
    }

    fn instr_def(&mut self) -> ParseResult {
        let tok = self.peek(0)?;
        let term = match tok {
            _ if tok.is_id() => self.assign_instr(),
            Token::Reserved(_) => self.ctrl_instr(),
            _ => return self.err(vec!["Id", "Reserved"], tok)
        };
        let semi = self.consume()?;
        check_op!(self, semi, Semicolon);
        term
    }

    fn assign_instr(&mut self) -> ParseResult {
        let loc = self.loc.clone();
        let id = self.consume()?; // Id
        if !id.is_id() { return self.err(vec!["Id"], id) }
        let arr = self.consume()?; // `<-`
        check_op!(self, arr, LeftArrow);
        let expr = self.expr_body()?;
        Ok(AssignInstr { loc, id, expr: Box::new(expr) })
    }

    fn expr_body(&mut self) -> ParseResult {
        let tok = self.peek(0)?;
        return match tok {
            Token::Reserved(_) => self.arith_expr(),
            _ if tok.is_opd() => self.opd(),
            _ => return self.err(vec!["Reserved", "Operand"], tok)
        };
    }

    fn arith_expr(&mut self) -> ParseResult {
        unreachable!()
    }

    fn ctrl_instr(&mut self) -> ParseResult {
        unreachable!()
    }

    fn type_decl(&mut self) -> ParseResult {
        let loc = self.loc.clone();
        let ty = self.consume()?; // Reserved
        if let Token::Reserved(r) = &ty {} else {
            return self.err(vec!["Reserved"], ty)
        }
        Ok(Term::TypeDecl { loc, ty })
    }

    fn opd(&mut self) -> ParseResult {
        let loc = self.loc.clone();
        let opd = self.consume()?;
        if !opd.is_opd() { return self.err(vec!["Operand"], opd) }
        Ok(Term::Opd { loc, opd })
    }

    /// Consume one lexeme from stream
    fn consume(&mut self) -> Result<Token, ParseErr> {
        let lex = match self.buf.pop_front() {
            Some(l) => l,
            None => self.lexer.next()?
        };
        self.loc = lex.loc.clone();
        Ok(lex.tok)
    }

    /// Look ahead certain lexeme in the stream.
    fn peek(&mut self, idx: usize) -> Result<Token, ParseErr> {
        if idx >= self.buf.len() {
            for _ in 0..(idx - self.buf.len() + 1) {
                self.buf.push_back(self.lexer.next()?)
            }
        }
        let lex = self.buf[idx].clone();
        self.loc = lex.loc.clone();
        Ok(lex.tok)
    }

    /// Report error with current location
    fn err(&self, exp: Vec<&str>, fnd: Token) -> Result<Term, ParseErr> {
        Err(ParseErr{
            loc: self.loc.clone(),
            msg: format!("expect {:?}, found {:?}", exp, fnd).replace("\"", "")
        })
    }
}

#[test]
fn test_parse() {
    use std::fs::File;
    let mut file = File::open("test/parse.ir").unwrap();
    let mut lexer = Lexer::from_read(&mut file).unwrap();
    let mut parser = Parser::new(lexer);
    println!("{:?}", parser.parse())
}