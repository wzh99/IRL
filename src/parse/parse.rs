use crate::parse::lex::{Lexer, Lexeme};
use crate::parse::{ParseErr, Loc};
use crate::parse::syntax::{Term, Token};
use std::collections::VecDeque;

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
            let term = match self.peek(0)? {
                Token::GlobalId(_) => self.var_def()?,
                Token::Reserved(k) if &k == "fn" => self.fn_def()?,
                Token::Eof => break,
                tok => self.err(vec!["GlobalId", "Reserved", "Eof"], tok)?
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
        match self.consume()? {
            Token::Reserved(k) if &k == "fn" => (),
            kw => return self.err(vec!["fn"], kw)
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
        match self.peek(0)? { // FnRet?
            Token::RightArrow => ret = Some(self.fn_ret()?),
            Token::LeftCurly => ret = None,
            tok => return self.err(vec!["->", "{"], tok)
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
            match self.peek(0)? {
                Token::LocalId(_) => list.push(self.param_def()?), // ParamDef
                Token::Comma => { // (`,` ParamDef)*
                    self.consume()?;
                    list.push(self.param_def()?)
                }
                Token::RightParent => break,
                tok => return self.err(vec!["LocalId", "RightParent"], tok)
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
            match self.peek(0)? { // BlockDef+
                // Until at least a basic block is parsed, `}` cannot be accepted.
                Token::LocalId(_) => bb.push(self.block_def()?),
                Token::RightCurly if !bb.is_empty() => {
                    let right = self.consume()?;
                    check_op!(self, right, RightCurly);
                    break
                },
                tok => {
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
            self.peek(0)?; // reset parser location
            match next_two {
                (id, Token::LeftArrow) if id.is_id() => { // AssignInstr
                    instr.push(self.instr_def()?)
                }
                (Token::Reserved(_), _) => instr.push(self.instr_def()?), // CtrlInstr
                (id, Token::Colon) if id.is_id() && !instr.is_empty() => break,
                (Token::RightCurly, _) if !instr.is_empty() => break,
                (tok0, _) => {
                    let mut expect = vec!["Id", "Reserved"];
                    if !instr.is_empty() { expect.push("}") }
                    return self.err(expect, tok0)
                }
            }
        }
        Ok(Term::BlockDef { loc, id, instr })
    }

    fn instr_def(&mut self) -> ParseResult {
        let term = match self.peek(0)? {
            id if id.is_id() => self.assign_instr(),
            Token::Reserved(_) => self.ctrl_instr(),
            tok => return self.err(vec!["Id", "Reserved"], tok)
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
        Ok(Term::AssignInstr { loc, id, expr: Box::new(expr) })
    }

    fn expr_body(&mut self) -> ParseResult {
        match self.peek(0)? {
            Token::Reserved(_) => self.arith_expr(),
            opd if opd.is_opd() => self.opd_rhs(),
            tok => return self.err(vec!["Reserved", "Operand"], tok)
        }
    }

    fn opd_rhs(&mut self) -> ParseResult {
        let loc = self.loc.clone();
        let opd = self.consume()?;
        if !opd.is_opd() { return self.err(vec!["Operand"], opd) }
        let ty = match self.peek(0)? {
            Token::Colon => {
                self.consume()?;
                Some(Box::new(self.type_decl()?))
            }
            Token::Semicolon => None,
            tok => return self.err(vec![":", ";"], tok)
        };
        Ok(Term::OpdRhs { loc, opd, ty })
    }

    fn arith_expr(&mut self) -> ParseResult {
        let loc = self.loc.clone();
        let name = self.consume()?; // Reserved
        if let Token::Reserved(_) = name {} else {
            return self.err(vec!["Reserved"], name)
        }
        let ty = self.type_decl()?; // TypeDecl
        let opd = self.arith_opd()?; // ArithOpd
        Ok(Term::ArithExpr { loc, name, ty: Box::new(ty), opd: Box::new(opd) })
    }

    fn arith_opd(&mut self) -> ParseResult {
        Ok(match self.peek(0)? {
            opd if opd.is_opd() => match self.peek(1)? {
                Token::Comma | Token::Semicolon => self.opd_list()?, // OpdList
                Token::LeftParent => self.fn_call()?, // FnCall
                tok => self.err(vec![",", ";", "(", "["], tok)?
            }
            Token::LeftSquare => self.phi_list()?,
            tok => return self.err(vec!["Operand"], tok)
        })
    }

    fn opd_list(&mut self) -> ParseResult {
        let loc = self.loc.clone();
        let mut list = Vec::new();
        loop {
            match self.peek(0)? {
                opd if opd.is_opd() => { // Opd
                    self.consume()?;
                    list.push(opd)
                },
                Token::Comma => { // `,` Opd
                    self.consume()?;
                    let opd = self.consume()?;
                    if !opd.is_opd() { return self.err(vec!["Operand"], opd) }
                    list.push(opd)
                }
                Token::Semicolon | Token::RightParent => break,
                tok => return self.err(vec!["Operand", ",", ";"], tok)
            }
        }
        Ok(Term::OpdList { loc, list })
    }

    fn phi_list(&mut self) -> ParseResult {
        let loc = self.loc.clone();
        let mut list = Vec::new();
        loop {
            match self.peek(0)? {
                Token::LeftSquare => list.push(self.phi_opd()?),
                Token::Semicolon if !list.is_empty() => break,
                tok => {
                    let mut expect = vec!["["];
                    if !list.is_empty() { expect.push(";") }
                    return self.err(expect, tok)
                }
            }
        }
        Ok(Term::PhiList { loc, list })
    }

    fn phi_opd(&mut self) -> ParseResult {
        let loc = self.loc.clone();
        let left = self.consume()?; // `[`
        check_op!(self, left, LeftSquare);
        let bb = self.consume()?; // LocalId
        if let Token::LocalId(_) = bb {} else {
            return self.err(vec!["LocalId"], bb)
        }
        let col = self.consume()?; // `:`
        check_op!(self, col, Colon);
        let opd = self.consume()?;
        if !opd.is_local_opd() { // LocalOpd
            return self.err(vec!["LocalOpd"], opd)
        }
        let right = self.consume()?; // `]`
        check_op!(self, right, RightSquare);
        Ok(Term::PhiOpd { loc, bb, opd })
    }

    fn fn_call(&mut self) -> ParseResult {
        let loc = self.loc.clone();
        let func = self.consume()?;
        if let Token::GlobalId(_) = func {} else {
            return self.err(vec!["GlobalId"], func)
        }
        let left = self.consume()?;
        check_op!(self, left, LeftParent);
        let arg = self.opd_list()?;
        let right = self.consume()?;
        check_op!(self, right, RightParent);
        Ok(Term::FnCall { loc, func, arg: Box::new(arg) })
    }

    fn ctrl_instr(&mut self) -> ParseResult {
        let loc = self.loc.clone();
        let name = self.consume()?; // Reserved
        if let Token::Reserved(_) = name {} else {
            return self.err(vec!["Reserved"], name)
        }
        let tgt = self.ctrl_tgt()?; // CtrlTgt
        Ok(Term::CtrlInstr { loc, name, tgt: Box::new(tgt) })
    }

    fn ctrl_tgt(&mut self) -> ParseResult {
        match self.peek(0)? {
            Token::Semicolon => self.opd_list(),
            opd if opd.is_opd() => match self.peek(1)? {
                Token::Semicolon | Token::Comma => self.opd_list(),
                Token::LeftParent => self.fn_call(),
                Token::Question => self.branch(),
                tok => self.err(vec![";", "(", "?"], tok)
            }
            tok => self.err(vec!["Operand"], tok)
        }
    }

    fn branch(&mut self) -> ParseResult {
        let loc = self.loc.clone();
        let cond = self.consume()?; // Opd
        if !cond.is_opd() { return self.err(vec!["Operand"], cond) }
        let ques = self.consume()?; // `?`
        check_op!(self, ques, Question);
        let tr = self.consume()?; // LocalId
        if let Token::LocalId(_) = tr {} else {
            return self.err(vec!["LocalId"], tr)
        }
        let col = self.consume()?; // `:`
        check_op!(self, col, Colon);
        let fls = self.consume()?; // LocalId
        if let Token::LocalId(_) = fls {} else {
            return self.err(vec!["LocalId"], fls)
        }
        Ok(Term::Branch { loc, cond, tr, fls })
    }

    fn type_decl(&mut self) -> ParseResult {
        let loc = self.loc.clone();
        let ty = self.consume()?; // Reserved
        if let Token::Reserved(_) = ty {} else {
            return self.err(vec!["Reserved"], ty)
        }
        Ok(Term::TypeDecl { loc, ty })
    }

    /// Consume one lexeme from stream
    fn consume(&mut self) -> Result<Token, ParseErr> {
        let lex = match self.buf.pop_front() {
            Some(l) => l,
            None => self.lexer.next()?
        };
        self.loc = lex.loc.clone();
        println!("{}", self.loc);
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
    fn err(&self, exp: Vec<&str>, fnd: Token) -> ParseResult {
        Err(ParseErr{
            loc: self.loc.clone(),
            msg: format!("expect {:?}, found \"{}\"", exp, fnd.to_string())
        })
    }
}

#[test]
fn test_parse() {
    use std::fs::File;
    let mut file = File::open("test/parse.ir").unwrap();
    let lexer = Lexer::from_read(&mut file).unwrap();
    let mut parser = Parser::new(lexer);
    println!("{:#?}", parser.parse())
}