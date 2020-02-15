use crate::parse::lex::{Lexer, Lexeme};
use crate::parse::ParseErr;
use crate::parse::syntax::Term;
use std::collections::VecDeque;

pub struct Parser {
    lex: Lexer,
    buf: VecDeque<Lexeme>
}

impl Parser {
    /// Construct parser from lexer object
    pub fn new(lex: Lexer) -> Parser {
        Parser{ lex, buf: VecDeque::new() }
    }

    /// Parse the source file from token stream.
    /// `Ok(t)` if the source is successfully parsed, or `Err(e)` if some syntax error is found.
    pub fn parse(&mut self) -> Result<Term, ParseErr> {
        let mut def = Vec::new();
        loop {

        }
    }

    /// Consume one lexeme from stream
    fn consume(&mut self) -> Result<Lexeme, ParseErr> {
        match self.buf.pop_front() {
            Some(l) => Ok(l),
            None => self.lex.next()
        }
    }

    /// Look ahead certain lexeme in the stream.
    fn peek(&mut self, idx: usize) -> Result<&Lexeme, ParseErr> {
        if idx >= self.buf.len() {
            for _ in 0..(idx - self.buf.len() + 1) {
                self.buf.push_back(self.lex.next()?)
            }
        }
        Ok(&self.buf[idx])
    }
}