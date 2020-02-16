use std::fmt::{self, Display, Formatter};
use std::io::{self, Read};
use std::iter::FromIterator;
use std::str::FromStr;
use crate::compile::syntax::Token;
use crate::compile::{Loc, ParseErr};

#[derive(Clone)]
pub struct Lexeme {
    pub loc: Loc,
    pub tok: Token
}

impl Display for Lexeme {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{} {:?}", self.loc, self.tok)
    }
}

pub struct Lexer {
    /// Characters from source
    chars: Vec<char>,
    /// Point to current location in the char vector
    ptr: usize,
    /// Location of current pointer in source file
    loc: Loc,
    /// If there was an error during lexing
    err: Option<ParseErr>
}

impl FromStr for Lexer {
    type Err = io::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Lexer {
            chars: s.to_string().chars().collect(),
            ptr: 0,
            loc: Loc { line: 0, col: 0 },
            err: None
        })
    }
}

impl Lexer {
    pub fn from_read(read: &mut dyn Read) -> Result<Lexer, io::Error> {
        let mut s = String::new();
        read.read_to_string(&mut s)?;
        Ok(Self::from_str(&s)?)
    }
}

/// Only keep NFA states that need to be recorded. Those states whose transition function
/// are too simple are omitted.
enum NfaState {
    /// Fresh beginning, not knowing which token to get
    Start,
    /// Expect name part for global identifier
    GlobalIdName,
    /// Expect name part for local identifier
    LocalIdName,
    /// Expect version part for local identifier
    IdVer,
    /// Expect name part for reserved words
    ResName,
    /// Expect integer
    Int
}

type LexResult = Result<Lexeme, ParseErr>;

impl Lexer {
    /// Get next lexeme. This function simulates an NFA to perform lexical analysis.
    /// `Ok(l)` if a valid lexeme is found.
    /// `Err(e)` if there is some error occurred during lexing.
    pub fn next(&mut self) -> LexResult {
        // Early exit if there was an error
        if let Some(ref e) = self.err { return Err(e.clone()) }

        // Mutable data during lexing
        let mut buf = Vec::new();
        let mut state = NfaState::Start;

        macro_rules! read_char {
            () => {
                let c = self.chars[self.ptr];
                buf.push(c);
                self.ptr += 1;
                if c == '\n' { self.loc.new_line() } else { self.loc.shift() }
            };
        }
        macro_rules! skip_char {
            () => {
                let c = self.chars[self.ptr];
                self.ptr += 1;
                if c == '\n' { self.loc.new_line() } else { self.loc.shift() }
            };
        }

        // Iterate until all the characters are consumed
        while self.ptr < self.chars.len() {
            let c = self.peek();
            match state {
                // A new round of lexing, not holding any data in buffer.
                NfaState::Start => match c {
                    '@' => {
                        read_char!();
                        if !Self::is_alpha_num_under(self.peek()) {
                            return self.err("expect [A-Za-z0-9_]");
                        }
                        read_char!();
                        state = NfaState::GlobalIdName;
                    }
                    '%' => { // local identifier
                        read_char!();
                        if !Self::is_alpha_num_under(self.peek()) {
                            return self.err("expect [A-Za-z0-9_]");
                        }
                        read_char!();
                        state = NfaState::LocalIdName
                    }
                    _ if Self::is_alpha_under(c) => { // reserved word
                        read_char!();
                        state = NfaState::ResName
                    }
                    '-' => { // signed integer or right arrow
                        read_char!();
                        match self.peek() {
                            '0'..='9' => { read_char!(); state = NfaState::Int },
                            '>' => { skip_char!(); return self.lex(Token::RightArrow) }
                            _ => return self.err("expect [0-9>]")
                        }
                    }
                    '<' => {
                        skip_char!(); // '<'
                        if self.peek() != '-' {
                            return self.err("expect -")
                        }
                        skip_char!(); // '-'
                        return self.lex(Token::LeftArrow)
                    }
                    '0'..='9' => { read_char!(); state = NfaState::Int }
                    ',' => { skip_char!(); return self.lex(Token::Comma) }
                    '(' => { skip_char!(); return self.lex(Token::LeftParent) }
                    ')' => { skip_char!(); return self.lex(Token::RightParent) }
                    '[' => { skip_char!(); return self.lex(Token::LeftSquare) }
                    ']' => { skip_char!(); return self.lex(Token::RightSquare) }
                    '{' => { skip_char!(); return self.lex(Token::LeftCurly) }
                    '}' => { skip_char!(); return self.lex(Token::RightCurly) }
                    ':' => { skip_char!(); return self.lex(Token::Colon) }
                    ';' => { skip_char!(); return self.lex(Token::Semicolon) }
                    '?' => { skip_char!(); return self.lex(Token::Question) }
                    ' ' | '\t' | '\r' | '\n' => { skip_char!(); }
                    _ => return self.err("unknown character")
                }
                NfaState::GlobalIdName => match c {
                    _ if Self::is_alpha_num_under(c) => { read_char!(); }
                    _ => return self.pop_buf(state, buf)
                }
                NfaState::LocalIdName => match c {
                    _ if Self::is_alpha_num_under(c) => { read_char!(); }
                    '.' => { // reaching version part of identifier
                        read_char!();
                        match self.peek() {
                            '0'..='9' => { read_char!(); state = NfaState::IdVer }
                            _ => return self.err("expect [0-9]")
                        }
                    }
                    _ => return self.pop_buf(state, buf),
                }
                NfaState::IdVer => match c {
                    '0'..='9' => { read_char!(); }
                    _ => return self.pop_buf(state, buf),
                }
                NfaState::ResName => match c {
                    _ if Self::is_alpha_num_under(c) => { read_char!(); }
                    _ => return self.pop_buf(state, buf)
                }
                NfaState::Int => match c {
                    '0'..='9' => { read_char!(); }
                    _ => return self.pop_buf(state, buf)
                }
            }
        }

        // Possibly clear the buffer and create the final lexeme
        if buf.is_empty() {
            self.lex(Token::Eof)
        } else {
            self.pop_buf(state, buf)
        }
    }

    /// Look ahead one character in the buffer list.
    /// If EOF id reached, return `\0`.
    fn peek(&self) -> char {
        match self.chars.get(self.ptr) {
            Some(c) => c.clone(),
            None => '\0'
        }
    }

    /// Create lexeme from given token
    fn lex(&self, tok: Token) -> LexResult {
        let mut loc = self.loc.clone();
        loc.col -= tok.len();
        Ok(Lexeme{ loc, tok })
    }

    fn err(&mut self, msg: &str) -> LexResult{
        let err = ParseErr{ loc: self.loc.clone(), msg: msg.to_string() };
        self.err = Some(err.clone());
        Err(err)
    }

    /// Pop all characters in buffer to create a lexeme
    fn pop_buf(&self, state: NfaState, buf: Vec<char>) -> LexResult {
        let s = String::from_iter(buf.into_iter());
        match state {
            // When the buffer is not empty, it cannot be in the start state.
            NfaState::Start => unreachable!(),
            NfaState::GlobalIdName => self.lex(Token::GlobalId(s)),
            NfaState::LocalIdName | NfaState::IdVer => self.lex(Token::LocalId(s)),
            NfaState::ResName => self.lex(Token::Reserved(s)),
            NfaState::Int => self.lex(Token::Integer(s))
        }
    }

    /// Decide if `c` is ASCII alphanumeric or underline [A-Za-z0-9_]
    fn is_alpha_num_under(c: char) -> bool { c.is_ascii_alphanumeric() || c == '_' }

    /// Decide if `c` is ASCII alphabetic or underline [A-Za-z_]
    fn is_alpha_under(c: char) -> bool { c.is_ascii_alphabetic() || c == '_' }
}

#[test]
fn test_lex() {
    use std::fs::File;
    let mut file = File::open("test/compile.ir").unwrap();
    let mut lexer = Lexer::from_read(&mut file).unwrap();
    loop {
        match lexer.next() {
            Ok(Lexeme{loc: _, tok: Token::Eof}) => break,
            Ok(l) => println!("{}", l),
            Err(e) => { println!("{}", e); break }
        }
    }
}