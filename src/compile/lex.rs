use std::convert::TryFrom;
use std::io::{self, Read};
use std::iter::FromIterator;
use std::str::FromStr;

use crate::compile::{CompileErr, Loc};
use crate::compile::syntax::Token;

pub struct Lexer {
    /// Characters from source
    chars: Vec<char>,
    /// Point to current location in the char vector
    ptr: usize,
    /// Location of current pointer in source file
    loc: Loc,
    /// If there was an error during lexing
    err: Option<CompileErr>,
}

impl FromStr for Lexer {
    type Err = io::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Lexer {
            chars: s.to_string().chars().collect(),
            ptr: 0,
            loc: Loc { line: 0, col: 0 },
            err: None,
        })
    }
}

impl TryFrom<&mut dyn Read> for Lexer {
    type Error = io::Error;

    fn try_from(read: &mut dyn Read) -> Result<Self, Self::Error> {
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
    GlobalName,
    /// Expect name part for local identifier
    LocalName,
    /// Expect version part for local identifier
    LocalVer,
    /// Expect name part for label
    LabelName,
    /// Expect name part for reserved words
    ResName,
    /// Expect integer
    Int,
    /// In comment, ignore all characters until a new line
    Comment
}

type LexResult = Result<Token, CompileErr>;

impl Lexer {
    /// Get next lexeme. This function simulates an NFA to perform lexical analysis.
    /// `Ok(l)` if a valid lexeme is found.
    /// `Err(e)` if there is some error occurred during lexing.
    pub fn next(&mut self) -> LexResult {
        // Early exit if there was an error
        if let Some(ref e) = self.err { return Err(e.clone()); }

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
                        state = NfaState::GlobalName;
                    }
                    '$' => {
                        // local identifier
                        read_char!();
                        if !Self::is_alpha_num_under(self.peek()) {
                            return self.err("expect [A-Za-z0-9_]");
                        }
                        read_char!();
                        state = NfaState::LocalName
                    }
                    '%' => {
                        // label
                        read_char!();
                        if !Self::is_alpha_num_under(self.peek()) {
                            return self.err("expect [A-Za-z0-9_]");
                        }
                        read_char!();
                        state = NfaState::LabelName
                    }
                    _ if Self::is_alpha_under(c) => {
                        // reserved word
                        read_char!();
                        state = NfaState::ResName
                    }
                    '-' => {
                        // signed integer or right arrow
                        read_char!();
                        match self.peek() {
                            '0'..='9' => {
                                read_char!();
                                state = NfaState::Int
                            }
                            '>' => {
                                skip_char!();
                                return Ok(Token::RightArrow(self.loc.clone()));
                            }
                            _ => return self.err("expect [0-9>]")
                        }
                    }
                    '<' => {
                        skip_char!(); // '<'
                        if self.peek() != '-' {
                            return self.err("expect -");
                        }
                        skip_char!(); // '-'
                        return Ok(Token::LeftArrow(self.loc.clone()));
                    }
                    '0'..='9' => {
                        read_char!();
                        state = NfaState::Int
                    }
                    ',' => {
                        skip_char!();
                        return Ok(Token::Comma(self.loc.clone()));
                    }
                    '*' => {
                        skip_char!();
                        return Ok(Token::Asterisk(self.loc.clone()));
                    }
                    '=' => {
                        skip_char!();
                        return Ok(Token::Equal(self.loc.clone()));
                    }
                    '(' => {
                        skip_char!();
                        return Ok(Token::LeftParent(self.loc.clone()));
                    }
                    ')' => {
                        skip_char!();
                        return Ok(Token::RightParent(self.loc.clone()));
                    }
                    '[' => {
                        skip_char!();
                        return Ok(Token::LeftSquare(self.loc.clone()));
                    }
                    ']' => {
                        skip_char!();
                        return Ok(Token::RightSquare(self.loc.clone()));
                    }
                    '{' => {
                        skip_char!();
                        return Ok(Token::LeftCurly(self.loc.clone()));
                    }
                    '}' => {
                        skip_char!();
                        return Ok(Token::RightCurly(self.loc.clone()));
                    }
                    ':' => {
                        skip_char!();
                        return Ok(Token::Colon(self.loc.clone()));
                    }
                    ';' => {
                        skip_char!();
                        return Ok(Token::Semicolon(self.loc.clone()));
                    }
                    '?' => {
                        skip_char!();
                        return Ok(Token::Question(self.loc.clone()));
                    }
                    '/' => {
                        skip_char!(); // `/`
                        if self.peek() != '/' {
                            return self.err("expect /")
                        }
                        skip_char!(); // `/`
                        state = NfaState::Comment
                    }
                    ' ' | '\t' | '\r' | '\n' => { skip_char!(); }
                    _ => return self.err("unknown character")
                }
                NfaState::GlobalName =>
                    if Self::is_alpha_num_under(c) {
                        read_char!();
                    } else {
                        return self.pop_buf(state, buf);
                    }
                NfaState::LocalName => match c {
                    _ if Self::is_alpha_num_under(c) => { read_char!(); }
                    '.' => {
                        // reaching version part of identifier
                        read_char!();
                        match self.peek() {
                            '0'..='9' => {
                                read_char!();
                                state = NfaState::LocalVer
                            }
                            _ => return self.err("expect [0-9]")
                        }
                    }
                    _ => return self.pop_buf(state, buf),
                }
                NfaState::LabelName =>
                    if Self::is_alpha_num_under(c) {
                        read_char!();
                    } else {
                        return self.pop_buf(state, buf);
                    }
                NfaState::LocalVer => match c {
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
                NfaState::Comment => {
                    skip_char!();
                    match c {
                        '\n' => state = NfaState::Start,
                        _ => continue
                    }
                }
            }
        }

        // Possibly clear the buffer and create the final lexeme
        if buf.is_empty() {
            Ok(Token::Eof(self.loc.clone()))
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

    fn err(&mut self, msg: &str) -> LexResult {
        let err = CompileErr { loc: self.loc.clone(), msg: msg.to_string() };
        self.err = Some(err.clone());
        Err(err)
    }

    /// Pop all characters in buffer to create a lexeme
    fn pop_buf(&self, state: NfaState, buf: Vec<char>) -> LexResult {
        let s = String::from_iter(buf.into_iter());
        match state {
            // When the buffer is not empty, it cannot be in the start state.
            NfaState::Start | NfaState::Comment => unreachable!(),
            NfaState::GlobalName => Ok(Token::GlobalId(self.loc.clone(), s)),
            NfaState::LocalName | NfaState::LocalVer =>
                Ok(Token::LocalId(self.loc.clone(), s)),
            NfaState::LabelName => Ok(Token::Label(self.loc.clone(), s)),
            NfaState::ResName => Ok(Token::Reserved(self.loc.clone(), s)),
            NfaState::Int => Ok(Token::Integer(self.loc.clone(), s))
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
    let mut file = File::open("test/example.ir").unwrap();
    let mut lexer = Lexer::try_from(&mut file as &mut dyn Read).unwrap();
    loop {
        match lexer.next() {
            Ok(Token::Eof(_)) => break,
            Ok(l) => println!("{:?}", l),
            Err(e) => {
                println!("{}", e);
                break;
            }
        }
    }
}