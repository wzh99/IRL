mod parse;
mod syntax;
mod lex;
mod build;

use std::fmt::{Display, Formatter, Error, Debug};

#[derive(Debug, Clone)]
pub struct Loc {
    /// Line number (0-indexed) in the source file
    line: usize,
    /// Column number (0-indexed) in the source file
    col: usize,
}

impl Display for Loc {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        write!(f, "{}:{}", self.line, self.col)
    }
}

impl Loc {
    fn shift(&mut self) { self.col += 1 }
    fn new_line(&mut self) { self.line += 1; self.col = 0 }
}

#[derive(Debug, Clone)]
pub struct ParseErr {
    /// Where this error starts in the source file
    loc: Loc,
    /// What causes this error
    msg: String
}

impl Display for ParseErr {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        write!(f, "{}\t{}", self.loc, self.msg)
    }
}
