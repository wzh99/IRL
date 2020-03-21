use std::fmt::{Debug, Display, Error, Formatter};

mod syntax;
pub mod lex;
pub mod parse;
pub mod build;

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
    fn new_line(&mut self) {
        self.line += 1;
        self.col = 0
    }
}

#[derive(Debug, Clone)]
pub struct CompileErr {
    /// Where this error starts in the source file
    loc: Loc,
    /// What causes this error
    msg: String,
}

impl Display for CompileErr {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        write!(f, "{}\t{}", self.loc, self.msg)
    }
}
