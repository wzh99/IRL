use crate::parse::Loc;

#[derive(Debug)]
pub enum Token {
    /// Identifier `[@%][A-Za-z0-9_]+(.[0-9]+)?`
    Id(String),
    /// Reserved words `[A-Za-z_][A-Za-z0-9_]*`
    Reserved(String),
    /// Integer `-?[0-9]+`
    Integer(String),
    /// Comma, for separating list elements `,`
    Comma,
    /// Left parenthesis `(`
    LeftParent,
    /// Right parenthesis  `)`
    RightParent,
    /// Left square bracket `[`
    LeftSquare,
    /// Right square bracket `]`
    RightSquare,
    /// Left curly bracket `{`
    LeftCurly,
    /// Right curly bracket `}`
    RightCurly,
    /// Left arrow, for assignment `<-`
    LeftArrow,
    /// Right arrow, used in function type `->`
    RightArrow,
    /// Colon, separating label and value in phi instruction `:`
    Colon,
    /// Semicolon, ending indication of one instruction `;`
    Semicolon,
    /// Question mark, used in `br` instruction `?`
    Question,
    /// End-of-file indicator
    Eof
}

impl Token {
    pub fn len(&self) -> usize {
        match self {
            Token::Id(s) | Token::Reserved(s) | Token::Integer(s) => s.len(),
            Token::LeftArrow | Token::RightArrow => 2,
            Token::Eof => 0,
            _ => 1
        }
    }
}

#[derive(Debug)]
pub enum Term {
    /// Program : FnDef* ;
    Program{func: Vec<Term>},
    /// FnDef : `fn` FnSig FnBody ;
    FnDef{loc: Loc, sig: Box<Term>, body: Box<Term>},
    /// FnSig : GlobalId `(` ( ParamDef ( `,` ParamDef )* )? `)` ( `->` TypeDecl )? ;
    FnSig{loc: Loc, id: Box<Term>, param: Vec<Term>, ret: Option<Box<Term>>},
    /// ParamDef : LocalId `:` TypeDecl ;
    ParamDef{loc: Loc, id: Box<Term>, ret: Box<Term>},
    /// FnBody : BlockDef* ;
    FnBody{loc: Loc, bb: Vec<Term>},
    /// BlockDef : LocalId `:` InstrDef+ ;
    BlockDef{loc: Loc, name: String, instr: Vec<Term>},
    /// InstrDef : AssignInstr | CtrlInstr ;
    /// AssignInstr : LocalId `<-` ExprBody `;` ;
    AssignInstr{loc: Loc, id: Box<Term>, expr: Box<Term>},
    /// ExprBody : Reserved TypeDecl ( OpdList | FnCall ) ;
    ExprBody{loc: Loc, name: String, opd: Box<Term>},
    /// CtrlInstr : Reserved ( OpdList | FnCall | Branch ) `;` ;
    CtrlInstr{loc: Loc, name: String, opd: Box<Term>},
    /// FnCall : GlobalId `(` OpdList `)` ;
    FnCall{loc: Loc, func: Box<Term>, arg: Vec<Term>},
    /// OpdList : ( Opd | ( `,` Opd )* )?
    OpdList{loc: Loc, id: Vec<Term>},
    /// Opd : GlobalId | LocalId | Integer ;
    /// GlobalId : `/@[A-Za-z0-9_]+(.[0-9]+)?/` ;
    GlobalId{loc: Loc, name: String},
    /// LocalId : `/%[A-Za-z0-9_]+(.[0-9]+)?/` ;
    LocalId{loc: Loc, name: String},
    /// Integer : `/-?[0-9]+/` ;
    Integer{loc: Loc, val: i64},
    /// TypeDecl : Reserved ;
    TypeDecl{loc: Loc, name: String},
}