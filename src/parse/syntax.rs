use crate::parse::Loc;

/// Lexical rules for the language.
#[derive(Clone, Debug)]
pub enum Token {
    /// Global identifier `/@[A-Za-z0-9_]+/`
    GlobalId(String),
    /// Local identifier `/%[A-Za-z0-9_]+(.[0-9]+)?/`
    LocalId(String),
    /// Reserved words `/[A-Za-z_][A-Za-z0-9_]*/`
    Reserved(String),
    /// Integer `/-?[0-9]+/`
    Integer(String),
    /// Comma, for separating list elements `,`
    Comma,
    /// Colon, separating label and value in phi instruction `:`
    Colon,
    /// Semicolon, ending indication of one instruction `;`
    Semicolon,
    /// Question mark, used in `br` instruction `?`
    Question,
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
    /// End-of-file indicator
    Eof
}

impl ToString for Token {
    fn to_string(&self) -> String {
        match self {
            Token::GlobalId(s) | Token::LocalId(s) | Token::Reserved(s)
                | Token::Integer(s) => s.clone(),
            Token::Comma => ",".to_string(),
            Token::Colon => ":".to_string(),
            Token::Semicolon => ";".to_string(),
            Token::Question => "?".to_string(),
            Token::LeftParent => "(".to_string(),
            Token::RightParent => ")".to_string(),
            Token::LeftSquare => "[".to_string(),
            Token::RightSquare => "]".to_string(),
            Token::LeftCurly => "{".to_string(),
            Token::RightCurly => "}".to_string(),
            Token::LeftArrow => "<-".to_string(),
            Token::RightArrow => "->".to_string(),
            Token::Eof => "".to_string()
        }
    }
}

impl Token {
    pub fn len(&self) -> usize { self.to_string().len() }

    pub fn is_id(&self) -> bool {
        match self {
            Token::GlobalId(_) | Token::LocalId(_) => true,
            _ => false
        }
    }

    pub fn is_local_opd(&self) -> bool {
        match self {
            Token::LocalId(_) | Token::Integer(_) => true,
            _ => false
        }
    }

    pub fn is_opd(&self) -> bool {
        match self {
            Token::GlobalId(_) | Token::LocalId(_) | Token::Integer(_) => true,
            _ => false
        }
    }
}

/// Syntactical rules for the language.
/// Technically speaking, this is an LL(2) grammar.
#[derive(Debug)]
pub enum Term {
    /// Program : ( VarDef | FnDef )* ;
    /// FIRST = { GlobalId -> VarDef, `fn` -> FnDef, `` }
    /// FOLLOW = { EOF }
    Program{def: Vec<Term>},

    /// VarDef : GlobalId `:` TypeDecl `;` ;
    /// FIRST = { GlobalId }
    /// FOLLOW = { GlobalId, `fn` }
    VarDef{loc: Loc, id: Token, ty: Box<Term>},

    /// FnDef : `fn` FnSig FnBody ;
    /// FIRST = { `fn` }
    /// FOLLOW = { GlobalId, `fn` }
    FnDef{loc: Loc, sig: Box<Term>, body: Box<Term>},

    /// FnSig : GlobalId `(` ParamList `)` FnRet? ;
    /// FIRST = { GlobalId }
    /// FOLLOW = { `{` }
    FnSig{loc: Loc, id: Token, param: Box<Term>, ret: Option<Box<Term>>},

    /// FnRet : `->` TypeDecl ;
    /// FIRST = { `->`, `` }
    /// FOLLOW = { `{` }
    FnRet{loc: Loc, ty: Box<Term>},

    /// ParamList : ( ParamDef ( `,` ParamDef )* )?  ;
    /// FIRST = { LocalId, `` }
    /// FOLLOW = { `)` }
    ParamList{loc: Loc, list: Vec<Term>},

    /// ParamDef : LocalId `:` TypeDecl ;
    /// FIRST = { LocalId }
    /// FOLLOW = { `)`, `,` }
    ParamDef{loc: Loc, id: Token, ty: Box<Term>},

    /// FnBody : `{` BlockDef+ `}` ;
    /// FIRST = { `{` }
    /// FOLLOW = { GlobalId, `fn` }
    FnBody{loc: Loc, bb: Vec<Term>},

    /// BlockDef : LocalId `:` InstrDef+ ;
    /// FIRST = { LocalId }
    /// FOLLOW = { LocalId -> BlockDef, `}` -> FnBody }
    BlockDef{loc: Loc, id: Token, instr: Vec<Term>},

    /// InstrDef : ( AssignInstr | CtrlInstr ) `;` ;
    /// FIRST = { Id -> AssignInstr, Reserved -> CtrlInstr }
    /// FOLLOW = { Id: { `<-` -> AssignInstr, `:` -> BlockDef }, Reserved -> CtrlInstr,
    /// `}` -> FnBody }

    /// AssignInstr : Id `<-` ExprBody ;
    /// FIRST = { Id }
    /// FOLLOW = { `;` }
    AssignInstr{loc: Loc, id: Token, expr: Box<Term>},

    /// ExprBody : ArithExpr | Opd ;
    /// FIRST = { Reserved -> ArithExpr, Opd }
    /// FOLLOW = { `;` }

    /// ArithExpr : Reserved TypeDecl ArithOpd ;
    /// FIRST = { Reserved }
    /// FOLLOW = { `;` }
    ArithExpr{loc: Loc, name: Token, opd: Box<Term>},

    /// ArithOpd :  OpdList | FnCall | PhiList ;
    /// FIRST = { Opd: { `(` -> FnCall, { `,`, `;` } -> OpdList }, `[` -> PhiList }
    /// FOLLOW = { `;` }

    /// CtrlInstr : Reserved CtrlTgt ;
    /// FIRST = { Reserved }
    /// FOLLOW = { `;` }
    CtrlInstr{loc: Loc, name: Token, tgt: Box<Term>},

    /// CtrlTgt : Opd | FnCall | Branch ;
    /// FIRST = { Opd: { `;` -> Opd, `(` -> FnCall, `?` -> Branch } }
    /// FOLLOW = { `;` }

    /// FnCall : GlobalId `(` OpdList `)` ;
    /// FIRST = { GlobalId }
    /// FOLLOW = { `;` }
    FnCall{loc: Loc, func: Token, arg: Vec<Term>},

    /// PhiList : PhiOpd+ ;
    /// FIRST = { `[` }
    /// FOLLOW = { `[`, `;` }
    PhiList{loc: Loc, opd: Vec<Term>},

    /// PhiOpd : `[` LocalId `:` LocalOpd `]`
    /// FIRST = { `[` }
    /// FOLLOW = { `[`, `;` }
    PhiOpd{loc: Loc, bb: Token, opd: Box<Term>},

    /// Branch : Opd `?` LocalId `:` LocalId ;
    /// FIRST = { Opd }
    /// FOLLOW = { `;` }
    Branch{loc: Loc, cond: Token, tr: Token, fls: Token},

    /// OpdList : ( Opd | ( `,` Opd )* )?
    /// FIRST = { Opd, `` }
    /// FOLLOW = { `;` }
    OpdList{loc: Loc, list: Vec<Token>},

    /// Opd : Id | Integer ;
    Opd{loc: Loc, opd: Token},

    /// Id : GlobalId | LocalId

    /// LocalOpd : LocalId | Integer

    /// TypeDecl : Reserved ;
    TypeDecl{loc: Loc, ty: Token},
}