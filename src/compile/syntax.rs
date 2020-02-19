use crate::compile::Loc;

/// Lexical rules for the language.
#[derive(Clone, Debug)]
pub enum Token {
    /// Global identifier `/@[A-Za-z0-9_]+/`
    GlobalId(Loc, String),
    /// Local identifier `/$[A-Za-z0-9_]+(.[0-9]+)?/`
    LocalId(Loc, String),
    /// Label `/%[A-Za-z0-9_]+/`
    Label(Loc, String),
    /// Reserved words `/[A-Za-z_][A-Za-z0-9_]*/`
    Reserved(Loc, String),
    /// Integer `/-?[0-9]+/`
    Integer(Loc, String),
    /// Comma, for separating list elements `,`
    Comma(Loc),
    /// Colon, separating label and value in phi instruction `:`
    Colon(Loc),
    /// Semicolon, ending indication of one instruction `;`
    Semicolon(Loc),
    /// Question mark, used in `br` instruction `?`
    Question(Loc),
    /// Left parenthesis `(`
    LeftParent(Loc),
    /// Right parenthesis  `)`
    RightParent(Loc),
    /// Left square bracket `[`
    LeftSquare(Loc),
    /// Right square bracket `]`
    RightSquare(Loc),
    /// Left curly bracket `{`
    LeftCurly(Loc),
    /// Right curly bracket `}`
    RightCurly(Loc),
    /// Left arrow, for assignment `<-`
    LeftArrow(Loc),
    /// Right arrow, used in function type `->`
    RightArrow(Loc),
    /// Comment `//`
    Comment(Loc),
    /// End-of-file indicator
    Eof(Loc),
}

impl ToString for Token {
    fn to_string(&self) -> String {
        match self {
            Token::GlobalId(_, s) | Token::LocalId(_, s) | Token::Label(_, s)
            | Token::Reserved(_, s) | Token::Integer(_, s) => s.clone(),
            Token::Comma(_) => ",".to_string(),
            Token::Colon(_) => ":".to_string(),
            Token::Semicolon(_) => ";".to_string(),
            Token::Question(_) => "?".to_string(),
            Token::LeftParent(_) => "(".to_string(),
            Token::RightParent(_) => ")".to_string(),
            Token::LeftSquare(_) => "[".to_string(),
            Token::RightSquare(_) => "]".to_string(),
            Token::LeftCurly(_) => "{".to_string(),
            Token::RightCurly(_) => "}".to_string(),
            Token::LeftArrow(_) => "<-".to_string(),
            Token::RightArrow(_) => "->".to_string(),
            Token::Comment(_) => "//".to_string(),
            Token::Eof(_) => "".to_string()
        }
    }
}

impl Token {
    pub fn len(&self) -> usize { self.to_string().len() }

    pub fn is_id(&self) -> bool {
        match self {
            Token::GlobalId(_, _) | Token::LocalId(_, _) => true,
            _ => false
        }
    }

    pub fn is_local_opd(&self) -> bool {
        match self {
            Token::LocalId(_, _) | Token::Integer(_, _) => true,
            _ => false
        }
    }

    pub fn is_opd(&self) -> bool {
        match self {
            Token::GlobalId(_, _) | Token::LocalId(_, _) | Token::Integer(_, _) => true,
            _ => false
        }
    }

    pub fn loc(&self) -> Loc {
        match self {
            Token::GlobalId(l, _) | Token::LocalId(l, _) | Token::Label(l, _)
            | Token::Reserved(l, _) | Token::Integer(l, _) => l.clone(),
            Token::Comma(l) | Token::Colon(l) | Token::Semicolon(l) | Token::Question(l)
            | Token::LeftParent(l) | Token::RightParent(l) | Token::LeftSquare(l)
            | Token::RightSquare(l) | Token::LeftCurly(l) | Token::RightCurly(l)
            | Token::LeftArrow(l) | Token::RightArrow(l) | Token::Comment(l)
            | Token::Eof(l) => l.clone()
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
    Program { def: Vec<Term> },

    /// VarDef : GlobalId ( `<-` Integer )? `:`  TypeDecl `;` ;
    /// FIRST = { GlobalId }
    /// FOLLOW = { GlobalId, `fn` }
    VarDef { loc: Loc, id: Token, init: Option<Token>, ty: Box<Term> },

    /// FnDef : `fn` FnSig FnBody ;
    /// FIRST = { `fn` }
    /// FOLLOW = { GlobalId, `fn` }
    FnDef { loc: Loc, sig: Box<Term>, body: Box<Term> },

    /// FnSig : GlobalId `(` ParamList `)` FnRet? ;
    /// FIRST = { GlobalId }
    /// FOLLOW = { `{` }
    FnSig { loc: Loc, id: Token, param: Box<Term>, ret: Option<Box<Term>> },

    /// FnRet : `->` TypeDecl ;
    /// FIRST = { `->`, `` }
    /// FOLLOW = { `{` }
    FnRet { loc: Loc, ty: Box<Term> },

    /// ParamList : ( ParamDef ( `,` ParamDef )* )?  ;
    /// FIRST = { LocalId, `` }
    /// FOLLOW = { `)` }
    ParamList { loc: Loc, list: Vec<Term> },

    /// ParamDef : LocalId `:` TypeDecl ;
    /// FIRST = { LocalId }
    /// FOLLOW = { `)`, `,` }
    ParamDef { loc: Loc, id: Token, ty: Box<Term> },

    /// FnBody : `{` BlockDef+ `}` ;
    /// FIRST = { `{` }
    /// FOLLOW = { GlobalId, `fn` }
    FnBody { loc: Loc, bb: Vec<Term> },

    /// BlockDef : Label `:` InstrDef+ ;
    /// FIRST = { Label }
    /// FOLLOW = { Label -> BlockDef, `}` -> FnBody }
    BlockDef { loc: Loc, id: Token, instr: Vec<Term> },

    /// InstrDef : ( AssignInstr | CtrlInstr ) `;` ;
    /// FIRST = { Id -> AssignInstr, Reserved -> CtrlInstr }
    /// FOLLOW = { Id -> AssignInstr, Label -> BlockDef , Reserved -> CtrlInstr,
    /// `}` -> FnBody }

    /// AssignInstr : Id `<-` AssignRhs ;
    /// FIRST = { Id }
    /// FOLLOW = { `;` }
    AssignInstr { loc: Loc, id: Token, rhs: Box<Term> },

    /// AssignRhs : Reserved TypeDecl ArithOpd ;
    /// FIRST = { Reserved }
    /// FOLLOW = { `;` }
    AssignRhs { loc: Loc, name: Token, ty: Box<Term>, opd: Box<Term> },

    /// ArithOpd :  OpdList | FnCall | PhiList ;
    /// FIRST = { Opd: { { `,`, `;` } -> OpdList, `(` -> FnCall }, `[` -> PhiList }
    /// FOLLOW = { `;` }

    /// OpdList : ( Opd | ( `,` Opd )* )?
    /// FIRST = { Opd, `` }
    /// FOLLOW = { `;` -> { ArithOpd, CtrlTgt}, `)` -> FnCall }
    OpdList { loc: Loc, list: Vec<Token> },

    /// FnCall : GlobalId `(` OpdList `)` ;
    /// FIRST = { GlobalId }
    /// FOLLOW = { `;` }
    FnCall { loc: Loc, func: Token, arg: Box<Term> },

    /// PhiList : PhiOpd+ ;
    /// FIRST = { `[` }
    /// FOLLOW = { `[`, `;` }
    PhiList { loc: Loc, list: Vec<Term> },

    /// PhiOpd : `[` ( Label `:` )? LocalOpd `]`
    /// FIRST = { `[` }
    /// FOLLOW = { `[`, `;` }
    PhiOpd { loc: Loc, bb: Option<Token>, opd: Token },

    /// CtrlInstr : RetInstr | JmpInstr | `call` FnCall | BrInstr ;
    /// FIRST = { `ret` -> RetInstr, `jmp` -> JmpInstr, `br` -> BrInstr }
    /// FOLLOW = { `;` }
    CtrlInstr { loc: Loc, instr: Box<Term> },

    /// RetInstr : `ret` Opd
    /// FIRST = { `ret` }
    /// FOLLOW = { `;` }
    RetInstr { loc: Loc, opd: Option<Token> },

    /// JmpInstr : `jmp` Label
    /// FIRST = { `jmp` }
    /// FOLLOW = { `;` }
    JmpInstr { loc: Loc, tgt: Token },

    /// Branch : `br` Opd `?` Label `:` Label ;
    /// FIRST = { Opd }
    /// FOLLOW = { `;` }
    BrInstr { loc: Loc, cond: Token, tr: Token, fls: Token },

    /// Id : GlobalId | LocalId

    /// LocalOpd : LocalId | Integer

    /// TypeDecl : Reserved ;
    TypeDecl { loc: Loc, ty: Token },
}