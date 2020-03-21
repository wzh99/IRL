use crate::irc::Loc;

/// Syntactical rules for the language.
/// Technically speaking, this is an LL(2) grammar.
#[derive(Clone, Debug)]
pub enum Term {
    /// Program : ( VarDef | AliasDef | FnDef)* ;
    /// FIRST = { GlobalId -> VarDef, `fn` -> FnDef, `` }
    /// FOLLOW = { EOF }
    Program { def: Vec<Term> },

    /// VarDef : GlobalId ( `<-` Integer )? `:`  TypeDecl `;` ;
    /// FIRST = { GlobalId }
    /// FOLLOW = { GlobalId, `fn`, `type` }
    VarDef { loc: Loc, id: Token, init: Option<Token>, ty: Box<Term> },

    /// TypeAlias : `type` GlobalId `=` TypeDecl `;` ;
    /// FIRST = { `type` }
    /// FOLLOW = { GlobalId, `fn`, `type` }
    AliasDef { loc: Loc, id: Token, ty: Box<Term> },

    /// FnDef : `fn` FnSig FnBody ;
    /// FIRST = { `fn` }
    /// FOLLOW = { GlobalId, `fn`, `type` }
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

    /// InstrDef : ( AssignInstr | NonAssignInstr ) `;` ;
    /// FIRST = { Id -> AssignInstr, Reserved -> NonAssignInstr }
    /// FOLLOW = { Id -> AssignInstr, Label -> BlockDef , Reserved -> NonAssignInstr,
    /// `}` -> FnBody }

    /// AssignInstr : Id `<-` AssignRhs ;
    AssignInstr { loc: Loc, id: Token, rhs: Box<Term> },

    /// AssignRhs : CommonRhs | CallRhs | PhiRhs | PtrRhs | NewRhs ;
    /// FIRST = { `call` -> CallRhs, `phi` -> PhiRhs, `ptr` -> PtrRhs, `new` -> NewRhs,
    ///     Reserved -> CommonRhs }
    /// FOLLOW = { `;` }
    AssignRhs { loc: Loc, rhs: Box<Term> },

    /// CommonRhs : Reserved TypeDecl OpdList ;
    CommonRhs { loc: Loc, name: Token, ty: Box<Term>, opd: Box<Term> },

    /// CallRhs : `call` TypeDecl FnCall ;
    CallRhs { loc: Loc, ty: Box<Term>, call: Box<Term> },

    /// PhiRhs : `phi` TypeDecl PhiList;
    PhiRhs { loc: Loc, ty: Box<Term>, list: Box<Term> },

    /// PtrRhs : `ptr` TypeDecl OpdList IndexList? ;
    PtrRhs { loc: Loc, ty: Box<Term>, opd: Box<Term>, idx: Option<Box<Term>> },

    /// AllocRhs : `alloc` TypeDecl ;
    AllocRhs { loc: Loc, ty: Box<Term> },

    /// NewRhs : `new` ( `[` Integer `]` )? TypeDecl ;
    NewRhs { loc: Loc, ty: Box<Term>, len: Option<Token> },

    /// OpdList : ( Opd ( `,` Opd )* )?
    /// FIRST = { Opd, `` }
    /// FOLLOW = { `;` -> { EvalOpd, CtrlTgt }, `)` -> FnCall, `]` -> IndexList }
    OpdList { loc: Loc, list: Vec<Token> },

    /// IndexList : `[` OpdList `]`
    IndexList { loc: Loc, list: Box<Term> },

    /// FnCall : GlobalId `(` OpdList `)` ;
    FnCall { loc: Loc, func: Token, arg: Box<Term> },

    /// PhiList : PhiOpd+ ;
    /// FIRST = { `[` }
    /// FOLLOW = { `[`, `;` }
    PhiList { loc: Loc, list: Vec<Term> },

    /// PhiOpd : `[` ( Label `:` )? LocalOpd `]`
    PhiOpd { loc: Loc, bb: Option<Token>, opd: Token },

    /// NonAssignInstr : RetInstr | JmpInstr | NoRetCall | BrInstr | StInstr;
    /// FIRST = { `ret` -> RetInstr, `jmp` -> JmpInstr, `call` -> NoRetCall, `br` -> BrInstr,
    ///     `st` -> StInstr }
    /// FOLLOW = { `;` }
    NonAssignInstr { loc: Loc, instr: Box<Term> },

    /// RetInstr : `ret` Opd ;
    RetInstr { loc: Loc, opd: Option<Token> },

    /// NoRetCall : `call` FnCall ;
    NoRetCall { loc: Loc, call: Box<Term> },

    /// JmpInstr : `jmp` Label ;
    JmpInstr { loc: Loc, tgt: Token },

    /// BrInstr : `br` Opd `?` Label `:` Label ;
    BrInstr { loc: Loc, cond: Token, tr: Token, fls: Token },

    /// StInstr : `st` TypeDecl Opd `->` Opd ;
    StInstr { loc: Loc, ty: Box<Term>, src: Token, dst: Token },

    /// Id : GlobalId | LocalId ;

    /// LocalOpd : LocalId | Integer ;

    /// TypeDecl : PrimType | AliasName | PtrType | ArrayType | StructType
    /// FIRST = { Reserved -> PrimType, GlobalId -> AliasName, `*` -> PtrType, `[` -> ArrayType,
    ///     `{` -> StructType }
    /// FOLLOW = { `;` -> { AliasDef, VarDef }, `,` -> { ParamList, TypeList }, `)` -> FnSig,
    ///     Opd -> { CommonRhs, PtrRhs }, GlobalId -> CallRhs, `[` -> PhiRhs  `;` -> AssignRhs
    /// }
    TypeDecl { loc: Loc, ty: Box<Term> },

    /// PrimType : Reserved ;
    PrimType { loc: Loc, ty: Token },

    /// AliasName : GlobalId ;
    AliasName { loc: Loc, id: Token },

    /// PtrType : `*` TypeDecl ;
    PtrType { loc: Loc, tgt: Box<Term> },

    /// ArrayType : `[` Integer `]` TypeDecl ;
    ArrayType { loc: Loc, len: Token, elem: Box<Term> },

    /// StructType : `{` TypeList `}` ;
    StructType { loc: Loc, field: Box<Term> },

    /// TypeList : ( TypeDecl | ( `,` TypeDecl )* )?
    /// FIRST = { Reserved, GlobalId, `*`, `[`, `{`, `` }
    /// FOLLOW = { `}` }
    TypeList { loc: Loc, list: Vec<Term> },
}

/// Lexical rules for the language.
#[derive(Clone, Debug)]
pub enum Token {
    /// Global identifier `/@[A-Za-z0-9._]+/`
    GlobalId(Loc, String),
    /// Local identifier `/$[A-Za-z0-9._]/`
    LocalId(Loc, String),
    /// Label `/%[A-Za-z0-9_]+/`
    Label(Loc, String),
    /// Reserved words `/[A-Za-z_][A-Za-z0-9._]*/`
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
    /// Asterisk, for representing pointer type `*`
    Asterisk(Loc),
    /// Equal, for type alias declaration `=`
    Equal(Loc),
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
            Token::Asterisk(_) => "*".to_string(),
            Token::Equal(_) => "=".to_string(),
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
            Token::Comma(l) | Token::Semicolon(l)
            | Token::Colon(l) | Token::Question(l)
            | Token::Asterisk(l) | Token::Equal(l)
            | Token::LeftParent(l) | Token::RightParent(l)
            | Token::LeftSquare(l) | Token::RightSquare(l)
            | Token::LeftCurly(l) | Token::RightCurly(l)
            | Token::LeftArrow(l) | Token::RightArrow(l)
            | Token::Comment(l)
            | Token::Eof(l) => l.clone()
        }
    }
}
