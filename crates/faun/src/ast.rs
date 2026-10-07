//! Syntax retained by the Ori-compatible frontend.
//!
//! Parsed modules own a source identity, while names and literals retain
//! compact byte ranges into that source. Resolution replaces these ranges with
//! interned symbols; the parser does not allocate a string for every name.

use super::source::SourceId;

/// A half-open byte range in one source file.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Span {
    pub start: u32,
    pub end: u32,
}

impl Span {
    pub(crate) fn new(start: usize, end: usize) -> Self {
        Self {
            start: u32::try_from(start).expect("source is smaller than 4 GiB"),
            end: u32::try_from(end).expect("source is smaller than 4 GiB"),
        }
    }

    /// Return the source text covered by this span.
    ///
    /// # Panics
    ///
    /// Panics when the span did not come from `source`.
    #[must_use]
    pub fn text(self, source: &str) -> &str {
        let start = usize::try_from(self.start).expect("u32 fits usize");
        let end = usize::try_from(self.end).expect("u32 fits usize");
        &source[start..end]
    }

    pub(crate) const fn through(self, end: Self) -> Self {
        Self {
            start: self.start,
            end: end.end,
        }
    }
}

/// A name written in the source.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Name(pub Span);

impl Name {
    /// Return this name's spelling.
    ///
    /// # Panics
    ///
    /// Panics when the name did not come from `source`.
    #[must_use]
    pub fn text(self, source: &str) -> &str {
        self.0.text(source)
    }
}

/// A parsed source file, before name resolution or type checking.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Module {
    pub source: SourceId,
    pub items: Vec<Item>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Item {
    Header(HeaderDecl),
    Import(ImportDecl),
    Exports(ExportsDecl),
    Data(DataDecl),
    Alias(AliasDecl),
    Constraints(ConstraintAliasDecl),
    Signature(SignatureDecl),
    Clause(Clause),
    /// `expect body`: a claim the module makes of its definitions, which
    /// `faun test` runs. It is a clause of no parameters answering a `Bool`,
    /// named by its `expect` keyword.
    Expect(Clause),
}

/// `Name = Type`, or `Name(a) = Type`: a second spelling of a type, which
/// mints nothing. Where it has parameters, each use applies it to as many
/// types.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AliasDecl {
    pub span: Span,
    pub name: Name,
    pub params: Vec<Name>,
    pub ty: Type,
}

/// `Name(a) = where ...`: a name for requirements a `where` clause may
/// apply together, which is no type and mints nothing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConstraintAliasDecl {
    pub span: Span,
    pub name: Name,
    pub parameters: Vec<Name>,
    pub constraints: Vec<Constraint>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HeaderKind {
    Package,
}

/// A package root, `package {}`, and the packages it depends on,
/// `package {md5: "../md5/src/md5"}`.
///
/// Whether a package builds a binary is whether its entry defines `main!`,
/// not its header.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HeaderDecl {
    pub span: Span,
    pub kind: HeaderKind,
    pub dependencies: Vec<Dependency>,
}

/// `name: "path"`: the package whose root module is at `path`, a module
/// base relative to the header's file, imported as `name`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Dependency {
    pub span: Span,
    pub name: Name,
    /// The path's text, as written, escapes and all.
    pub path: Vec<Span>,
}

/// `import foo.bar {Name, Other.*, source: local}`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ImportDecl {
    pub span: Span,
    pub path: Vec<Name>,
    pub exposures: Vec<Exposure>,
}

/// `export {Name, Other.*}`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExportsDecl {
    pub span: Span,
    pub exports: Vec<Export>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Exposure {
    pub exported: Name,
    pub local: Name,
    pub constructors: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Export {
    pub name: Name,
    pub constructors: bool,
}

/// `Name(a) : [First, Second(a)].(methods)` or `Name : Repr.(methods)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DataDecl {
    pub span: Span,
    pub name: Name,
    pub params: Vec<Name>,
    pub representation: DataRepresentation,
    pub methods: Vec<MethodItem>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DataRepresentation {
    Sum(Vec<ConstructorDecl>),
    Wrapper(Type),
}

impl DataDecl {
    #[must_use]
    pub fn constructors(&self) -> &[ConstructorDecl] {
        match &self.representation {
            DataRepresentation::Sum(constructors) => constructors,
            DataRepresentation::Wrapper(_) => &[],
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConstructorDecl {
    pub name: Name,
    pub fields: Vec<Type>,
}

/// A method-block item. Module directives and nested types cannot occur here.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MethodItem {
    Signature(SignatureDecl),
    Clause(Clause),
}

/// A signature such as `add : (Nat, Nat) -> Nat where Hashable(a)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SignatureDecl {
    pub span: Span,
    pub name: Name,
    pub parameters: Vec<Type>,
    pub result: Type,
    pub constraints: Vec<Constraint>,
}

/// One requirement in a `where` clause.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Constraint {
    /// `a.add : (a, a) -> a`, a method every type `a` stands for must have; or
    /// `a.zero : a`, a value it must supply, read as `a.zero`.
    Member {
        span: Span,
        variable: Name,
        member: Name,
        parameters: Vec<Type>,
        result: Type,
    },
    /// `Summable(a)`: a named conjunction of requirements, applied.
    Alias {
        span: Span,
        name: Name,
        arguments: Vec<Type>,
    },
}

impl Constraint {
    #[must_use]
    pub const fn span(&self) -> Span {
        match self {
            Self::Member { span, .. } | Self::Alias { span, .. } => *span,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    Named {
        span: Span,
        name: Name,
        arguments: Vec<Self>,
    },
    Function {
        span: Span,
        parameters: Vec<Self>,
        result: Box<Self>,
    },
    Variants {
        span: Span,
        constructors: Vec<ConstructorDecl>,
    },
    /// `{x: T}`, or with `*`, `{x: T, *}`: a record with at least these
    /// fields, whatever else a caller's has.
    Record {
        span: Span,
        fields: Vec<(Name, Self)>,
        open: bool,
    },
    /// `(A, B)`: a positional product of two or more.
    Tuple { span: Span, members: Vec<Self> },
    /// `_`: in a function's signature, whatever its clauses make it.
    Hole { span: Span },
}

/// One `name(patterns) if guard -> body` row. Consecutive rows are grouped later.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Clause {
    pub span: Span,
    pub name: Name,
    pub patterns: Vec<Pattern>,
    pub guard: Option<Expr>,
    pub body: Body,
}

/// `pattern if guard -> body`: one way an `is` with arms goes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Arm {
    pub pattern: Pattern,
    pub guard: Option<Expr>,
    pub body: Expr,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Body {
    pub bindings: Vec<Binding>,
    pub result: Expr,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Binding {
    pub pattern: Pattern,
    pub value: Expr,
    /// Written as a line of its own, whose answer nothing keeps: an effect
    /// asked for what it does.
    pub discarded: bool,
}

/// A written integer. Its type and magnitude are deliberately not decided by
/// parsing; `span` retains every digit and radix marker for later elaboration.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Numeral {
    pub span: Span,
    pub kind: NumeralKind,
}

/// One end of a range: a numeral, negated or not.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Bound {
    pub numeral: Numeral,
    pub negative: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NumeralKind {
    Number,
    Character,
    /// `1.5` or `1.0e-12`: digits either side of a point, a float's.
    Decimal,
}

impl Numeral {
    #[must_use]
    pub fn text(self, source: &str) -> &str {
        self.span.text(source)
    }

    #[must_use]
    pub fn radix(self, source: &str) -> u32 {
        let text = self.text(source);
        if text.starts_with("0x") {
            16
        } else if text.starts_with("0b") {
            2
        } else {
            10
        }
    }

    #[must_use]
    pub fn digits(self, source: &str) -> &str {
        let text = self.text(source);
        text.strip_prefix("0x")
            .or_else(|| text.strip_prefix("0b"))
            .unwrap_or(text)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Pattern {
    Wild(Span),
    Bind(Name),
    Constructor {
        span: Span,
        /// The type a qualified `Type.Ctor` names its constructor through.
        qualifier: Option<Name>,
        name: Name,
        fields: Vec<Self>,
    },
    Number {
        span: Span,
        numeral: Numeral,
        negative: bool,
    },
    /// `lo..hi`, either end `_` to leave that side open.
    Range {
        span: Span,
        start: Option<Bound>,
        end: Option<Bound>,
    },
    List {
        span: Span,
        elements: Vec<Self>,
        rest: Option<Box<Self>>,
    },
    /// A list's rest with elements after it, `*front, a, b`: a list ending
    /// in `a` and `b`, what comes before them matched by `front`.
    Ending {
        span: Span,
        front: Box<Self>,
        last: Vec<Self>,
    },
    /// `{x}`, or with `*`, `{x, *}`: naming some fields and ignoring the rest.
    Record {
        span: Span,
        fields: Vec<(Name, Self)>,
        open: bool,
    },
    Tuple {
        span: Span,
        members: Vec<Self>,
    },
    /// `"get"`: a string with no splice, matched by equality.
    String {
        span: Span,
        parts: Vec<Span>,
    },
    /// `==name`: a value equal, by its type's `equals`, to `name`.
    Equal {
        span: Span,
        name: Name,
    },
    /// `name is pattern`: the whole value named, and taken apart.
    As {
        span: Span,
        name: Name,
        pattern: Box<Self>,
    },
    /// `A | B`: either alternative, each binding the same names. Only a
    /// clause's parameters take one.
    Or {
        span: Span,
        alternatives: Vec<Self>,
    },
}

impl Pattern {
    #[must_use]
    pub const fn span(&self) -> Span {
        match self {
            Self::Wild(span)
            | Self::Bind(Name(span))
            | Self::Constructor { span, .. }
            | Self::Number { span, .. }
            | Self::Range { span, .. }
            | Self::List { span, .. }
            | Self::Ending { span, .. }
            | Self::Record { span, .. }
            | Self::Tuple { span, .. }
            | Self::String { span, .. }
            | Self::As { span, .. }
            | Self::Equal { span, .. }
            | Self::Or { span, .. } => *span,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Expr {
    pub span: Span,
    pub kind: ExprKind,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExprKind {
    Name(Name),
    Number(Numeral),
    String(Vec<StringPart>),
    List(Vec<Expr>, Option<Box<Expr>>),
    Record(Vec<(Name, Expr)>),
    /// `{x: e, *base}`: `base` with the fields named replaced.
    Update(Vec<(Name, Expr)>, Box<Expr>),
    /// `(a, b)`: a positional product of two or more.
    Tuple(Vec<Expr>),
    Lambda(Vec<Pattern>, Box<Expr>),
    Call(Box<Expr>, Vec<Expr>),
    Member(Box<Expr>, Name),
    Method(Box<Expr>, Name, Vec<Expr>),
    Unary(UnaryOp, Box<Expr>),
    Binary(BinaryOp, Box<Expr>, Box<Expr>),
    /// `value?`: an `Ok`'s value, or the `Err` answered at once.
    Try(Box<Expr>),
    /// `if condition then yes else no`: only the branch the condition
    /// chooses is worked out.
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    /// `value is pattern`: whether it matches, binding the pattern's names
    /// where it is known to have.
    Is(Box<Expr>, Pattern),
    /// `value is ( arms )`: the first arm whose pattern matches and whose
    /// guard holds answers, what both bind seen by its body.
    Match(Box<Expr>, Vec<Arm>),
    /// `( pattern -> value` … `)`: arms, read before an `is` takes them,
    /// and refused by the parser wherever no `is` does.
    Arms(Vec<Arm>),
    /// A block's line `condition else otherwise`, holding the lines after
    /// it: where the condition holds, those lines answer, seeing what it
    /// bound; where it fails, `otherwise` leaves.
    Else {
        condition: Box<Expr>,
        otherwise: Box<Expr>,
        rest: Box<Body>,
    },
    /// `return value`: the answer of the clause or lambda, which stands
    /// only where a line's `else` leaves.
    Return(Box<Expr>),
    /// `(x = f(y)` … `x + 1)`: bindings, then the answer, in parentheses.
    /// Its names are seen by its later lines and its answer alone.
    Block(Box<Body>),
    /// `_`, or a rest with nothing after its `*`: read as an expression
    /// before its line says it is a pattern, and refused by the parser
    /// wherever it is not one, so it never leaves the parser.
    Wild,
    /// `==name`: as `Wild`, a pattern's alone, matching a value equal to
    /// `name`.
    Equal(Name),
    /// `1..9`, or `_..-1`: as `Wild`, a pattern's alone, which never leaves
    /// the parser. An end written `_` is open.
    Range(Option<Bound>, Option<Bound>),
    /// `*front, a, b` as a list's rest: a list ending in `a` and `b`, what
    /// comes before them `front`. As `Wild`, a pattern's alone.
    Ending(Box<Expr>, Vec<Expr>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StringPart {
    /// Raw source text, including any written escapes. Decoding is explicit so
    /// parsing a large source does not allocate a second copy of every string.
    Text(Span),
    /// `${value}`, or `${value:>7}` with its text padded to a width.
    Splice(Expr, Option<Width>),
}

/// A splice's `:<12` or `:>7`: its text padded with spaces to at
/// least `columns` characters, on the side `align` leaves free.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Width {
    pub align: Align,
    pub columns: Numeral,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Align {
    Left,
    Right,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnaryOp {
    Negate,
    Not,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinaryOp {
    Or,
    Xor,
    And,
    Equal,
    NotEqual,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
    Add,
    Subtract,
    Multiply,
    Divide,
    Remainder,
}
