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
    Signature(SignatureDecl),
    Clause(Clause),
}

/// `Name = Type`: a second spelling of a type, which mints nothing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AliasDecl {
    pub span: Span,
    pub name: Name,
    pub ty: Type,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HeaderKind {
    Package,
}

/// A package root, `package {}`.
///
/// Dependency entries will be added when package dependency syntax is needed;
/// an empty header already establishes the root boundary. Whether a package
/// builds a binary is whether its entry defines `main!`, not its header.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HeaderDecl {
    pub span: Span,
    pub kind: HeaderKind,
}

/// `import foo.bar {Name Other.* source: local}`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ImportDecl {
    pub span: Span,
    pub path: Vec<Name>,
    pub exposures: Vec<Exposure>,
}

/// `exports {Name Other.*}`.
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

/// `Name(a) : [First Second(a)].(methods)` or `Name : Repr.(methods)`.
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

/// A signature such as `add : Nat Nat -> Nat where Hashable(a)`.
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
    /// `a.add : a a -> a`, a method every type `a` stands for must have; or
    /// `a.zero : a`, a value it must supply, read as `a.zero()`.
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
    /// `{x: T}`, or with `*`, `{x: T *}`: a record with at least these
    /// fields, whatever else a caller's has.
    Record {
        span: Span,
        fields: Vec<(Name, Self)>,
        open: bool,
    },
    /// `(A B)`: a positional product of two or more.
    Tuple { span: Span, members: Vec<Self> },
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Body {
    pub bindings: Vec<Binding>,
    pub result: Expr,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Binding {
    pub pattern: Pattern,
    pub value: Expr,
}

/// A written integer. Its type and magnitude are deliberately not decided by
/// parsing; `span` retains every digit and radix marker for later elaboration.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Numeral {
    pub span: Span,
    pub kind: NumeralKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NumeralKind {
    Number,
    Character,
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
    Range {
        span: Span,
        start: Numeral,
        end: Numeral,
    },
    List {
        span: Span,
        elements: Vec<Self>,
        rest: Option<Box<Self>>,
    },
    /// `{x}`, or with `*`, `{x *}`: naming some fields and ignoring the rest.
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
    /// `{x: e *base}`: `base` with the fields named replaced.
    Update(Vec<(Name, Expr)>, Box<Expr>),
    /// `(a b)`: a positional product of two or more.
    Tuple(Vec<Expr>),
    Lambda(Vec<Pattern>, Box<Expr>),
    Call(Box<Expr>, Vec<Expr>),
    Member(Box<Expr>, Name),
    Method(Box<Expr>, Name, Vec<Expr>),
    Unary(UnaryOp, Box<Expr>),
    Binary(BinaryOp, Box<Expr>, Box<Expr>),
    /// `value?`: an `Ok`'s value, or the `Err` answered at once.
    Try(Box<Expr>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StringPart {
    /// Raw source text, including any written escapes. Decoding is explicit so
    /// parsing a large source does not allocate a second copy of every string.
    Text(Span),
    Splice(Expr),
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
