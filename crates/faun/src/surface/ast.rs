//! Syntax retained by the Ori-compatible frontend.
//!
//! Names are source spans rather than allocated strings. A parsed module is
//! therefore cheap to build and callers resolve spelling against the source
//! text only when they need it.

/// A half-open byte range in one source file.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
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
    pub items: Vec<Item>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Item {
    Data(DataDecl),
    Signature(SignatureDecl),
    Clause(Clause),
}

/// `Name(a) : [First Second(a)]`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DataDecl {
    pub span: Span,
    pub name: Name,
    pub params: Vec<Name>,
    pub constructors: Vec<ConstructorDecl>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConstructorDecl {
    pub name: Name,
    pub fields: Vec<Type>,
}

/// A first-order signature such as `add : Nat Nat -> Nat`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SignatureDecl {
    pub span: Span,
    pub name: Name,
    pub parameters: Vec<Type>,
    pub result: Type,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    Named {
        span: Span,
        name: Name,
        arguments: Vec<Self>,
    },
}

/// One `name(patterns) -> body` row. Consecutive rows are grouped later.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Clause {
    pub span: Span,
    pub name: Name,
    pub patterns: Vec<Pattern>,
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Pattern {
    Wild(Span),
    Bind(Name),
    Constructor {
        span: Span,
        name: Name,
        fields: Vec<Self>,
    },
    Number {
        span: Span,
        negative: bool,
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
    Number,
    Call(Box<Expr>, Vec<Expr>),
    Method(Box<Expr>, Name, Vec<Expr>),
    Unary(UnaryOp, Box<Expr>),
    Binary(BinaryOp, Box<Expr>, Box<Expr>),
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
