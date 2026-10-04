//! The grammar of `grammar.ebnf`, read by recursive descent.
//!
//! A file is lines, each one item. A line begins with a keyword, a type's
//! name, or an expression, and the token after that expression says what the
//! line is; [`lines`](super::lines) makes the heads that are patterns into
//! patterns. A body of several lines is a block, `(` … `)`, read as an
//! expression, so a line is whole when it is read. Every choice is made by the
//! next token. Each rule of the file is a method here, and the `ebnf` tests
//! check that the file is LL(1) and that this reads what it does.
//!
//! A line that cannot be read is an error, and reading goes on from the next
//! line, so one file's errors are all found at once.

use super::ast::{
    Align, BinaryOp, Bound, Constraint, ConstructorDecl, Dependency, Export, ExportsDecl, Exposure,
    Expr, ExprKind, HeaderDecl, HeaderKind, ImportDecl, Name, Numeral, NumeralKind, Span,
    StringPart, Type, UnaryOp, Width,
};
use super::diagnostic::{Advice, Advised};
use super::lex::{Kind, Token};
use super::lines::{self, Line, Statement, Typed};

/// Why a line could not be read.
#[derive(Debug)]
pub(crate) struct SyntaxError {
    pub(crate) span: Span,
    pub(crate) message: String,
    pub(crate) advice: Advice,
}

impl SyntaxError {
    fn new(span: Span, message: impl Into<String>) -> Self {
        Self {
            span,
            message: message.into(),
            advice: Advice::default(),
        }
    }
}

impl Advised for SyntaxError {
    fn advice(&mut self) -> &mut Advice {
        &mut self.advice
    }
}

impl From<lines::Error> for SyntaxError {
    fn from(error: lines::Error) -> Self {
        Self {
            span: error.span,
            message: error.message,
            advice: error.advice,
        }
    }
}

type Parsed<T> = Result<T, SyntaxError>;

/// The lines of the file `tokens` lex, and the error of each line that
/// could not be read.
pub(crate) fn file(tokens: &[Token], source: &str) -> (Vec<Line>, Vec<SyntaxError>) {
    let mut parser = Parser {
        tokens,
        source,
        at: 0,
        expected: Vec::new(),
        errors: Vec::new(),
    };
    let lines = parser.lines(false);
    (lines, parser.errors)
}

struct Parser<'a> {
    tokens: &'a [Token],
    source: &'a str,
    at: usize,
    /// What was looked for at the current token, for the message if none
    /// of it is there.
    expected: Vec<&'static str>,
    errors: Vec<SyntaxError>,
}

/// The binding strength of an infix operator, loosest first, and what it
/// makes.
const fn infix(kind: Kind) -> Option<(u8, BinaryOp)> {
    Some(match kind {
        Kind::Bar => (1, BinaryOp::Or),
        Kind::Caret => (2, BinaryOp::Xor),
        Kind::Amp => (3, BinaryOp::And),
        Kind::EqEq => (4, BinaryOp::Equal),
        Kind::Ne => (4, BinaryOp::NotEqual),
        Kind::Lt => (4, BinaryOp::Less),
        Kind::Le => (4, BinaryOp::LessEqual),
        Kind::Gt => (4, BinaryOp::Greater),
        Kind::Ge => (4, BinaryOp::GreaterEqual),
        Kind::Plus => (5, BinaryOp::Add),
        Kind::Minus => (5, BinaryOp::Subtract),
        Kind::Slash => (6, BinaryOp::Divide),
        Kind::Percent => (6, BinaryOp::Remainder),
        Kind::Star => (6, BinaryOp::Multiply),
        _ => return None,
    })
}

/// Whether an expression can begin with `kind`.
const fn begins_expr(kind: Kind) -> bool {
    matches!(
        kind,
        Kind::Minus
            | Kind::Bang
            | Kind::Number
            | Kind::Char
            | Kind::Decimal
            | Kind::Wild
            | Kind::StrStart
            | Kind::LBracket
            | Kind::LBrace
            | Kind::LParen
            | Kind::TypeIdent
            | Kind::Ident
            | Kind::EffectIdent
            | Kind::KwIf
    )
}

/// Whether a type can begin with `kind`.
const fn begins_type(kind: Kind) -> bool {
    matches!(
        kind,
        Kind::TypeIdent | Kind::Ident | Kind::Wild | Kind::LParen | Kind::LBracket | Kind::LBrace
    )
}

/// Whether `kind` is a name of any sort.
const fn is_name(kind: Kind) -> bool {
    matches!(kind, Kind::Ident | Kind::EffectIdent | Kind::TypeIdent)
}

impl Parser<'_> {
    fn peek(&self) -> Kind {
        self.tokens[self.at].kind
    }

    /// Take the current token, which the end of the file never gives up.
    fn bump(&mut self) -> Token {
        let token = self.tokens[self.at];
        if token.kind != Kind::Eof {
            self.at += 1;
        }
        self.expected.clear();
        token
    }

    fn eat(&mut self, kind: Kind) -> Option<Token> {
        (self.peek() == kind).then(|| self.bump())
    }

    /// Take a `kind`, said as `what` where it is missing.
    fn expect(&mut self, kind: Kind, what: &'static str) -> Parsed<Token> {
        self.eat(kind).ok_or_else(|| {
            self.note(what);
            self.fail()
        })
    }

    /// Note that a type was looked for at the current token.
    fn note_type_starts(&mut self) {
        for what in ["a type name", "a name", "`_`", "`(`", "`[`", "`{`"] {
            self.note(what);
        }
    }

    /// Note that `what` was looked for at the current token.
    fn note(&mut self, what: &'static str) {
        if !self.expected.contains(&what) {
            self.expected.push(what);
        }
    }

    /// `xs = x [ "," [ xs ] ]`, or nothing where it is not `required`: an
    /// `item` wherever one `begins`, commas between, and perhaps one after,
    /// which is said with the items.
    fn separated<T>(
        &mut self,
        required: bool,
        begins: fn(Kind) -> bool,
        what: &'static str,
        mut item: impl FnMut(&mut Self) -> Parsed<T>,
    ) -> Parsed<(Vec<T>, bool)> {
        let mut items = Vec::new();
        while required && items.is_empty() || begins(self.peek()) {
            items.push(item(self)?);
            if self.eat(Kind::Comma).is_none() {
                self.note("`,`");
                return Ok((items, false));
            }
        }
        self.note(what);
        let trailing = !items.is_empty();
        Ok((items, trailing))
    }

    /// Why the current token cannot be read: what was looked for, or what
    /// is wrong with the token itself.
    fn fail(&self) -> SyntaxError {
        let token = self.tokens[self.at];
        let text = token.text(self.source);
        let message = match token.kind {
            Kind::Error if token.start == token.end => "unterminated string literal".to_owned(),
            Kind::Error => format!("invalid token `{text}`"),
            Kind::Detached if matches!(text, "." | "..") => {
                format!("`{text}` goes against what it joins: no space around it")
            }
            Kind::Detached => format!("`{text}` goes against what it follows: no space before it"),
            kind => {
                let mut expected = self.expected.clone();
                expected.sort_unstable();
                let wanted = match expected.as_slice() {
                    [] => "something else".to_owned(),
                    [one] => (*one).to_owned(),
                    many => format!("one of {}", many.join(", ")),
                };
                match kind {
                    Kind::Eof => format!("expected {wanted} before the end of the file"),
                    Kind::Newline => format!("expected {wanted} before the end of the line"),
                    _ => format!("expected {wanted}, found `{text}`"),
                }
            }
        };
        SyntaxError::new(token.span(), message)
    }

    /// Lines up to the end of the file, or of a method block, each read or
    /// its error kept and the rest of it passed over.
    fn lines(&mut self, block: bool) -> Vec<Line> {
        let mut lines = Vec::new();
        loop {
            match self.peek() {
                Kind::Eof => return lines,
                Kind::RParen if block => return lines,
                Kind::Newline => {
                    self.bump();
                    continue;
                }
                _ => {}
            }
            match self
                .line()
                .and_then(|line| self.line_end(block).map(|()| line))
            {
                Ok(line) => lines.push(line),
                Err(error) => {
                    self.errors.push(error);
                    self.pass_line(block);
                }
            }
        }
    }

    fn line_end(&mut self, block: bool) -> Parsed<()> {
        match self.peek() {
            Kind::Newline | Kind::Eof => Ok(()),
            Kind::RParen if block => Ok(()),
            _ => {
                self.note("a new line");
                self.note(if block { "`)`" } else { "the end of the file" });
                Err(self.fail())
            }
        }
    }

    /// Pass over what is left of a line that could not be read, up to its
    /// newline, the end of the file, or the method block it is in.
    fn pass_line(&mut self, block: bool) {
        let mut depth = 0_usize;
        loop {
            match self.peek() {
                Kind::Eof => return,
                Kind::Newline if depth == 0 => return,
                Kind::RParen if depth == 0 && block => return,
                Kind::LParen | Kind::CallParen | Kind::LBracket | Kind::LBrace | Kind::DotParen => {
                    depth += 1;
                }
                Kind::RParen | Kind::RBracket | Kind::RBrace => depth = depth.saturating_sub(1),
                _ => {}
            }
            self.bump();
        }
    }

    /// `line`: a keyword's line, a type's, or an expression and what
    /// follows it.
    fn line(&mut self) -> Parsed<Line> {
        match self.peek() {
            Kind::KwPackage => self.package().map(Line::Header),
            Kind::KwImport => self.import().map(Line::Import),
            Kind::KwExport => self.exports().map(Line::Exports),
            Kind::KwExpect => {
                let keyword = self.bump();
                let value = self.expr()?;
                self.no_binding_after()?;
                Ok(Line::Expect(keyword.span(), value))
            }
            Kind::TypeIdent => self.type_line(),
            _ => {
                let head = self.expr()?;
                match self.peek() {
                    Kind::Colon => {
                        self.bump();
                        Ok(Line::Typed(head, self.typed()?))
                    }
                    Kind::KwIf | Kind::Arrow => self.clause(head),
                    Kind::Eq => {
                        self.bump();
                        let value = self.expr()?;
                        self.no_binding_after()?;
                        Ok(Line::Value(head, value))
                    }
                    Kind::Newline | Kind::Eof | Kind::RParen => Err(SyntaxError::new(
                        head.span,
                        "this line belongs to no definition: a body of several lines is \
                         `-> (` … `)`",
                    )),
                    _ => {
                        self.note("`->`");
                        self.note("`:`");
                        self.note("`=`");
                        Err(self.fail())
                    }
                }
            }
        }
    }

    /// A line beginning with a type's name, perhaps with its parameters:
    /// an alias, a constraint alias, or a data declaration.
    fn type_line(&mut self) -> Parsed<Line> {
        let token = self.bump();
        let mut head = atom(token, ExprKind::Name(name(token)));
        if self.peek() == Kind::CallParen {
            let (arguments, end) = self.arguments()?;
            head = Expr {
                span: head.span.through(end),
                kind: ExprKind::Call(Box::new(head), arguments),
            };
        }
        match self.peek() {
            Kind::Eq => {
                self.bump();
                if self.peek() == Kind::KwWhere {
                    Ok(Line::Constraints(head, self.constraints()?))
                } else {
                    Ok(Line::Alias(head, self.ty()?))
                }
            }
            Kind::Colon => {
                self.bump();
                Ok(Line::Typed(head, self.typed()?))
            }
            Kind::Arrow | Kind::KwIf => Err(SyntaxError::new(
                head.span,
                "a clause begins with its name and its patterns: `name(patterns) -> ...`",
            )),
            _ => {
                self.note("`=`");
                self.note("`:`");
                Err(self.fail())
            }
        }
    }

    /// `clause`: `if guard -> body`, after its head.
    fn clause(&mut self, head: Expr) -> Parsed<Line> {
        let guard = match self.eat(Kind::KwIf) {
            Some(_) => Some(self.expr()?),
            None => None,
        };
        self.expect(Kind::Arrow, "`->`")?;
        let body = self.expr()?;
        self.no_binding_after()?;
        Ok(Line::Clause { head, guard, body })
    }

    /// A clause's or an `expect`'s body read as one expression, which a
    /// binding cannot follow: one written after `->` wants a block.
    fn no_binding_after(&self) -> Parsed<()> {
        if self.peek() == Kind::Eq {
            return Err(SyntaxError::new(
                self.tokens[self.at].span(),
                "a binding belongs to a block: a body of several lines is `-> (` … `)`",
            ));
        }
        Ok(())
    }

    /// `statement`: a value, or `pattern = value`.
    fn statement(&mut self) -> Parsed<Statement> {
        let value = self.expr()?;
        self.statement_after(value)
    }

    /// The statement `value` begins.
    fn statement_after(&mut self, value: Expr) -> Parsed<Statement> {
        Ok(match self.eat(Kind::Eq) {
            Some(_) => Statement::Binding(value, self.expr()?),
            None => Statement::Value(value),
        })
    }

    fn package(&mut self) -> Parsed<HeaderDecl> {
        let start = self.bump();
        self.expect(Kind::LBrace, "`{`")?;
        let (dependencies, _) = self.separated(
            false,
            |kind| kind == Kind::Ident,
            "a name",
            |parser| {
                let named = parser.bump();
                parser.expect(Kind::Colon, "`:`")?;
                parser.expect(Kind::StrStart, "a path")?;
                let mut path = Vec::new();
                while let Some(text) = parser.eat(Kind::StrText) {
                    path.push(text.span());
                }
                let close = parser.expect(Kind::StrEnd, "the path's closing quote")?;
                Ok(Dependency {
                    span: named.span().through(close.span()),
                    name: name(named),
                    path,
                })
            },
        )?;
        let close = self.expect(Kind::RBrace, "`}`")?;
        Ok(HeaderDecl {
            span: start.span().through(close.span()),
            kind: HeaderKind::Package,
            dependencies,
        })
    }

    fn import(&mut self) -> Parsed<ImportDecl> {
        let start = self.bump();
        let mut path = vec![name(self.expect(Kind::Ident, "a name")?)];
        while self.eat(Kind::Dot).is_some() {
            path.push(name(self.expect(Kind::Ident, "a name")?));
        }
        self.expect(Kind::LBrace, "`{`")?;
        let (exposures, _) = self.separated(false, is_name, "a name", |parser| {
            let exported = parser.bump();
            let constructors = parser.eat(Kind::DotStar).is_some();
            let local = match parser.eat(Kind::Colon) {
                Some(_) => parser.any_name()?,
                None => exported,
            };
            Ok(Exposure {
                exported: name(exported),
                local: name(local),
                constructors,
            })
        })?;
        let close = self.expect(Kind::RBrace, "`}`")?;
        Ok(ImportDecl {
            span: start.span().through(close.span()),
            path,
            exposures,
        })
    }

    fn exports(&mut self) -> Parsed<ExportsDecl> {
        let start = self.bump();
        self.expect(Kind::LBrace, "`{`")?;
        let (exports, _) = self.separated(false, is_name, "a name", |parser| {
            let exported = parser.bump();
            Ok(Export {
                name: name(exported),
                constructors: parser.eat(Kind::DotStar).is_some(),
            })
        })?;
        let close = self.expect(Kind::RBrace, "`}`")?;
        Ok(ExportsDecl {
            span: start.span().through(close.span()),
            exports,
        })
    }

    fn any_name(&mut self) -> Parsed<Token> {
        if is_name(self.peek()) {
            Ok(self.bump())
        } else {
            self.note("a name");
            Err(self.fail())
        }
    }

    /// `typed`: what follows a `:`.
    fn typed(&mut self) -> Parsed<Typed> {
        let (parameters, result) = self.signature()?;
        let constraints = match self.peek() {
            Kind::KwWhere => Some(self.constraints()?),
            _ => None,
        };
        let methods = match self.peek() {
            Kind::DotParen => {
                self.bump();
                let lines = self.lines(true);
                let close = self.expect(Kind::RParen, "`)`")?;
                Some((lines, close.span()))
            }
            _ => None,
        };
        Ok(Typed {
            parameters,
            result,
            constraints,
            methods,
        })
    }

    /// A signature's `type`: a function type's parameters and result, or the
    /// result alone.
    fn signature(&mut self) -> Parsed<(Vec<Type>, Type)> {
        let (parameters, result) = self.function()?;
        Ok((parameters.unwrap_or_default(), result))
    }

    /// `types`: one or more.
    fn types(&mut self) -> Parsed<Vec<Type>> {
        Ok(self.separated(true, begins_type, "a type", Self::ty)?.0)
    }

    /// `constraints`: after `where`, constraints parted by commas. A comma
    /// never ends a line, so a list of one constraint to a line is one
    /// line, and the last takes no comma: the line would run on.
    fn constraints(&mut self) -> Parsed<(Vec<Constraint>, Span)> {
        self.bump();
        let mut constraints = vec![self.constraint()?];
        while let Some(comma) = self.eat(Kind::Comma) {
            let member = self.peek() == Kind::Ident
                && self
                    .tokens
                    .get(self.at + 1)
                    .is_some_and(|next| next.kind == Kind::Dot);
            if self.peek() != Kind::TypeIdent && !member {
                return Err(SyntaxError::new(
                    comma.span(),
                    "a `where` list's last constraint takes no comma: the line runs on into \
                     the next",
                ));
            }
            constraints.push(self.constraint()?);
        }
        self.note("`,`");
        self.constrained(constraints)
    }

    /// `constraint`: an alias applied, `Name(a)`, or a member's type,
    /// `a.member : type`.
    fn constraint(&mut self) -> Parsed<Constraint> {
        if let Some(head) = self.eat(Kind::TypeIdent) {
            self.expect(Kind::CallParen, "`(`")?;
            let arguments = self.types()?;
            let close = self.expect(Kind::RParen, "`)`")?;
            return Ok(Constraint::Alias {
                span: head.span().through(close.span()),
                name: name(head),
                arguments,
            });
        }
        let Some(variable) = self.eat(Kind::Ident) else {
            self.note("a constraint");
            return Err(self.fail());
        };
        self.expect(Kind::Dot, "`.`")?;
        let member = match self.peek() {
            Kind::Ident | Kind::EffectIdent => self.bump(),
            _ => {
                self.note("a member's name");
                return Err(self.fail());
            }
        };
        self.expect(Kind::Colon, "`:`")?;
        let (parameters, result) = self.signature()?;
        Ok(Constraint::Member {
            span: variable.span().through(type_span(&result)),
            variable: name(variable),
            member: name(member),
            parameters,
            result,
        })
    }

    /// Constraints and where they end, if there are any.
    fn constrained(&mut self, constraints: Vec<Constraint>) -> Parsed<(Vec<Constraint>, Span)> {
        let end = constraints.last().map(Constraint::span).ok_or_else(|| {
            self.note("a constraint");
            self.fail()
        })?;
        Ok((constraints, end))
    }

    /// `type`.
    fn ty(&mut self) -> Parsed<Type> {
        let start = self.tokens[self.at].span();
        Ok(match self.function()? {
            (None, ty) => ty,
            (Some(parameters), result) => Type::Function {
                span: start.through(type_span(&result)),
                parameters,
                result: Box::new(result),
            },
        })
    }

    /// `type`: an operand, and the parameters it is if an arrow follows.
    fn function(&mut self) -> Parsed<(Option<Vec<Type>>, Type)> {
        let operand = self.type_operand()?;
        if self.eat(Kind::Arrow).is_none() {
            self.note("`->`");
            return Ok((None, Self::alone(operand)?));
        }
        let parameters = match operand {
            Operand::Listed { members, .. } => members,
            Operand::One(ty) => vec![ty],
        };
        let result = self.type_operand()?;
        Ok((Some(parameters), Self::alone(result)?))
    }

    /// A type operand with no arrow after it: parenthesized, one type
    /// grouped or a tuple.
    fn alone(operand: Operand) -> Parsed<Type> {
        match operand {
            Operand::One(ty) => Ok(ty),
            Operand::Listed {
                mut members,
                span,
                trailing,
            } => match members.len() {
                1 if !trailing => Ok(members.pop().expect("one type")),
                1 => Err(one_tuple(span)),
                _ => Ok(Type::Tuple { span, members }),
            },
        }
    }

    /// `type-operand`.
    fn type_operand(&mut self) -> Parsed<Operand> {
        Ok(Operand::One(match self.peek() {
            Kind::TypeIdent => {
                let head = self.bump();
                let (arguments, end) = self.type_arguments(head.span())?;
                named_type(head, arguments, end)
            }
            Kind::Ident => {
                let variable = self.bump();
                named_type(variable, Vec::new(), variable.span())
            }
            Kind::Wild => Type::Hole {
                span: self.bump().span(),
            },
            Kind::LParen => {
                let open = self.bump();
                let (members, trailing) = self.separated(true, begins_type, "a type", Self::ty)?;
                let close = self.expect(Kind::RParen, "`)`")?;
                return Ok(Operand::Listed {
                    members,
                    span: open.span().through(close.span()),
                    trailing,
                });
            }
            Kind::LBracket => self.variants()?,
            Kind::LBrace => self.record_type()?,
            _ => {
                self.note_type_starts();
                return Err(self.fail());
            }
        }))
    }

    /// `[A, B(x)]`: a tag row's constructors.
    fn variants(&mut self) -> Parsed<Type> {
        let open = self.bump();
        let (constructors, _) = self.separated(
            false,
            |kind| kind == Kind::TypeIdent,
            "a type name",
            |parser| {
                let head = parser.bump();
                let (fields, _) = parser.type_arguments(head.span())?;
                Ok(ConstructorDecl {
                    name: name(head),
                    fields,
                })
            },
        )?;
        let close = self.expect(Kind::RBracket, "`]`")?;
        Ok(Type::Variants {
            span: open.span().through(close.span()),
            constructors,
        })
    }

    /// `{x: A}`, or `{x: A, *}`, open to more fields.
    fn record_type(&mut self) -> Parsed<Type> {
        let open = self.bump();
        let (fields, trailing) = self.separated(
            false,
            |kind| kind == Kind::Ident,
            "a name",
            |parser| {
                let field = parser.bump();
                parser.expect(Kind::Colon, "`:`")?;
                Ok((name(field), parser.ty()?))
            },
        )?;
        let open_record = (fields.is_empty() || trailing) && {
            self.note("`*`");
            self.eat(Kind::Star).is_some()
        };
        if open_record {
            self.eat(Kind::Comma);
        }
        let close = self.expect(Kind::RBrace, "`}`")?;
        Ok(Type::Record {
            span: open.span().through(close.span()),
            fields,
            open: open_record,
        })
    }

    /// A type name's arguments, `(A, B)`, if it is given any, and where it
    /// ends, from `end` where it is given none.
    fn type_arguments(&mut self, end: Span) -> Parsed<(Vec<Type>, Span)> {
        if self.eat(Kind::CallParen).is_none() {
            return Ok((Vec::new(), end));
        }
        let arguments = self.types()?;
        let close = self.expect(Kind::RParen, "`)`")?;
        Ok((arguments, close.span()))
    }

    /// `expr`: operands and the infix operators between them, each binding
    /// as tight as its level and its left side first.
    fn expr(&mut self) -> Parsed<Expr> {
        if self.peek() == Kind::KwIf {
            return self.if_();
        }
        self.binary(0)
    }

    fn binary(&mut self, looser: u8) -> Parsed<Expr> {
        let mut left = self.operand()?;
        while let Some((level, op)) = infix(self.peek())
            && level > looser
        {
            self.bump();
            let right = self.binary(level)?;
            left = binary(op, left, right);
        }
        Ok(left)
    }

    /// `operand`: prefixes, a primary, and its postfixes.
    fn operand(&mut self) -> Parsed<Expr> {
        match self.peek() {
            Kind::Minus => {
                let token = self.bump();
                Ok(negated(token, self.operand()?))
            }
            Kind::Bang => {
                let token = self.bump();
                Ok(unary(UnaryOp::Not, token, self.operand()?))
            }
            _ => {
                let mut value = self.primary()?;
                loop {
                    value = match self.peek() {
                        Kind::CallParen => {
                            let (arguments, end) = self.arguments()?;
                            Expr {
                                span: value.span.through(end),
                                kind: ExprKind::Call(Box::new(value), arguments),
                            }
                        }
                        Kind::Question => {
                            let question = self.bump();
                            Expr {
                                span: value.span.through(question.span()),
                                kind: ExprKind::Try(Box::new(value)),
                            }
                        }
                        Kind::Dot => self.member(value)?,
                        _ => return Ok(value),
                    };
                }
            }
        }
    }

    /// `.name`, or `.name(arguments)`, of `value`.
    fn member(&mut self, value: Expr) -> Parsed<Expr> {
        self.bump();
        let member = self.any_name()?;
        if self.peek() != Kind::CallParen {
            return Ok(Expr {
                span: value.span.through(member.span()),
                kind: ExprKind::Member(Box::new(value), name(member)),
            });
        }
        let (arguments, end) = self.arguments()?;
        Ok(Expr {
            span: value.span.through(end),
            kind: ExprKind::Method(Box::new(value), name(member), arguments),
        })
    }

    /// A call's arguments, and where they end.
    fn arguments(&mut self) -> Parsed<(Vec<Expr>, Span)> {
        self.bump();
        let (arguments, _) = self.separated(
            false,
            |kind| kind == Kind::Bar || begins_expr(kind),
            "an expression",
            |parser| {
                if parser.peek() == Kind::Bar {
                    parser.lambda()
                } else {
                    parser.expr()
                }
            },
        )?;
        let close = self.expect(Kind::RParen, "`)`")?;
        Ok((arguments, close.span()))
    }

    /// `|x, Some(y)| body`: its parameters are operands, being no `or`,
    /// each the pattern it spells.
    fn lambda(&mut self) -> Parsed<Expr> {
        let open = self.bump();
        let (parameters, _) = self.separated(true, begins_expr, "a pattern", Self::operand)?;
        self.expect(Kind::Bar, "`|`")?;
        let body = self.expr()?;
        let patterns = parameters
            .into_iter()
            .map(|parameter| lines::pattern(parameter, self.source))
            .collect::<Result<_, _>>()
            .map_err(SyntaxError::from)?;
        Ok(Expr {
            span: open.span().through(body.span),
            kind: ExprKind::Lambda(patterns, Box::new(body)),
        })
    }

    /// `primary`.
    fn primary(&mut self) -> Parsed<Expr> {
        match self.peek() {
            Kind::Number | Kind::Char => self.numeral(),
            Kind::Wild => {
                let token = self.bump();
                if self.eat(Kind::DotDot).is_none() {
                    return Ok(atom(token, ExprKind::Wild));
                }
                let (end, span) = self.range_end()?;
                Ok(Expr {
                    span: token.span().through(span),
                    kind: ExprKind::Range(None, end),
                })
            }
            Kind::Decimal | Kind::TypeIdent | Kind::Ident | Kind::EffectIdent => {
                let token = self.bump();
                Ok(atom(
                    token,
                    match token.kind {
                        Kind::Decimal => ExprKind::Number(numeral(token)),
                        _ => ExprKind::Name(name(token)),
                    },
                ))
            }
            Kind::StrStart => self.string(),
            Kind::KwIf => Err(SyntaxError::new(
                self.tokens[self.at].span(),
                "an `if` takes everything after its `else`, so as an operand it is \
                 written in parentheses: `(if c then a else b)`",
            )),
            Kind::LParen => self.parenthesized(),
            Kind::LBracket => self.list(),
            Kind::LBrace => self.record(),
            _ => {
                self.note("an expression");
                Err(self.fail())
            }
        }
    }

    /// `if condition then yes else no`, its `else` as far as an expression
    /// goes, so it begins an expression and is no operand.
    fn if_(&mut self) -> Parsed<Expr> {
        let keyword = self.bump();
        let condition = self.expr()?;
        self.expect(Kind::KwThen, "`then`")?;
        let yes = self.expr()?;
        self.expect(Kind::KwElse, "`else`")?;
        let no = self.expr()?;
        Ok(Expr {
            span: keyword.span().through(no.span),
            kind: ExprKind::If(Box::new(condition), Box::new(yes), Box::new(no)),
        })
    }

    /// A numeral, or a range from it.
    fn numeral(&mut self) -> Parsed<Expr> {
        let start = self.bump();
        if self.eat(Kind::DotDot).is_none() {
            return Ok(atom(start, ExprKind::Number(numeral(start))));
        }
        let (end, span) = self.range_end()?;
        let start = Bound {
            numeral: numeral(start),
            negative: false,
        };
        Ok(Expr {
            span: start.numeral.span.through(span),
            kind: ExprKind::Range(Some(start), end),
        })
    }

    /// `range-end`: a numeral, negated or not, or `_` for no end.
    fn range_end(&mut self) -> Parsed<(Option<Bound>, Span)> {
        if let Some(wild) = self.eat(Kind::Wild) {
            return Ok((None, wild.span()));
        }
        let minus = self.eat(Kind::Minus);
        match self.peek() {
            Kind::Number | Kind::Char => {
                let end = self.bump();
                let span =
                    minus.map_or_else(|| end.span(), |minus| minus.span().through(end.span()));
                Ok((
                    Some(Bound {
                        numeral: numeral(end),
                        negative: minus.is_some(),
                    }),
                    span,
                ))
            }
            _ => {
                if minus.is_none() {
                    self.note("`_`");
                }
                self.note("the range's last numeral");
                Err(self.fail())
            }
        }
    }

    /// After `(` and one expression, the next token says which: `,` a
    /// tuple, `=` or a line's end a block, and `)` one value grouped.
    fn parenthesized(&mut self) -> Parsed<Expr> {
        let open = self.bump();
        let first = self.expr()?;
        match self.peek() {
            Kind::Comma => self.tuple(open, first),
            Kind::Eq | Kind::Newline => self.block(open, first),
            _ => {
                self.note("`,`");
                self.note("`=`");
                let close = self.expect(Kind::RParen, "`)`")?;
                Ok(Expr {
                    span: open.span().through(close.span()),
                    ..first
                })
            }
        }
    }

    /// The rest of a tuple, after its first member.
    fn tuple(&mut self, open: Token, first: Expr) -> Parsed<Expr> {
        let mut members = vec![first];
        while self.eat(Kind::Comma).is_some() {
            if !begins_expr(self.peek()) {
                self.note("an expression");
                break;
            }
            members.push(self.expr()?);
        }
        self.note("`,`");
        let span = open
            .span()
            .through(self.expect(Kind::RParen, "`)`")?.span());
        if members.len() == 1 {
            return Err(one_tuple(span));
        }
        Ok(Expr {
            span,
            kind: ExprKind::Tuple(members),
        })
    }

    /// `block`: statements a line apiece, the last its answer, after the
    /// first expression.
    fn block(&mut self, open: Token, first: Expr) -> Parsed<Expr> {
        let mut statements = vec![self.statement_after(first)?];
        while self.eat(Kind::Newline).is_some() {
            statements.push(self.statement()?);
        }
        // A clause's `->` and a signature's `:` stand in no block: this one
        // ran on into the next item, never closed.
        if matches!(self.peek(), Kind::Arrow | Kind::Colon) {
            return Err(SyntaxError::new(
                open.span(),
                "this `(` is not closed: its block runs on into the next item",
            )
            .label("opened here"));
        }
        self.note("a new line");
        let close = self.expect(Kind::RParen, "`)`")?;
        let body = lines::body(statements, self.source)?;
        Ok(Expr {
            span: open.span().through(close.span()),
            kind: ExprKind::Block(Box::new(body)),
        })
    }

    fn string(&mut self) -> Parsed<Expr> {
        let open = self.bump();
        let mut parts = Vec::new();
        loop {
            match self.peek() {
                Kind::StrText => parts.push(StringPart::Text(self.bump().span())),
                Kind::SpliceStart => {
                    self.bump();
                    let value = self.expr()?;
                    let width = match self.eat(Kind::Colon) {
                        Some(_) => Some(self.width()?),
                        None => None,
                    };
                    parts.push(StringPart::Splice(value, width));
                    self.expect(Kind::SpliceEnd, "`}`")?;
                }
                _ => break,
            }
        }
        let close = self.expect(Kind::StrEnd, "the string's closing quote")?;
        Ok(Expr {
            span: open.span().through(close.span()),
            kind: ExprKind::String(parts),
        })
    }

    /// A splice's width after its `:`: an alignment, then a count.
    fn width(&mut self) -> Parsed<Width> {
        let align = match self.peek() {
            Kind::Lt => Align::Left,
            Kind::Gt => Align::Right,
            _ => {
                for what in ["`<`", "`>`"] {
                    self.note(what);
                }
                return Err(self.fail());
            }
        };
        self.bump();
        let columns = self.expect(Kind::Number, "a numeral for the width")?;
        Ok(Width {
            align,
            columns: numeral(columns),
        })
    }

    fn list(&mut self) -> Parsed<Expr> {
        let open = self.bump();
        let (elements, trailing) =
            self.separated(false, begins_expr, "an expression", Self::expr)?;
        let rest = self.rest(elements.is_empty() || trailing)?;
        let close = self.expect(Kind::RBracket, "`]`")?;
        Ok(Expr {
            span: open.span().through(close.span()),
            kind: ExprKind::List(elements, rest.map(Box::new)),
        })
    }

    fn record(&mut self) -> Parsed<Expr> {
        let open = self.bump();
        let (fields, trailing) = self.separated(
            false,
            |kind| kind == Kind::Ident,
            "a name",
            |parser| {
                let field = parser.bump();
                let value = match parser.eat(Kind::Colon) {
                    Some(_) => parser.expr()?,
                    None => atom(field, ExprKind::Name(name(field))),
                };
                Ok((name(field), value))
            },
        )?;
        let base = self.rest(fields.is_empty() || trailing)?;
        let span = open
            .span()
            .through(self.expect(Kind::RBrace, "`}`")?.span());
        Ok(Expr {
            span,
            kind: match base {
                Some(base) => ExprKind::Update(fields, Box::new(base)),
                None => ExprKind::Record(fields),
            },
        })
    }

    /// `rest`, where one may stand: `*rest`, or `*` alone, a pattern's
    /// rest it does not name, and perhaps a comma after it.
    fn rest(&mut self, may: bool) -> Parsed<Option<Expr>> {
        if !may {
            return Ok(None);
        }
        self.note("`*`");
        let Some(star) = self.eat(Kind::Star) else {
            return Ok(None);
        };
        let rest = if begins_expr(self.peek()) {
            self.expr()?
        } else {
            atom(star, ExprKind::Wild)
        };
        self.eat(Kind::Comma);
        Ok(Some(rest))
    }
}

/// A type operand: parenthesized types, which are a function type's
/// parameters where an arrow follows, or one type.
enum Operand {
    Listed {
        members: Vec<Type>,
        span: Span,
        trailing: bool,
    },
    One(Type),
}

fn one_tuple(span: Span) -> SyntaxError {
    SyntaxError::new(
        span,
        "a tuple has at least two members: write `(a)` to group one",
    )
}

fn name(token: Token) -> Name {
    Name(token.span())
}

fn named_type(token: Token, arguments: Vec<Type>, end: Span) -> Type {
    Type::Named {
        span: token.span().through(end),
        name: name(token),
        arguments,
    }
}

fn numeral(token: Token) -> Numeral {
    Numeral {
        span: token.span(),
        kind: match token.kind {
            Kind::Char => NumeralKind::Character,
            Kind::Decimal => NumeralKind::Decimal,
            _ => NumeralKind::Number,
        },
    }
}

fn atom(token: Token, kind: ExprKind) -> Expr {
    Expr {
        span: token.span(),
        kind,
    }
}

/// `-` and what it negates. A range whose first end it is held to,
/// `-3..5`, takes it as that end's sign.
fn negated(token: Token, value: Expr) -> Expr {
    match value.kind {
        ExprKind::Range(Some(start), end)
            if !start.negative && start.numeral.span.start == token.span().end =>
        {
            Expr {
                span: token.span().through(value.span),
                kind: ExprKind::Range(
                    Some(Bound {
                        negative: true,
                        ..start
                    }),
                    end,
                ),
            }
        }
        _ => unary(UnaryOp::Negate, token, value),
    }
}

fn unary(op: UnaryOp, token: Token, value: Expr) -> Expr {
    Expr {
        span: token.span().through(value.span),
        kind: ExprKind::Unary(op, Box::new(value)),
    }
}

fn binary(op: BinaryOp, left: Expr, right: Expr) -> Expr {
    Expr {
        span: left.span.through(right.span),
        kind: ExprKind::Binary(op, Box::new(left), Box::new(right)),
    }
}

const fn type_span(ty: &Type) -> Span {
    match ty {
        Type::Named { span, .. }
        | Type::Function { span, .. }
        | Type::Variants { span, .. }
        | Type::Record { span, .. }
        | Type::Tuple { span, .. }
        | Type::Hole { span } => *span,
    }
}
