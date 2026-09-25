//! The grammar of `grammar.ebnf`, read by recursive descent.
//!
//! A file is lines. Each begins with a keyword or an expression, and the token
//! after that expression says what the line is; [`lines`](super::lines) makes
//! the heads that are patterns into patterns, and groups the lines into items.
//! Every choice is made by the next token, but for `Name =`, whose right side
//! is a type because its head, already read, is a type's name. Each rule of
//! the file is a method here, and the `ebnf` tests check that the file is
//! LL(1) and that this reads what it does.
//!
//! A line that cannot be read is an error, and reading goes on from the next
//! line, so one file's errors are all found at once.

use super::ast::{
    BinaryOp, Constraint, ConstructorDecl, Dependency, Export, ExportsDecl, Exposure, Expr,
    ExprKind, HeaderDecl, HeaderKind, ImportDecl, Name, Numeral, NumeralKind, Span, StringPart,
    Type, UnaryOp,
};
use super::lex::{Kind, Token};
use super::lines::{self, Equals, Line, Statement, Trailer, Typed};

/// Why a line could not be read.
#[derive(Debug)]
pub(crate) struct SyntaxError {
    pub(crate) span: Span,
    pub(crate) message: String,
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
        Kind::Negate
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
    )
}

/// Whether a type can begin with `kind`.
const fn begins_type(kind: Kind) -> bool {
    matches!(
        kind,
        Kind::TypeIdent | Kind::Ident | Kind::LParen | Kind::LBracket | Kind::LBrace
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
        for what in ["a type name", "a name", "`(`", "`[`", "`{`"] {
            self.note(what);
        }
    }

    /// Note that `what` was looked for at the current token.
    fn note(&mut self, what: &'static str) {
        if !self.expected.contains(&what) {
            self.expected.push(what);
        }
    }

    /// Why the current token cannot be read: what was looked for, or what
    /// is wrong with the token itself.
    fn fail(&self) -> SyntaxError {
        let token = self.tokens[self.at];
        let text = token.text(self.source);
        let message = match token.kind {
            Kind::Error if token.start == token.end => "unterminated string literal".to_owned(),
            Kind::Error => format!("invalid token `{text}`"),
            Kind::Lopsided => {
                format!("`{text}` has space on one side only: write `a {text} b`, or `a{text}b`")
            }
            Kind::NegatedElement => "this `-` begins an element of its own: write `a - b` to \
                                     subtract, or `(-b)` for a negated element"
                .to_owned(),
            Kind::Detached if matches!(text, "." | "..") => {
                format!("`{text}` goes against what it joins: no space around it")
            }
            Kind::Detached => format!("`{text}` goes against what it follows: no space before it"),
            Kind::Adjacent => {
                let before = self.tokens[self.at - 1].text(self.source);
                format!("`{before}` and `{text}` are two elements: part them with a space")
            }
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
        SyntaxError {
            span: token.span(),
            message,
        }
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

    /// `line`: a keyword's line, or an expression and what follows it.
    fn line(&mut self) -> Parsed<Line> {
        match self.peek() {
            Kind::KwPackage => self.package().map(Line::Header),
            Kind::KwImport => self.import().map(Line::Import),
            Kind::KwExports => self.exports().map(Line::Exports),
            Kind::KwExpect => {
                let keyword = self.bump();
                Ok(Line::Expect(keyword.span(), self.statement()?))
            }
            _ => {
                let head = self.expr()?;
                let trailer = self.trailer(lines::names_a_type(&head, self.source))?;
                Ok(Line::new(head, trailer))
            }
        }
    }

    /// `trailer`, or `after-type` where the head is a type's name alone.
    fn trailer(&mut self, names_a_type: bool) -> Parsed<Option<Trailer>> {
        Ok(Some(match self.peek() {
            Kind::Eq => {
                self.bump();
                Trailer::Equals(if self.peek() == Kind::KwWhere {
                    Equals::Constraints(self.constraints()?)
                } else if names_a_type {
                    Equals::Type(self.ty()?)
                } else {
                    Equals::Value(self.expr()?)
                })
            }
            Kind::Colon => {
                self.bump();
                Trailer::Typed(self.typed()?)
            }
            Kind::KwIf | Kind::Arrow => {
                let guard = match self.eat(Kind::KwIf) {
                    Some(_) => Some(self.expr()?),
                    None => None,
                };
                self.expect(Kind::Arrow, "`->`")?;
                Trailer::Clause {
                    guard,
                    first: self.statement()?,
                }
            }
            _ => return Ok(None),
        }))
    }

    /// `statement`: a value, or `pattern = value`.
    fn statement(&mut self) -> Parsed<Statement> {
        let value = self.expr()?;
        Ok(match self.eat(Kind::Eq) {
            Some(_) => Statement::Binding(value, self.expr()?),
            None => Statement::Value(value),
        })
    }

    fn package(&mut self) -> Parsed<HeaderDecl> {
        let start = self.bump();
        self.expect(Kind::LBrace, "`{`")?;
        let mut dependencies = Vec::new();
        while let Some(named) = self.eat(Kind::Ident) {
            self.expect(Kind::Colon, "`:`")?;
            self.expect(Kind::StrStart, "a path")?;
            let mut path = Vec::new();
            while let Some(text) = self.eat(Kind::StrText) {
                path.push(text.span());
            }
            let close = self.expect(Kind::StrEnd, "the path's closing quote")?;
            dependencies.push(Dependency {
                span: named.span().through(close.span()),
                name: name(named),
                path,
            });
        }
        self.note("a name");
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
        let mut exposures = Vec::new();
        while is_name(self.peek()) {
            let exported = self.bump();
            let constructors = self.eat(Kind::DotStar).is_some();
            let local = match self.eat(Kind::Colon) {
                Some(_) => self.any_name()?,
                None => exported,
            };
            exposures.push(Exposure {
                exported: name(exported),
                local: name(local),
                constructors,
            });
        }
        self.note("a name");
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
        let mut exports = Vec::new();
        while is_name(self.peek()) {
            let exported = self.bump();
            exports.push(Export {
                name: name(exported),
                constructors: self.eat(Kind::DotStar).is_some(),
            });
        }
        self.note("a name");
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

    /// `signature`: parameters and an arrow to the result, or the result
    /// alone.
    fn signature(&mut self) -> Parsed<(Vec<Type>, Type)> {
        let mut types = self.types()?;
        if self.eat(Kind::Arrow).is_some() {
            return Ok((types, self.ty()?));
        }
        if types.len() == 1 {
            return Ok((Vec::new(), types.pop().expect("one type")));
        }
        self.note("`->` and the result after the parameter types");
        Err(self.fail())
    }

    /// `type { type }`.
    fn types(&mut self) -> Parsed<Vec<Type>> {
        let mut types = vec![self.ty()?];
        while begins_type(self.peek()) {
            types.push(self.ty()?);
        }
        self.note_type_starts();
        Ok(types)
    }

    /// `constraints`: after `where`, aliases, and a member's constraint
    /// last.
    fn constraints(&mut self) -> Parsed<(Vec<Constraint>, Span)> {
        self.bump();
        let mut constraints = Vec::new();
        while let Some(head) = self.eat(Kind::TypeIdent) {
            self.expect(Kind::CallParen, "`(`")?;
            let arguments = self.types()?;
            let close = self.expect(Kind::RParen, "`)`")?;
            constraints.push(Constraint::Alias {
                span: head.span().through(close.span()),
                name: name(head),
                arguments,
            });
        }
        if let Some(variable) = self.eat(Kind::Ident) {
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
            constraints.push(Constraint::Member {
                span: variable.span().through(type_span(&result)),
                variable: name(variable),
                member: name(member),
                parameters,
                result,
            });
        }
        let end = constraints.last().map(Constraint::span).ok_or_else(|| {
            self.note("a constraint");
            self.fail()
        })?;
        Ok((constraints, end))
    }

    /// `type`.
    fn ty(&mut self) -> Parsed<Type> {
        match self.peek() {
            Kind::TypeIdent => {
                let head = self.bump();
                let (arguments, end) = self.type_arguments(head.span())?;
                Ok(named_type(head, arguments, end))
            }
            Kind::Ident => {
                let variable = self.bump();
                Ok(named_type(variable, Vec::new(), variable.span()))
            }
            Kind::LParen => self.parenthesized_type(),
            Kind::LBracket => self.variants(),
            Kind::LBrace => self.record_type(),
            _ => {
                self.note_type_starts();
                Err(self.fail())
            }
        }
    }

    /// A function type, a tuple, or one type grouped.
    fn parenthesized_type(&mut self) -> Parsed<Type> {
        let open = self.bump();
        let mut members = self.types()?;
        let result = if self.eat(Kind::Arrow).is_some() {
            Some(self.ty()?)
        } else {
            self.note("`->`");
            None
        };
        let span = open
            .span()
            .through(self.expect(Kind::RParen, "`)`")?.span());
        Ok(match result {
            Some(result) => Type::Function {
                span,
                parameters: members,
                result: Box::new(result),
            },
            None if members.len() == 1 => members.pop().expect("one type"),
            None => Type::Tuple { span, members },
        })
    }

    /// `[A B(x)]`: a tag row's constructors.
    fn variants(&mut self) -> Parsed<Type> {
        let open = self.bump();
        let mut constructors = Vec::new();
        while let Some(head) = self.eat(Kind::TypeIdent) {
            let (fields, _) = self.type_arguments(head.span())?;
            constructors.push(ConstructorDecl {
                name: name(head),
                fields,
            });
        }
        self.note("a type name");
        let close = self.expect(Kind::RBracket, "`]`")?;
        Ok(Type::Variants {
            span: open.span().through(close.span()),
            constructors,
        })
    }

    /// `{x: A}`, or `{x: A *}`, open to more fields.
    fn record_type(&mut self) -> Parsed<Type> {
        let open = self.bump();
        let mut fields = Vec::new();
        while let Some(field) = self.eat(Kind::Ident) {
            self.expect(Kind::Colon, "`:`")?;
            fields.push((name(field), self.ty()?));
        }
        self.note("a name");
        let open_record = self.eat(Kind::Rest).is_some();
        let close = self.expect(Kind::RBrace, "`}`")?;
        Ok(Type::Record {
            span: open.span().through(close.span()),
            fields,
            open: open_record,
        })
    }

    /// A type name's arguments, `(A B)`, if it is given any, and where it
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
            Kind::Negate => {
                let token = self.bump();
                Ok(unary(UnaryOp::Negate, token, self.operand()?))
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
        let mut arguments = Vec::new();
        loop {
            match self.peek() {
                Kind::LambdaBar => arguments.push(self.lambda()?),
                kind if begins_expr(kind) => arguments.push(self.expr()?),
                _ => break,
            }
        }
        self.note("an expression");
        let close = self.expect(Kind::RParen, "`)`")?;
        Ok((arguments, close.span()))
    }

    /// `|x Some(y)| body`: its parameters are operands, being no `or`,
    /// each the pattern it spells.
    fn lambda(&mut self) -> Parsed<Expr> {
        let open = self.bump();
        let mut parameters = vec![self.operand()?];
        while begins_expr(self.peek()) {
            parameters.push(self.operand()?);
        }
        self.expect(Kind::Bar, "`|`")?;
        let body = self.expr()?;
        let patterns = parameters
            .into_iter()
            .map(|parameter| lines::pattern(parameter, self.source))
            .collect::<Result<_, _>>()
            .map_err(|error| SyntaxError {
                span: error.span,
                message: error.message,
            })?;
        Ok(Expr {
            span: open.span().through(body.span),
            kind: ExprKind::Lambda(patterns, Box::new(body)),
        })
    }

    /// `primary`.
    fn primary(&mut self) -> Parsed<Expr> {
        match self.peek() {
            Kind::Number | Kind::Char => self.numeral(),
            Kind::Decimal | Kind::Wild | Kind::TypeIdent | Kind::Ident | Kind::EffectIdent => {
                let token = self.bump();
                Ok(atom(
                    token,
                    match token.kind {
                        Kind::Decimal => ExprKind::Number(numeral(token)),
                        Kind::Wild => ExprKind::Wild,
                        _ => ExprKind::Name(name(token)),
                    },
                ))
            }
            Kind::StrStart => self.string(),
            Kind::LParen => self.parenthesized(),
            Kind::LBracket => self.list(),
            Kind::LBrace => self.record(),
            _ => {
                self.note("an expression");
                Err(self.fail())
            }
        }
    }

    /// A numeral, or a range of two.
    fn numeral(&mut self) -> Parsed<Expr> {
        let start = self.bump();
        if self.eat(Kind::DotDot).is_none() {
            return Ok(atom(start, ExprKind::Number(numeral(start))));
        }
        let end = match self.peek() {
            Kind::Number | Kind::Char => self.bump(),
            _ => {
                self.note("the range's last numeral");
                return Err(self.fail());
            }
        };
        Ok(Expr {
            span: start.span().through(end.span()),
            kind: ExprKind::Range(numeral(start), numeral(end)),
        })
    }

    /// A tuple, or one value grouped.
    fn parenthesized(&mut self) -> Parsed<Expr> {
        let open = self.bump();
        let mut members = vec![self.expr()?];
        while begins_expr(self.peek()) {
            members.push(self.expr()?);
        }
        self.note("an expression");
        let span = open
            .span()
            .through(self.expect(Kind::RParen, "`)`")?.span());
        Ok(if members.len() == 1 {
            Expr {
                span,
                ..members.pop().expect("one value")
            }
        } else {
            Expr {
                span,
                kind: ExprKind::Tuple(members),
            }
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
                    parts.push(StringPart::Splice(self.expr()?));
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

    fn list(&mut self) -> Parsed<Expr> {
        let open = self.bump();
        let mut elements = Vec::new();
        while begins_expr(self.peek()) {
            elements.push(self.expr()?);
        }
        self.note("an expression");
        let rest = self.rest()?;
        let close = self.expect(Kind::RBracket, "`]`")?;
        Ok(Expr {
            span: open.span().through(close.span()),
            kind: ExprKind::List(elements, rest.map(Box::new)),
        })
    }

    fn record(&mut self) -> Parsed<Expr> {
        let open = self.bump();
        let mut fields = Vec::new();
        while let Some(field) = self.eat(Kind::Ident) {
            let value = match self.eat(Kind::Colon) {
                Some(_) => self.expr()?,
                None => atom(field, ExprKind::Name(name(field))),
            };
            fields.push((name(field), value));
        }
        self.note("a name");
        let base = self.rest()?;
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

    /// `rest`: `*rest`, or `*` alone, a pattern's rest it does not name.
    fn rest(&mut self) -> Parsed<Option<Expr>> {
        let Some(star) = self.eat(Kind::Rest) else {
            return Ok(None);
        };
        if begins_expr(self.peek()) {
            return self.expr().map(Some);
        }
        Ok(Some(atom(star, ExprKind::Wild)))
    }
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
        | Type::Tuple { span, .. } => *span,
    }
}
