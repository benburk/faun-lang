//! From a file's lines to its items, a line apiece.
//!
//! The grammar reads a line as a name and its arguments, and what the token
//! after them says the line is: `: type` declares, `= value` names a value,
//! and `-> value` is a clause. A pattern is written as the expression that
//! would build what it matches, so a clause's arguments, a lambda's
//! parameters and a block's bindings are read as expressions and made
//! patterns here, once the line has said they are ones. A body of several lines is a block, and a `where` list's
//! constraints are parted by commas, so each line is one item whole.
//!
//! An expression may hold what only a pattern can, `_`, a range, or a rest
//! with nothing after its `*`, since it is read before anyone knows which it
//! is; such a form is refused wherever it stays an expression.

use super::ast::{
    AliasDecl, BinaryOp, Binding, Body, Bound, Clause, Constraint, ConstraintAliasDecl, DataDecl,
    DataRepresentation, ExportsDecl, Expr, ExprKind, HeaderDecl, ImportDecl, Item, MethodItem,
    Name, NumeralKind, Pattern, SignatureDecl, Span, StringPart, Type, UnaryOp,
};
use super::diagnostic::Advised;
use super::grammar::SyntaxError;

/// One line of a file or of a method block, as the grammar reads it.
#[derive(Debug)]
pub(crate) enum Line {
    Header(HeaderDecl),
    Import(ImportDecl),
    Exports(ExportsDecl),
    /// `expect` and what it expects.
    Expect(Span, Expr),
    /// `head if guard -> body`.
    Clause {
        head: Expr,
        guard: Option<Expr>,
        body: Expr,
    },
    /// `name = value`.
    Value(Expr, Expr),
    /// `head : ...`: a signature or a data declaration.
    Typed(Expr, Typed),
    /// `Name = type`.
    Alias(Expr, Type),
    /// `Name(a) = where constraints`.
    Constraints(Expr, (Vec<Constraint>, Span)),
}

/// `: parameters -> result where constraints .(methods)`.
#[derive(Debug)]
pub(crate) struct Typed {
    pub(crate) parameters: Vec<Type>,
    pub(crate) result: Type,
    pub(crate) constraints: Option<(Vec<Constraint>, Span)>,
    pub(crate) methods: Option<(Vec<Line>, Span)>,
}

impl Typed {
    /// Where what it says ends.
    fn end(&self) -> Span {
        self.methods.as_ref().map_or_else(
            || {
                self.constraints
                    .as_ref()
                    .map_or_else(|| self.result.span(), |constraints| constraints.1)
            },
            |methods| methods.1,
        )
    }
}

/// A line of a block: a value, or `pattern = value`.
#[derive(Debug)]
pub(crate) enum Statement {
    Value(Expr),
    Binding(Expr, Expr),
    /// `condition else otherwise`, written at `span`.
    Else(Span, Expr, Expr),
    /// `if condition out`, written at `span`.
    If(Span, Expr, Expr),
}

/// Whether `name` is a type's or a constructor's.
pub(crate) fn is_type_name(name: Name, source: &str) -> bool {
    name.text(source)
        .starts_with(|c: char| c.is_ascii_uppercase())
}

/// The items `lines` make.
///
/// # Errors
///
/// A head that is not the pattern or name its line needs, a line that
/// belongs to nothing, a body that ends in a binding, or a pattern-only form
/// left in an expression.
pub(crate) fn items(lines: Vec<Line>, source: &str) -> Result<Vec<Item>, SyntaxError> {
    let items = Grouping::new(source, false).group(lines)?;
    for item in &items {
        match item {
            Item::Clause(clause) | Item::Expect(clause) => clause_expressions(clause, source)?,
            Item::Data(data) => {
                for method in &data.methods {
                    if let MethodItem::Clause(clause) = method {
                        clause_expressions(clause, source)?;
                    }
                }
            }
            _ => {}
        }
    }
    Ok(items)
}

/// Items from lines, a line apiece.
struct Grouping<'s> {
    source: &'s str,
    /// Whether these are a method block's lines, which hold only
    /// signatures and clauses.
    methods: bool,
    items: Vec<Item>,
}

impl<'s> Grouping<'s> {
    const fn new(source: &'s str, methods: bool) -> Self {
        Self {
            source,
            methods,
            items: Vec::new(),
        }
    }

    fn group(mut self, lines: Vec<Line>) -> Result<Vec<Item>, SyntaxError> {
        for line in lines {
            self.line(line)?;
        }
        Ok(self.items)
    }

    fn line(&mut self, line: Line) -> Result<(), SyntaxError> {
        match line {
            Line::Header(header) => self.item(header.span, Item::Header(header)),
            Line::Import(import) => self.item(import.span, Item::Import(import)),
            Line::Exports(exports) => self.item(exports.span, Item::Exports(exports)),
            Line::Expect(keyword, value) => {
                let body = body_of(value);
                self.item(
                    keyword,
                    Item::Expect(Clause {
                        span: keyword.through(body.result.span),
                        name: Name(keyword),
                        patterns: Vec::new(),
                        guard: None,
                        body,
                    }),
                )
            }
            Line::Clause { head, guard, body } => self.clause(head, guard, body),
            Line::Value(head, value) => self.value(&head, value),
            Line::Typed(head, typed) => self.typed(head, typed),
            Line::Alias(head, ty) => {
                let span = head.span.through(ty.span());
                let (name, params) = self.type_head(head)?;
                self.item(
                    span,
                    Item::Alias(AliasDecl {
                        span,
                        name,
                        params: params.unwrap_or_default(),
                        ty,
                    }),
                )
            }
            Line::Constraints(head, constraints) => self.constraint_alias(head, constraints),
        }
    }

    /// A clause: its head's name and patterns, its guard, and its body.
    fn clause(&mut self, head: Expr, guard: Option<Expr>, value: Expr) -> Result<(), SyntaxError> {
        let (name, arguments) = self.clause_head(head)?;
        if arguments.is_empty() {
            let text = name.text(self.source);
            let message = if text.ends_with('!') {
                "a definition of no parameters is a value, and a value is no effect".to_owned()
            } else {
                format!("a definition of no parameters is a value: `{text} = ...`")
            };
            return Err(SyntaxError::new(name.0, message));
        }
        let body = body_of(value);
        self.item(
            name.0,
            Item::Clause(Clause {
                span: name.0.through(body.result.span),
                name,
                patterns: patterns(arguments, self.source)?,
                guard,
                body,
            }),
        )
    }

    /// A value, `name = value`: a definition of no parameters.
    fn value(&mut self, head: &Expr, value: Expr) -> Result<(), SyntaxError> {
        let span = head.span;
        let ExprKind::Name(name) = head.kind else {
            return Err(SyntaxError::new(
                span,
                "a value is named by one name: `name = ...`",
            ));
        };
        let text = name.text(self.source);
        if text.ends_with('!') {
            return Err(SyntaxError::new(
                span,
                "a value is no effect: its name takes no `!`",
            ));
        }
        let body = body_of(value);
        self.item(
            name.0,
            Item::Clause(Clause {
                span: name.0.through(body.result.span),
                name,
                patterns: Vec::new(),
                guard: None,
                body,
            }),
        )
    }

    fn constraint_alias(
        &mut self,
        head: Expr,
        (constraints, end): (Vec<Constraint>, Span),
    ) -> Result<(), SyntaxError> {
        let span = head.span;
        let (name, Some(parameters)) = self.type_head(head)? else {
            return Err(SyntaxError::new(
                span,
                "a constraint alias takes parameters: `Name(a) = where ...`",
            ));
        };
        self.item(
            span,
            Item::Constraints(ConstraintAliasDecl {
                span: span.through(end),
                name,
                parameters,
                constraints,
            }),
        )
    }

    /// Add `item`, which a method block may not hold unless it is a
    /// signature or a clause.
    fn item(&mut self, span: Span, item: Item) -> Result<(), SyntaxError> {
        if self.methods && !matches!(item, Item::Signature(_) | Item::Clause(_)) {
            return Err(SyntaxError::new(
                span,
                "a method block holds signatures and clauses",
            ));
        }
        self.items.push(item);
        Ok(())
    }

    /// A clause's name and what it is applied to: `name(patterns)`.
    fn clause_head(&self, head: Expr) -> Result<(Name, Vec<Expr>), SyntaxError> {
        let span = head.span;
        if let ExprKind::Call(callee, arguments) = head.kind
            && let ExprKind::Name(name) = callee.kind
            && !is_type_name(name, self.source)
        {
            return Ok((name, arguments));
        }
        Err(SyntaxError::new(
            span,
            "a clause begins with its name and its patterns: `name(patterns) -> ...`",
        ))
    }

    /// A type's name and its parameters, if it is written with any:
    /// `Name`, or `Name(a, b)`.
    fn type_head(&self, head: Expr) -> Result<(Name, Option<Vec<Name>>), SyntaxError> {
        let span = head.span;
        match head.kind {
            ExprKind::Name(name) if is_type_name(name, self.source) => Ok((name, None)),
            ExprKind::Call(callee, arguments) if matches!(callee.kind, ExprKind::Name(name) if is_type_name(name, self.source)) =>
            {
                let ExprKind::Name(name) = callee.kind else {
                    unreachable!("matched above")
                };
                let parameters = arguments
                    .into_iter()
                    .map(|argument| match argument.kind {
                        ExprKind::Name(parameter)
                            if !is_type_name(parameter, self.source)
                                && !parameter.text(self.source).ends_with('!') =>
                        {
                            Ok(parameter)
                        }
                        _ => Err(SyntaxError::new(
                            argument.span,
                            "a type's parameter is a lowercase name",
                        )),
                    })
                    .collect::<Result<_, _>>()?;
                Ok((name, Some(parameters)))
            }
            _ => Err(SyntaxError::new(
                span,
                "a type's name, and its parameters if it has any",
            )),
        }
    }

    /// A signature or a data declaration, as its head is a term's name or
    /// a type's.
    fn typed(&mut self, head: Expr, typed: Typed) -> Result<(), SyntaxError> {
        let span = head.span;
        match head.kind {
            ExprKind::Name(name) if !is_type_name(name, self.source) => {
                if let Some((_, block)) = typed.methods {
                    return Err(SyntaxError::new(block, "only a type has a method block"));
                }
                let span = span.through(typed.end());
                let constraints = typed
                    .constraints
                    .map_or_else(Vec::new, |constraints| constraints.0);
                self.item(
                    span,
                    Item::Signature(SignatureDecl {
                        span,
                        name,
                        parameters: typed.parameters,
                        result: typed.result,
                        constraints,
                    }),
                )
            }
            _ => self.data(head, typed),
        }
    }

    /// `Name(a) : type .(methods)`: a data declaration, whose type in
    /// brackets is its constructors.
    fn data(&mut self, head: Expr, typed: Typed) -> Result<(), SyntaxError> {
        let span = head.span.through(typed.end());
        let (name, params) = self.type_head(head)?;
        if let Some(parameter) = typed.parameters.first() {
            return Err(SyntaxError::new(
                parameter.span(),
                "a type is represented by one type, not a function of some",
            ));
        }
        if let Some((_, constraints)) = typed.constraints {
            return Err(SyntaxError::new(
                constraints,
                "a type takes no `where` constraints",
            ));
        }
        let methods = match typed.methods {
            Some((lines, _)) => Grouping::new(self.source, true)
                .group(lines)?
                .into_iter()
                .map(|item| match item {
                    Item::Signature(signature) => MethodItem::Signature(signature),
                    Item::Clause(clause) => MethodItem::Clause(clause),
                    _ => unreachable!("a method block holds signatures and clauses"),
                })
                .collect(),
            None => Vec::new(),
        };
        let representation = match typed.result {
            Type::Variants { constructors, .. } => DataRepresentation::Sum(constructors),
            wrapped => DataRepresentation::Wrapper(wrapped),
        };
        self.item(
            span,
            Item::Data(DataDecl {
                span,
                name,
                params: params.unwrap_or_default(),
                representation,
                methods,
            }),
        )
    }
}

/// The body a clause's or an `expect`'s value makes: a block's lines, or
/// the value alone.
fn body_of(value: Expr) -> Body {
    match value.kind {
        ExprKind::Block(body) => *body,
        _ => Body {
            bindings: Vec::new(),
            result: value,
        },
    }
}

/// A block of its lines: the last, a value, is its answer, and each before
/// it binds a pattern, or `_` where it is a value asked for what it does.
/// Whether such a value is an effect, as only one may be, is asked once the
/// items are made ([`thrown_away`]).
///
/// # Errors
///
/// A binding whose head is no pattern.
pub(crate) fn body(lines: Vec<Statement>, source: &str) -> Result<Body, SyntaxError> {
    block(lines, source)
}

/// [`body`]: a block answers its last line where that is a value, and `{}`
/// where it is not.
fn block(lines: Vec<Statement>, source: &str) -> Result<Body, SyntaxError> {
    let (mut lines, held) = held(lines, source)?;
    let answered = matches!(lines.last(), Some(Statement::Value(_)));
    let result = match held {
        Some(held) => held,
        None if answered => {
            let Some(Statement::Value(value)) = lines.pop() else {
                unreachable!("the last line is a value")
            };
            value
        }
        // The whole of the line it answers after, a binding's pattern too,
        // where a mismatch is told.
        None => Expr {
            span: match lines.last() {
                Some(Statement::Binding(bound, value)) => bound.span.through(value.span),
                line => line.map_or_else(Span::default, statement_span),
            },
            kind: ExprKind::Record(Vec::new()),
        },
    };
    let bindings = lines
        .into_iter()
        .map(|line| binding(line, source))
        .collect::<Result<_, SyntaxError>>()?;
    Ok(Body { bindings, result })
}

/// Whether a line's value is one that goes on with nothing: arms, or an
/// `if` whose branches each answer `{}`, as a block of bindings does.
fn goes_on(value: &Expr) -> bool {
    match &value.kind {
        ExprKind::Match(..) => true,
        ExprKind::If(_, yes, no) => answers_nothing(yes) && answers_nothing(no),
        _ => false,
    }
}

/// Whether a branch answers `{}`: written so, or a block whose answer is.
fn answers_nothing(branch: &Expr) -> bool {
    match &branch.kind {
        ExprKind::Record(fields) => fields.is_empty(),
        ExprKind::Block(body) => answers_nothing(&body.result),
        _ => goes_on(branch),
    }
}

/// A block's line before its last as a binding: a value on a line of its
/// own is thrown away, but arms there go on with nothing, so each that does
/// not leave answers `{}`, and so does an `if` whose branches only bind.
fn binding(line: Statement, source: &str) -> Result<Binding, SyntaxError> {
    match line {
        Statement::Value(value) if goes_on(&value) => Ok(Binding {
            pattern: Pattern::Record {
                span: value.span,
                fields: Vec::new(),
                open: false,
            },
            value,
            discarded: false,
        }),
        Statement::Value(value) => Ok(Binding {
            pattern: Pattern::Wild(value.span),
            value,
            discarded: true,
        }),
        Statement::Binding(bound, value) => Ok(Binding {
            pattern: pattern(bound, source)?,
            value,
            discarded: false,
        }),
        Statement::Else(..) | Statement::If(..) => {
            unreachable!("a leaving line holds the lines after it")
        }
    }
}

/// Where `line` was written.
const fn statement_span(line: &Statement) -> Span {
    match line {
        Statement::Value(value) | Statement::Binding(_, value) => value.span,
        Statement::Else(span, ..) | Statement::If(span, ..) => *span,
    }
}

/// `lines` before their first leaving line, and that line holding the
/// lines after it, which go on where it does, those taken apart the same
/// way. The lines after it answer; where there are none, the block answers
/// `{}`.
fn held(
    mut lines: Vec<Statement>,
    source: &str,
) -> Result<(Vec<Statement>, Option<Expr>), SyntaxError> {
    let Some(at) = lines
        .iter()
        .position(|line| matches!(line, Statement::Else(..) | Statement::If(..)))
    else {
        return Ok((lines, None));
    };
    let rest = lines.split_off(at + 1);
    // What is left keeps what it held for every line; the rest are held
    // again further in, each line once.
    lines.shrink_to_fit();
    let line = lines.pop().expect("the line found");
    let span = statement_span(&line);
    let empty = rest.is_empty();
    let mut rest = Box::new(block(rest, source)?);
    if empty {
        // A block answering `{}` after its last line, which is this one.
        rest.result.span = span;
    }
    let span = span.through(rest.result.span);
    let kind = match line {
        Statement::Else(_, condition, otherwise) => ExprKind::Else {
            condition: Box::new(condition),
            otherwise: Box::new(otherwise),
            rest,
        },
        Statement::If(_, condition, out) => ExprKind::Leave {
            condition: Box::new(condition),
            out: Box::new(out),
            rest,
        },
        _ => unreachable!("the line found leaves"),
    };
    Ok((lines, Some(Expr { span, kind })))
}

/// Refuse a line of a body whose value nothing keeps, unless it is a call
/// written as an effect, its failure passed on with `?` or not.
fn thrown_away(body: &Body, source: &str) -> Result<(), SyntaxError> {
    for binding in body.bindings.iter().filter(|binding| binding.discarded) {
        let value = &binding.value;
        let mut called = value;
        while let ExprKind::Try(tried) = &called.kind {
            called = tried;
        }
        let effect = match &called.kind {
            ExprKind::Call(head, _) => {
                matches!(&head.kind, ExprKind::Name(name) if name.text(source).ends_with('!'))
            }
            ExprKind::Method(_, name, _) => name.text(source).ends_with('!'),
            _ => false,
        };
        if !effect {
            return Err(SyntaxError::new(
                value.span,
                "this value is worked out and then thrown away",
            )
            .label("unused")
            .help("remove the line, or bind the value to a name if you need it"));
        }
    }
    Ok(())
}

/// The patterns `exprs` spell.
fn patterns(exprs: Vec<Expr>, source: &str) -> Result<Vec<Pattern>, SyntaxError> {
    exprs
        .into_iter()
        .map(|expr| pattern(expr, source))
        .collect()
}

/// The pattern `expr` spells: the expression that would build what it
/// matches.
///
/// # Errors
///
/// An expression no pattern is spelled as.
#[expect(
    clippy::too_many_lines,
    reason = "one arm for each expression a pattern is spelled as"
)]
pub(crate) fn pattern(expr: Expr, source: &str) -> Result<Pattern, SyntaxError> {
    let span = expr.span;
    let not_a_pattern = || {
        SyntaxError::new(
            span,
            format!(
                "`{}` is not a pattern: a pattern is a name, `_`, a constructor, a literal, \
                 a range, a list, a record or a tuple",
                span.text(source)
            ),
        )
    };
    let constructor = |qualifier: Option<Name>, name: Name, fields: Vec<Expr>| {
        if !is_type_name(name, source) {
            return Err(not_a_pattern());
        }
        Ok(Pattern::Constructor {
            span,
            qualifier,
            name,
            fields: patterns(fields, source)?,
        })
    };
    let qualifier = |receiver: &Expr| match receiver.kind {
        ExprKind::Name(qualifier) if is_type_name(qualifier, source) => Some(qualifier),
        _ => None,
    };
    match expr.kind {
        ExprKind::Wild => Ok(Pattern::Wild(span)),
        ExprKind::Equal(name) => Ok(Pattern::Equal { span, name }),
        ExprKind::Name(name) if is_type_name(name, source) => constructor(None, name, Vec::new()),
        ExprKind::Name(name) if name.text(source).ends_with('!') => Err(not_a_pattern()),
        ExprKind::Name(name) => Ok(Pattern::Bind(name)),
        ExprKind::Number(numeral) if numeral.kind != NumeralKind::Decimal => Ok(Pattern::Number {
            span,
            numeral,
            negative: false,
        }),
        ExprKind::Unary(UnaryOp::Negate, value) => match value.kind {
            ExprKind::Number(numeral) if numeral.kind != NumeralKind::Decimal => {
                Ok(Pattern::Number {
                    span,
                    numeral,
                    negative: true,
                })
            }
            _ => Err(not_a_pattern()),
        },
        ExprKind::Range(None, None) => Err(SyntaxError::new(
            span,
            "`_.._` bounds nothing: it is the wildcard `_`",
        )),
        ExprKind::Range(start, end) => {
            if start.zip(end).is_some_and(|(start, end)| {
                // A malformed end is told when literals are validated.
                bound_value(start, source)
                    .zip(bound_value(end, source))
                    .is_some_and(|(start, end)| start > end)
            }) {
                let message = format!("the range `{}` is reversed", span.text(source));
                return Err(SyntaxError::new(span, message)
                    .label("matches nothing")
                    .note("a range runs up, from its start to its end"));
            }
            Ok(Pattern::Range { span, start, end })
        }
        ExprKind::String(parts) => Ok(Pattern::String {
            span,
            parts: parts
                .into_iter()
                .map(|part| match part {
                    StringPart::Text(text) => Ok(text),
                    StringPart::Splice(splice, _) => Err(SyntaxError::new(
                        splice.span,
                        "a string pattern is text alone, with no `${...}`",
                    )),
                })
                .collect::<Result<_, _>>()?,
        }),
        ExprKind::List(elements, rest) => Ok(Pattern::List {
            span,
            elements: patterns(elements, source)?,
            rest: rest
                .map(|rest| pattern(*rest, source).map(Box::new))
                .transpose()?,
        }),
        ExprKind::Ending(front, last) => Ok(Pattern::Ending {
            span,
            front: Box::new(pattern(*front, source)?),
            last: patterns(last, source)?,
        }),
        ExprKind::Record(fields) => record(span, fields, false, source),
        ExprKind::Update(fields, base) => {
            if !matches!(base.kind, ExprKind::Wild) {
                return Err(SyntaxError::new(
                    base.span,
                    "a record pattern names no rest: `{x, *}` matches any other fields",
                ));
            }
            record(span, fields, true, source)
        }
        ExprKind::Tuple(members) => Ok(Pattern::Tuple {
            span,
            members: patterns(members, source)?,
        }),
        ExprKind::Call(callee, fields) if !fields.is_empty() => match callee.kind {
            ExprKind::Name(name) => constructor(None, name, fields),
            _ => Err(not_a_pattern()),
        },
        ExprKind::Member(ref receiver, name) => qualifier(receiver).map_or_else(
            || Err(not_a_pattern()),
            |qualifier| constructor(Some(qualifier), name, Vec::new()),
        ),
        ExprKind::Method(ref receiver, name, ref fields) if !fields.is_empty() => {
            match qualifier(receiver) {
                Some(qualifier) => {
                    let ExprKind::Method(_, _, fields) = expr.kind else {
                        unreachable!("matched above")
                    };
                    constructor(Some(qualifier), name, fields)
                }
                None => Err(not_a_pattern()),
            }
        }
        // The whole value named, and taken apart.
        ExprKind::Is(value, inner) => match value.kind {
            ExprKind::Name(name) if !is_type_name(name, source) => Ok(Pattern::As {
                span,
                name,
                pattern: Box::new(inner),
            }),
            _ => Err(SyntaxError::new(
                value.span,
                "in a pattern, `is` names the whole value: a name stands on its left",
            )),
        },
        ExprKind::Binary(BinaryOp::Or, left, right) => {
            let mut alternatives = Vec::new();
            for side in [*left, *right] {
                match pattern(side, source)? {
                    Pattern::Or {
                        alternatives: more, ..
                    } => alternatives.extend(more),
                    single => alternatives.push(single),
                }
            }
            Ok(Pattern::Or { span, alternatives })
        }
        _ => Err(not_a_pattern()),
    }
}

fn record(
    span: Span,
    fields: Vec<(Name, Expr)>,
    open: bool,
    source: &str,
) -> Result<Pattern, SyntaxError> {
    Ok(Pattern::Record {
        span,
        fields: fields
            .into_iter()
            .map(|(field, value)| Ok((field, pattern(value, source)?)))
            .collect::<Result<_, SyntaxError>>()?,
        open,
    })
}

/// Refuse a pattern-only form left in a clause's expressions, and a value
/// a body throws away.
fn clause_expressions(clause: &Clause, source: &str) -> Result<(), SyntaxError> {
    if let Some(guard) = &clause.guard {
        expression(guard, source, false)?;
    }
    body_expressions(&clause.body, source)
}

fn body_expressions(body: &Body, source: &str) -> Result<(), SyntaxError> {
    thrown_away(body, source)?;
    for binding in &body.bindings {
        expression(&binding.value, source, true)?;
    }
    expression(&body.result, source, true)
}

/// Refuse a pattern-only form anywhere in `expr`, and a leaving arm where
/// `expr` is not the `whole` of a line's value, or a branch of one.
#[expect(
    clippy::too_many_lines,
    reason = "one arm for each kind of expression, to reach every one it holds"
)]
fn expression(expr: &Expr, source: &str, whole: bool) -> Result<(), SyntaxError> {
    match &expr.kind {
        ExprKind::Wild => Err(SyntaxError::new(expr.span, "`_` stands only in a pattern")),
        ExprKind::Equal(_) => Err(SyntaxError::new(
            expr.span,
            format!(
                "`{}` stands only in a pattern, where it matches a value equal to the name",
                expr.span.text(source)
            ),
        )
        .help("to compare two values, write `==` between them")),
        ExprKind::Range(..) => Err(SyntaxError::new(
            expr.span,
            "a range stands only in a pattern",
        )),
        ExprKind::Ending(..) => Err(SyntaxError::new(
            expr.span,
            "a list's rest stands last where the list is built",
        )
        .note("`[*front, last]` only takes a list apart")
        .help("build it with `front.append(last)`")),
        ExprKind::List(_, Some(rest)) if matches!(rest.kind, ExprKind::Wild) => Err(
            SyntaxError::new(rest.span, "a list's rest names what follows: `[a, *rest]`"),
        ),
        ExprKind::Update(_, base) if matches!(base.kind, ExprKind::Wild) => Err(SyntaxError::new(
            base.span,
            "a record's rest names the record it updates: `{x: 1, *base}`",
        )),
        ExprKind::Lambda(_, body) => expression(body, source, true),
        ExprKind::Block(body) => body_expressions(body, source),
        ExprKind::Binary(operator @ (BinaryOp::And | BinaryOp::Or), left, right) => {
            if *operator == BinaryOp::Or && is_test(left) && is_constructor(right, source) {
                return Err(SyntaxError::new(
                    right.span,
                    "alternatives after `is` are grouped, or `|` reads as an or of a test",
                )
                .label("taken as a `Bool`")
                .help("write the alternatives in parentheses: `x is (A | B)`"));
            }
            if let Some(span) = passed_on(right) {
                return Err(SyntaxError::new(
                    span,
                    "the right of `&` or `|` may not be worked out, so `?` does not leave from it",
                )
                .label("would leave here")
                .help("bind it with `?` on a line before, and use the name here"));
            }
            expr.try_for_each_child(|inner| expression(inner, source, false))
        }
        ExprKind::Arms(arms) => Err(SyntaxError::new(
            arms.first().map_or(expr.span, |arm| arm.pattern.span()),
            "arms stand after an `is`, which says what they match: `value is (P then a` … `)`",
        )),
        // An arm is a branch, which may leave where a line could.
        ExprKind::Match(value, arms) => {
            expression(value, source, false)?;
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    expression(guard, source, false)?;
                }
                let leaves = matches!(arm.body.kind, ExprKind::Return(_));
                if leaves && !whole {
                    return Err(SyntaxError::new(
                        arm.body.span,
                        "an arm leaves only where its `is` is a line's value, or a body's answer",
                    )
                    .help(
                        "bind what the `is` answers on a line of its own, and use the name here",
                    ));
                }
                if leaves {
                    left_by(&arm.body, source)?;
                } else {
                    expression(&arm.body, source, whole)?;
                }
            }
            Ok(())
        }
        // A branch may leave, as a body may.
        ExprKind::If(condition, yes, no) => {
            expression(condition, source, false)?;
            expression(yes, source, whole)?;
            expression(no, source, whole)
        }
        ExprKind::Else {
            condition,
            otherwise,
            rest,
        } => {
            expression(condition, source, false)?;
            left_by(otherwise, source)?;
            body_expressions(rest, source)
        }
        // What the condition binds, the leave sees; the lines after it
        // answer where it fails.
        ExprKind::Leave {
            condition,
            out,
            rest,
        } => {
            expression(condition, source, false)?;
            left_by(out, source)?;
            body_expressions(rest, source)
        }
        ExprKind::Return(_) => Err(SyntaxError::new(
            expr.span,
            "`return` stands only in a leaving line, `c else return x` or `if c return x`, \
             or an arm, `P return x`",
        )),
        _ => expr.try_for_each_child(|inner| expression(inner, source, false)),
    }
}

/// Refuse a pattern-only form in what `leave` leaves with.
fn left_by(leave: &Expr, source: &str) -> Result<(), SyntaxError> {
    match &leave.kind {
        ExprKind::Return(value) => expression(value, source, true),
        _ => Err(SyntaxError::new(
            leave.span,
            "a leaving line leaves by `return` a value",
        )),
    }
}

/// Whether `expr` is a test, or a chain of `&` ending in one.
fn is_test(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Is(..) => true,
        ExprKind::Binary(BinaryOp::And, _, right) => is_test(right),
        _ => false,
    }
}

/// Whether `expr` names a constructor, alone or applied: what an
/// alternative after `is` would be.
fn is_constructor(expr: &Expr, source: &str) -> bool {
    match &expr.kind {
        ExprKind::Name(name) => is_type_name(*name, source),
        ExprKind::Call(head, _) => is_constructor(head, source),
        _ => false,
    }
}

/// Where `expr` passes a failure on with `?` from the clause it stands in:
/// a `?` in a lambda answers the lambda, so one there is not.
fn passed_on(expr: &Expr) -> Option<Span> {
    match &expr.kind {
        ExprKind::Try(_) => Some(expr.span),
        ExprKind::Lambda(..) => None,
        _ => expr
            .try_for_each_child(|inner| passed_on(inner).map_or(Ok(()), Err))
            .err(),
    }
}

/// The value a range's end is written as, where its numeral reads.
fn bound_value(bound: Bound, source: &str) -> Option<num_bigint::BigInt> {
    let magnitude =
        num_bigint::BigInt::from(crate::literal::magnitude(bound.numeral, source).ok()?);
    Some(if bound.negative {
        -magnitude
    } else {
        magnitude
    })
}
