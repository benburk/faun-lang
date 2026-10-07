//! From a file's lines to its items, a line apiece.
//!
//! The grammar reads a line as an expression, and what the token after it
//! says the line is: `: type` declares, and `-> value` is a clause. A pattern
//! is written as the expression that would build what it matches, so the
//! head of a clause, a lambda's parameters and a block's bindings are read
//! as expressions and made patterns here, once the line has said they are
//! ones. A body of several lines is a block, and a `where` list's
//! constraints are parted by commas, so each line is one item whole.
//!
//! An expression may hold what only a pattern can, `_`, a range, or a rest
//! with nothing after its `*`, since it is read before anyone knows which it
//! is; such a form is refused wherever it stays an expression.

use super::ast::{
    AliasDecl, Arm, BinaryOp, Binding, Body, Bound, Clause, Constraint, ConstraintAliasDecl,
    DataDecl, DataRepresentation, ExportsDecl, Expr, ExprKind, HeaderDecl, ImportDecl, Item,
    MethodItem, Name, NumeralKind, Pattern, SignatureDecl, Span, StringPart, Type, UnaryOp,
};
use super::diagnostic::{Advice, Advised};

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
                    .map_or_else(|| type_span(&self.result), |constraints| constraints.1)
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
}

/// Why lines do not make items.
#[derive(Debug)]
pub(crate) struct Error {
    pub(crate) span: Span,
    pub(crate) message: String,
    pub(crate) advice: Advice,
}

impl Advised for Error {
    fn advice(&mut self) -> &mut Advice {
        &mut self.advice
    }
}

fn error(span: Span, message: impl Into<String>) -> Error {
    Error {
        span,
        message: message.into(),
        advice: Advice::default(),
    }
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
pub(crate) fn items(lines: Vec<Line>, source: &str) -> Result<Vec<Item>, Error> {
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

    fn group(mut self, lines: Vec<Line>) -> Result<Vec<Item>, Error> {
        for line in lines {
            self.line(line)?;
        }
        Ok(self.items)
    }

    fn line(&mut self, line: Line) -> Result<(), Error> {
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
                let span = head.span.through(type_span(&ty));
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
    fn clause(&mut self, head: Expr, guard: Option<Expr>, value: Expr) -> Result<(), Error> {
        let (name, arguments) = self.clause_head(head)?;
        if arguments.is_empty() {
            let text = name.text(self.source);
            let message = if text.ends_with('!') {
                "a definition of no parameters is a value, and a value is no effect".to_owned()
            } else {
                format!("a definition of no parameters is a value: `{text} = ...`")
            };
            return Err(error(name.0, message));
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
    fn value(&mut self, head: &Expr, value: Expr) -> Result<(), Error> {
        let span = head.span;
        let ExprKind::Name(name) = head.kind else {
            return Err(error(span, "a value is named by one name: `name = ...`"));
        };
        let text = name.text(self.source);
        if text.ends_with('!') {
            return Err(error(span, "a value is no effect: its name takes no `!`"));
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
    ) -> Result<(), Error> {
        let span = head.span;
        let (name, Some(parameters)) = self.type_head(head)? else {
            return Err(error(
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
    fn item(&mut self, span: Span, item: Item) -> Result<(), Error> {
        if self.methods && !matches!(item, Item::Signature(_) | Item::Clause(_)) {
            return Err(error(span, "a method block holds signatures and clauses"));
        }
        self.items.push(item);
        Ok(())
    }

    /// A clause's name and what it is applied to: `name(patterns)`.
    fn clause_head(&self, head: Expr) -> Result<(Name, Vec<Expr>), Error> {
        let span = head.span;
        if let ExprKind::Call(callee, arguments) = head.kind
            && let ExprKind::Name(name) = callee.kind
            && !is_type_name(name, self.source)
        {
            return Ok((name, arguments));
        }
        Err(error(
            span,
            "a clause begins with its name and its patterns: `name(patterns) -> ...`",
        ))
    }

    /// A type's name and its parameters, if it is written with any:
    /// `Name`, or `Name(a, b)`.
    fn type_head(&self, head: Expr) -> Result<(Name, Option<Vec<Name>>), Error> {
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
                        _ => Err(error(
                            argument.span,
                            "a type's parameter is a lowercase name",
                        )),
                    })
                    .collect::<Result<_, _>>()?;
                Ok((name, Some(parameters)))
            }
            _ => Err(error(
                span,
                "a type's name, and its parameters if it has any",
            )),
        }
    }

    /// A signature, a data declaration, or a `where` list's constraint,
    /// as its head is a term's name, a type's, or a type variable's member.
    fn typed(&mut self, head: Expr, typed: Typed) -> Result<(), Error> {
        let span = head.span;
        match head.kind {
            ExprKind::Member(..) => Err(error(
                span,
                "a `where` list's constraints are parted by commas, \
                 `where a.zero : a, a.add : (a, a) -> a`, and a list of one to a line ends each \
                 but the last with its comma",
            )),
            ExprKind::Name(name) if !is_type_name(name, self.source) => {
                if let Some((_, block)) = typed.methods {
                    return Err(error(block, "only a type has a method block"));
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
    fn data(&mut self, head: Expr, typed: Typed) -> Result<(), Error> {
        let span = head.span.through(typed.end());
        let (name, params) = self.type_head(head)?;
        if let Some(parameter) = typed.parameters.first() {
            return Err(error(
                type_span(parameter),
                "a type is represented by one type, not a function of some",
            ));
        }
        if let Some((_, constraints)) = typed.constraints {
            return Err(error(constraints, "a type takes no `where` constraints"));
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
/// A block that ends in a binding, or a binding whose head is no pattern.
pub(crate) fn body(lines: Vec<Statement>, source: &str) -> Result<Body, Error> {
    let mut lines = held(lines, source)?;
    let result = match lines.pop().expect("a block has its first line") {
        Statement::Value(value) => value,
        Statement::Binding(_, value) => {
            return Err(error(
                value.span,
                "a block ends with its answer, a line after its last binding",
            ));
        }
        Statement::Else(..) => unreachable!("an `else` line holds the lines after it"),
    };
    let bindings = lines
        .into_iter()
        .map(|line| match line {
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
            Statement::Else(..) => unreachable!("an `else` line holds the lines after it"),
        })
        .collect::<Result<_, Error>>()?;
    Ok(Body { bindings, result })
}

/// `lines` with their first `else` line holding the lines after it, which
/// answer where it holds, those taken apart the same way.
fn held(mut lines: Vec<Statement>, source: &str) -> Result<Vec<Statement>, Error> {
    let Some(at) = lines
        .iter()
        .position(|line| matches!(line, Statement::Else(..)))
    else {
        return Ok(lines);
    };
    let rest = lines.split_off(at + 1);
    let Some(Statement::Else(span, condition, otherwise)) = lines.pop() else {
        unreachable!("the line found has an `else`")
    };
    if rest.is_empty() {
        return Err(error(
            span,
            "a line with `else` is not a block's last: the lines after it answer where its condition holds",
        ));
    }
    let rest = body(rest, source)?;
    lines.push(Statement::Value(Expr {
        span: span.through(rest.result.span),
        kind: ExprKind::Else {
            condition: Box::new(condition),
            otherwise: Box::new(otherwise),
            rest: Box::new(rest),
        },
    }));
    Ok(lines)
}

/// Refuse a line of a body whose value nothing keeps, unless it is a call
/// written as an effect, its failure passed on with `?` or not.
fn thrown_away(body: &Body, source: &str) -> Result<(), Error> {
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
            return Err(
                error(value.span, "this value is worked out and then thrown away")
                    .label("unused")
                    .help("remove the line, or bind the value to a name if you need it"),
            );
        }
    }
    Ok(())
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

/// The patterns `exprs` spell.
fn patterns(exprs: Vec<Expr>, source: &str) -> Result<Vec<Pattern>, Error> {
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
pub(crate) fn pattern(expr: Expr, source: &str) -> Result<Pattern, Error> {
    let span = expr.span;
    let not_a_pattern = || {
        error(
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
        ExprKind::Range(None, None) => {
            Err(error(span, "`_.._` bounds nothing: it is the wildcard `_`"))
        }
        ExprKind::Range(start, end) => {
            if start.zip(end).is_some_and(|(start, end)| {
                // A malformed end is told when literals are validated.
                bound_value(start, source)
                    .zip(bound_value(end, source))
                    .is_some_and(|(start, end)| start > end)
            }) {
                let message = format!("the range `{}` is reversed", span.text(source));
                return Err(error(span, message)
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
                    StringPart::Splice(splice, _) => Err(error(
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
                return Err(error(
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
            _ => Err(error(
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
) -> Result<Pattern, Error> {
    Ok(Pattern::Record {
        span,
        fields: fields
            .into_iter()
            .map(|(field, value)| Ok((field, pattern(value, source)?)))
            .collect::<Result<_, Error>>()?,
        open,
    })
}

/// Refuse a pattern-only form left in a clause's expressions, and a value
/// a body throws away.
fn clause_expressions(clause: &Clause, source: &str) -> Result<(), Error> {
    if let Some(guard) = &clause.guard {
        expression(guard, source, false)?;
    }
    body_expressions(&clause.body, source, true)
}

fn body_expressions(body: &Body, source: &str, answering: bool) -> Result<(), Error> {
    thrown_away(body, source)?;
    for binding in &body.bindings {
        expression(&binding.value, source, false)?;
    }
    expression(&body.result, source, answering)
}

/// Refuse a pattern-only form anywhere in `expr`.
#[expect(
    clippy::too_many_lines,
    reason = "one arm for each kind of expression, to reach every one it holds"
)]
fn expression(expr: &Expr, source: &str, answering: bool) -> Result<(), Error> {
    match &expr.kind {
        ExprKind::Wild => Err(error(expr.span, "`_` stands only in a pattern")),
        ExprKind::Equal(_) => Err(error(
            expr.span,
            format!(
                "`{}` stands only in a pattern, where it matches a value equal to the name",
                expr.span.text(source)
            ),
        )
        .help("to compare two values, write `==` between them")),
        ExprKind::Range(..) => Err(error(expr.span, "a range stands only in a pattern")),
        ExprKind::Ending(..) => Err(error(
            expr.span,
            "a list's rest stands last where the list is built",
        )
        .note("`[*front, last]` only takes a list apart")
        .help("build it with `front.append(last)`")),
        ExprKind::Name(_) | ExprKind::Number(_) => Ok(()),
        ExprKind::String(parts) => parts.iter().try_for_each(|part| match part {
            StringPart::Text(_) => Ok(()),
            StringPart::Splice(splice, _) => expression(splice, source, false),
        }),
        ExprKind::List(elements, rest) => {
            if let Some(rest) = rest
                && matches!(rest.kind, ExprKind::Wild)
            {
                return Err(error(
                    rest.span,
                    "a list's rest names what follows: `[a, *rest]`",
                ));
            }
            elements
                .iter()
                .chain(rest.as_deref())
                .try_for_each(|each| expression(each, source, false))
        }
        ExprKind::Record(fields) => fields
            .iter()
            .try_for_each(|(_, value)| expression(value, source, false)),
        ExprKind::Update(fields, base) => {
            if matches!(base.kind, ExprKind::Wild) {
                return Err(error(
                    base.span,
                    "a record's rest names the record it updates: `{x: 1, *base}`",
                ));
            }
            fields
                .iter()
                .map(|(_, value)| value)
                .chain(std::iter::once(&**base))
                .try_for_each(|each| expression(each, source, false))
        }
        ExprKind::Tuple(members) => members
            .iter()
            .try_for_each(|each| expression(each, source, false)),
        ExprKind::Lambda(_, body) => expression(body, source, true),
        ExprKind::Call(head, arguments) | ExprKind::Method(head, _, arguments) => {
            expression(head, source, false)?;
            arguments
                .iter()
                .try_for_each(|each| expression(each, source, false))
        }
        ExprKind::Member(value, _) | ExprKind::Unary(_, value) | ExprKind::Try(value) => {
            expression(value, source, false)
        }
        ExprKind::Block(body) => body_expressions(body, source, answering),
        ExprKind::Binary(operator @ (BinaryOp::And | BinaryOp::Or), left, right) => {
            if *operator == BinaryOp::Or && is_test(left) && is_constructor(right, source) {
                return Err(error(
                    right.span,
                    "alternatives after `is` are grouped, or `|` reads as an or of a test",
                )
                .label("taken as a `Bool`")
                .help("write the alternatives in parentheses: `x is (A | B)`"));
            }
            if let Some(span) = passed_on(right) {
                return Err(error(
                    span,
                    "the right of `&` or `|` may not be worked out, so `?` does not leave from it",
                )
                .label("would leave here")
                .help("bind it with `?` on a line before, and use the name here"));
            }
            expression(left, source, false)?;
            expression(right, source, false)
        }
        ExprKind::Binary(_, left, right) => {
            expression(left, source, false)?;
            expression(right, source, false)
        }
        ExprKind::Is(value, _) => expression(value, source, false),
        ExprKind::Arms(arms) => Err(error(
            arms.first().map_or(expr.span, |arm| arm.pattern.span()),
            "arms stand after an `is`, which says what they match: `value is (P -> a` … `)`",
        )),
        // An arm is a branch: where the `is` answers the clause, it may
        // leave it.
        ExprKind::Match(value, arms) => {
            expression(value, source, false)?;
            for arm in arms {
                if !answering && let Some(span) = passed_on(&arm.body) {
                    return Err(
                        error(span, "an arm is a value, so `?` does not leave from it")
                            .label("would leave here")
                            .help(
                                "answer a `Result` from every arm, and ask `?` of the whole `is`",
                            ),
                    );
                }
                if let Some(guard) = &arm.guard {
                    expression(guard, source, false)?;
                }
                expression(&arm.body, source, answering)?;
            }
            Ok(())
        }
        // A branch that answers the clause may leave it, as its body may;
        // one whose value goes on into more of the body cannot, yet.
        ExprKind::If(condition, yes, no) => {
            for branch in [yes, no].into_iter().filter(|_| !answering) {
                if let Some(span) = passed_on(branch) {
                    return Err(error(
                        span,
                        "a branch of an `if` is a value, so `?` does not leave from it",
                    )
                    .label("would leave here")
                    .help(
                        "answer a `Result` from both branches, and ask `?` of the whole `if`: \
                               `(if c then f(x) else Ok(0))?`",
                    ));
                }
            }
            expression(condition, source, false)?;
            expression(yes, source, answering)?;
            expression(no, source, answering)
        }
        ExprKind::Else {
            condition,
            otherwise,
            rest,
        } => {
            if !answering {
                return Err(error(
                    expr.span,
                    "a line's `else` leaves where its block answers the clause or lambda, and nowhere else yet",
                )
                .label("its block's value goes on into more of the body")
                .help("take this step out into a function of its own, where its block answers"));
            }
            let leaving = match &otherwise.kind {
                ExprKind::Return(value) => Some(value),
                ExprKind::Block(body) => match &body.result.kind {
                    ExprKind::Return(value) => {
                        thrown_away(body, source)?;
                        for binding in &body.bindings {
                            expression(&binding.value, source, false)?;
                        }
                        Some(value)
                    }
                    _ => None,
                },
                _ => None,
            };
            let Some(value) = leaving else {
                return Err(error(
                    otherwise.span,
                    "a line's `else` leaves: `return` a value, or a block whose last line does",
                )
                .label("goes on rather than leaving"));
            };
            expression(condition, source, false)?;
            expression(value, source, true)?;
            body_expressions(rest, source, true)
        }
        ExprKind::Return(_) => Err(error(
            expr.span,
            "`return` stands only where a line's `else` leaves: `c else return x`",
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
/// Where a `?` in `arms`, in a guard or a value, would leave from.
fn arms_passed_on(arms: &[Arm]) -> Option<Span> {
    arms.iter()
        .find_map(|arm| arm.guard.iter().chain([&arm.body]).find_map(passed_on))
}

#[expect(
    clippy::too_many_lines,
    reason = "one arm for each kind of expression, to reach every one it holds"
)]
fn passed_on(expr: &Expr) -> Option<Span> {
    fn each<'a>(exprs: impl IntoIterator<Item = &'a Expr>) -> Option<Span> {
        exprs.into_iter().find_map(passed_on)
    }
    match &expr.kind {
        ExprKind::Try(_) => Some(expr.span),
        ExprKind::Lambda(..)
        | ExprKind::Name(_)
        | ExprKind::Number(_)
        | ExprKind::Wild
        | ExprKind::Equal(_)
        | ExprKind::Range(..) => None,
        ExprKind::String(parts) => parts.iter().find_map(|part| match part {
            StringPart::Text(_) => None,
            StringPart::Splice(splice, _) => passed_on(splice),
        }),
        ExprKind::List(elements, rest) => each(elements.iter().chain(rest.as_deref())),
        ExprKind::Ending(front, last) => each(std::iter::once(&**front).chain(last)),
        ExprKind::Record(fields) => each(fields.iter().map(|(_, value)| value)),
        ExprKind::Update(fields, base) => {
            each(fields.iter().map(|(_, value)| value).chain([&**base]))
        }
        ExprKind::Tuple(members) => each(members.iter()),
        ExprKind::Call(head, arguments) | ExprKind::Method(head, _, arguments) => {
            each(std::iter::once(&**head).chain(arguments))
        }
        ExprKind::Member(value, _) | ExprKind::Unary(_, value) | ExprKind::Is(value, _) => {
            passed_on(value)
        }
        ExprKind::Binary(_, left, right) => each([&**left, &**right]),
        ExprKind::If(condition, yes, no) => each([&**condition, &**yes, &**no]),
        ExprKind::Match(value, arms) => passed_on(value).or_else(|| arms_passed_on(arms)),
        ExprKind::Arms(arms) => arms_passed_on(arms),
        ExprKind::Return(value) => passed_on(value),
        ExprKind::Else {
            condition,
            otherwise,
            rest,
        } => each(
            [&**condition, &**otherwise]
                .into_iter()
                .chain(rest.bindings.iter().map(|binding| &binding.value))
                .chain([&rest.result]),
        ),
        ExprKind::Block(body) => each(
            body.bindings
                .iter()
                .map(|binding| &binding.value)
                .chain([&body.result]),
        ),
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
