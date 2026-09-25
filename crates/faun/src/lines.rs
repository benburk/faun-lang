//! From a file's lines to its items.
//!
//! The grammar reads every line the same way: an expression, and what the
//! token after it says the line is. `= value` binds, `: type` declares,
//! `-> value` begins a clause, and a line with none of these is a value. A
//! pattern is written as the expression that would build what it matches, so
//! the head of a binding or a clause is read as an expression and made a
//! pattern here, once the line has said it is one. Then lines are grouped: a
//! clause or an `expect` takes the lines after it as its body, and a
//! signature the `where` lines after it as its constraints.
//!
//! An expression may hold what only a pattern can, `_`, a range, or a rest
//! with nothing after its `*`, since it is read before anyone knows which it
//! is; such a form is refused wherever it stays an expression.

use super::ast::{
    AliasDecl, Binding, Body, Bound, Clause, Constraint, ConstraintAliasDecl, DataDecl,
    DataRepresentation, ExportsDecl, Expr, ExprKind, HeaderDecl, ImportDecl, Item, MethodItem,
    Name, NumeralKind, Pattern, SignatureDecl, Span, StringPart, Type, UnaryOp,
};

/// One line of a file or of a method block, as the grammar reads it.
#[derive(Debug)]
pub(crate) enum Line {
    Header(HeaderDecl),
    Import(ImportDecl),
    Exports(ExportsDecl),
    /// `expect` and its first line.
    Expect(Span, Statement),
    /// A value, or a binding: a line of a body.
    Statement(Statement),
    /// `head if guard -> first`: a clause and its first line.
    Clause {
        head: Expr,
        guard: Option<Expr>,
        first: Statement,
    },
    /// `head : ...`: a signature, a data declaration, or a `where` list's
    /// constraint.
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

/// A line of a body: a value, or `pattern = value`.
#[derive(Debug)]
pub(crate) enum Statement {
    Value(Expr),
    Binding(Expr, Expr),
}

/// What follows the expression beginning a line.
#[derive(Debug)]
pub(crate) enum Trailer {
    Equals(Equals),
    Typed(Typed),
    Clause {
        guard: Option<Expr>,
        first: Statement,
    },
}

/// What follows `=`.
#[derive(Debug)]
pub(crate) enum Equals {
    Value(Expr),
    Type(Type),
    Constraints((Vec<Constraint>, Span)),
}

impl Line {
    /// The line an expression and what follows it make.
    pub(crate) fn new(head: Expr, trailer: Option<Trailer>) -> Self {
        match trailer {
            None => Self::Statement(Statement::Value(head)),
            Some(Trailer::Equals(Equals::Value(value))) => {
                Self::Statement(Statement::Binding(head, value))
            }
            Some(Trailer::Equals(Equals::Type(ty))) => Self::Alias(head, ty),
            Some(Trailer::Equals(Equals::Constraints(constraints))) => {
                Self::Constraints(head, constraints)
            }
            Some(Trailer::Typed(typed)) => Self::Typed(head, typed),
            Some(Trailer::Clause { guard, first }) => Self::Clause { head, guard, first },
        }
    }
}

/// Why lines do not make items.
#[derive(Debug)]
pub(crate) struct Error {
    pub(crate) span: Span,
    pub(crate) message: String,
}

fn error(span: Span, message: impl Into<String>) -> Error {
    Error {
        span,
        message: message.into(),
    }
}

/// Whether `name` is a type's or a constructor's.
pub(crate) fn is_type_name(name: Name, source: &str) -> bool {
    name.text(source)
        .starts_with(|c: char| c.is_ascii_uppercase())
}

/// Whether `head` is a type's name alone, whose `=` names a type.
pub(crate) fn names_a_type(head: &Expr, source: &str) -> bool {
    matches!(head.kind, ExprKind::Name(name) if is_type_name(name, source))
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
            Item::Clause(clause) | Item::Expect(clause) => clause_expressions(clause)?,
            Item::Data(data) => {
                for method in &data.methods {
                    if let MethodItem::Clause(clause) = method {
                        clause_expressions(clause)?;
                    }
                }
            }
            _ => {}
        }
    }
    Ok(items)
}

/// A body being gathered: its clause, or its `expect`, and its lines.
struct Open {
    name: Name,
    start: Span,
    patterns: Vec<Pattern>,
    guard: Option<Expr>,
    expect: bool,
    lines: Vec<Statement>,
}

struct Grouping<'s> {
    source: &'s str,
    /// Whether these are a method block's lines, which hold only
    /// signatures and clauses.
    methods: bool,
    items: Vec<Item>,
    open: Option<Open>,
}

impl<'s> Grouping<'s> {
    const fn new(source: &'s str, methods: bool) -> Self {
        Self {
            source,
            methods,
            items: Vec::new(),
            open: None,
        }
    }

    fn group(mut self, lines: Vec<Line>) -> Result<Vec<Item>, Error> {
        for line in lines {
            if let Line::Statement(statement) = line {
                let Some(open) = &mut self.open else {
                    return Err(error(
                        statement_span(&statement),
                        "this line belongs to no definition: a body's lines follow its clause's `->`",
                    ));
                };
                open.lines.push(statement);
                continue;
            }
            self.close()?;
            self.line(line)?;
        }
        self.close()?;
        Ok(self.items)
    }

    fn line(&mut self, line: Line) -> Result<(), Error> {
        match line {
            Line::Statement(_) => unreachable!("statements join the open body"),
            Line::Header(header) => self.item(header.span, Item::Header(header)),
            Line::Import(import) => self.item(import.span, Item::Import(import)),
            Line::Exports(exports) => self.item(exports.span, Item::Exports(exports)),
            Line::Expect(keyword, first) => {
                if self.methods {
                    return Err(error(
                        keyword,
                        "a method block holds signatures and clauses",
                    ));
                }
                self.open = Some(Open {
                    name: Name(keyword),
                    start: keyword,
                    patterns: Vec::new(),
                    guard: None,
                    expect: true,
                    lines: vec![first],
                });
                Ok(())
            }
            Line::Clause { head, guard, first } => self.clause(head, guard, first),
            Line::Typed(head, typed) => self.typed(head, typed),
            Line::Alias(head, ty) => {
                let ExprKind::Name(name) = head.kind else {
                    unreachable!("the grammar reads a type only after a type's name")
                };
                let span = head.span.through(type_span(&ty));
                self.item(head.span, Item::Alias(AliasDecl { span, name, ty }))
            }
            Line::Constraints(head, constraints) => self.constraint_alias(head, constraints),
        }
    }

    /// Begin a clause, whose body is `first` and the lines after it.
    fn clause(&mut self, head: Expr, guard: Option<Expr>, first: Statement) -> Result<(), Error> {
        let (name, arguments) = self.clause_head(head)?;
        self.open = Some(Open {
            name,
            start: name.0,
            patterns: patterns(arguments, self.source)?,
            guard,
            expect: false,
            lines: vec![first],
        });
        Ok(())
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

    /// Finish the body being gathered.
    fn close(&mut self) -> Result<(), Error> {
        let Some(open) = self.open.take() else {
            return Ok(());
        };
        let body = body(open.lines, self.source)?;
        let clause = Clause {
            span: open.start.through(body.result.span),
            name: open.name,
            patterns: open.patterns,
            guard: open.guard,
            body,
        };
        self.items.push(if open.expect {
            Item::Expect(clause)
        } else {
            Item::Clause(clause)
        });
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
    /// `Name`, or `Name(a b)`.
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
            ExprKind::Member(variable, member) => match variable.kind {
                ExprKind::Name(variable) if !is_type_name(variable, self.source) => {
                    self.constraint(span, variable, member, typed)
                }
                _ => Err(error(span, "a constraint is `a.member : type`")),
            },
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

    /// `a.add : a a -> a`: a `where` list's constraint on a line of its own,
    /// added to the list just before it.
    fn constraint(
        &mut self,
        span: Span,
        variable: Name,
        member: Name,
        typed: Typed,
    ) -> Result<(), Error> {
        if typed.constraints.is_some() || typed.methods.is_some() {
            return Err(error(span, "a constraint is `a.member : type`"));
        }
        let constraint = Constraint::Member {
            span: span.through(type_span(&typed.result)),
            variable,
            member,
            parameters: typed.parameters,
            result: typed.result,
        };
        self.constrain(span, constraint)
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

    /// Add a constraint on a line of its own to the `where` list just
    /// before it.
    fn constrain(&mut self, span: Span, constraint: Constraint) -> Result<(), Error> {
        let end = constraint.span();
        let listed = match self.items.last_mut() {
            Some(Item::Signature(signature)) if !signature.constraints.is_empty() => {
                signature.span = signature.span.through(end);
                &mut signature.constraints
            }
            Some(Item::Constraints(alias)) => {
                alias.span = alias.span.through(end);
                &mut alias.constraints
            }
            _ => {
                return Err(error(
                    span,
                    "a constraint on a line of its own continues a `where` list",
                ));
            }
        };
        listed.push(constraint);
        Ok(())
    }
}

/// A body of its lines: the last, a value, is its answer, and each before
/// it binds a pattern, or `_` where it is a value asked for what it does.
fn body(mut lines: Vec<Statement>, source: &str) -> Result<Body, Error> {
    let result = match lines.pop().expect("a body has its first line") {
        Statement::Value(value) => value,
        Statement::Binding(_, value) => {
            return Err(error(
                value.span,
                "a body ends with its answer, a line after its last binding",
            ));
        }
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
        })
        .collect::<Result<_, Error>>()?;
    Ok(Body { bindings, result })
}

const fn statement_span(statement: &Statement) -> Span {
    match statement {
        Statement::Value(value) => value.span,
        Statement::Binding(bound, value) => bound.span.through(value.span),
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
                return Err(error(
                    span,
                    format!(
                        "a range runs up, and `{}` is reversed: it matches nothing",
                        span.text(source)
                    ),
                ));
            }
            Ok(Pattern::Range { span, start, end })
        }
        ExprKind::String(parts) => Ok(Pattern::String {
            span,
            parts: parts
                .into_iter()
                .map(|part| match part {
                    StringPart::Text(text) => Ok(text),
                    StringPart::Splice(splice) => Err(error(
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
        ExprKind::Record(fields) => record(span, fields, false, source),
        ExprKind::Update(fields, base) => {
            if !matches!(base.kind, ExprKind::Wild) {
                return Err(error(
                    base.span,
                    "a record pattern names no rest: `{x *}` matches any other fields",
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
        ExprKind::Binary(super::ast::BinaryOp::Or, left, right) => {
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

/// Refuse a pattern-only form left in a clause's expressions.
fn clause_expressions(clause: &Clause) -> Result<(), Error> {
    if let Some(guard) = &clause.guard {
        expression(guard)?;
    }
    for binding in &clause.body.bindings {
        expression(&binding.value)?;
    }
    expression(&clause.body.result)
}

/// Refuse a pattern-only form anywhere in `expr`.
#[expect(
    clippy::too_many_lines,
    reason = "one arm for each kind of expression, to reach every one it holds"
)]
fn expression(expr: &Expr) -> Result<(), Error> {
    match &expr.kind {
        ExprKind::Wild => Err(error(expr.span, "`_` stands only in a pattern")),
        ExprKind::Range(..) => Err(error(expr.span, "a range stands only in a pattern")),
        ExprKind::Name(_) | ExprKind::Number(_) => Ok(()),
        ExprKind::String(parts) => parts.iter().try_for_each(|part| match part {
            StringPart::Text(_) => Ok(()),
            StringPart::Splice(splice) => expression(splice),
        }),
        ExprKind::List(elements, rest) => {
            if let Some(rest) = rest
                && matches!(rest.kind, ExprKind::Wild)
            {
                return Err(error(
                    rest.span,
                    "a list's rest names what follows: `[a *rest]`",
                ));
            }
            elements
                .iter()
                .chain(rest.as_deref())
                .try_for_each(expression)
        }
        ExprKind::Record(fields) => fields.iter().try_for_each(|(_, value)| expression(value)),
        ExprKind::Update(fields, base) => {
            if matches!(base.kind, ExprKind::Wild) {
                return Err(error(
                    base.span,
                    "a record's rest names the record it updates: `{x: 1 *base}`",
                ));
            }
            fields
                .iter()
                .map(|(_, value)| value)
                .chain(std::iter::once(&**base))
                .try_for_each(expression)
        }
        ExprKind::Tuple(members) => members.iter().try_for_each(expression),
        ExprKind::Lambda(_, body) => expression(body),
        ExprKind::Call(head, arguments) | ExprKind::Method(head, _, arguments) => {
            expression(head)?;
            arguments.iter().try_for_each(expression)
        }
        ExprKind::Member(value, _) | ExprKind::Unary(_, value) | ExprKind::Try(value) => {
            expression(value)
        }
        ExprKind::Binary(_, left, right) => {
            expression(left)?;
            expression(right)
        }
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
