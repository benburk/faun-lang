//! The Ori grammar over compact lexer tokens.
//!
//! A file is lines. Each begins with a keyword or an expression, and the token
//! after that expression says what the line is; [`lines`](super::lines) makes
//! the heads that are patterns into patterns, and groups the lines into items.
//! Every choice is made by the next token, but for `Name =`, whose right side
//! is a type because its head, already read, is a type's name.
//!
//! The grammar this reads is written out in `grammar.ebnf`, which the `ebnf`
//! tests check is LL(1) and reads what this does.

use super::ast::{
    BinaryOp, Constraint, ConstructorDecl, Dependency, Export, ExportsDecl, Exposure, Expr,
    ExprKind, HeaderDecl, HeaderKind, ImportDecl, Name, Numeral, NumeralKind, Span, StringPart,
    Type, UnaryOp,
};
use super::lex::{Kind, Token};
use super::lines::{self, Equals, Line, Statement, Trailer, Typed};

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

/// A lambda of `parameters`, each written as the pattern-shaped expression
/// that is its pattern.
fn lambda(
    open: Token,
    parameters: Vec<Expr>,
    body: Expr,
    source: &str,
) -> Result<Expr, &'static str> {
    let patterns = parameters
        .into_iter()
        .map(|parameter| lines::pattern(parameter, source))
        .collect::<Result<_, _>>()
        .map_err(|_| "a pattern for each of the lambda's parameters")?;
    Ok(Expr {
        span: open.span().through(body.span),
        kind: ExprKind::Lambda(patterns, Box::new(body)),
    })
}

/// Match nothing at `at` where `condition` holds, and fail where not.
const fn holds(condition: bool, at: usize) -> peg::RuleResult<()> {
    if condition {
        peg::RuleResult::Matched(at, ())
    } else {
        peg::RuleResult::Failed
    }
}

peg::parser! {
    pub grammar source(src: &str) for [Token] {
        rule tok(kind: Kind) -> Token
            = quiet!{[token if token.kind == kind]}
        rule eof()
            = quiet!{[Token { kind: Kind::Eof, .. }]}
              / expected!("the end of the file")
        rule newline()
            = quiet!{[Token { kind: Kind::Newline, .. }]}
              / expected!("a new line")
        rule lparen() -> Token = tok(Kind::LParen) / expected!("`(`")
        rule rparen() -> Token = tok(Kind::RParen) / expected!("`)`")
        rule lbracket() -> Token = tok(Kind::LBracket) / expected!("`[`")
        rule rbracket() -> Token = tok(Kind::RBracket) / expected!("`]`")
        rule lbrace() -> Token = tok(Kind::LBrace) / expected!("`{`")
        rule rbrace() -> Token = tok(Kind::RBrace) / expected!("`}`")
        rule colon() = tok(Kind::Colon) / expected!("`:`")
        rule arrow() = tok(Kind::Arrow) / expected!("`->`")
        rule ident() -> Token = tok(Kind::Ident) / expected!("a name")
        rule type_ident() -> Token = tok(Kind::TypeIdent) / expected!("a type name")
        rule source_name() -> Token
            = quiet!{[token if matches!(token.kind,
                Kind::TypeIdent | Kind::Ident | Kind::EffectIdent)]}
              / expected!("a name")

        pub rule program() -> Vec<Line>
            = lines:(line() ** newline()) newline()? eof() { lines }

        // A keyword's line, or an expression and what follows it.
        rule line() -> Line
            = header:header() { Line::Header(header) }
            / import:import_decl() { Line::Import(import) }
            / exports:exports_decl() { Line::Exports(exports) }
            / keyword:tok(Kind::KwExpect) first:statement() {
                Line::Expect(keyword.span(), first)
            }
            / head:expr() trailer:trailer(lines::names_a_type(&head, src))? {
                Line::new(head, trailer)
            }

        // `= value`, or after a type's name `= type`; `= where ...`;
        // `: type`; or `if guard -> value` and `-> value`.
        rule trailer(names_a_type: bool) -> Trailer
            = tok(Kind::Eq) equals:(
                constraints:constraints() { Equals::Constraints(constraints) }
                / when(names_a_type) ty:ty() { Equals::Type(ty) }
                / when(!names_a_type) value:expr() { Equals::Value(value) }
            ) { Trailer::Equals(equals) }
            / colon() shape:member_type() constraints:constraints()? methods:method_block()? {
                let (parameters, result) = shape;
                Trailer::Typed(Typed { parameters, result, constraints, methods })
            }
            / guard:(tok(Kind::KwIf) guard:expr() { guard })? arrow() first:statement() {
                Trailer::Clause { guard, first }
            }

        rule when(condition: bool) = #{|_, at| holds(condition, at)}

        // A body's line: a value, or `pattern = value`.
        rule statement() -> Statement
            = value:expr() bound:(tok(Kind::Eq) bound:expr() { bound })? {
                match bound {
                    Some(bound) => Statement::Binding(value, bound),
                    None => Statement::Value(value),
                }
            }

        rule header() -> HeaderDecl
            = start:tok(Kind::KwPackage) lbrace() dependencies:(dependency()*)
              close:rbrace() {
                HeaderDecl {
                    span: start.span().through(close.span()),
                    kind: HeaderKind::Package,
                    dependencies,
                }
            }

        rule dependency() -> Dependency
            = named:ident() colon() tok(Kind::StrStart)
              path:(text:tok(Kind::StrText) { text.span() })* close:tok(Kind::StrEnd) {
                Dependency {
                    span: named.span().through(close.span()),
                    name: name(named),
                    path,
                }
            }

        rule import_decl() -> ImportDecl
            = start:tok(Kind::KwImport) path:module_path()
              lbrace() exposures:(exposure()*) close:rbrace() {
                ImportDecl {
                    span: start.span().through(close.span()),
                    path,
                    exposures,
                }
            }

        rule module_path() -> Vec<Name>
            = first:ident() rest:(tok(Kind::Dot) next:tok(Kind::Ident) { next })* {
                std::iter::once(first).chain(rest).map(name).collect()
            }

        rule exposure() -> Exposure
            = exported:source_name() constructors:tok(Kind::DotStar)?
              local:(colon() local:source_name() { local })? {
                Exposure {
                    exported: name(exported),
                    local: name(local.unwrap_or(exported)),
                    constructors: constructors.is_some(),
                }
            }

        rule exports_decl() -> ExportsDecl
            = start:tok(Kind::KwExports) lbrace()
              exports:(export()*) close:rbrace() {
                ExportsDecl {
                    span: start.span().through(close.span()),
                    exports,
                }
            }

        rule export() -> Export
            = exported:source_name() constructors:tok(Kind::DotStar)? {
                Export { name: name(exported), constructors: constructors.is_some() }
            }

        rule constructor() -> ConstructorDecl
            = head:type_ident()
              fields:(tok(Kind::CallParen) fields:(ty()+) rparen() { fields })? {
                ConstructorDecl {
                    name: name(head),
                    fields: fields.unwrap_or_default(),
                }
            }

        rule method_block() -> (Vec<Line>, Span)
            = tok(Kind::DotParen) lines:(line() ** newline()) newline()? close:rparen() {
                (lines, close.span())
            }

        rule constraints() -> (Vec<Constraint>, Span)
            = tok(Kind::KwWhere) aliases:alias_constraint()* member:member_constraint()? {?
                let constraints: Vec<_> = aliases.into_iter().chain(member).collect();
                let end = constraints.last().map(Constraint::span).ok_or("a constraint")?;
                Ok((constraints, end))
            }

        // `a.add : a a -> a`. It ends its `where` line, as a value's
        // constraint, `a.zero : a`, reads no end of its own.
        rule member_constraint() -> Constraint
            = variable:ident() tok(Kind::Dot) member:(tok(Kind::Ident) / tok(Kind::EffectIdent))
              colon() shape:member_type() {
                let (parameters, result) = shape;
                Constraint::Member {
                    span: variable.span().through(type_span(&result)),
                    variable: name(variable),
                    member: name(member),
                    parameters,
                    result,
                }
            }

        rule alias_constraint() -> Constraint
            = head:type_ident() tok(Kind::CallParen)
              arguments:(ty()+) close:rparen() {
                Constraint::Alias {
                    span: head.span().through(close.span()),
                    name: name(head),
                    arguments,
                }
            }

        // Parameters and an arrow to the result, or the result alone.
        rule member_type() -> (Vec<Type>, Type)
            = types:(ty()+) result:(arrow() result:ty() { result })? {?
                match result {
                    Some(result) => Ok((types, result)),
                    None if types.len() == 1 => {
                        Ok((Vec::new(), types.into_iter().next().expect("one")))
                    }
                    None => Err("`->` and the result after the parameter types"),
                }
            }

        rule ty() -> Type
            = head:type_ident()
              args:(tok(Kind::CallParen) args:(ty()+) close:rparen() { (args, close.span()) })? {
                match args {
                    Some((args, end)) => named_type(head, args, end),
                    None => named_type(head, Vec::new(), head.span()),
                }
            }
            / variable:ident() { named_type(variable, Vec::new(), variable.span()) }
            // A function type, a tuple, or one type grouped.
            / open:lparen() members:(ty()+) result:(arrow() result:ty() { result })?
              close:rparen() {
                let span = open.span().through(close.span());
                match result {
                    Some(result) => Type::Function {
                        span,
                        parameters: members,
                        result: Box::new(result),
                    },
                    None if members.len() == 1 => members.into_iter().next().expect("one"),
                    None => Type::Tuple { span, members },
                }
            }
            / open:lbracket() constructors:(constructor()*) close:rbracket() {
                Type::Variants {
                    span: open.span().through(close.span()),
                    constructors,
                }
            }
            / open:lbrace() fields:(record_type_field()*)
              rest:tok(Kind::Rest)? close:rbrace() {
                Type::Record {
                    span: open.span().through(close.span()),
                    fields,
                    open: rest.is_some(),
                }
            }

        rule record_type_field() -> (Name, Type)
            = field:ident() colon() value:ty() { (name(field), value) }

        rule expr() -> Expr = precedence! {
            left:(@) tok(Kind::Bar) right:@ { binary(BinaryOp::Or, left, right) }
            --
            left:(@) tok(Kind::Caret) right:@ { binary(BinaryOp::Xor, left, right) }
            --
            left:(@) tok(Kind::Amp) right:@ { binary(BinaryOp::And, left, right) }
            --
            left:(@) tok(Kind::EqEq) right:@ { binary(BinaryOp::Equal, left, right) }
            left:(@) tok(Kind::Ne) right:@ { binary(BinaryOp::NotEqual, left, right) }
            left:(@) tok(Kind::Lt) right:@ { binary(BinaryOp::Less, left, right) }
            left:(@) tok(Kind::Le) right:@ { binary(BinaryOp::LessEqual, left, right) }
            left:(@) tok(Kind::Gt) right:@ { binary(BinaryOp::Greater, left, right) }
            left:(@) tok(Kind::Ge) right:@ { binary(BinaryOp::GreaterEqual, left, right) }
            --
            left:(@) tok(Kind::Plus) right:@ { binary(BinaryOp::Add, left, right) }
            left:(@) tok(Kind::Minus) right:@ { binary(BinaryOp::Subtract, left, right) }
            --
            left:(@) tok(Kind::Slash) right:@ { binary(BinaryOp::Divide, left, right) }
            left:(@) tok(Kind::Percent) right:@ { binary(BinaryOp::Remainder, left, right) }
            left:(@) tok(Kind::Star) right:@ { binary(BinaryOp::Multiply, left, right) }
            --
            operand:operand() { operand }
        }

        // What an operator applies to: a prefix, a postfix, or a primary.
        rule operand() -> Expr = precedence! {
            token:tok(Kind::Negate) value:@ { unary(UnaryOp::Negate, token, value) }
            token:tok(Kind::Bang) value:@ { unary(UnaryOp::Not, token, value) }
            --
            head:@ args:call_args() {
                let span = head.span.through(args.1);
                Expr { span, kind: ExprKind::Call(Box::new(head), args.0) }
            }
            value:@ question:tok(Kind::Question) {
                Expr { span: value.span.through(question.span()), kind: ExprKind::Try(Box::new(value)) }
            }
            head:@ member:dot_access() {
                let span = head.span.through(member.2);
                match member.1 {
                    Some(arguments) => Expr {
                        span,
                        kind: ExprKind::Method(Box::new(head), name(member.0), arguments),
                    },
                    None => Expr {
                        span,
                        kind: ExprKind::Member(Box::new(head), name(member.0)),
                    },
                }
            }
            --
            primary:primary() { primary }
        }


        rule call_args() -> (Vec<Expr>, Span)
            = tok(Kind::CallParen) args:(argument()*) close:rparen() {
                (args, close.span())
            }

        rule argument() -> Expr = lambda() / expr()

        // `|x Some(y)| body`: its parameters are operands, being no `or`,
        // each the pattern it spells.
        rule lambda() -> Expr
            = open:tok(Kind::LambdaBar) parameters:(operand()+) tok(Kind::Bar)
              body:expr() {? lambda(open, parameters, body, src) }

        rule dot_access() -> (Token, Option<Vec<Expr>>, Span)
            = tok(Kind::Dot) member:(tok(Kind::Ident) / tok(Kind::EffectIdent) / tok(Kind::TypeIdent))
              args:call_args()? {
                let end = args.as_ref().map_or_else(|| member.span(), |args| args.1);
                (member, args.map(|args| args.0), end)
            }

        rule primary() -> Expr
            = start:(tok(Kind::Number) / tok(Kind::Char))
              end:(tok(Kind::DotDot) end:(tok(Kind::Number) / tok(Kind::Char)) { end })? {
                end.map_or_else(
                    || atom(start, ExprKind::Number(numeral(start))),
                    |end| Expr {
                        span: start.span().through(end.span()),
                        kind: ExprKind::Range(numeral(start), numeral(end)),
                    },
                )
            }
            / value:tok(Kind::Decimal) { atom(value, ExprKind::Number(numeral(value))) }
            / wild:tok(Kind::Wild) { atom(wild, ExprKind::Wild) }
            / string:string() { string }
            / list:list() { list }
            / record:record() { record }
            // A tuple, or one value grouped.
            / open:lparen() members:(expr()+) close:rparen() {
                let span = open.span().through(close.span());
                if members.len() == 1 {
                    Expr { span, ..members.into_iter().next().expect("one") }
                } else {
                    Expr { span, kind: ExprKind::Tuple(members) }
                }
            }
            / token:quiet!{[token if matches!(token.kind,
                Kind::TypeIdent | Kind::Ident | Kind::EffectIdent)]} {
                atom(token, ExprKind::Name(name(token)))
            }
            / expected!("an expression")

        rule string() -> Expr
            = open:tok(Kind::StrStart) parts:string_part()* close:tok(Kind::StrEnd) {
                Expr {
                    span: open.span().through(close.span()),
                    kind: ExprKind::String(parts),
                }
            }

        rule string_part() -> StringPart
            = text:tok(Kind::StrText) { StringPart::Text(text.span()) }
            / tok(Kind::SpliceStart) value:expr() tok(Kind::SpliceEnd) {
                StringPart::Splice(value)
            }

        rule record() -> Expr
            = open:lbrace() fields:(record_expr_field()*)
              base:rest()? close:rbrace() {
                let span = open.span().through(close.span());
                match base {
                    Some(base) => Expr { span, kind: ExprKind::Update(fields, Box::new(base)) },
                    None => Expr { span, kind: ExprKind::Record(fields) },
                }
            }

        rule record_expr_field() -> (Name, Expr)
            = field:ident() value:(colon() value:expr() { value })? {
                let field_name = name(field);
                let value = value.unwrap_or_else(|| atom(field, ExprKind::Name(field_name)));
                (field_name, value)
            }

        // `*rest`, or `*` alone, a pattern's rest it does not name.
        rule rest() -> Expr
            = star:tok(Kind::Rest) rest:expr()? {
                rest.unwrap_or_else(|| atom(star, ExprKind::Wild))
            }

        rule list() -> Expr
            = open:lbracket() elements:(expr()*)
              rest:rest()? close:rbracket() {
                Expr {
                    span: open.span().through(close.span()),
                    kind: ExprKind::List(elements, rest.map(Box::new)),
                }
            }
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
