//! The Ori grammar over compact lexer tokens.
//!
//! Alternatives are dispatched by their leading token wherever possible. In
//! particular, module directives, types, signatures, clauses, and literal
//! kinds do not retry one another after constructing syntax trees.

use super::ast::{
    AliasDecl, BinaryOp, Binding, Body, Clause, Constraint, ConstraintAliasDecl, ConstructorDecl,
    DataDecl, DataRepresentation, Dependency, Export, ExportsDecl, Exposure, Expr, ExprKind,
    HeaderDecl, HeaderKind, ImportDecl, Item, MethodItem, Module, Name, Numeral, NumeralKind,
    Pattern, SignatureDecl, Span, StringPart, Type, UnaryOp,
};
use super::lex::{Kind, Token};
use super::source::SourceId;

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

/// What follows a type name and its parameters at the head of an item.
enum Declared {
    Alias(Type),
    Constraints((Vec<Constraint>, Span)),
    Data(Type, Option<(Vec<MethodItem>, Span)>),
}

enum TermDeclaration {
    Signature(Vec<Type>, Type, Vec<Constraint>, Span),
    Clause(Vec<Pattern>, Option<Expr>, Body),
}

/// Return whether the next pattern-shaped token run is followed by `=`.
///
/// A constructor expression and a constructor pattern have the same spelling.
/// Letting `binding()*` discover the difference through PEG backtracking builds
/// and drops the entire pattern tree before parsing a body's final expression.
fn binding_ahead(tokens: &[Token], at: usize) -> bool {
    let Some(first) = tokens.get(at) else {
        return false;
    };
    let end = match first.kind {
        Kind::Ident | Kind::Wild | Kind::Number => Some(at + 1),
        Kind::Negate
            if tokens
                .get(at + 1)
                .is_some_and(|token| token.kind == Kind::Number && !token.space_before) =>
        {
            Some(at + 2)
        }
        Kind::TypeIdent => constructor_pattern_end(tokens, at),
        Kind::LBrace => closed_by(tokens, at, Kind::LBrace, Kind::RBrace),
        Kind::LParen => closed_by(tokens, at, Kind::LParen, Kind::RParen),
        _ => None,
    };
    end.and_then(|end| tokens.get(end))
        .is_some_and(|token| token.kind == Kind::Eq)
}

/// Whether the line at `at` begins an item rather than going on with a
/// body.
fn item_ahead(tokens: &[Token], at: usize) -> bool {
    begins_item(tokens, at, line_end(tokens, at))
}

/// Where the line beginning at `at` ends: at its newline, where a bracket
/// around it closes, or at the end of the file.
fn line_end(tokens: &[Token], at: usize) -> usize {
    let mut depth = 0usize;
    for (offset, token) in tokens.iter().enumerate().skip(at) {
        match token.kind {
            Kind::Newline | Kind::Eof if depth == 0 => return offset,
            Kind::LParen
            | Kind::LBracket
            | Kind::LBrace
            | Kind::DotParen
            | Kind::StrStart
            | Kind::SpliceStart => depth += 1,
            Kind::RParen | Kind::RBracket | Kind::RBrace | Kind::StrEnd | Kind::SpliceEnd => {
                if depth == 0 {
                    return offset;
                }
                depth -= 1;
            }
            _ => {}
        }
    }
    tokens.len()
}

/// Whether the line from `at` to `end` begins an item rather than going on
/// with a body: a clause's head, with its arrow; a signature or declaration,
/// with its colon; a directive; an `expect`; an alias.
fn begins_item(tokens: &[Token], at: usize, end: usize) -> bool {
    let line = &tokens[at..end];
    if matches!(
        line.first().map(|token| token.kind),
        Some(Kind::KwImport | Kind::KwExports | Kind::KwPackage | Kind::KwExpect)
    ) {
        return true;
    }
    let mut depth = 0usize;
    for (offset, token) in line.iter().enumerate() {
        match token.kind {
            Kind::LParen
            | Kind::LBracket
            | Kind::LBrace
            | Kind::DotParen
            | Kind::StrStart
            | Kind::SpliceStart => depth += 1,
            Kind::RParen | Kind::RBracket | Kind::RBrace | Kind::StrEnd | Kind::SpliceEnd => {
                depth = depth.saturating_sub(1);
            }
            Kind::Arrow | Kind::Colon | Kind::KwWhere if depth == 0 => return true,
            // `Name = ...` names a type, where a binding's pattern would be
            // a constructor that holds nothing, which binds nothing.
            Kind::Eq if depth == 0 && offset == 1 => {
                return line[0].kind == Kind::TypeIdent;
            }
            _ => {}
        }
    }
    false
}

/// Where the bracket opening at `at` is closed, just past it.
fn closed_by(tokens: &[Token], at: usize, open: Kind, close: Kind) -> Option<usize> {
    let mut depth = 0usize;
    for (offset, token) in tokens.get(at..)?.iter().enumerate() {
        match token.kind {
            kind if kind == open => depth += 1,
            kind if kind == close => {
                depth -= 1;
                if depth == 0 {
                    return Some(at + offset + 1);
                }
            }
            Kind::Eof => return None,
            _ => {}
        }
    }
    None
}

fn constructor_pattern_end(tokens: &[Token], at: usize) -> Option<usize> {
    if !tokens
        .get(at + 1)
        .is_some_and(|token| token.kind == Kind::LParen && !token.space_before)
    {
        return Some(at + 1);
    }
    let mut depth = 1usize;
    let mut cursor = at + 2;
    loop {
        let token = tokens.get(cursor)?;
        match token.kind {
            Kind::LParen => depth += 1,
            Kind::RParen => {
                depth -= 1;
                if depth == 0 {
                    return Some(cursor + 1);
                }
            }
            Kind::Eof => return None,
            _ => {}
        }
        cursor += 1;
    }
}

peg::parser! {
    pub grammar source() for [Token] {
        rule tok(kind: Kind) -> Token
            = quiet!{[token if token.kind == kind]}
        rule adj(kind: Kind) -> Token
            = quiet!{[token if token.kind == kind && !token.space_before]}
        rule sep()
            = quiet!{&[token if token.space_before]}
        rule chain_dot() -> Token
            = quiet!{[token if token.kind == Kind::Dot && (!token.space_before || token.newline_before)]}
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
        rule equals() = tok(Kind::Eq) / expected!("`=`")
        rule ident() -> Token = tok(Kind::Ident) / expected!("a name")
        rule type_ident() -> Token = tok(Kind::TypeIdent) / expected!("a type name")
        rule term_name() -> Token
            = quiet!{[token if matches!(token.kind, Kind::Ident | Kind::EffectIdent)]}
              / expected!("a term name")
        rule source_name() -> Token
            = quiet!{[token if matches!(token.kind,
                Kind::TypeIdent | Kind::Ident | Kind::EffectIdent)]}
              / expected!("a name")

        pub rule program() -> Module
            = items:(item() ** newline()) newline()? eof() {
                Module { source: SourceId::DETACHED, items }
            }

        rule item() -> Item
            = header:header() { Item::Header(header) }
            / import:import_decl() { Item::Import(import) }
            / exports:exports_decl() { Item::Exports(exports) }
            / declaration:type_declaration() { declaration }
            / expect:expect_decl() { Item::Expect(expect) }
            / declaration:term_declaration() { term_item(declaration) }

        rule expect_decl() -> Clause
            = head:tok(Kind::KwExpect) body:body() {
                Clause {
                    span: head.span().through(body.result.span),
                    name: name(head),
                    patterns: Vec::new(),
                    guard: None,
                    body,
                }
            }

        rule header() -> HeaderDecl
            = start:tok(Kind::KwPackage) lbrace() dependencies:(dependency() ** sep())
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
              lbrace() exposures:(exposure() ** sep()) close:rbrace() {
                ImportDecl {
                    span: start.span().through(close.span()),
                    path,
                    exposures,
                }
            }

        rule module_path() -> Vec<Name>
            = first:ident() rest:(adj(Kind::Dot) next:adj(Kind::Ident) { next })* {
                std::iter::once(first).chain(rest).map(name).collect()
            }

        rule exposure() -> Exposure
            = exported:source_name() constructors:adj(Kind::DotStar)?
              local:(colon() local:source_name() { local })? {
                Exposure {
                    exported: name(exported),
                    local: name(local.unwrap_or(exported)),
                    constructors: constructors.is_some(),
                }
            }

        rule exports_decl() -> ExportsDecl
            = start:tok(Kind::KwExports) lbrace()
              exports:(export() ** sep()) close:rbrace() {
                ExportsDecl {
                    span: start.span().through(close.span()),
                    exports,
                }
            }

        rule export() -> Export
            = exported:source_name() constructors:adj(Kind::DotStar)? {
                Export { name: name(exported), constructors: constructors.is_some() }
            }

        // `Name = ty`, `Name(a) = where ...` or `Name(a) : ty`, told apart
        // after the name and its parameters by the token that follows.
        rule type_declaration() -> Item
            = head:type_ident() params:type_params()? declared:(
                tok(Kind::Eq) declared:(
                    constraints:constraints() { Declared::Constraints(constraints) }
                    / ty:ty() { Declared::Alias(ty) }
                ) { declared }
                / colon() representation:ty() methods:method_block()? {
                    Declared::Data(representation, methods)
                }
            ) {? type_declaration(head, params, declared) }

        rule type_params() -> Vec<Name>
            = adj(Kind::LParen) params:(ident() ++ sep()) rparen() {
                params.into_iter().map(name).collect()
            }

        rule constructor() -> ConstructorDecl
            = head:type_ident()
              fields:(adj(Kind::LParen) fields:(ty() ++ sep()) rparen() { fields })? {
                ConstructorDecl {
                    name: name(head),
                    fields: fields.unwrap_or_default(),
                }
            }

        rule method_block() -> (Vec<MethodItem>, Span)
            = tok(Kind::DotParen) methods:(method_declaration() ** newline()) newline()?
              close:rparen() {
                (methods, close.span())
            }

        rule method_declaration() -> MethodItem
            = declaration:term_declaration() { method_item(declaration) }

        rule term_declaration() -> (Token, TermDeclaration)
            = head:term_name() declaration:term_tail() { (head, declaration) }

        rule term_tail() -> TermDeclaration
            = colon() signature:signature_type() {
                TermDeclaration::Signature(signature.0, signature.1, signature.2, signature.3)
            }
            / adj(Kind::LParen) patterns:(pattern() ** sep()) rparen()
              guard:(tok(Kind::KwIf) guard:expr() { guard })?
              arrow() body:body() {
                TermDeclaration::Clause(patterns, guard, body)
            }

        rule signature_type() -> (Vec<Type>, Type, Vec<Constraint>, Span)
            = shape:member_type() constraints:constraints()? {
                let (parameters, result) = shape;
                let end = constraints.as_ref().map_or_else(
                    || type_span(&result),
                    |constraints| constraints.1,
                );
                (parameters, result, constraints.map_or_else(Vec::new, |value| value.0), end)
            }

        rule constraints() -> (Vec<Constraint>, Span)
            = tok(Kind::KwWhere) constraints:(constraint() ++ constraint_sep()) {
                let end = constraints.last().map_or_else(Span::default, Constraint::span);
                (constraints, end)
            }

        // A `where` list goes on to the next line with a member's constraint,
        // `a.add : a a -> a`, which no item begins as.
        rule constraint_sep()
            = sep() / newline() &(tok(Kind::Ident) adj(Kind::Dot))

        rule constraint() -> Constraint
            = variable:ident() adj(Kind::Dot) member:(adj(Kind::Ident) / adj(Kind::EffectIdent))
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
            / head:type_ident() adj(Kind::LParen)
              arguments:(ty() ++ sep()) close:rparen() {
                Constraint::Alias {
                    span: head.span().through(close.span()),
                    name: name(head),
                    arguments,
                }
            }

        // Parameters and an arrow to the result, or the result alone.
        rule member_type() -> (Vec<Type>, Type)
            = types:(ty() ++ sep()) result:(arrow() result:ty() { result })? {?
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
              args:(adj(Kind::LParen) args:(ty() ++ sep()) close:rparen() { (args, close.span()) })? {
                match args {
                    Some((args, end)) => named_type(head, args, end),
                    None => named_type(head, Vec::new(), head.span()),
                }
            }
            / variable:ident() { named_type(variable, Vec::new(), variable.span()) }
            // A function type, a tuple, or one type grouped.
            / open:lparen() members:(ty() ++ sep()) result:(arrow() result:ty() { result })?
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
            / open:lbracket() constructors:(constructor() ** sep()) close:rbracket() {
                Type::Variants {
                    span: open.span().through(close.span()),
                    constructors,
                }
            }
            / open:lbrace() fields:(record_type_field() ** sep())
              rest:tok(Kind::Rest)? close:rbrace() {
                Type::Record {
                    span: open.span().through(close.span()),
                    fields,
                    open: rest.is_some(),
                }
            }

        rule record_type_field() -> (Name, Type)
            = field:ident() colon() value:ty() { (name(field), value) }

        // Lines, each but the last a binding or an effect asked for what it
        // does, which binds `_`; the last is the answer. A line beginning
        // an item ends the body before it.
        rule body() -> Body
            = lines:(body_line() ++ (newline() !item_ahead())) {? body(lines) }

        rule body_line() -> Binding
            = binding_ahead() binding:binding() { binding }
            / value:expr() {
                Binding { pattern: Pattern::Wild(value.span), value, discarded: true }
            }

        rule item_ahead()
            = #{|input, at| {
                if item_ahead(input, at) {
                    peg::RuleResult::Matched(at, ())
                } else {
                    peg::RuleResult::Failed
                }
            }}

        rule binding_ahead()
            = #{|input, at| {
                if binding_ahead(input, at) {
                    peg::RuleResult::Matched(at, ())
                } else {
                    peg::RuleResult::Failed
                }
            }}

        rule binding() -> Binding
            = pattern:pattern() equals() value:expr() {
                Binding { pattern, value, discarded: false }
            }

        // `A | B`: either of two or more alternatives.
        rule pattern() -> Pattern
            = first:single_pattern() rest:(tok(Kind::Bar) next:single_pattern() { next })* {
                if rest.is_empty() {
                    return first;
                }
                let alternatives: Vec<Pattern> = std::iter::once(first).chain(rest).collect();
                Pattern::Or {
                    span: alternatives[0]
                        .span()
                        .through(alternatives.last().expect("two or more").span()),
                    alternatives,
                }
            }

        rule single_pattern() -> Pattern
            = start:(tok(Kind::Number) / tok(Kind::Char))
              end:(adj(Kind::DotDot) end:(adj(Kind::Number) / adj(Kind::Char)) { end })? {
                end.map_or_else(
                    || Pattern::Number {
                        span: start.span(),
                        numeral: numeral(start),
                        negative: false,
                    },
                    |end| Pattern::Range {
                        span: start.span().through(end.span()),
                        start: numeral(start),
                        end: numeral(end),
                    },
                )
            }
            / minus:tok(Kind::Negate) value:(tok(Kind::Number) / tok(Kind::Char)) {
                Pattern::Number {
                    span: minus.span().through(value.span()),
                    numeral: numeral(value),
                    negative: true,
                }
            }
            // `[a *]` takes a rest it does not name.
            / open:lbracket() elements:(pattern() ** sep())
              rest:(star:tok(Kind::Rest) rest:pattern()? {
                  rest.unwrap_or_else(|| Pattern::Wild(star.span()))
              })?
              close:rbracket() {
                Pattern::List {
                    span: open.span().through(close.span()),
                    elements,
                    rest: rest.map(Box::new),
                }
            }
            / open:tok(Kind::StrStart) parts:(text:tok(Kind::StrText) { text.span() })*
              close:tok(Kind::StrEnd) {
                Pattern::String {
                    span: open.span().through(close.span()),
                    parts,
                }
            }
            // A tuple, or one pattern grouped.
            / open:lparen() members:(pattern() ++ sep()) close:rparen() {
                if members.len() == 1 {
                    members.into_iter().next().expect("one")
                } else {
                    Pattern::Tuple {
                        span: open.span().through(close.span()),
                        members,
                    }
                }
            }
            / open:lbrace() fields:(record_pattern_field() ** sep())
              rest:tok(Kind::Rest)? close:rbrace() {
                Pattern::Record {
                    span: open.span().through(close.span()),
                    fields,
                    open: rest.is_some(),
                }
            }
            / head:type_ident()
              member:(adj(Kind::Dot) member:adj(Kind::TypeIdent) { member })?
              fields:(adj(Kind::LParen) fields:(pattern() ++ sep()) close:rparen() {
                  (fields, close.span())
              })? {
                let last = member.unwrap_or(head);
                let (fields, end) = fields.unwrap_or_else(|| (Vec::new(), last.span()));
                Pattern::Constructor {
                    span: head.span().through(end),
                    qualifier: member.map(|_| name(head)),
                    name: name(last),
                    fields,
                }
            }
            / wild:tok(Kind::Wild) { Pattern::Wild(wild.span()) }
            / bind:ident() { Pattern::Bind(name(bind)) }

        rule record_pattern_field() -> (Name, Pattern)
            = field:ident() value:(colon() value:pattern() { value })? {
                let field = name(field);
                (field, value.unwrap_or(Pattern::Bind(field)))
            }

        pub rule expr() -> Expr = precedence! {
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
            token:tok(Kind::Negate) value:@ { unary(UnaryOp::Negate, token, value) }
            token:tok(Kind::Bang) value:@ { unary(UnaryOp::Not, token, value) }
            --
            head:@ args:call_args() {
                let span = head.span.through(args.1);
                Expr { span, kind: ExprKind::Call(Box::new(head), args.0) }
            }
            value:@ question:adj(Kind::Question) {
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
            = adj(Kind::LParen) args:(argument() ** sep()) close:rparen() {
                (args, close.span())
            }

        rule argument() -> Expr = lambda() / expr()

        rule lambda() -> Expr
            = open:tok(Kind::LambdaBar) patterns:(single_pattern() ++ sep()) tok(Kind::Bar)
              body:expr() {
                Expr {
                    span: open.span().through(body.span),
                    kind: ExprKind::Lambda(patterns, Box::new(body)),
                }
            }

        rule dot_access() -> (Token, Option<Vec<Expr>>, Span)
            = chain_dot() member:(adj(Kind::Ident) / adj(Kind::EffectIdent) / adj(Kind::TypeIdent))
              args:call_args()? {
                let end = args.as_ref().map_or_else(|| member.span(), |args| args.1);
                (member, args.map(|args| args.0), end)
            }

        rule primary() -> Expr
            = value:(tok(Kind::Number) / tok(Kind::Char) / tok(Kind::Decimal)) {
                atom(value, ExprKind::Number(numeral(value)))
            }
            / string:string() { string }
            / list:list() { list }
            / record:record() { record }
            // A tuple, or one value grouped.
            / open:lparen() members:(expr() ++ sep()) close:rparen() {
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
            = open:lbrace() fields:(record_expr_field() ** sep())
              base:(tok(Kind::Rest) base:expr() { base })? close:rbrace() {
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

        rule list() -> Expr
            = open:lbracket() elements:(expr() ** sep())
              rest:(tok(Kind::Rest) rest:expr() { rest })?
              close:rbracket() {
                Expr {
                    span: open.span().through(close.span()),
                    kind: ExprKind::List(elements, rest.map(Box::new)),
                }
            }
    }
}

/// The item a type name heads: an alias of no parameters, a constraint alias
/// of some, or a data declaration, whose representation in brackets is its
/// constructors.
fn type_declaration(
    head: Token,
    params: Option<Vec<Name>>,
    declared: Declared,
) -> Result<Item, &'static str> {
    match (declared, params) {
        (Declared::Alias(ty), None) => Ok(Item::Alias(AliasDecl {
            span: head.span().through(type_span(&ty)),
            name: name(head),
            ty,
        })),
        (Declared::Alias(_), Some(_)) => {
            Err("`where` and the constraints a parameterized alias stands for")
        }
        (Declared::Constraints((constraints, end)), Some(parameters)) => {
            Ok(Item::Constraints(ConstraintAliasDecl {
                span: head.span().through(end),
                name: name(head),
                parameters,
                constraints,
            }))
        }
        (Declared::Constraints(_), None) => Err("`(` and the parameters a constraint alias takes"),
        (Declared::Data(represented, methods), params) => {
            let end = methods
                .as_ref()
                .map_or_else(|| type_span(&represented), |methods| methods.1);
            let representation = match represented {
                Type::Variants { constructors, .. } => DataRepresentation::Sum(constructors),
                wrapped => DataRepresentation::Wrapper(wrapped),
            };
            Ok(Item::Data(DataDecl {
                span: head.span().through(end),
                name: name(head),
                params: params.unwrap_or_default(),
                representation,
                methods: methods.map_or_else(Vec::new, |methods| methods.0),
            }))
        }
    }
}

/// A body of its lines: the last, which must be a value, is its answer.
fn body(mut lines: Vec<Binding>) -> Result<Body, &'static str> {
    let last = lines.pop().expect("a body has a line");
    if !last.discarded {
        return Err("a line answering the body after its last binding");
    }
    Ok(Body {
        bindings: lines,
        result: last.value,
    })
}

fn term_item((head, declaration): (Token, TermDeclaration)) -> Item {
    match declaration {
        TermDeclaration::Signature(parameters, result, constraints, end) => {
            Item::Signature(SignatureDecl {
                span: head.span().through(end),
                name: name(head),
                parameters,
                result,
                constraints,
            })
        }
        TermDeclaration::Clause(patterns, guard, body) => Item::Clause(Clause {
            span: head.span().through(body.result.span),
            name: name(head),
            patterns,
            guard,
            body,
        }),
    }
}

fn method_item((head, declaration): (Token, TermDeclaration)) -> MethodItem {
    match term_item((head, declaration)) {
        Item::Signature(signature) => MethodItem::Signature(signature),
        Item::Clause(clause) => MethodItem::Clause(clause),
        _ => unreachable!("term items are signatures or clauses"),
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
