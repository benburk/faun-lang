//! The Ori grammar over compact lexer tokens.
//!
//! Alternatives are dispatched by their leading token wherever possible. In
//! particular, module directives, types, signatures, clauses, and literal
//! kinds do not retry one another after constructing syntax trees.

use super::ast::{
    AliasDecl, BinaryOp, Binding, Body, Clause, Constraint, ConstructorDecl, DataDecl,
    DataRepresentation, Export, ExportsDecl, Exposure, Expr, ExprKind, HeaderDecl, HeaderKind,
    ImportDecl, Item, MethodItem, Module, Name, Numeral, NumeralKind, Pattern, SignatureDecl, Span,
    StringPart, Type, UnaryOp,
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
        kind: if token.kind == Kind::Char {
            NumeralKind::Character
        } else {
            NumeralKind::Number
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
        Kind::Minus
            if tokens
                .get(at + 1)
                .is_some_and(|token| token.kind == Kind::Number && !token.space_before) =>
        {
            Some(at + 2)
        }
        Kind::TypeIdent => constructor_pattern_end(tokens, at),
        Kind::LBrace => record_pattern_end(tokens, at),
        _ => None,
    };
    end.and_then(|end| tokens.get(end))
        .is_some_and(|token| token.kind == Kind::Eq)
}

fn record_pattern_end(tokens: &[Token], at: usize) -> Option<usize> {
    let mut depth = 0usize;
    for (offset, token) in tokens.get(at..)?.iter().enumerate() {
        match token.kind {
            Kind::LBrace => depth += 1,
            Kind::RBrace => {
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
        rule tight()
            = quiet!{&[token if !token.space_before]}
        rule chain_dot() -> Token
            = quiet!{[token if token.kind == Kind::Dot && (!token.space_before || token.newline_before)]}
        rule eof()
            = quiet!{[Token { kind: Kind::Eof, .. }]}
              / expected!("the end of the file")
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
            = items:item()* eof() { Module { source: SourceId::DETACHED, items } }

        rule item() -> Item
            = header:header() { Item::Header(header) }
            / import:import_decl() { Item::Import(import) }
            / exports:exports_decl() { Item::Exports(exports) }
            / alias:alias_decl() { Item::Alias(alias) }
            / data:data_decl() { Item::Data(data) }
            / declaration:term_declaration() { term_item(declaration) }

        rule header() -> HeaderDecl
            = start:tok(Kind::KwPackage) lbrace() close:rbrace() {
                HeaderDecl { span: start.span().through(close.span()), kind: HeaderKind::Package }
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

        rule alias_decl() -> AliasDecl
            = head:type_ident() quiet!{tok(Kind::Eq)} ty:ty() {
                AliasDecl {
                    span: head.span().through(type_span(&ty)),
                    name: name(head),
                    ty,
                }
            }

        rule data_decl() -> DataDecl
            = head:type_ident() params:type_params()? colon()
              representation:data_representation()
              methods:method_block()?
              {
                let end = methods.as_ref().map_or(representation.1, |methods| methods.1);
                DataDecl {
                    span: head.span().through(end),
                    name: name(head),
                    params: params.unwrap_or_default(),
                    representation: representation.0,
                    methods: methods.map_or_else(Vec::new, |methods| methods.0),
                }
            }

        rule data_representation() -> (DataRepresentation, Span)
            = lbracket() constructors:(constructor() ** sep()) close:rbracket() {
                (DataRepresentation::Sum(constructors), close.span())
            }
            / represented:ty() {
                let span = type_span(&represented);
                (DataRepresentation::Wrapper(represented), span)
            }

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
            = tok(Kind::DotParen) methods:method_declaration()* close:rparen() {
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
            = parameters:(ty() ++ sep()) arrow() result:ty()
              constraints:constraints()? {
                let end = constraints.as_ref().map_or_else(
                    || type_span(&result),
                    |constraints| constraints.1,
                );
                (parameters, result, constraints.map_or_else(Vec::new, |value| value.0), end)
            }
            / result:ty() constraints:constraints()? {
                let end = constraints.as_ref().map_or_else(
                    || type_span(&result),
                    |constraints| constraints.1,
                );
                (Vec::new(), result, constraints.map_or_else(Vec::new, |value| value.0), end)
            }

        rule constraints() -> (Vec<Constraint>, Span)
            = tok(Kind::KwWhere) constraints:(constraint() ++ sep()) {
                let end = constraints.last().map_or_else(Span::default, |constraint| constraint.span);
                (constraints, end)
            }

        rule constraint() -> Constraint
            = head:type_ident() adj(Kind::LParen)
              arguments:(ty() ++ sep()) close:rparen() {
                Constraint {
                    span: head.span().through(close.span()),
                    name: name(head),
                    arguments,
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
            / open:lparen() parameters:(ty() ++ sep()) arrow() result:ty() close:rparen() {
                Type::Function {
                    span: open.span().through(close.span()),
                    parameters,
                    result: Box::new(result),
                }
            }
            / open:lbracket() constructors:(constructor() ** sep()) close:rbracket() {
                Type::Variants {
                    span: open.span().through(close.span()),
                    constructors,
                }
            }
            / open:lbrace() fields:(record_type_field() ** sep()) close:rbrace() {
                Type::Record {
                    span: open.span().through(close.span()),
                    fields,
                }
            }

        rule record_type_field() -> (Name, Type)
            = field:ident() colon() value:ty() { (name(field), value) }

        rule body() -> Body
            = bindings:(binding_ahead() binding:binding() { binding })*
              result:expr() { Body { bindings, result } }

        rule binding_ahead()
            = #{|input, at| {
                if binding_ahead(input, at) {
                    peg::RuleResult::Matched(at, ())
                } else {
                    peg::RuleResult::Failed
                }
            }}

        rule binding() -> Binding
            = pattern:pattern() equals() value:expr() { Binding { pattern, value } }

        rule pattern() -> Pattern
            = start:(tok(Kind::Number) / tok(Kind::Char)) adj(Kind::DotDot)
              end:(adj(Kind::Number) / adj(Kind::Char)) {
                Pattern::Range {
                    span: start.span().through(end.span()),
                    start: numeral(start),
                    end: numeral(end),
                }
            }
            / minus:tok(Kind::Minus) value:(adj(Kind::Number) / adj(Kind::Char)) {
                Pattern::Number {
                    span: minus.span().through(value.span()),
                    numeral: numeral(value),
                    negative: true,
                }
            }
            / value:(tok(Kind::Number) / tok(Kind::Char)) {
                Pattern::Number {
                    span: value.span(),
                    numeral: numeral(value),
                    negative: false,
                }
            }
            / open:lbracket() elements:(pattern() ** sep())
              rest:(sep()? tok(Kind::Star) tight() rest:pattern() { rest })?
              close:rbracket() {
                Pattern::List {
                    span: open.span().through(close.span()),
                    elements,
                    rest: rest.map(Box::new),
                }
            }
            / open:lbrace() fields:(record_pattern_field() ** sep()) close:rbrace() {
                Pattern::Record {
                    span: open.span().through(close.span()),
                    fields,
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
            left:(@) bar_sep() right:@ { binary(BinaryOp::Or, left, right) }
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
            left:(@) minus_sep() right:@ { binary(BinaryOp::Subtract, left, right) }
            --
            left:(@) tok(Kind::Slash) right:@ { binary(BinaryOp::Divide, left, right) }
            left:(@) tok(Kind::Percent) right:@ { binary(BinaryOp::Remainder, left, right) }
            left:(@) star_sep() right:@ { binary(BinaryOp::Multiply, left, right) }
            --
            token:tok(Kind::Minus) tight() value:@ { unary(UnaryOp::Negate, token, value) }
            token:tok(Kind::Bang) tight() value:@ { unary(UnaryOp::Not, token, value) }
            --
            head:@ args:call_args() {
                let span = head.span.through(args.1);
                Expr { span, kind: ExprKind::Call(Box::new(head), args.0) }
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

        rule bar_sep() = adj(Kind::Bar) / tok(Kind::Bar) sep()
        rule minus_sep() = adj(Kind::Minus) / tok(Kind::Minus) sep()
        rule star_sep() = adj(Kind::Star) / tok(Kind::Star) sep()

        rule call_args() -> (Vec<Expr>, Span)
            = adj(Kind::LParen) args:(argument() ** sep()) close:rparen() {
                (args, close.span())
            }

        rule argument() -> Expr = lambda() / expr()

        rule lambda() -> Expr
            = open:tok(Kind::Bar) patterns:(pattern() ++ sep()) tok(Kind::Bar) body:expr() {
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
            = value:(tok(Kind::Number) / tok(Kind::Char)) {
                atom(value, ExprKind::Number(numeral(value)))
            }
            / string:string() { string }
            / list:list() { list }
            / record:record() { record }
            / open:lparen() value:expr() close:rparen() {
                Expr { span: open.span().through(close.span()), ..value }
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
            = open:lbrace() fields:(record_expr_field() ** sep()) close:rbrace() {
                Expr {
                    span: open.span().through(close.span()),
                    kind: ExprKind::Record(fields),
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
              rest:(sep()? tok(Kind::Star) tight() rest:expr() { rest })?
              close:rbracket() {
                Expr {
                    span: open.span().through(close.span()),
                    kind: ExprKind::List(elements, rest.map(Box::new)),
                }
            }
    }
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
        | Type::Record { span, .. } => *span,
    }
}
