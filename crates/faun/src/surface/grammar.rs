//! The initial Ori grammar over lexer tokens.
//!
//! This deliberately accepts a strict subset: nominal constructor types,
//! first-order signatures, clause patterns, local bindings, calls, methods,
//! and operators. Unsupported Ori forms fail in the parser rather than being
//! accepted into an AST that later stages cannot represent.

use super::ast::{
    BinaryOp, Binding, Body, Clause, ConstructorDecl, DataDecl, Expr, ExprKind, Item, Module, Name,
    Pattern, SignatureDecl, Span, Type, UnaryOp,
};
use super::lex::{Kind, Token};

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
    Signature(Vec<Type>, Type, Span),
    Clause(Vec<Pattern>, Body),
}

/// Return whether the next pattern-shaped token run is followed by `=`.
///
/// A constructor expression and a constructor pattern have the same spelling.
/// Letting `binding()*` discover the difference through PEG backtracking builds
/// and drops the entire pattern tree before parsing a body's final expression.
/// This scan follows only the delimiters needed to locate the possible `=`;
/// the ordinary pattern rule remains the authority on whether the run is valid.
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
        _ => None,
    };
    end.and_then(|end| tokens.get(end))
        .is_some_and(|token| token.kind == Kind::Eq)
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
        rule colon() = tok(Kind::Colon) / expected!("`:`")
        rule arrow() = tok(Kind::Arrow) / expected!("`->`")
        rule equals() = tok(Kind::Eq) / expected!("`=`")
        rule ident() -> Token = tok(Kind::Ident) / expected!("a name")
        rule type_ident() -> Token = tok(Kind::TypeIdent) / expected!("a type name")
        rule term_name() -> Token
            = quiet!{[token if matches!(token.kind, Kind::Ident | Kind::EffectIdent)]}
              / expected!("a term name")

        pub rule program() -> Module
            = items:item()* eof() { Module { items } }

        rule item() -> Item
            = data:data_decl() { Item::Data(data) }
            / declaration:term_declaration() { declaration }

        rule data_decl() -> DataDecl
            = head:type_ident() params:type_params()? colon()
              lbracket() constructors:(constructor() ** sep()) close:rbracket() {
                DataDecl {
                    span: head.span().through(close.span()),
                    name: name(head),
                    params: params.unwrap_or_default(),
                    constructors,
                }
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

        rule term_declaration() -> Item
            = head:term_name() declaration:(
                colon() signature:signature_type() {
                    TermDeclaration::Signature(signature.0, signature.1, signature.2)
                }
                / adj(Kind::LParen) patterns:(pattern() ** sep()) rparen()
                  arrow() body:body() {
                    TermDeclaration::Clause(patterns, body)
                }
            ) {
                match declaration {
                    TermDeclaration::Signature(parameters, result, end) => {
                        Item::Signature(SignatureDecl {
                            span: head.span().through(end),
                            name: name(head),
                            parameters,
                            result,
                        })
                    }
                    TermDeclaration::Clause(patterns, body) => Item::Clause(Clause {
                        span: head.span().through(body.result.span),
                        name: name(head),
                        patterns,
                        body,
                    }),
                }
            }

        rule signature_type() -> (Vec<Type>, Type, Span)
            = parameters:(ty() ++ sep()) arrow() result:ty() {
                let end = type_span(&result);
                (parameters, result, end)
            }
            / result:ty() {
                let end = type_span(&result);
                (Vec::new(), result, end)
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
            = minus:tok(Kind::Minus) number:adj(Kind::Number) {
                Pattern::Number {
                    span: minus.span().through(number.span()),
                    negative: true,
                }
            }
            / number:tok(Kind::Number) {
                Pattern::Number { span: number.span(), negative: false }
            }
            / head:type_ident()
              fields:(adj(Kind::LParen) fields:(pattern() ++ sep()) close:rparen() {
                  (fields, close.span())
              })? {
                let (fields, end) = fields.unwrap_or_else(|| (Vec::new(), head.span()));
                Pattern::Constructor {
                    span: head.span().through(end),
                    name: name(head),
                    fields,
                }
            }
            / wild:tok(Kind::Wild) { Pattern::Wild(wild.span()) }
            / bind:ident() { Pattern::Bind(name(bind)) }

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
            head:@ member:dot_call() {
                let span = head.span.through(member.2);
                Expr {
                    span,
                    kind: ExprKind::Method(Box::new(head), name(member.0), member.1),
                }
            }
            --
            primary:primary() { primary }
        }

        rule bar_sep() = adj(Kind::Bar) / tok(Kind::Bar) sep()
        rule minus_sep() = adj(Kind::Minus) / tok(Kind::Minus) sep()
        rule star_sep() = adj(Kind::Star) / tok(Kind::Star) sep()

        rule call_args() -> (Vec<Expr>, Span)
            = adj(Kind::LParen) args:(expr() ** sep()) close:rparen() {
                (args, close.span())
            }

        rule dot_call() -> (Token, Vec<Expr>, Span)
            = chain_dot() member:(adj(Kind::Ident) / adj(Kind::EffectIdent))
              args:call_args() {
                (member, args.0, args.1)
            }

        rule primary() -> Expr
            = number:tok(Kind::Number) { atom(number, ExprKind::Number) }
            / open:lparen() value:expr() close:rparen() {
                Expr { span: open.span().through(close.span()), ..value }
            }
            / token:quiet!{[token if matches!(token.kind,
                Kind::TypeIdent | Kind::Ident | Kind::EffectIdent)]} {
                atom(token, ExprKind::Name(name(token)))
            }
            / expected!("an expression")
    }
}

const fn type_span(ty: &Type) -> Span {
    match ty {
        Type::Named { span, .. } => *span,
    }
}
