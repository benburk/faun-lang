use std::fmt;

use super::ast::Module;
use super::ast::Span;
use super::grammar;
use super::lex::{self, Kind};
use super::lines;
use super::literal;
use super::source::SourceId;

/// A lexical or grammatical error at a source position.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParseError {
    pub offset: usize,
    /// Where what it is about ends, which is `offset` where it is about a
    /// place rather than a stretch of text.
    pub end: usize,
    pub line: usize,
    pub column: usize,
    pub message: String,
    /// The errors after this one in the same source, for a parse that went
    /// on past it: each line that could not be read is one.
    pub also: Vec<Self>,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}: {}", self.line, self.column, self.message)
    }
}

impl std::error::Error for ParseError {}

/// Parse the currently implemented strict subset of Ori source syntax.
///
/// The parser retains byte spans into `source`; it does not allocate strings
/// for names. Parsing performs no name resolution, typing, or lowering.
///
/// # Errors
///
/// Returns the first lexical or grammatical error with a one-based line and
/// column. Forms outside the subset are syntax errors for now.
pub fn parse(source: &str) -> Result<Module, ParseError> {
    parse_in(source, SourceId::DETACHED)
}

/// Parse source already owned by a source collection.
///
/// The returned module records `source_id`; all spans inside it are byte ranges
/// into `source`.
///
/// # Errors
///
/// Returns the first lexical or grammatical error.
///
/// # Panics
///
/// Panics only on a target whose address space cannot represent a `u32` byte
/// offset; such a target cannot hold a maximum-size accepted source.
pub fn parse_in(source: &str, source_id: SourceId) -> Result<Module, ParseError> {
    let tokens = lex::lex(source).map_err(|error| error_at(source, 0, error.to_string()))?;
    let validate_literals = tokens
        .iter()
        .any(|token| matches!(token.kind, Kind::Char | Kind::StrText));
    let (lines, errors) = grammar::file(&tokens, source);
    let mut errors = errors
        .into_iter()
        .map(|error| spanned(source, error.span, error.message));
    if let Some(mut first) = errors.next() {
        first.also = errors.collect();
        return Err(first);
    }
    let items =
        lines::items(lines, source).map_err(|error| spanned(source, error.span, error.message))?;
    let mut module = Module {
        source: SourceId::DETACHED,
        items,
    };
    if let Some(line) = discarded_values(&module, source) {
        return Err(spanned(
            source,
            line,
            "this value is worked out and then thrown away; remove the line, or bind the value to a name if you need it".to_owned(),
        ));
    }
    if validate_literals {
        literal::validate(&module, source).map_err(|error| {
            let offset = usize::try_from(error.span.start).expect("u32 fits usize");
            error_at(source, offset, error.message)
        })?;
    }
    module.source = source_id;
    Ok(module)
}

/// The first line of a body that keeps nothing of what it works out and is
/// no effect: a call of a name ending `!`, directly or as a method, is the
/// only thing worth asking for what it does.
fn discarded_values(module: &Module, source: &str) -> Option<Span> {
    use crate::ast::{ExprKind, Item, MethodItem};
    let effect = |expression: &crate::ast::Expr| match &expression.kind {
        ExprKind::Call(head, _) => {
            matches!(&head.kind, ExprKind::Name(name) if name.text(source).ends_with('!'))
        }
        ExprKind::Method(_, name, _) => name.text(source).ends_with('!'),
        _ => false,
    };
    let clauses = module.items.iter().flat_map(|item| match item {
        Item::Clause(clause) | Item::Expect(clause) => vec![clause],
        Item::Data(data) => data
            .methods
            .iter()
            .filter_map(|method| match method {
                MethodItem::Clause(clause) => Some(clause),
                MethodItem::Signature(_) => None,
            })
            .collect(),
        _ => Vec::new(),
    });
    clauses
        .flat_map(|clause| &clause.body.bindings)
        .find(|binding| binding.discarded && !effect(&binding.value))
        .map(|binding| binding.value.span)
}

/// An error about the text `span` covers.
fn spanned(source: &str, span: Span, message: String) -> ParseError {
    let mut error = error_at(
        source,
        usize::try_from(span.start).expect("u32 fits usize"),
        message,
    );
    error.end = usize::try_from(span.end).expect("u32 fits usize");
    error
}

fn error_at(source: &str, offset: usize, message: String) -> ParseError {
    let before = &source[..offset.min(source.len())];
    let line = before.bytes().filter(|byte| *byte == b'\n').count() + 1;
    let line_start = before.rfind('\n').map_or(0, |at| at + 1);
    let column = before[line_start..].chars().count() + 1;
    ParseError {
        offset,
        end: offset,
        line,
        column,
        message,
        also: Vec::new(),
    }
}
