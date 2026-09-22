use std::fmt;

use super::ast::Module;
use super::grammar;
use super::lex::{self, Kind, Token};
use super::literal;
use super::source::SourceId;

/// A lexical or grammatical error at a source position.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParseError {
    pub offset: usize,
    pub line: usize,
    pub column: usize,
    pub message: String,
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
    let mut module =
        grammar::source::program(&tokens).map_err(|error| syntax_error(source, &tokens, &error))?;
    if validate_literals {
        literal::validate(&module, source).map_err(|error| {
            let offset = usize::try_from(error.span.start).expect("u32 fits usize");
            error_at(source, offset, error.message)
        })?;
    }
    module.source = source_id;
    Ok(module)
}

fn syntax_error(
    source: &str,
    tokens: &[Token],
    error: &peg::error::ParseError<usize>,
) -> ParseError {
    let token = tokens
        .get(error.location)
        .or_else(|| tokens.last())
        .copied()
        .expect("the lexer always writes an end token");
    let message = match token.kind {
        Kind::Error if token.start == token.end => "unterminated string literal".to_owned(),
        Kind::Error => format!("invalid token `{}`", token.text(source)),
        Kind::Eof => format!("expected {} before the end of the file", error.expected),
        _ => format!(
            "expected {}, found `{}`",
            error.expected,
            token.text(source)
        ),
    };
    let offset = usize::try_from(token.start).expect("u32 fits usize");
    error_at(source, offset, message)
}

fn error_at(source: &str, offset: usize, message: String) -> ParseError {
    let before = &source[..offset.min(source.len())];
    let line = before.bytes().filter(|byte| *byte == b'\n').count() + 1;
    let line_start = before.rfind('\n').map_or(0, |at| at + 1);
    let column = before[line_start..].chars().count() + 1;
    ParseError {
        offset,
        line,
        column,
        message,
    }
}
