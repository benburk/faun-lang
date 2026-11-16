use std::fmt;

use super::ast::Module;
use super::ast::Span;
use super::diagnostic::{Advice, Advised};
use super::grammar;
use super::lex;
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
    /// Boxed, as it is rarely more than empty, so a `Result` carrying the
    /// error stays small on the path that succeeds.
    pub advice: Box<Advice>,
    /// The errors after this one in the same source, for a parse that went
    /// on past it: each line that could not be read is one.
    pub also: Vec<Self>,
}

impl Advised for ParseError {
    fn advice(&mut self) -> &mut Advice {
        &mut self.advice
    }
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
/// Report syntax errors with one-based lines and columns, collecting those
/// found by grammar recovery. Reject invalid literals and discarded pure values.
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
/// Report syntax errors as [`parse`] does. Reject invalid literals and
/// discarded pure values.
///
/// # Panics
///
/// Panics only on a target whose address space cannot represent a `u32` byte
/// offset; such a target cannot hold a maximum-size accepted source.
pub fn parse_in(source: &str, source_id: SourceId) -> Result<Module, ParseError> {
    let tokens = lex::lex(source).map_err(|error| error_at(source, 0, error.to_string()))?;
    let (lines, mut errors) = grammar::file(&tokens, source);
    let more = errors.len() >= grammar::ERRORS_SHOWN;
    errors.truncate(grammar::ERRORS_SHOWN);
    let mut errors = errors.into_iter().map(|error| syntax(source, error));
    if let Some(mut first) = errors.next() {
        first.also = errors.collect();
        if more {
            first.advice.notes.push(format!(
                "the file is read no further than its first {} errors",
                grammar::ERRORS_SHOWN
            ));
        }
        return Err(first);
    }
    let items = lines::items(lines, source).map_err(|error| syntax(source, error))?;
    literal::validate(&tokens, source)
        .map_err(|error| spanned(source, error.span, error.message))?;
    Ok(Module {
        source: source_id,
        items,
    })
}

/// A line's syntax error, with what it advises.
fn syntax(source: &str, error: grammar::SyntaxError) -> ParseError {
    let mut spanned = spanned(source, error.span, error.message);
    spanned.advice = Box::new(error.advice);
    spanned
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
        advice: Box::default(),
        also: Vec::new(),
    }
}
