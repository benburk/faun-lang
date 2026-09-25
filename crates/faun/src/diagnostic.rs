//! What the frontend says when it refuses a program.
//!
//! A [`Diagnostic`] is a message, where it happened, and what else helps
//! understand or fix it. Places are resolved when the diagnostic is made,
//! while the source is at hand, so a diagnostic renders on its own: as
//! `path:line:column`, the line itself, and a caret under the span. One made
//! where no source is known renders as its message.

use std::fmt;
use std::path::PathBuf;

use crate::ast::Span;
use crate::source::Source;

/// A span resolved against its source: where it is, and the line it is on.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Location {
    pub path: PathBuf,
    /// One-based.
    pub line: usize,
    /// One-based, in characters.
    pub column: usize,
    /// The whole line the span starts on, without its newline.
    pub text: String,
    /// How many characters of that line the span covers, at least one.
    pub width: usize,
}

impl Location {
    /// Resolve `span` in `source`.
    #[must_use]
    pub fn of(source: &Source, span: Span) -> Self {
        let text = source.text();
        let start = usize::try_from(span.start).map_or(text.len(), |at| at.min(text.len()));
        let end = usize::try_from(span.end).map_or(start, |at| at.clamp(start, text.len()));
        let line_start = text[..start].rfind('\n').map_or(0, |at| at + 1);
        let line_end = text[start..].find('\n').map_or(text.len(), |at| start + at);
        let before = &text[line_start..start];
        let covered = &text[start..end.min(line_end)];
        Self {
            path: source.name().to_path_buf(),
            line: text[..start].matches('\n').count() + 1,
            column: before.chars().count() + 1,
            text: text[line_start..line_end].to_owned(),
            width: covered.chars().count().max(1),
        }
    }
}

/// Why a program was refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diagnostic {
    pub message: String,
    /// Where it happened, when a source is known. Boxed so a `Result`
    /// carrying a diagnostic stays small on the path that succeeds.
    pub location: Option<Box<Location>>,
    /// What else explains it.
    pub notes: Vec<String>,
    /// What would fix it.
    pub help: Vec<String>,
    /// The diagnostics found with this one, told after it: the other lines
    /// of a file that could not be read.
    pub also: Vec<Self>,
}

impl Diagnostic {
    /// A diagnostic with no place in the source.
    pub fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
            location: None,
            notes: Vec::new(),
            help: Vec::new(),
            also: Vec::new(),
        }
    }

    /// The same, at `span` in `source`.
    #[must_use]
    pub fn at(mut self, source: &Source, span: Span) -> Self {
        self.location = Some(Box::new(Location::of(source, span)));
        self
    }

    #[must_use]
    pub fn note(mut self, note: impl Into<String>) -> Self {
        self.notes.push(note.into());
        self
    }

    #[must_use]
    pub fn help(mut self, help: impl Into<String>) -> Self {
        self.help.push(help.into());
        self
    }
}

impl fmt::Display for Diagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)?;
        if let Some(at) = &self.location {
            let number = at.line.to_string();
            let gutter = " ".repeat(number.len());
            write!(
                f,
                "\n{gutter}--> {}:{}:{}\n{gutter} |\n{number} | {}\n{gutter} | {}{}",
                at.path.display(),
                at.line,
                at.column,
                at.text,
                " ".repeat(at.column - 1),
                "^".repeat(at.width),
            )?;
        }
        for note in &self.notes {
            write!(f, "\n  = note: {note}")?;
        }
        for help in &self.help {
            write!(f, "\n  = help: {help}")?;
        }
        for also in &self.also {
            write!(f, "\n\n{also}")?;
        }
        Ok(())
    }
}

impl std::error::Error for Diagnostic {}

/// A diagnostic told to someone is its rendering.
impl From<Diagnostic> for String {
    fn from(diagnostic: Diagnostic) -> Self {
        diagnostic.to_string()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::source::Sources;

    #[test]
    fn a_located_diagnostic_shows_its_line_and_span() {
        let mut sources = Sources::default();
        let id = sources.add(
            "main.fn",
            "main! : Host -> []\nmain!(host) ->\n  host.exit!(True)\n",
        );
        let source = sources.get(id).unwrap();
        let text = source.text();
        let start = text.find("True").unwrap();
        let diagnostic = Diagnostic::new("expected a Nat, found a Bool")
            .at(source, Span::new(start, start + 4))
            .help("exit with a number");
        assert_eq!(
            diagnostic.to_string(),
            "expected a Nat, found a Bool\n \
             --> main.fn:3:14\n  \
             |\n\
             3 |   host.exit!(True)\n  \
             |              ^^^^\n  \
             = help: exit with a number"
        );
    }

    #[test]
    fn an_unplaced_diagnostic_is_its_message() {
        assert_eq!(Diagnostic::new("no entry").to_string(), "no entry");
    }
}
