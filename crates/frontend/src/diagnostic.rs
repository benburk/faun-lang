//! What the frontend says when it refuses a program.
//!
//! A [`Diagnostic`] is a message, the places it points at, and what else
//! helps understand or fix it, rendered as rustc renders one: the message,
//! `path:line:column`, each line a place is on with marks under the place
//! and what is there beside them, then its notes and help. Where it
//! happened is marked `^`; other places explaining it `-`. Places are
//! resolved when the diagnostic is made, while the source is at hand, so a
//! diagnostic renders on its own. One made where no source is known
//! renders as its message. Either way it starts `error: `, as each
//! diagnostic found with it does.
//!
//! Reading a file refuses with a syntax error, and every pass after loading
//! with a `Refusal`: a place in a module rather than in a source, so it is
//! made without the sources at hand. Either gathers the same [`Advice`],
//! carried over when it is told as a diagnostic.

use std::fmt;
use std::path::{Path, PathBuf};

use crate::ast::Span;
use crate::source::Source;

/// What a refusal says besides its message, gathered by a pass before the
/// source is at hand: what is at its place, what explains it, and what
/// would fix it.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Advice {
    /// What is at the place; may be empty.
    pub label: String,
    pub notes: Vec<String>,
    pub help: Vec<String>,
}

/// A pass's refusal, which carries [`Advice`] to its diagnostic.
pub trait Advised: Sized {
    fn advice(&mut self) -> &mut Advice;

    /// The same, saying what is at its place.
    #[must_use]
    fn label(mut self, label: impl Into<String>) -> Self {
        self.advice().label = label.into();
        self
    }

    #[must_use]
    fn note(mut self, note: impl Into<String>) -> Self {
        self.advice().notes.push(note.into());
        self
    }

    #[must_use]
    fn help(mut self, help: impl Into<String>) -> Self {
        self.advice().help.push(help.into());
        self
    }
}

/// `count` of `noun`, as a sentence says it: `1 argument`, `2 arguments`.
pub(crate) fn counted(count: usize, noun: &str) -> String {
    if count == 1 {
        format!("1 {noun}")
    } else {
        format!("{count} {noun}s")
    }
}

/// How many `were given`, as a sentence says it: `1 was`, `2 were`.
pub(crate) fn given(count: usize) -> String {
    if count == 1 {
        "1 was".to_owned()
    } else {
        format!("{count} were")
    }
}

/// Why a pass after loading refuses a program: what it says, where, and
/// what else helps. Places are a module and a span, so a refusal is made
/// without the sources at hand and told as a [`Diagnostic`] by whoever holds
/// them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Refusal {
    pub message: String,
    /// Where it happened. A refusal made where that is not known is placed
    /// by whoever knows it; one never placed is told without a place.
    pub at: Option<(crate::ModuleId, Span)>,
    /// Boxed, as it is only filled on the way out, so a `Result` carrying
    /// the refusal stays small on the path that succeeds.
    pub advice: Box<Advice>,
    /// Other places explaining it, and what is at each.
    pub secondary: Vec<((crate::ModuleId, Span), String)>,
}

impl Refusal {
    /// A refusal at `span` in `module`.
    pub(crate) fn at(module: crate::ModuleId, span: Span, message: impl Into<String>) -> Self {
        Self::from(message.into()).placed(module, span)
    }

    /// The same, at `span` in `module`.
    #[must_use]
    pub(crate) const fn placed(mut self, module: crate::ModuleId, span: Span) -> Self {
        self.at = Some((module, span));
        self
    }

    /// The same, saying too what is at another place explaining it.
    #[must_use]
    pub(crate) fn also(
        mut self,
        module: crate::ModuleId,
        span: Span,
        text: impl Into<String>,
    ) -> Self {
        self.secondary.push(((module, span), text.into()));
        self
    }

    /// The same, saying another thing first.
    #[must_use]
    pub(crate) fn retitled(mut self, message: impl Into<String>) -> Self {
        self.message = message.into();
        self
    }

    /// Told as a diagnostic, each place read from the source of its module.
    pub(crate) fn told<'s>(self, source: impl Fn(crate::ModuleId) -> &'s Source) -> Diagnostic {
        let diagnostic = Diagnostic::new(self.message);
        let diagnostic = match self.at {
            Some((module, span)) => diagnostic.at(source(module), span),
            None => diagnostic,
        };
        let mut diagnostic = diagnostic.advised(*self.advice);
        for ((module, span), text) in self.secondary {
            diagnostic = diagnostic.secondary(source(module), span, text);
        }
        diagnostic
    }
}

impl From<String> for Refusal {
    fn from(message: String) -> Self {
        Self {
            message,
            at: None,
            advice: Box::default(),
            secondary: Vec::new(),
        }
    }
}

impl From<&str> for Refusal {
    fn from(message: &str) -> Self {
        Self::from(message.to_owned())
    }
}

impl Advised for Refusal {
    fn advice(&mut self) -> &mut Advice {
        &mut self.advice
    }
}

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

/// A place a diagnostic points at, and what it says of it there.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Label {
    pub location: Location,
    /// Written after the marks under the place; may be empty.
    pub text: String,
}

/// Why a program was refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diagnostic {
    pub message: String,
    /// The places it points at, where a source is known: first where it
    /// happened, marked `^`, then any others explaining it, marked `-`.
    pub labels: Vec<Label>,
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
            labels: Vec::new(),
            notes: Vec::new(),
            help: Vec::new(),
            also: Vec::new(),
        }
    }

    /// The same, at `span` in `source`.
    #[must_use]
    pub fn at(self, source: &Source, span: Span) -> Self {
        let location = Location::of(source, span);
        self.at_location(location)
    }

    /// The same, at a place already resolved.
    #[must_use]
    pub fn at_location(mut self, location: Location) -> Self {
        let primary = Label {
            location,
            text: String::new(),
        };
        if self.labels.is_empty() {
            self.labels.push(primary);
        } else {
            self.labels[0] = primary;
        }
        self
    }

    /// The same, saying what is at the place it happened. Where no place is
    /// known there is nowhere to say it.
    #[must_use]
    pub fn label(mut self, text: impl Into<String>) -> Self {
        if let Some(primary) = self.labels.first_mut() {
            primary.text = text.into();
        }
        self
    }

    /// The same, with what a pass said besides its message.
    #[must_use]
    pub fn advised(self, advice: Advice) -> Self {
        let mut diagnostic = self.label(advice.label);
        diagnostic.notes.extend(advice.notes);
        diagnostic.help.extend(advice.help);
        diagnostic
    }

    /// The same, pointing too at `span` in `source`, which explains it.
    #[must_use]
    pub fn secondary(self, source: &Source, span: Span, text: impl Into<String>) -> Self {
        let location = Location::of(source, span);
        self.secondary_at(location, text)
    }

    /// The same, pointing too at a place already resolved. One given before
    /// any place it happened would be read as that place, so it is dropped.
    #[must_use]
    pub fn secondary_at(mut self, location: Location, text: impl Into<String>) -> Self {
        if !self.labels.is_empty() {
            let text = text.into();
            self.labels.push(Label { location, text });
        }
        self
    }

    /// Where it happened, when a source is known.
    #[must_use]
    pub fn location(&self) -> Option<&Location> {
        self.labels.first().map(|label| &label.location)
    }

    /// The same, each place in it shown from `base` where it lies beneath:
    /// as a command shows paths from where it was run.
    #[must_use]
    pub fn relative_to(mut self, base: &Path) -> Self {
        for label in &mut self.labels {
            if let Ok(relative) = label.location.path.strip_prefix(base) {
                label.location.path = relative.to_path_buf();
            }
        }
        let also = std::mem::take(&mut self.also);
        self.also = also
            .into_iter()
            .map(|also| also.relative_to(base))
            .collect();
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

    /// Write the lines its labels are on, each followed by the marks under
    /// its places, file by file with the file it happened in first. Lines
    /// not next to each other are parted by `...`.
    fn write_snippets(&self, f: &mut fmt::Formatter<'_>, gutter: &str) -> fmt::Result {
        let mut files: Vec<(&Path, Vec<(bool, &Label)>)> = Vec::new();
        for (index, label) in self.labels.iter().enumerate() {
            let path = label.location.path.as_path();
            let primary = index == 0;
            match files.iter_mut().find(|(file, _)| *file == path) {
                Some((_, labels)) => labels.push((primary, label)),
                None => files.push((path, vec![(primary, label)])),
            }
        }
        for (index, (path, mut labels)) in files.into_iter().enumerate() {
            labels.sort_by_key(|(primary, label)| {
                (label.location.line, !primary, label.location.column)
            });
            if index > 0 {
                let first = &labels[0].1.location;
                write!(
                    f,
                    "\n{gutter}::: {}:{}:{}",
                    path.display(),
                    first.line,
                    first.column
                )?;
            }
            write!(f, "\n{gutter} |")?;
            let mut previous: Option<usize> = None;
            for line in labels.chunk_by(|a, b| a.1.location.line == b.1.location.line) {
                let at = &line[0].1.location;
                if previous.is_some_and(|number| at.line > number + 1) {
                    write!(f, "\n...")?;
                }
                previous = Some(at.line);
                let width = gutter.len();
                write!(f, "\n{:<width$} | {}", at.line, at.text)?;
                write_marks(f, gutter, line)?;
            }
        }
        Ok(())
    }
}

/// Write the marks under one line's places. Places apart from each other
/// share a row, the rightmost saying what it is beside its marks and each
/// other below, hung from a `|`; places that overlap each get a row.
fn write_marks(f: &mut fmt::Formatter<'_>, gutter: &str, labels: &[(bool, &Label)]) -> fmt::Result {
    let mut labels = labels.to_vec();
    labels.sort_by_key(|(_, label)| label.location.column);
    let apart = labels.windows(2).all(|pair| {
        let left = &pair[0].1.location;
        let right = &pair[1].1.location;
        left.column + left.width < right.column
    });
    if !apart {
        for (primary, label) in labels {
            write!(f, "\n{gutter} | ")?;
            write_row(f, &[(primary, label)], label.text.as_str())?;
        }
        return Ok(());
    }
    let (rightmost, hung) = labels.split_last().expect("a line has a place");
    write!(f, "\n{gutter} | ")?;
    write_row(f, &labels, rightmost.1.text.as_str())?;
    let hung: Vec<_> = hung
        .iter()
        .filter(|(_, label)| !label.text.is_empty())
        .collect();
    if hung.is_empty() {
        return Ok(());
    }
    write!(f, "\n{gutter} | ")?;
    write_pipes(f, &hung, "")?;
    for index in (0..hung.len()).rev() {
        write!(f, "\n{gutter} | ")?;
        let text = &hung[index].1.text;
        write_pipes(f, &hung[..=index], text)?;
    }
    Ok(())
}

/// The marks under `labels`, `^` for where it happened and `-` elsewhere,
/// then `text` after them.
fn write_row(f: &mut fmt::Formatter<'_>, labels: &[(bool, &Label)], text: &str) -> fmt::Result {
    let mut written = 1;
    for (primary, label) in labels {
        let at = &label.location;
        let mark = if *primary { "^" } else { "-" };
        write!(
            f,
            "{}{}",
            " ".repeat(at.column - written),
            mark.repeat(at.width)
        )?;
        written = at.column + at.width;
    }
    if !text.is_empty() {
        write!(f, " {text}")?;
    }
    Ok(())
}

/// A `|` under the start of each of `labels`, the last replaced by `text`
/// where there is one.
fn write_pipes(f: &mut fmt::Formatter<'_>, labels: &[&(bool, &Label)], text: &str) -> fmt::Result {
    let mut written = 1;
    for (index, (_, label)) in labels.iter().enumerate() {
        let column = label.location.column;
        let last = index + 1 == labels.len();
        let mark = if last && !text.is_empty() { text } else { "|" };
        write!(f, "{}{mark}", " ".repeat(column - written))?;
        written = column + 1;
    }
    Ok(())
}

impl fmt::Display for Diagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "error: {}", self.message)?;
        let widest = self
            .labels
            .iter()
            .map(|label| label.location.line.to_string().len())
            .max();
        let gutter = " ".repeat(widest.unwrap_or(1));
        if let Some(at) = self.location() {
            write!(
                f,
                "\n{gutter}--> {}:{}:{}",
                at.path.display(),
                at.line,
                at.column
            )?;
            self.write_snippets(f, &gutter)?;
            if !self.notes.is_empty() || !self.help.is_empty() {
                write!(f, "\n{gutter} |")?;
            }
        }
        for note in &self.notes {
            write!(f, "\n{gutter} = note: {note}")?;
        }
        for help in &self.help {
            write!(f, "\n{gutter} = help: {help}")?;
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
        let diagnostic = Diagnostic::new("mismatched types")
            .at(source, Span::new(start, start + 4))
            .label("expected `U8`, found `Bool`")
            .help("exit with a number");
        assert_eq!(
            diagnostic.to_string(),
            "error: mismatched types\n \
             --> main.fn:3:14\n  \
             |\n\
             3 |   host.exit!(True)\n  \
             |              ^^^^ expected `U8`, found `Bool`\n  \
             |\n  \
             = help: exit with a number"
        );
    }

    /// Other places explaining it are marked `-`, in line order, with lines
    /// not next to each other parted by `...`, and the gutter as wide as the
    /// widest line number.
    #[test]
    fn a_diagnostic_points_too_at_what_explains_it() {
        let mut sources = Sources::default();
        let text = "f : Nat -> Nat\nf(n) ->\n  n\n\n\n\n\n\n\nx = f(True)\n";
        let id = sources.add("main.fn", text);
        let source = sources.get(id).unwrap();
        let at = |word: &str| {
            let start = text.find(word).unwrap();
            Span::new(start, start + word.len())
        };
        let diagnostic = Diagnostic::new("mismatched types")
            .at(source, at("True"))
            .label("expected `Nat`, found `Bool`")
            .secondary(source, at("Nat"), "expected because of this")
            .note("a numeral is a `Nat`");
        assert_eq!(
            diagnostic.to_string(),
            "error: mismatched types\n  \
             --> main.fn:10:7\n   \
             |\n\
             1  | f : Nat -> Nat\n   \
             |     --- expected because of this\n\
             ...\n\
             10 | x = f(True)\n   \
             |       ^^^^ expected `Nat`, found `Bool`\n   \
             |\n   \
             = note: a numeral is a `Nat`"
        );
    }

    /// Places on one line share a row of marks; the rightmost says what it
    /// is beside them, and the others below, hung from a `|`.
    #[test]
    fn places_on_one_line_share_a_row() {
        let mut sources = Sources::default();
        let text = "x = both!(file, file)\n";
        let id = sources.add("main.fn", text);
        let source = sources.get(id).unwrap();
        let diagnostic = Diagnostic::new("used after it was used up")
            .at(source, Span::new(16, 20))
            .label("used again here")
            .secondary(source, Span::new(10, 14), "used up here");
        assert_eq!(
            diagnostic.to_string(),
            "error: used after it was used up\n \
             --> main.fn:1:17\n  \
             |\n\
             1 | x = both!(file, file)\n  \
             |           ----  ^^^^ used again here\n  \
             |           |\n  \
             |           used up here"
        );
    }

    #[test]
    fn an_unplaced_diagnostic_is_its_message() {
        assert_eq!(Diagnostic::new("no entry").to_string(), "error: no entry");
    }
}
