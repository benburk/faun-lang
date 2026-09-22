//! Source ownership for parsed modules and diagnostics.
//!
//! Syntax spans stay as two-word byte ranges. A parsed module carries the
//! source identity once, rather than paying for it on every name and node.

use std::path::{Path, PathBuf};

use super::ast::Span;

/// The identity of one source in a [`Sources`] collection.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SourceId(u32);

impl Default for SourceId {
    fn default() -> Self {
        Self::DETACHED
    }
}

impl SourceId {
    /// A source parsed without being inserted into a collection.
    pub const DETACHED: Self = Self(u32::MAX);

    #[must_use]
    fn index(self) -> Option<usize> {
        (self != Self::DETACHED).then(|| usize::try_from(self.0).expect("u32 fits usize"))
    }
}

/// One immutable source file.
#[derive(Clone, Debug)]
pub struct Source {
    name: PathBuf,
    text: String,
}

impl Source {
    #[must_use]
    pub fn name(&self) -> &Path {
        &self.name
    }

    #[must_use]
    pub fn text(&self) -> &str {
        &self.text
    }

    /// Read a span known to belong to this source.
    ///
    /// # Panics
    ///
    /// Panics when `span` did not come from this source.
    #[must_use]
    pub fn get(&self, span: Span) -> &str {
        span.text(&self.text)
    }
}

/// Own all source text used by one frontend invocation.
#[derive(Clone, Debug, Default)]
pub struct Sources {
    files: Vec<Source>,
}

impl Sources {
    /// Insert source text and return the identity used by its parsed module.
    ///
    /// # Panics
    ///
    /// Panics when inserting `u32::MAX` source files in one invocation; that
    /// identity is reserved for detached syntax.
    pub fn add(&mut self, name: impl Into<PathBuf>, text: impl Into<String>) -> SourceId {
        let raw = u32::try_from(self.files.len()).expect("fewer than 2^32 source files");
        assert_ne!(raw, u32::MAX, "the detached source ID stays reserved");
        let id = SourceId(raw);
        self.files.push(Source {
            name: name.into(),
            text: text.into(),
        });
        id
    }

    #[must_use]
    pub fn get(&self, id: SourceId) -> Option<&Source> {
        id.index().and_then(|index| self.files.get(index))
    }

    #[must_use]
    pub const fn len(&self) -> usize {
        self.files.len()
    }

    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.files.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn equal_ranges_belong_to_their_module_source() {
        let mut sources = Sources::default();
        let first = sources.add("first.ori", "Alpha");
        let second = sources.add("second.ori", "Bravo");
        let span = Span::new(0, 5);
        assert_eq!(sources.get(first).unwrap().get(span), "Alpha");
        assert_eq!(sources.get(second).unwrap().get(span), "Bravo");
    }
}
