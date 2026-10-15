//! Compact names used after source resolution.
//!
//! Parsed names remain spans. Crossing into resolved syntax interns each
//! spelling once and stores this four-byte identity instead of allocating it
//! again at every occurrence.

use std::collections::HashMap;

/// An interned spelling owned by one [`Symbols`] collection.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Symbol(u32);

impl Symbol {
    #[must_use]
    pub(crate) fn index(self) -> usize {
        usize::try_from(self.0).expect("u32 fits usize")
    }
}

/// Own interned spellings for one frontend invocation.
#[derive(Clone, Debug, Default)]
pub struct Symbols {
    names: Vec<Box<str>>,
    buckets: HashMap<u64, Vec<Symbol>>,
}

impl Symbols {
    /// Return the existing identity for `text`, or insert it once.
    ///
    /// # Panics
    ///
    /// Panics after more than `u32::MAX` distinct names in one invocation.
    pub fn intern(&mut self, text: &str) -> Symbol {
        let hash = hash(text.as_bytes());
        if let Some(found) = self.buckets.get(&hash).and_then(|bucket| {
            bucket
                .iter()
                .copied()
                .find(|symbol| self.names[symbol.index()].as_ref() == text)
        }) {
            return found;
        }
        let symbol = Symbol(u32::try_from(self.names.len()).expect("fewer than 2^32 symbols"));
        self.names.push(text.into());
        self.buckets.entry(hash).or_default().push(symbol);
        symbol
    }

    #[must_use]
    pub fn text(&self, symbol: Symbol) -> &str {
        &self.names[symbol.index()]
    }

    /// A global's name as its program spells it: its text without the
    /// module identity resolution prefixes it with, `$$`.
    #[must_use]
    pub fn spelling(&self, symbol: Symbol) -> &str {
        let text = self.text(symbol);
        text.rsplit_once("$$").map_or(text, |(_, spelled)| spelled)
    }

    #[must_use]
    pub fn find(&self, text: &str) -> Option<Symbol> {
        self.buckets.get(&hash(text.as_bytes())).and_then(|bucket| {
            bucket
                .iter()
                .copied()
                .find(|symbol| self.names[symbol.index()].as_ref() == text)
        })
    }

    #[must_use]
    pub const fn len(&self) -> usize {
        self.names.len()
    }

    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.names.is_empty()
    }
}

// A fixed hash avoids per-invocation random state and stores each spelling only
// in the indexed pool. Full string comparison in a hash bucket remains the
// authority, so collisions do not change identity.
fn hash(bytes: &[u8]) -> u64 {
    let mut value = 0xcbf2_9ce4_8422_2325u64;
    for &byte in bytes {
        value ^= u64::from(byte);
        value = value.wrapping_mul(0x0000_0100_0000_01b3);
    }
    value
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn one_spelling_has_one_identity() {
        let mut symbols = Symbols::default();
        let first = symbols.intern("Nat");
        let second = symbols.intern("Nat");
        assert_eq!(first, second);
        assert_eq!(symbols.len(), 1);
        assert_eq!(symbols.text(first), "Nat");
    }
}
