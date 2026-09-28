//! How every tier keeps a program: dense indices into flat arrays, and
//! runs within them.
//!
//! A tier holds its program as one array per kind of thing, and points into
//! them with a four-byte index rather than a pointer. Nothing is boxed,
//! nothing is reference counted, a program is a handful of `Vec`s, and
//! copying an index copies four bytes.
//!
//! Individually addressed entities use a typed, append-only `Pool`: insertion
//! returns the entity's ID and indexing requires that kind of ID. A `BitSet`
//! holds a set of one kind of ID. Variable-length runs still use ordinary
//! vectors and `Range`; temporary vectors and coupled instruction/result
//! arrays retain their own construction rules.
//!
//! Targets declare their own IDs with [`index!`], so every tier below the IR
//! indexes the same way.

/// Declare dense index types: `index!(pub(crate) BlockId, InstId)`. Each
/// type, its `u32` field, and its `at` and `index` take the given visibility.
#[doc(hidden)]
#[macro_export]
macro_rules! __index {
    ($vis:vis $($name:ident),+ $(,)?) => {$(
        #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
        $vis struct $name($vis u32);

        impl $crate::index::Id for $name {
            fn at(index: usize) -> Self { Self::at(index) }
            fn index(self) -> usize { self.index() }
        }

        impl $name {
            /// # Panics
            ///
            /// If the program outgrew the four billion of these it may have.
            #[must_use]
            $vis fn at(index: usize) -> Self {
                Self(u32::try_from(index).expect("a program within 4G of these"))
            }

            #[must_use]
            $vis fn index(self) -> usize {
                usize::try_from(self.0).expect("an index that fits a pointer")
            }
        }
    )+};
}

pub use crate::__index as index;

/// Dense indices used by the compiler's entity pools. Conversion must round
/// trip and reject unrepresentable positions rather than truncate them.
pub trait Id: Copy {
    fn at(index: usize) -> Self;
    fn index(self) -> usize;
}

/// Append-only slots addressed by one kind of ID.
///
/// Replacing an entry preserves its slot; middle insertion, removal and reordering are deliberately absent.
/// IDs distinguish entity kinds, not programs or generations: rebuilding a
/// pool still requires remapping references into it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Pool<I, T> {
    entries: Vec<T>,
    id: std::marker::PhantomData<fn() -> I>,
}

impl<I, T> Default for Pool<I, T> {
    fn default() -> Self {
        Self {
            entries: Vec::new(),
            id: std::marker::PhantomData,
        }
    }
}

/// Each entry at the slot its position says, in order.
impl<I: Id, T> FromIterator<T> for Pool<I, T> {
    fn from_iter<V: IntoIterator<Item = T>>(values: V) -> Self {
        let mut pool = Self::default();
        for value in values {
            pool.push(value);
        }
        pool
    }
}

impl<I: Id, T> Pool<I, T> {
    /// Check representability before changing storage, then return the slot
    /// actually inserted. This does not make surrounding construction atomic.
    pub fn push(&mut self, value: T) -> I {
        let id = I::at(self.entries.len());
        self.entries.push(value);
        id
    }

    #[must_use]
    pub const fn len(&self) -> usize {
        self.entries.len()
    }

    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    #[must_use]
    pub fn get(&self, id: I) -> Option<&T> {
        self.entries.get(id.index())
    }

    #[must_use]
    pub fn as_slice(&self) -> &[T] {
        &self.entries
    }

    pub fn iter(&self) -> std::slice::Iter<'_, T> {
        self.entries.iter()
    }

    pub fn iter_mut(&mut self) -> std::slice::IterMut<'_, T> {
        self.entries.iter_mut()
    }

    /// The ID of the first entry matching a predicate.
    pub fn position(&self, predicate: impl FnMut(&T) -> bool) -> Option<I> {
        self.entries.iter().position(predicate).map(I::at)
    }

    #[must_use]
    pub fn iter_enumerated(&self) -> impl DoubleEndedIterator<Item = (I, &T)> + ExactSizeIterator {
        self.entries
            .iter()
            .enumerate()
            .map(|(at, value)| (I::at(at), value))
    }

    /// A snapshot of existing IDs. Owns only a length, so the caller can
    /// replace entries while walking it; later appends are not visited.
    pub fn ids(&self) -> impl DoubleEndedIterator<Item = I> + ExactSizeIterator + use<I, T> {
        (0..self.entries.len()).map(I::at)
    }
}

impl<I: Id, T> std::ops::Index<I> for Pool<I, T> {
    type Output = T;
    fn index(&self, id: I) -> &T {
        &self.entries[id.index()]
    }
}

impl<I: Id, T> std::ops::IndexMut<I> for Pool<I, T> {
    fn index_mut(&mut self, id: I) -> &mut T {
        &mut self.entries[id.index()]
    }
}

impl<I, T> IntoIterator for Pool<I, T> {
    type Item = T;
    type IntoIter = std::vec::IntoIter<T>;
    fn into_iter(self) -> Self::IntoIter {
        self.entries.into_iter()
    }
}

impl<'a, I, T> IntoIterator for &'a Pool<I, T> {
    type Item = &'a T;
    type IntoIter = std::slice::Iter<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        self.entries.iter()
    }
}

impl<'a, I, T> IntoIterator for &'a mut Pool<I, T> {
    type Item = &'a mut T;
    type IntoIter = std::slice::IterMut<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        self.entries.iter_mut()
    }
}

/// A dense set of one kind of ID, one bit each.
///
/// The set holds IDs below a bound fixed at construction, and never grows.
pub struct BitSet<I> {
    words: Vec<u64>,
    id: std::marker::PhantomData<fn() -> I>,
}

impl<I> Clone for BitSet<I> {
    fn clone(&self) -> Self {
        Self {
            words: self.words.clone(),
            id: std::marker::PhantomData,
        }
    }

    fn clone_from(&mut self, source: &Self) {
        self.words.clone_from(&source.words);
    }
}

impl<I> PartialEq for BitSet<I> {
    fn eq(&self, other: &Self) -> bool {
        self.words == other.words
    }
}

impl<I> Eq for BitSet<I> {}

impl<I: Id + std::fmt::Debug> std::fmt::Debug for BitSet<I> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}

impl<I: Id> BitSet<I> {
    /// The empty set of IDs below `bound`.
    #[must_use]
    pub fn new(bound: usize) -> Self {
        Self {
            words: vec![0; bound.div_ceil(64)],
            id: std::marker::PhantomData,
        }
    }

    /// Add `id`.
    ///
    /// # Panics
    ///
    /// If `id` is at or past the bound the set was built for.
    pub fn insert(&mut self, id: I) {
        let (word, bit) = Self::locate(id);
        self.words[word] |= bit;
    }

    /// Remove `id`.
    ///
    /// # Panics
    ///
    /// If `id` is at or past the bound the set was built for.
    pub fn remove(&mut self, id: I) {
        let (word, bit) = Self::locate(id);
        self.words[word] &= !bit;
    }

    /// Whether `id` is a member.
    ///
    /// # Panics
    ///
    /// If `id` is at or past the bound the set was built for.
    #[must_use]
    pub fn contains(&self, id: I) -> bool {
        let (word, bit) = Self::locate(id);
        self.words[word] & bit != 0
    }

    /// Add every member of a set over the same bound.
    ///
    /// # Panics
    ///
    /// If `other` was built for a different bound.
    pub fn union_with(&mut self, other: &Self) {
        assert_eq!(self.words.len(), other.words.len(), "sets over one bound");
        for (held, &added) in self.words.iter_mut().zip(&other.words) {
            *held |= added;
        }
    }

    /// Remove every member of a set over the same bound.
    ///
    /// # Panics
    ///
    /// If `other` was built for a different bound.
    pub fn subtract(&mut self, other: &Self) {
        assert_eq!(self.words.len(), other.words.len(), "sets over one bound");
        for (held, &removed) in self.words.iter_mut().zip(&other.words) {
            *held &= !removed;
        }
    }

    /// Members in ascending order.
    ///
    /// # Panics
    ///
    /// Never for a set whose bound its IDs can represent.
    pub fn iter(&self) -> impl Iterator<Item = I> + '_ {
        self.words.iter().enumerate().flat_map(|(at, &word)| {
            let mut rest = word;
            std::iter::from_fn(move || {
                (rest != 0).then(|| {
                    let bit = rest.trailing_zeros();
                    rest &= rest - 1;
                    I::at(at * 64 + usize::try_from(bit).expect("a bit within a word"))
                })
            })
        })
    }

    fn locate(id: I) -> (usize, u64) {
        let index = id.index();
        (index / 64, 1 << (index % 64))
    }
}

/// Append a slice and return its run, checking the encoded start and length
/// before extending storage. Empty runs retain the current end position.
/// This neither caps the total pool at `u32::MAX` nor makes a panicking `Clone`
/// or surrounding multi-pool construction transactional.
pub(crate) fn append_range<T: Clone>(pool: &mut Vec<T>, values: &[T]) -> Range {
    let range = Range::of(pool.len(), values.len());
    pool.extend_from_slice(values);
    range
}

/// A run in one of those arrays: the arguments a call holds, a region's
/// parameters, the characters of a name.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Range {
    start: u32,
    len: u32,
}

impl Range {
    /// A run of nothing, for a place that holds none yet.
    pub const EMPTY: Self = Self { start: 0, len: 0 };

    /// # Panics
    ///
    /// If the program outgrew the four billion entries a pool may hold.
    #[must_use]
    pub fn of(start: usize, len: usize) -> Self {
        Self {
            start: u32::try_from(start).expect("a pool within 4G"),
            len: u32::try_from(len).expect("a run within 4G"),
        }
    }

    /// # Panics
    ///
    /// Never, on any machine whose pointers reach 32 bits.
    #[must_use]
    pub fn len(self) -> usize {
        usize::try_from(self.len).expect("a length that fits a pointer")
    }

    #[must_use]
    pub const fn is_empty(self) -> bool {
        self.len == 0
    }

    /// Where it starts, for reading one thing out of a run rather than the
    /// whole of it.
    #[must_use]
    pub const fn start(self) -> u32 {
        self.start
    }

    /// # Panics
    ///
    /// Never, on any machine whose pointers reach 32 bits.
    #[must_use]
    pub fn range(self) -> std::ops::Range<usize> {
        let start = usize::try_from(self.start).expect("an index that fits a pointer");
        start..start + self.len()
    }
}

#[cfg(test)]
mod tests {
    use super::{BitSet, index};

    index!(Probe);

    #[test]
    fn a_bit_set_lists_members_in_order_across_word_boundaries() {
        let mut set = BitSet::new(130);
        for at in [129, 0, 64, 63, 1] {
            set.insert(Probe::at(at));
        }
        set.remove(Probe::at(1));
        assert!(set.contains(Probe::at(63)) && !set.contains(Probe::at(1)));
        let members: Vec<_> = set.iter().map(Probe::index).collect();
        assert_eq!(members, [0, 63, 64, 129]);

        let mut other = BitSet::new(130);
        other.insert(Probe::at(64));
        other.insert(Probe::at(100));
        set.subtract(&other);
        set.union_with(&BitSet::new(130));
        let members: Vec<_> = set.iter().map(Probe::index).collect();
        assert_eq!(members, [0, 63, 129]);
    }
}
