//! How every tier keeps a program: dense indices into flat arrays, and
//! runs within them.
//!
//! A tier holds its program as one array per kind of thing, and points into
//! them with a four-byte index rather than a pointer. Nothing is boxed,
//! nothing is reference counted, a program is a handful of `Vec`s, and
//! copying an index copies four bytes.
//!
//! Individually addressed entities use a typed, append-only `Pool`: insertion
//! returns the entity's ID and indexing requires that kind of ID. Variable-length
//! runs still use ordinary vectors and `Range`; temporary vectors and coupled
//! instruction/result arrays retain their own construction rules.

macro_rules! index {

    ($($name:ident),* $(,)?) => {$(
        #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
        pub struct $name(pub u32);

        impl crate::index::Id for $name {
            fn at(index: usize) -> Self { Self::at(index) }
            fn index(self) -> usize { self.index() }
        }

        impl $name {
            /// # Panics
            ///
            /// If the program outgrew the four billion of these it may have.
            #[must_use]
            pub fn at(index: usize) -> Self {
                Self(u32::try_from(index).expect("a program within 4G of these"))
            }

            #[must_use]
            pub fn index(self) -> usize {
                usize::try_from(self.0).expect("an index that fits a pointer")
            }
        }
    )*};
}

pub(crate) use index;

#[cfg(test)]
mod tests;

/// Dense indices used by the compiler's entity pools. Conversion must round
/// trip and reject unrepresentable positions rather than truncate them.
pub(crate) trait Id: Copy {
    fn at(index: usize) -> Self;
    fn index(self) -> usize;
}

/// Append-only slots addressed by one kind of ID. Replacing an entry preserves
/// its slot; middle insertion, removal and reordering are deliberately absent.
/// IDs distinguish entity kinds, not programs or generations: rebuilding a
/// pool still requires remapping references into it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Pool<I, T> {
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

impl<I: Id, T> Pool<I, T> {
    /// Check representability before changing storage, then return the slot
    /// actually inserted. This does not make surrounding construction atomic.
    pub(crate) fn push(&mut self, value: T) -> I {
        let id = I::at(self.entries.len());
        self.entries.push(value);
        id
    }

    pub(crate) const fn len(&self) -> usize {
        self.entries.len()
    }

    pub(crate) fn get(&self, id: I) -> Option<&T> {
        self.entries.get(id.index())
    }

    pub(crate) fn as_slice(&self) -> &[T] {
        &self.entries
    }

    pub(crate) fn iter(&self) -> std::slice::Iter<'_, T> {
        self.entries.iter()
    }

    /// The ID of the first entry matching a predicate.
    pub(crate) fn position(&self, predicate: impl FnMut(&T) -> bool) -> Option<I> {
        self.entries.iter().position(predicate).map(I::at)
    }

    pub(crate) fn iter_enumerated(
        &self,
    ) -> impl DoubleEndedIterator<Item = (I, &T)> + ExactSizeIterator {
        self.entries
            .iter()
            .enumerate()
            .map(|(at, value)| (I::at(at), value))
    }

    /// A snapshot of existing IDs. Owns only a length, so the caller can
    /// replace entries while walking it; later appends are not visited.
    pub(crate) fn ids(&self) -> impl DoubleEndedIterator<Item = I> + ExactSizeIterator + use<I, T> {
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
