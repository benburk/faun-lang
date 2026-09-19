//! How every tier keeps a program: dense indices into flat arrays, and
//! runs within them.
//!
//! A tier holds its program as one array per kind of thing, and points into
//! them with a four-byte index rather than a pointer. Nothing is boxed,
//! nothing is reference counted, a program is a handful of `Vec`s, and
//! copying an index copies four bytes.
//!
//! Every tier keeps this shape, and the tier below the machine will too
//! when it grows something to keep.

macro_rules! index {

    ($($name:ident),* $(,)?) => {$(
        #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
        pub struct $name(pub u32);

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
