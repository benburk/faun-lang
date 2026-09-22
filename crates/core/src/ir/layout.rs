//! Layout obligations introduced when symbolic values become serialized data.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Endian {
    Little,
    Big,
}

/// A program containing target-sized data may only run at this layout.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Layout {
    pub word_bits: u16,
    pub endian: Endian,
}
