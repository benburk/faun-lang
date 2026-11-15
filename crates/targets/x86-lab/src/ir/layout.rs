//! Layout obligations introduced when symbolic values become serialized data.
//! Every target is little-endian, so a layout is only a word width.

/// A program containing target-sized data may only run at this word width.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Layout {
    pub word_bits: u16,
}
