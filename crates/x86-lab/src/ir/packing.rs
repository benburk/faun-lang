//! Where each leaf of a shape lies in memory, as a target of one word width
//! stores it.
//!
//! A leaf takes as many bytes as its class needs, rounded up to one, two,
//! four or eight, and never more than a word: a number of eight bits is a
//! byte, a pattern of sixty-four is eight, and a cell, a buffer, a natural
//! or an address is a word. A number that can only be nought takes nothing,
//! and reads back as nought. Each leaf lies at the next offset its own width
//! divides, in the order the shape names them, and the whole is as long as
//! a multiple of its widest leaf: the layout Rust gives a struct it may not
//! reorder, so an element of a sequence is its size apart from the next.
//!
//! A leaf holding a claim -- a cell, a buffer or a natural -- is what the
//! runtime gives up when the object holding it goes, and takes again when
//! it is copied. Where a shape has any, a descriptor in the data says where
//! they lie: a word counting them, then each one's offset and kind, a word
//! each. An object points at its shape's descriptor, or holds nought where
//! nothing in it holds a claim, so the runtime needs no per-shape code to
//! walk what any object holds.

use super::cell;
use super::{Class, Width};

/// One leaf of a shape, where it lies.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct Leaf {
    /// Bytes from the start of the object or element.
    pub offset: u64,
    /// How it is loaded and stored, or nothing where it takes no bytes.
    pub width: Option<Width>,
    /// What it is to the runtime: a scalar, or which kind of claim.
    pub kind: u64,
}

/// A shape laid out.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Packed {
    pub leaves: Vec<Leaf>,
    /// Bytes from one element to the next: a multiple of `align`.
    pub size: u64,
    pub align: u64,
}

impl Packed {
    /// `classes` laid out on a target whose word is `word_bits` wide.
    pub(super) fn of(classes: &[Class], word_bits: u16) -> Self {
        let mut offset: u64 = 0;
        let mut align: u64 = 1;
        let leaves = classes
            .iter()
            .map(|&class| {
                let bytes = bytes_of(class, word_bits);
                if bytes == 0 {
                    return Leaf {
                        offset: 0,
                        width: None,
                        kind: cell::SCALAR,
                    };
                }
                offset = offset.next_multiple_of(bytes);
                align = align.max(bytes);
                let leaf = Leaf {
                    offset,
                    width: Some(width(bytes, word_bits)),
                    kind: cell::kind(class),
                };
                offset += bytes;
                leaf
            })
            .collect();
        Self {
            leaves,
            size: offset.next_multiple_of(align),
            align,
        }
    }

    /// Each leaf holding a claim: its offset and kind.
    pub(super) fn managed(&self) -> impl Iterator<Item = (u64, u64)> + '_ {
        self.leaves
            .iter()
            .filter(|leaf| leaf.kind != cell::SCALAR)
            .map(|leaf| (leaf.offset, leaf.kind))
    }

    /// The descriptor saying where its claims lie, as a target's words in
    /// little-endian order, or nothing where it holds none.
    pub(super) fn descriptor(&self, word_bits: u16) -> Option<Vec<u8>> {
        let managed: Vec<_> = self.managed().collect();
        if managed.is_empty() {
            return None;
        }
        let word = usize::from(word_bits / 8);
        let mut bytes = Vec::with_capacity((1 + 2 * managed.len()) * word);
        let mut push = |value: u64| bytes.extend_from_slice(&value.to_le_bytes()[..word]);
        push(u64::try_from(managed.len()).expect("a count fits 64 bits"));
        for (offset, kind) in managed {
            push(offset);
            push(kind);
        }
        Some(bytes)
    }
}

/// How many bytes a leaf of `class` takes on a target whose word is
/// `word_bits` wide.
fn bytes_of(class: Class, word_bits: u16) -> u64 {
    let word = u64::from(word_bits / 8);
    match class {
        Class::Cell | Class::Buffer | Class::Natural | Class::Word | Class::Address => word,
        Class::Held(_) => match class.width() {
            Some(0) => 0,
            Some(bits) => u64::from(bits.div_ceil(8)).next_power_of_two().min(word),
            None => word,
        },
    }
}

/// The width a leaf of `bytes` is moved at.
const fn width(bytes: u64, word_bits: u16) -> Width {
    match bytes {
        1 => Width::Byte,
        2 if word_bits > 16 => Width::Bits16,
        4 if word_bits > 32 => Width::Bits32,
        _ => Width::Word,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A byte, a word and a byte, as Rust lays out a `repr(C)` struct: the
    /// word waits for the next multiple of eight, and the whole rounds up.
    #[test]
    fn each_leaf_lies_where_its_width_divides() {
        let packed = Packed::of(&[Class::fixed(8), Class::Word, Class::fixed(1)], 64);
        let offsets: Vec<_> = packed.leaves.iter().map(|leaf| leaf.offset).collect();
        assert_eq!(offsets, [0, 8, 16]);
        assert_eq!((packed.size, packed.align), (24, 8));
    }

    /// Bytes are bytes: a list of them is a run of them.
    #[test]
    fn a_byte_is_one_apart_from_the_next() {
        let packed = Packed::of(&[Class::fixed(8)], 64);
        assert_eq!((packed.size, packed.align), (1, 1));
        assert_eq!(packed.leaves[0].width, Some(Width::Byte));
    }

    /// Nothing wider than a word: sixty-four bits on a sixteen-bit machine
    /// is a word, and a pattern of sixty-four is eight bytes where the word
    /// holds it.
    #[test]
    fn no_leaf_is_wider_than_a_word() {
        let wide = Packed::of(&[Class::fixed(20)], 16);
        assert_eq!((wide.size, wide.leaves[0].width), (2, Some(Width::Word)));
        let float = Packed::of(&[Class::fixed(64), Class::fixed(16)], 64);
        assert_eq!(float.size, 16);
        assert_eq!(float.leaves[1].width, Some(Width::Bits16));
    }

    /// A number that can only be nought takes no room.
    #[test]
    fn nought_takes_nothing() {
        let packed = Packed::of(&[Class::fixed(0), Class::fixed(8)], 64);
        assert_eq!(packed.leaves[0].width, None);
        assert_eq!(packed.size, 1);
    }

    /// Only a shape holding a claim has a descriptor, which counts them and
    /// says where each is.
    #[test]
    fn a_descriptor_says_where_the_claims_are() {
        assert_eq!(Packed::of(&[Class::fixed(8)], 16).descriptor(16), None);
        let packed = Packed::of(&[Class::fixed(8), Class::Cell], 16);
        assert_eq!(packed.descriptor(16), Some(vec![1, 0, 2, 0, 2, 0]));
    }
}
