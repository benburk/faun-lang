//! Where each leaf of a shape lies in memory, as a target of one word width
//! stores it.
//!
//! A leaf takes as many bytes as its class needs, rounded up to one, two,
//! four or eight, and never more than a word: a number of eight bits is a
//! byte, a pattern of sixty-four is eight, and a cell, a buffer, a natural
//! or an address is a word. A number that can only be nought takes nothing,
//! and reads back as nought. The leaves lie widest first, as Rust lays out a
//! struct it may reorder, and leaves of one width in the order the shape
//! names them: a record's fields by their names, as the frontend orders
//! them, and a constructor's by their places. Every width is a power of two
//! no wider than a word and lies where it divides, so nothing waits for an
//! offset and there is no padding between leaves; the whole is as long as a
//! multiple of its widest leaf, so an element of a sequence is its size apart
//! from the next. `Packed::of` is the one way a shape is laid out: a cell's
//! fields, a sequence's elements and a table laid out in the image all are,
//! so what writes a shape and what reads it agree.
//!
//! What is laid out from outside is not a shape and is not laid out here:
//! the header of a cell, a buffer or a natural, a descriptor below, the
//! array of arguments the system hands the entry, and what a target hands
//! its host, such as WASI's `iovec`. Each is a run of words, or bytes, in an
//! order the runtime or the system fixes, read and written where it lies by
//! the routines that know it.
//!
//! A leaf holding a claim -- a cell, a buffer or a natural -- is what the
//! runtime gives up when the object holding it goes, and takes again when
//! it is copied. Where a shape has any, a descriptor in the data says where
//! they lie, read from the layout itself: a word counting them, then each
//! one's offset and kind, a word each. An object points at its shape's
//! descriptor, or holds nought where nothing in it holds a claim, so the
//! runtime needs no per-shape code to walk what any object holds.

use super::{Binary, Builder, Class, Direction, ValueId, Width};

pub(super) const SCALAR: u64 = 0;
pub(super) const NATURAL: u64 = 1;
pub(super) const CELL: u64 = 2;
pub(super) const BUFFER: u64 = 3;

/// The kind a value of `class` is stored as, in a cell field or a buffer.
pub(super) const fn kind(class: Class) -> u64 {
    match class {
        Class::Natural => NATURAL,
        Class::Cell => CELL,
        Class::Buffer => BUFFER,
        _ => SCALAR,
    }
}

/// One leaf of a shape, where it lies and how it is read back.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct Leaf {
    /// Bytes from the start of the object or element to what is read.
    pub offset: u64,
    /// How much is read, or nothing where it takes no bytes.
    pub width: Option<Width>,
    /// What it is to the runtime: a scalar, or which kind of claim.
    pub kind: u64,
    /// How far up what is read it lies, where it shares its bytes.
    pub shift: u16,
    /// How many bits it keeps, where another leaf lies above it in what is
    /// read, which are all a read keeps.
    pub mask: Option<u16>,
}

impl Leaf {
    /// A leaf that takes no bytes, which reads back as nought.
    const NOTHING: Self = Self {
        offset: 0,
        width: None,
        kind: SCALAR,
        shift: 0,
        mask: None,
    };

    /// The leaf, from `loaded`, what reading it answered: moved down, and
    /// kept to its own bits where another lies above it.
    pub(super) fn unpacked(self, b: &mut Builder, loaded: ValueId) -> ValueId {
        let moved = if self.shift == 0 {
            loaded
        } else {
            b.shift(Class::Word, Direction::Down, loaded, self.shift)
        };
        self.mask.map_or(moved, |bits| {
            let mask = b.constant(Class::Word, (1u64 << bits) - 1);
            b.binary(Binary::And, moved, mask)
        })
    }
}

/// Bytes a store writes at once: one leaf, or several small numbers
/// sharing them, each moved up where it lies among them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Unit {
    /// Bytes from the start of the object or element.
    pub offset: u64,
    pub width: Width,
    /// Each leaf it holds, by its index in the shape, and how far up it
    /// lies.
    pub leaves: Vec<(usize, u16)>,
}

impl Unit {
    /// What it writes, from `values`, one per leaf of the shape: its one
    /// leaf, or each of its leaves moved up where it lies, joined.
    pub(super) fn value(&self, b: &mut Builder, values: &[ValueId]) -> ValueId {
        if let [(index, _)] = self.leaves[..] {
            return values[index];
        }
        let mut whole = None;
        for &(index, shift) in &self.leaves {
            let mut value = values[index];
            if b.class(value) != Class::Word {
                value = b.convert(Class::Word, value);
            }
            if shift != 0 {
                value = b.shift(Class::Word, Direction::Up, value, shift);
            }
            whole = Some(whole.map_or(value, |whole| b.binary(Binary::Or, whole, value)));
        }
        whole.expect("a unit holds a leaf")
    }
}

/// A shape laid out.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Packed {
    pub leaves: Vec<Leaf>,
    /// What a store writes, leaves sharing bytes together; a leaf that
    /// takes no bytes is in none.
    pub units: Vec<Unit>,
    /// Bytes from one element to the next: a multiple of `align`.
    pub size: u64,
    pub align: u64,
}

impl Packed {
    /// `classes` laid out on a target whose word is `word_bits` wide: each
    /// leaf in its own bytes, or, where that is shorter, the small numbers
    /// packed by their bits.
    pub(super) fn of(classes: &[Class], word_bits: u16) -> Self {
        let plain = Self::plain(classes, word_bits);
        let packed = Self::by_bits(classes, word_bits);
        if packed.size < plain.size {
            packed
        } else {
            plain
        }
    }

    /// Each leaf in bytes of its own, widest first, and in the order the
    /// shape names them where they are as wide.
    pub(super) fn plain(classes: &[Class], word_bits: u16) -> Self {
        let mut items: Vec<_> = classes
            .iter()
            .enumerate()
            .map(|(index, &class)| (bytes_of(class, word_bits), vec![(index, 0)]))
            .filter(|&(bytes, _)| bytes > 0)
            .collect();
        widest_first(&mut items);
        Self::laid(classes, items, word_bits)
    }

    /// The numbers narrower than a word packed by their bits, widest first,
    /// each into the first group of a word's bits with room for it; each
    /// group, and each other leaf, in bytes of its own, widest first, so
    /// nothing waits for an offset its width divides.
    fn by_bits(classes: &[Class], word_bits: u16) -> Self {
        let groups = groups(classes, word_bits);
        let mut grouped = vec![false; classes.len()];
        for (_, members) in &groups {
            for &(index, _) in members {
                grouped[index] = true;
            }
        }
        let word = u64::from(word_bits / 8);
        let mut items: Vec<(u64, Vec<(usize, u16)>)> = groups
            .into_iter()
            .map(|(used, members)| {
                let bytes = u64::from(used.div_ceil(8)).next_power_of_two().min(word);
                (bytes, members)
            })
            .collect();
        items.extend(
            classes
                .iter()
                .enumerate()
                .filter(|&(index, _)| !grouped[index])
                .map(|(index, &class)| (bytes_of(class, word_bits), vec![(index, 0)]))
                .filter(|&(bytes, _)| bytes > 0),
        );
        widest_first(&mut items);
        Self::laid(classes, items, word_bits)
    }

    /// `items` laid out one after another, in order, each at the next
    /// offset its bytes divide: each item's bytes, and the leaves sharing
    /// them with where each lies among them. Laid widest first, each is
    /// where the last ended.
    fn laid(classes: &[Class], items: Vec<(u64, Vec<(usize, u16)>)>, word_bits: u16) -> Self {
        let mut leaves = vec![Leaf::NOTHING; classes.len()];
        let mut units = Vec::with_capacity(items.len());
        let mut offset: u64 = 0;
        let mut align: u64 = 1;
        for (bytes, members) in items {
            offset = offset.next_multiple_of(bytes);
            align = align.max(bytes);
            for &(index, shift) in &members {
                leaves[index] = read(
                    (offset, bytes, word_bits),
                    &members,
                    (index, shift),
                    classes,
                );
            }
            units.push(Unit {
                offset,
                width: width(bytes, word_bits),
                leaves: members,
            });
            offset += bytes;
        }
        Self {
            leaves,
            units,
            size: offset.next_multiple_of(align),
            align,
        }
    }
    /// Each leaf holding a claim: its offset and kind.
    pub(super) fn managed(&self) -> impl Iterator<Item = (u64, u64)> + '_ {
        self.leaves
            .iter()
            .filter(|leaf| leaf.kind != SCALAR)
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

    /// Each element of `values`, one value per leaf, laid out as the bytes
    /// of one element, the value of a natural held in place already doubled.
    pub(super) fn lay(&self, values: &[u64], word_bits: u16) -> Vec<u8> {
        let mut laid = vec![0; usize::try_from(self.size).expect("a size fits the host")];
        for unit in &self.units {
            let mut whole: u64 = 0;
            for &(index, shift) in &unit.leaves {
                let value = values.get(index).copied().unwrap_or(0);
                whole |= value << shift;
            }
            let offset = usize::try_from(unit.offset).expect("an offset fits the host");
            let bytes = usize::from(unit.width.bytes(word_bits));
            laid[offset..offset + bytes].copy_from_slice(&whole.to_le_bytes()[..bytes]);
        }
        laid
    }
}

/// `items`, each some bytes and the leaves sharing them, widest first, and
/// where two are as wide, the one holding the leaf the shape names first.
fn widest_first(items: &mut [(u64, Vec<(usize, u16)>)]) {
    items.sort_by_key(|(bytes, members)| (std::cmp::Reverse(*bytes), members[0].0));
}

/// The numbers narrower than a word, widest first, each in the first group
/// of a word's bits with room for it: each group's bits used, and its
/// leaves with how far up each lies.
fn groups(classes: &[Class], word_bits: u16) -> Vec<(u16, Vec<(usize, u16)>)> {
    let mut small: Vec<(usize, u16)> = classes
        .iter()
        .enumerate()
        .filter_map(|(index, &class)| match class {
            Class::Held(_) => class
                .width()
                .filter(|&bits| bits > 0 && bits < word_bits)
                .map(|bits| (index, bits)),
            _ => None,
        })
        .collect();
    small.sort_by_key(|&(index, bits)| (std::cmp::Reverse(bits), index));
    let mut groups: Vec<(u16, Vec<(usize, u16)>)> = Vec::new();
    for (index, bits) in small {
        match groups.iter_mut().find(|group| group.0 + bits <= word_bits) {
            Some(group) => {
                group.1.push((index, group.0));
                group.0 += bits;
            }
            None => groups.push((bits, vec![(index, 0)])),
        }
    }
    groups
}

/// How leaf `index`, `shift` bits up the group `members` lying in `bytes`
/// at `offset`, is read: by itself where it begins a run of bytes no other
/// leaf shares, and otherwise the group's bytes moved down and masked,
/// unmasked where nothing lies above it.
fn read(
    (offset, bytes, word_bits): (u64, u64, u16),
    members: &[(usize, u16)],
    (index, shift): (usize, u16),
    classes: &[Class],
) -> Leaf {
    let bits_of = |at: usize| classes[at].width().unwrap_or(word_bits);
    let bits = bits_of(index);
    let total = u16::try_from(bytes * 8).expect("a word's bits fit 16 bits");
    if members.len() == 1 {
        return Leaf {
            offset,
            width: Some(width(bytes, word_bits)),
            kind: kind(classes[index]),
            shift: 0,
            mask: None,
        };
    }
    let others = || members.iter().filter(move |&&(other, _)| other != index);
    if shift % 8 == 0 {
        let alone = u16::try_from(u64::from(bits.div_ceil(8)).next_power_of_two() * 8)
            .expect("a leaf's bits fit 16 bits");
        let fits = (shift / 8) % (alone / 8) == 0 && shift + alone <= total;
        let shared = others().any(|&(other, at)| at < shift + alone && shift < at + bits_of(other));
        if fits && !shared {
            return Leaf {
                offset: offset + u64::from(shift / 8),
                width: Some(width(u64::from(alone / 8), word_bits)),
                kind: SCALAR,
                shift: 0,
                mask: None,
            };
        }
    }
    let above = others().any(|&(_, at)| at > shift);
    Leaf {
        offset,
        width: Some(width(bytes, word_bits)),
        kind: SCALAR,
        shift,
        mask: above.then_some(bits),
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

    /// A byte, a word and a bit, each in bytes of its own, as Rust lays
    /// out a struct it may reorder: the word first, then the two bytes
    /// after it, so nothing waits for an offset and the whole is sixteen
    /// bytes, where in the order named it would be twenty-four.
    #[test]
    fn the_widest_leaf_lies_first() {
        let packed = Packed::plain(&[Class::fixed(8), Class::Word, Class::fixed(1)], 64);
        let offsets: Vec<_> = packed.leaves.iter().map(|leaf| leaf.offset).collect();
        assert_eq!(offsets, [8, 0, 9]);
        assert_eq!((packed.size, packed.align), (16, 8));
    }

    /// Leaves of one width lie in the order the shape names them, so the
    /// layout is the shape's alone.
    #[test]
    fn leaves_as_wide_lie_in_the_order_named() {
        let packed = Packed::plain(
            &[
                Class::fixed(8),
                Class::fixed(16),
                Class::fixed(8),
                Class::fixed(16),
            ],
            64,
        );
        let offsets: Vec<_> = packed.leaves.iter().map(|leaf| leaf.offset).collect();
        assert_eq!(offsets, [4, 0, 5, 2]);
        assert_eq!(packed.size, 6);
    }

    /// Whatever the shape, its leaves lie end to end with no bytes between
    /// them, and only the end is rounded up, to its widest leaf.
    #[test]
    fn no_shape_is_padded_between_its_leaves() {
        let classes = [
            Class::fixed(0),
            Class::fixed(1),
            Class::fixed(8),
            Class::fixed(12),
            Class::fixed(32),
            Class::Word,
            Class::Cell,
            Class::Natural,
        ];
        for word_bits in [16, 32, 64] {
            for a in classes {
                for b in classes {
                    for c in classes {
                        let shape = [a, b, c, Class::fixed(8)];
                        let packed = Packed::plain(&shape, word_bits);
                        let mut ends: Vec<_> = packed
                            .units
                            .iter()
                            .map(|unit| (unit.offset, u64::from(unit.width.bytes(word_bits))))
                            .collect();
                        ends.sort_unstable();
                        let mut at = 0;
                        for (offset, bytes) in ends {
                            assert_eq!(offset, at, "{shape:?} on {word_bits} bits");
                            at += bytes;
                        }
                        assert_eq!(packed.size, at.next_multiple_of(packed.align));
                    }
                }
            }
        }
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
        // The cell, a word, lies before the byte, and the descriptor says so.
        let packed = Packed::of(&[Class::fixed(8), Class::Cell], 16);
        assert_eq!(packed.descriptor(16), Some(vec![1, 0, 0, 0, 2, 0]));
        let packed = Packed::of(&[Class::Cell, Class::fixed(16), Class::Buffer], 64);
        let mut expected = Vec::new();
        for word in [2u64, 0, CELL, 8, BUFFER] {
            expected.extend_from_slice(&word.to_le_bytes());
        }
        assert_eq!(packed.descriptor(64), Some(expected));
    }

    /// Two numbers of four bits each take a byte of their own laid out
    /// whole, and share one packed by their bits. Where packing saves
    /// nothing, as for a byte, a word and a bit, which lie in sixteen bytes
    /// either way, the leaves keep bytes of their own.
    #[test]
    fn small_numbers_share_bytes_where_that_is_shorter() {
        let nibbles = [Class::fixed(4), Class::fixed(4)];
        assert_eq!(Packed::plain(&nibbles, 64).size, 2);
        let packed = Packed::of(&nibbles, 64);
        assert_eq!((packed.size, packed.units.len()), (1, 1));
        let reads: Vec<_> = packed
            .leaves
            .iter()
            .map(|leaf| (leaf.offset, leaf.shift, leaf.mask))
            .collect();
        assert_eq!(reads, [(0, 0, Some(4)), (0, 4, None)]);
        let mixed = [Class::fixed(8), Class::Word, Class::fixed(1)];
        assert_eq!(Packed::of(&mixed, 64), Packed::plain(&mixed, 64));
    }

    /// A tag, a length below 259 and a distance up to 32768, as a block's
    /// symbols hold them: six bytes each apart, four packed. The distance
    /// is read by itself, the length moved down and kept to its nine bits,
    /// and the tag, which lies above both, moved down.
    #[test]
    fn a_small_tag_and_its_fields_share_a_word() {
        let symbol = [
            Class::fixed(1),
            Class::Held(faun_base::facts::Facts {
                low: 0,
                high: Some(258),
            }),
            Class::Held(faun_base::facts::Facts {
                low: 1,
                high: Some(32768),
            }),
        ];
        assert_eq!(Packed::plain(&symbol, 64).size, 6);
        let packed = Packed::of(&symbol, 64);
        assert_eq!(packed.size, 4);
        assert_eq!(packed.units.len(), 1);
        let reads: Vec<_> = packed
            .leaves
            .iter()
            .map(|leaf| (leaf.offset, leaf.width, leaf.shift, leaf.mask))
            .collect();
        assert_eq!(
            reads,
            [
                (0, Some(Width::Bits32), 25, None),
                (0, Some(Width::Bits32), 16, Some(9)),
                (0, Some(Width::Bits16), 0, None),
            ]
        );
        assert_eq!(
            packed.lay(&[1, 258, 32768], 64),
            (32768u32 | 258 << 16 | 1 << 25).to_le_bytes()
        );
        // On a machine of sixteen bits nothing is wider than its word: the
        // tag and the length share one, and the distance has its own.
        let narrow = Packed::of(&symbol, 16);
        assert_eq!((narrow.size, narrow.units.len()), (4, 2));
    }

    /// Nothing that holds a claim shares its bytes, and nothing is packed
    /// where packing saves nothing.
    #[test]
    fn claims_and_shapes_packing_saves_nothing_stay_as_they_were() {
        let classes = [Class::fixed(8), Class::fixed(8)];
        assert_eq!(Packed::of(&classes, 64), Packed::plain(&classes, 64));
        let claims = [Class::fixed(1), Class::Natural, Class::Natural];
        assert_eq!(Packed::of(&claims, 64), Packed::plain(&claims, 64));
    }
}
