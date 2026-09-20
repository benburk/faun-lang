//! How a known value is encoded.
//!
//! The pool is one byte buffer and a value is a range into it. Everything is
//! self-delimiting, so no length is stored anywhere except where a value's
//! own shape needs one:
//!
//! - **spine-shaped** — a count, then that many element encodings
//! - **one constructor** — its fields, with no tag to choose between them
//! - **otherwise** — a tag, then its fields
//!
//! A type is spine-shaped when it has two constructors, one taking nothing
//! and one taking exactly one field of the type itself. That is `Nat` and it
//! is `List`, which is the point: `Nat` is the member whose elements carry
//! nothing, so all that survives is the count, and a chain of `Succ` costs
//! the logarithm of its value rather than its value.
//!
//! The encoding is structural — which constructor, which fields. It is not a
//! layout. A target is free to hold the same value as a word, as a view into
//! static memory, or as a counted cell, and [`crate::ir`] is where that is
//! decided.

use num_bigint::BigUint;

use super::{CtorId, Program, Range, TypeId};

mod checked;
mod view;
pub use checked::{ConstructionError, DecodeError};
pub(super) use checked::{fields as check_fields, read as read_checked, tree as check_tree};
pub(super) use view::natural_size;
pub use view::{
    ByteView, Constant, ConstantView, ConstructorView, NaturalView, SpineView, TooWide,
};

/// A typed entry: expressions cannot attach a different type to its bytes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct Entry {
    pub owner: TypeId,
    pub bytes: Range,
}

/// An owned, validated constant. Only the codec may create one.
#[derive(Clone, Debug)]
pub(super) struct Held {
    owner: TypeId,
    bytes: Vec<u8>,
}

impl Held {
    pub(super) const fn owner(&self) -> TypeId {
        self.owner
    }
    pub(super) fn encoded(&self) -> &[u8] {
        &self.bytes
    }
}

/// How a type's values are encoded, read off its declaration.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Shape {
    /// `nil` takes nothing; `cons` takes the rest of the value at `recursive`
    /// and carries its element in whatever fields remain.
    Spine {
        nil: CtorId,
        cons: CtorId,
        recursive: usize,
    },
    Tagged,
}

/// A value under construction, before it is encoded.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Value(pub CtorId, pub Vec<Self>);

#[must_use]
pub fn shape(program: &Program, id: TypeId) -> Shape {
    let ctors = program.type_(id).constructors();
    if ctors.len() != 2 {
        return Shape::Tagged;
    }
    let (first, second) = (program.ctor_at(id, 0), program.ctor_at(id, 1));
    for (nil, cons) in [(first, second), (second, first)] {
        if !program.fields(nil).is_empty() {
            continue;
        }
        let mut recursive = program
            .fields(cons)
            .iter()
            .enumerate()
            .filter(|(_, field)| **field == id);
        if let (Some((at, _)), None) = (recursive.next(), recursive.next()) {
            return Shape::Spine {
                nil,
                cons,
                recursive: at,
            };
        }
    }
    Shape::Tagged
}

/// Append `value` to `out`, answering how many elements it has when its type
/// is spine-shaped and zero otherwise.
///
/// # Panics
///
/// If `value` is not of type `id`.
pub(super) fn encode(program: &Program, id: TypeId, value: &Value, out: &mut Vec<u8>) -> u32 {
    match shape(program, id) {
        Shape::Spine {
            nil,
            cons,
            recursive,
        } => {
            // Count first, since a nested spine has no range end to stop at.
            // Walking twice beats holding the chain: it is already in hand.
            let mut count = 0u64;
            let mut rest = value;
            while rest.0 == cons {
                count += 1;
                rest = &rest.1[recursive];
            }
            assert_eq!(rest.0, nil, "a spine ends in its empty constructor");
            leb128(count, out);

            let mut rest = value;
            while rest.0 == cons {
                for (at, field) in rest.1.iter().enumerate() {
                    if at != recursive {
                        encode(program, program.fields(cons)[at], field, out);
                    }
                }
                rest = &rest.1[recursive];
            }
            u32::try_from(count).expect("a spine within 4G")
        }
        Shape::Tagged => {
            if program.type_(id).constructors().len() > 1 {
                leb128(u64::from(program.tag(value.0)), out);
            }
            for (field, at) in value.1.iter().zip(program.fields(value.0)) {
                encode(program, *at, field, out);
            }
            0
        }
    }
}

/// Independent, tree-materializing oracle for codec and optimizer tests.
/// Production consumers use validated views and bounded field scans.
#[cfg(test)]
pub(super) fn decode(program: &Program, id: TypeId, bytes: &[u8]) -> (Value, usize) {
    match shape(program, id) {
        Shape::Spine {
            nil,
            cons,
            recursive,
        } => decode_spine(program, bytes, nil, cons, recursive),
        Shape::Tagged => decode_tagged(program, id, bytes),
    }
}

#[cfg(test)]
fn decode_spine(
    program: &Program,
    bytes: &[u8],
    nil: CtorId,
    cons: CtorId,
    recursive: usize,
) -> (Value, usize) {
    let (count, mut at) = unleb128(bytes);
    let fields = program.fields(cons);
    let mut elements = Vec::new();
    for _ in 0..count {
        let mut element = Vec::new();
        for (index, field) in fields.iter().enumerate() {
            if index == recursive {
                element.push(Value(nil, Vec::new()));
            } else {
                let (value, took) = decode(program, *field, &bytes[at..]);
                element.push(value);
                at += took;
            }
        }
        elements.push(element);
    }
    // Built from the end, so each element holds the rest of the value.
    let mut value = Value(nil, Vec::new());
    for mut element in elements.into_iter().rev() {
        element[recursive] = value;
        value = Value(cons, element);
    }
    (value, at)
}

#[cfg(test)]
fn decode_tagged(program: &Program, id: TypeId, bytes: &[u8]) -> (Value, usize) {
    let mut at = 0;
    let ctor = if program.type_(id).constructors().len() > 1 {
        let (tag, took) = unleb128(bytes);
        at += took;
        program.ctor_at(id, u32::try_from(tag).expect("a tag within 4G"))
    } else {
        program.ctor_at(id, 0)
    };
    let mut fields = Vec::with_capacity(program.fields(ctor).len());
    for index in 0..program.fields(ctor).len() {
        let field = program.fields(ctor)[index];
        let (value, took) = decode(program, field, &bytes[at..]);
        fields.push(value);
        at += took;
    }
    (Value(ctor, fields), at)
}

pub(super) fn read_natural(bytes: &[u8]) -> (BigUint, usize) {
    let end = bytes
        .iter()
        .position(|byte| byte & 0x80 == 0)
        .expect("a terminated number");
    let digits: Vec<u8> = bytes[..=end].iter().map(|byte| byte & 0x7f).collect();
    (
        BigUint::from_radix_le(&digits, 128).expect("base 128 digits"),
        end + 1,
    )
}

pub(super) fn write_natural(value: &BigUint, out: &mut Vec<u8>) {
    let digits = value.to_radix_le(128);
    for (at, digit) in digits.iter().enumerate() {
        out.push(if at + 1 == digits.len() {
            *digit
        } else {
            *digit | 0x80
        });
    }
}

/// Write a number straight into the pool, without building the chain of
/// constructors it stands for.
pub(super) fn write_number(value: u64, out: &mut Vec<u8>) {
    leb128(value, out);
}

/// Seven bits a byte, low first, with the high bit set while more follow.
fn leb128(mut value: u64, out: &mut Vec<u8>) {
    loop {
        let byte = u8::try_from(value & 0x7F).expect("seven bits");
        value >>= 7;
        if value == 0 {
            out.push(byte);
            return;
        }
        out.push(byte | 0x80);
    }
}

// Read the bounded queries without allocating bigint digits. Find the end
// first so unterminated encodings still panic even after numerical overflow.
// Folding high digits first also accepts arbitrarily zero-padded encodings,
// just like read_natural; length alone is not evidence of overflow.
fn read_u64(bytes: &[u8]) -> (Option<u64>, usize) {
    let took = bytes
        .iter()
        .position(|byte| byte & 0x80 == 0)
        .expect("a terminated number")
        + 1;
    let value = bytes[..took].iter().rev().try_fold(0u64, |value, byte| {
        value.checked_mul(128)?.checked_add(u64::from(byte & 0x7f))
    });
    (value, took)
}

#[cfg(test)]
fn unleb128(bytes: &[u8]) -> (u64, usize) {
    let (value, took) = read_u64(bytes);
    (
        value.expect("a constructor count small enough to materialize"),
        took,
    )
}
