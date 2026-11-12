//! Three-word inline rows for tables of short byte sequences. The table itself
//! is one immortal byte buffer. Projecting a row produces an ordinary slice,
//! so readers, tails and calls use the existing buffer ABI.

use super::{Carried, Class, Lowering, Storage, ValueId, barb, peeled};
use crate::ir::{Binary, Builder, Relation, ShapeId};

const ROW: usize = 24;
const LENGTH_TAG: u8 = 0xc0;

fn encode(bytes: &[u8], kind: barb::ByteSequence) -> Option<[u8; ROW]> {
    let mut row = [0; ROW];
    if bytes.len() < ROW {
        row[ROW - 1] = LENGTH_TAG + u8::try_from(bytes.len()).ok()?;
    } else if bytes.len() != ROW
        || kind != barb::ByteSequence::Text
        || std::str::from_utf8(bytes).is_err()
    {
        return None;
    }
    row[..bytes.len()].copy_from_slice(bytes);
    Some(row)
}

impl Lowering<'_> {
    /// Each short row owns its bytes inline in the same immutable backing.
    /// A longer row or an element with another layout uses normal construction.
    pub(super) fn inline_rows(
        &self,
        b: &mut Builder,
        elements: &[Vec<barb::Constant<'_>>],
        outer: ShapeId,
        push: barb::CtorId,
        recursive: usize,
    ) -> Option<[ValueId; 3]> {
        if !self.native_inline_bytes || elements.len() < 2 {
            return None;
        }
        let ty = self.barb.fields(push)[1 - recursive];
        let kind = self.barb.byte_sequence(ty)?;
        if self.carries[ty.index()] != Storage::Seq {
            return None;
        }
        let list = peeled(self.barb, ty)?;
        let barb::TypeShape::Sequence {
            push, recursive, ..
        } = barb::type_shape(self.barb, list)
        else {
            return None;
        };
        let Some(Carried::One(byte)) = self.field_carried(push, 1 - recursive) else {
            return None;
        };
        if byte.width().is_none_or(|bits| bits == 0 || bits > 8) {
            return None;
        }
        let mut rows = Vec::with_capacity(elements.len().checked_mul(ROW)?);
        for fields in elements {
            let [value] = fields[..] else { return None };
            let value = barb::single_field_constant(self.barb, value);
            let barb::ConstantView::Spine(spine) = value.view() else {
                return None;
            };
            if spine.length() > ROW.into() {
                return None;
            }
            let bytes = spine.to_bytes()?;
            rows.extend_from_slice(&encode(&bytes, kind)?);
        }
        // Padding and tags are bytes too, even if range analysis has seen only
        // a subset of byte values in the actual elements.
        let shape = b.shape(&[Class::fixed(8)]);
        let data = b.data(&rows);
        let buffer = b.buffer_known(data, shape, 1);
        Some(table_views(b, (buffer, shape), outer, elements.len(), kind))
    }
}

fn row_length(
    b: &mut Builder,
    (buffer, first, shape): (ValueId, ValueId, ShapeId),
    stride: ValueId,
    kind: barb::ByteSequence,
) -> ValueId {
    let last = b.constant(Class::Word, u64::try_from(ROW).unwrap() - 1);
    let end = b.binary(Binary::Add, first, last);
    let tag = b.buffer_field((Class::fixed(8), shape), (buffer, end), 0);
    let tag = b.convert(Class::Word, tag);
    let base = b.constant(Class::Word, u64::from(LENGTH_TAG));
    if kind == barb::ByteSequence::Text {
        let full = b.compare(Relation::Less, tag, base);
        b.if_(
            full,
            &[Class::Word],
            |b| b.yield_(&[stride]),
            |b| {
                let len = b.binary(Binary::Sub, tag, base);
                b.yield_(&[len]);
            },
        )[0]
    } else {
        b.binary(Binary::Sub, tag, base)
    }
}

fn table_views(
    b: &mut Builder,
    (buffer, shape): (ValueId, ShapeId),
    outer: ShapeId,
    count: usize,
    kind: barb::ByteSequence,
) -> [ValueId; 3] {
    let count = b.constant(
        Class::Word,
        u64::try_from(count).expect("a table count fits in a word"),
    );
    let zero = b.constant(Class::Word, 0);
    let empty = b.buffer_empty(outer);
    let result = b.loop_(
        &[count, empty, zero],
        &[Class::Buffer, Class::Word],
        |b, state| {
            let [left, table, start] = state else {
                unreachable!()
            };
            b.if_(
                *left,
                &[],
                |b| {
                    let one = b.constant(Class::Word, 1);
                    let index = b.binary(Binary::Sub, *left, one);
                    let stride = b.constant(Class::Word, u64::try_from(ROW).unwrap());
                    let first = b.binary(Binary::Mul, index, stride);
                    let len = row_length(b, (buffer, first, shape), stride, kind);
                    let filled = b.binary(Binary::Sub, count, *left);
                    let [table, start] =
                        b.buffer_push((*table, *start, filled), outer, &[buffer, first, len]);
                    b.continue_(&[index, table, start]);
                },
                |b| b.yield_(&[]),
            );
            b.break_(&[*table, *start]);
        },
    );
    [result[0], result[1], count]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn arbitrary_bytes_and_full_utf8_rows_have_distinct_length_encodings() {
        use barb::ByteSequence::{Bytes, Text};
        for n in 0..ROW {
            let bytes = vec![0xff; n];
            let row = encode(&bytes, Bytes).unwrap();
            assert_eq!(&row[..n], bytes);
            assert_eq!(usize::from(row[ROW - 1] - LENGTH_TAG), n);
        }
        let bytes = "é".repeat(12);
        assert_eq!(encode(bytes.as_bytes(), Text).unwrap(), bytes.as_bytes());
        assert!(encode(bytes.as_bytes(), Bytes).is_none());
        assert!(encode(&[0xff; ROW], Text).is_none());
        assert!(encode(&[b'a'; ROW + 1], Text).is_none());
    }
}
