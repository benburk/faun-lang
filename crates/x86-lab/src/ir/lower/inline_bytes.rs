//! Bounded inline rows for tables of short byte sequences. The table itself
//! is one immortal byte buffer. Projecting a row produces an ordinary slice,
//! so readers, tails and calls use the existing buffer ABI.

use super::{Carried, Class, Lowering, Storage, ValueId, barb, peeled};
use crate::ir::{Binary, Builder, ShapeId};

const ROW: usize = 24;

/// A fixed-width row needs no stored length. Variable rows carry their length
/// after the payload. Both choices are made once for the whole table.
#[derive(Clone, Copy)]
struct Rows {
    width: usize,
    fixed: bool,
}

impl Rows {
    fn pack(values: &[Vec<u8>], kind: barb::ByteSequence) -> Option<(Self, Vec<u8>)> {
        let bounds = barb::SequenceLengths::of(values.iter().map(Vec::len))?;
        let width = bounds.longest;
        let limit = if kind == barb::ByteSequence::Text {
            ROW
        } else {
            ROW - 1
        };
        if width > limit {
            return None;
        }
        let fixed = bounds.shortest == width;
        let layout = Self { width, fixed };
        let mut bytes = Vec::with_capacity(values.len().checked_mul(layout.stride())?);
        for value in values {
            bytes.extend_from_slice(value);
            if !fixed {
                bytes.resize(bytes.len() + width - value.len(), 0);
                bytes.push(u8::try_from(value.len()).ok()?);
            }
        }
        Some((layout, bytes))
    }

    fn stride(self) -> usize {
        self.width + usize::from(!self.fixed)
    }
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
        let values = elements
            .iter()
            .map(|fields| {
                let [value] = fields[..] else { return None };
                let value = barb::single_field_constant(self.barb, value);
                let barb::ConstantView::Spine(spine) = value.view() else {
                    return None;
                };
                (spine.length() <= ROW.into()).then(|| spine.to_bytes())?
            })
            .collect::<Option<Vec<_>>>()?;
        let (rows, data) = Rows::pack(&values, kind)?;
        if data.is_empty() {
            return None;
        }
        // Padding and lengths are bytes too, even if range analysis has seen only
        // a subset of byte values in the actual elements.
        let shape = b.shape(&[Class::fixed(8)]);
        let data = b.data(&data);
        let buffer = b.buffer_known(data, shape, 1);
        Some(table_views(b, (buffer, shape), outer, elements.len(), rows))
    }
}

fn row_length(
    b: &mut Builder,
    (buffer, first, shape): (ValueId, ValueId, ShapeId),
    rows: Rows,
) -> ValueId {
    let width = b.constant(Class::Word, u64::try_from(rows.width).unwrap());
    if rows.fixed {
        return width;
    }
    let at = b.binary(Binary::Add, first, width);
    let len = b.buffer_field((Class::fixed(8), shape), (buffer, at), 0);
    b.convert(Class::Word, len)
}

fn table_views(
    b: &mut Builder,
    (buffer, shape): (ValueId, ShapeId),
    outer: ShapeId,
    count: usize,
    rows: Rows,
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
                    let stride = b.constant(Class::Word, u64::try_from(rows.stride()).unwrap());
                    let first = b.binary(Binary::Mul, index, stride);
                    let len = row_length(b, (buffer, first, shape), rows);
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
    fn rows_use_only_the_width_the_whole_table_needs() {
        use barb::ByteSequence::{Bytes, Text};
        let (fixed, data) = Rows::pack(&[vec![0xff; 23], vec![0xc0; 23]], Bytes).unwrap();
        assert!(fixed.fixed);
        assert_eq!((fixed.stride(), data.len()), (23, 46));
        let text = "é".repeat(12).into_bytes();
        let (mixed, data) = Rows::pack(&[text.clone(), vec![]], Text).unwrap();
        assert_eq!((mixed.stride(), data[24], data[49]), (25, 24, 0));
        assert!(Rows::pack(&[text], Bytes).is_none());
        assert!(Rows::pack(&[vec![b'a'; 25]], Text).is_none());
    }
}
