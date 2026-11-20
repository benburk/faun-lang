//! Bounded inline rows for tables of short byte sequences. The table itself
//! is one immortal byte buffer. Projecting a row produces an ordinary slice,
//! so readers, tails and calls use the existing buffer ABI.

use super::{Carried, Class, Lowering, Storage, ValueId, peeled};
use crate::ir::{Binary, Builder, Relation, ShapeId};

const ROW: usize = 24;

/// A fixed-width row needs no stored length. Variable rows carry their length
/// after the payload. Both choices are made once for the whole table.
#[derive(Clone, Copy)]
struct Rows {
    width: usize,
    fixed: bool,
}

impl Rows {
    fn from_bounds(bounds: barb::Bounds) -> Option<Self> {
        let high = bounds.high?;
        let width = usize::try_from(high).ok()?;
        (bounds.low <= high && width <= ROW).then_some(Self {
            width,
            fixed: bounds.low == high,
        })
    }

    fn write(self, bytes: &mut Vec<u8>, value: &[u8]) {
        bytes.extend_from_slice(value);
        if !self.fixed {
            bytes.resize(bytes.len() + self.width - value.len(), 0);
            bytes.push(u8::try_from(value.len()).expect("the proven row width fits in a byte"));
        }
    }

    fn stride(self) -> usize {
        self.width + usize::from(!self.fixed)
    }
}

impl Lowering<'_> {
    /// Whether `ty` holds bytes: a sequence, under any wrappers, held as a
    /// buffer, whose element is carried in at most eight bits. What it is
    /// called, and whether its bytes spell text, does not matter: a row
    /// stores its length apart from its bytes.
    pub(super) fn holds_bytes(&self, ty: barb::TypeId) -> bool {
        if self.carries[ty.index()] != Storage::Seq {
            return false;
        }
        let Some(list) = peeled(self.barb, ty) else {
            return false;
        };
        let barb::TypeShape::Sequence {
            push, recursive, ..
        } = barb::type_shape(self.barb, list)
        else {
            return false;
        };
        matches!(
            self.field_carried(push, 1 - recursive),
            Some(Carried::One(byte)) if byte.width().is_some_and(|bits| (1..=8).contains(&bits))
        )
    }

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
        if !self.holds_bytes(ty) {
            return None;
        }
        // Sequence constructors have exactly one element field and one tail.
        let values = elements.iter().map(|fields| fields[0]);
        let rows = Rows::from_bounds(barb::bounds_of_constants(self.barb, values.clone()))?;
        let mut data = Vec::with_capacity(elements.len().checked_mul(rows.stride())?);
        for value in values {
            let barb::ConstantView::Spine(spine) =
                barb::single_field_constant(self.barb, value).view()
            else {
                return None;
            };
            rows.write(&mut data, &spine.to_bytes()?);
        }
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
            let done = b.compare(Relation::Equal, *left, zero);
            b.if_(
                done,
                &[],
                |b| b.break_(&[*table, *start]),
                |b| b.yield_(&[]),
            );
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
    );
    [result[0], result[1], count]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rows_use_only_the_width_the_whole_table_needs() {
        let fixed = Rows::from_bounds(barb::Bounds::at(23)).unwrap();
        let mut data = Vec::new();
        fixed.write(&mut data, &[0xff; 23]);
        fixed.write(&mut data, &[0xc0; 23]);
        assert_eq!((fixed.stride(), data.len()), (23, 46));
        let bounds = barb::Bounds::at(24).or(barb::Bounds::at(0));
        let mixed = Rows::from_bounds(bounds).unwrap();
        data.clear();
        mixed.write(&mut data, &"é".repeat(12).into_bytes());
        mixed.write(&mut data, &[]);
        assert_eq!((mixed.stride(), data[24], data[49]), (25, 24, 0));
        mixed.write(&mut data, &[0xc0; 24]);
        assert_eq!(data[74], 24);
        assert!(Rows::from_bounds(barb::Bounds::at(25)).is_none());
        assert!(Rows::from_bounds(barb::Bounds::ANY).is_none());
        assert!(Rows::from_bounds(barb::Bounds::NOTHING).is_none());
    }
}
