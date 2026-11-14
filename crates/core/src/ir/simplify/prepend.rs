//! Eliminate a short temporary sequence consumed by a reverse prepend.

use super::{
    Binary, Builder, Class, HashMap, Op, Program, Range, ShapeId, Simplify, ValueId, rewrite,
};

/// The start returned alongside a buffer, and the push that produced it.
pub(super) struct Pushed {
    start: ValueId,
    operands: Range,
    shape: ShapeId,
}

/// Both results must have a single use. An escaping buffer may be read
/// through its address; a separately used start keeps the push live.
pub(super) fn temporary_pushes(source: &Program) -> HashMap<ValueId, Pushed> {
    if !source
        .ops
        .iter()
        .any(|op| matches!(op, Op::BufferPrepend { .. }))
    {
        return HashMap::new();
    }
    let uses = source.use_counts();
    let mut pushes = HashMap::new();
    for region in source.regions.ids() {
        for (op, results) in source.walk(region) {
            if let (Op::BufferPush { operands, shape }, &[buffer, start]) = (*op, results)
                && uses[buffer.index()] == 1
                && uses[start.index()] == 1
            {
                pushes.insert(
                    buffer,
                    Pushed {
                        start,
                        operands,
                        shape,
                    },
                );
            }
        }
    }
    pushes
}

impl Simplify {
    /// A short sequence constructed only to reverse it onto another can
    /// put its elements straight onto that destination, head first.
    pub(super) fn prepend_elements(
        &self,
        rebuild: &rewrite::Rebuild<'_>,
        b: &mut Builder,
        operands: Range,
        shape: ShapeId,
        results: &[ValueId],
    ) -> bool {
        let source = rebuild.source();
        let &[onto, start, len, mut from, mut first, count] = source.values(operands) else {
            unreachable!("a prepend has two sequence views")
        };
        let Some(count @ 1..=4) = self.number(count) else {
            return false;
        };
        // Bound the number of inlined pushes. Verify the exact view at
        // every link before emitting anything, including its tail length.
        let mut elements = Vec::new();
        for tail in (0..count).rev() {
            let Some(push) = self.pushes.get(&from) else {
                return false;
            };
            if push.shape != shape || push.start != first {
                return false;
            }
            let [buffer, start, len, fields @ ..] = source.values(push.operands) else {
                unreachable!("a push takes a sequence and element fields")
            };
            if self.number(*len) != Some(tail) {
                return false;
            }
            elements.push(fields);
            (from, first) = (*buffer, *start);
        }
        let (mut buffer, mut first, mut len) = (
            rebuild.value(onto),
            rebuild.value(start),
            rebuild.value(len),
        );
        for (at, fields) in elements.iter().enumerate() {
            if at > 0 {
                let one = b.constant(Class::Word, 1);
                len = b.binary_at(Class::Word, Binary::Add, len, one);
            }
            let fields: Vec<_> = fields.iter().map(|&field| rebuild.value(field)).collect();
            [buffer, first] = b.buffer_push((buffer, first, len), shape, &fields);
        }
        rebuild.stands_for(results[0], buffer);
        rebuild.stands_for(results[1], first);
        true
    }
}
