//! Share repeated scalar calculations within a region, without moving work
//! or reading memory fewer times. In particular, legalization computes the
//! same element address for each leaf of a flat record in a sequence.

use std::collections::HashMap;

use crate::float::Float;

use super::{
    Binary, Builder, Class, DataId, Direction, Op, Program, RegionId, Relation, ValueId, rewrite,
};

/// Bound the temporary table even in a very large straight-line region.
const MAX_EXPRESSIONS: usize = 1024;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Expression {
    Address(DataId),
    Binary(Binary, ValueId, ValueId),
    Compare(Relation, ValueId, ValueId),
    Convert(ValueId),
    Shift(Direction, ValueId, u16),
    Float(Float, ValueId, Option<ValueId>),
}

pub(super) fn common(source: &Program) -> Program {
    let mut regions = vec![RegionId::at(0); source.values_count()];
    for (id, _) in source.regions.iter_enumerated() {
        for (_, results) in source.walk(id) {
            for &value in results {
                regions[value.index()] = id;
            }
        }
    }
    rewrite::rebuild(
        source,
        &mut Common {
            regions,
            current: None,
            canonical: (0..source.values_count()).map(ValueId::at).collect(),
            constants: HashMap::new(),
            available: HashMap::new(),
        },
    )
}

struct Common {
    regions: Vec<RegionId>,
    current: Option<RegionId>,
    /// Source IDs used only as expression keys, never as replacement code.
    canonical: Vec<ValueId>,
    constants: HashMap<(Class, u64), ValueId>,
    available: HashMap<(Class, Expression), ValueId>,
}

impl rewrite::Pass for Common {
    #[expect(
        clippy::too_many_lines,
        reason = "one exhaustive key construction and region-local lookup"
    )]
    fn op(
        &mut self,
        rebuild: &rewrite::Rebuild<'_>,
        b: &mut Builder,
        op: Op,
        results: &[ValueId],
    ) -> bool {
        let [result] = *results else { return false };
        let class = rebuild.source().class(result);
        if !matches!(class, Class::Held(_) | Class::Word | Class::Address) {
            return false;
        }
        if let Op::Constant { value } = op {
            // Equal constants identify equal expressions, but keep each
            // literal at its use so targets can fold it into an immediate
            // instead of extending a shared constant's register lifetime.
            if self.constants.len() == MAX_EXPRESSIONS {
                self.constants.clear();
            }
            self.canonical[result.index()] =
                *self.constants.entry((class, value)).or_insert(result);
            return false;
        }
        let value = |value: ValueId| self.canonical[value.index()];
        let expression = match op {
            Op::AddressOf(data) => Expression::Address(data),
            Op::Binary { op, left, right } => Expression::Binary(op, value(left), value(right)),
            Op::Compare {
                relation,
                left,
                right,
            } => Expression::Compare(relation, value(left), value(right)),
            Op::Convert { value: from } => Expression::Convert(value(from)),
            Op::Shift {
                direction,
                value: from,
                by,
            } => Expression::Shift(direction, value(from), by),
            Op::Float { float, operands } => {
                let operands = rebuild.source().values(operands);
                Expression::Float(
                    float,
                    value(operands[0]),
                    operands.get(1).copied().map(value),
                )
            }
            // Loads, allocations and calls are deliberately not candidates.
            _ => return false,
        };
        let region = self.regions[result.index()];
        if self.current != Some(region) {
            // Never reuse a value from a sibling arm or an earlier loop
            // iteration. Losing parent candidates at a join is conservative.
            self.available.clear();
            self.current = Some(region);
        }
        let key = (class, expression);
        if let Some(&held) = self.available.get(&key) {
            self.canonical[result.index()] = self.canonical[held.index()];
            rebuild.stands_for(result, rebuild.value(held));
        } else {
            rebuild.copy(b, op, results, self);
            if self.available.len() == MAX_EXPRESSIONS {
                self.available.clear();
            }
            self.available.insert(key, result);
        }
        true
    }
}
