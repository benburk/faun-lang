//! Where managed values are used last, and which parameters a function owns.
//!
//! Legalization places reference-count operations from these facts. A claim
//! is released right after its value's last use in the region holding it,
//! and a use that takes a claim -- an exit, a cell field, a loop's initial
//! state, an owned parameter -- takes the value's own claim when that use
//! is its last. That is what lets a count of one mean that nothing else can
//! see a value, which is what updating one in place will ask.
//!
//! A parameter is owned when its function takes a claim to it somewhere:
//! the caller then hands over a claim, moving its own where the call is the
//! argument's last use. A parameter nothing consumes is borrowed, so reading
//! one costs its caller nothing. Owning is decided to a fixed point, since
//! passing a parameter on to an owned one consumes it.

use std::collections::HashMap;

use super::{Class, FunctionId, Op, Program, RegionId, ValueId};

/// Whether a value's class carries a reference count.
pub(super) const fn managed(class: Class) -> bool {
    matches!(class, Class::Cell | Class::Buffer | Class::Natural)
}

/// Every value an instruction reads, including everything read inside the
/// regions it holds and what they leave with, once per reading.
pub(super) fn deep_uses(source: &Program, op: &Op, out: &mut Vec<ValueId>) {
    out.extend(super::prune::operands(source, op));
    match *op {
        Op::If {
            then_region,
            else_region,
            ..
        } => {
            region_uses(source, then_region, out);
            region_uses(source, else_region, out);
        }
        Op::Loop { body, .. } => region_uses(source, body, out),
        _ => {}
    }
}

fn region_uses(source: &Program, region: RegionId, out: &mut Vec<ValueId>) {
    for (op, _) in source.walk(region) {
        deep_uses(source, op, out);
    }
    out.extend_from_slice(source.outgoing(region));
}

/// Where each value is read in one region: by which instruction last, with
/// the region's exit counted as the position after its last instruction,
/// and what each instruction reads.
pub(super) struct Liveness {
    last: HashMap<ValueId, usize>,
    uses: Vec<Vec<ValueId>>,
}

impl Liveness {
    pub(super) fn of(source: &Program, region: RegionId) -> Self {
        let mut last = HashMap::new();
        let mut uses = Vec::new();
        for (at, (op, _)) in source.walk(region).enumerate() {
            let mut read = Vec::new();
            deep_uses(source, op, &mut read);
            for &value in &read {
                last.insert(value, at);
            }
            uses.push(read);
        }
        let exit = uses.len();
        for &value in source.outgoing(region) {
            last.insert(value, exit);
        }
        Self { last, uses }
    }

    /// Whether nothing at or after position `at` reads `value`; `None` asks
    /// about the region's entry, before its first instruction.
    pub(super) fn dead(&self, value: ValueId, at: Option<usize>) -> bool {
        match (self.last.get(&value), at) {
            (None, _) => true,
            (Some(_), None) => false,
            (Some(&last), Some(at)) => last <= at,
        }
    }

    /// Whether instruction `at` is the only reading of `value` from there on:
    /// its last use, and read there exactly once, so taking its claim leaves
    /// nothing else in that instruction reading a released value.
    pub(super) fn only_last(&self, value: ValueId, at: usize) -> bool {
        self.last.get(&value) == Some(&at)
            && self.uses[at].iter().filter(|&&read| read == value).count() == 1
    }
}

/// Which parameters of each function are owned, by function and position.
/// External declarations own nothing.
pub(super) fn owned_parameters(source: &Program) -> Vec<Vec<bool>> {
    let mut owned: Vec<Vec<bool>> = source
        .functions()
        .iter()
        .map(|function| vec![false; function.params.len()])
        .collect();
    loop {
        let mut changed = false;
        for (id, function) in source.functions.iter_enumerated() {
            let Some(body) = function.body() else {
                continue;
            };
            let mut consumed = Vec::new();
            consumed_in(source, body, &owned, &mut consumed);
            for (at, &param) in source.values(source.region(body).params).iter().enumerate() {
                if managed(source.class(param))
                    && !owned[id.index()][at]
                    && consumed.contains(&param)
                {
                    owned[id.index()][at] = true;
                    changed = true;
                }
            }
        }
        if !changed {
            return owned;
        }
    }
}

/// The values some instruction in a region, or its exit, takes a claim to.
fn consumed_in(source: &Program, region: RegionId, owned: &[Vec<bool>], out: &mut Vec<ValueId>) {
    for (op, results) in source.walk(region) {
        match *op {
            Op::Cell { fields, .. } => out.extend_from_slice(source.values(fields)),
            Op::BufferPush { buffer, fields, .. } => {
                out.push(buffer);
                out.extend_from_slice(source.values(fields));
            }
            Op::BufferPrepend { buffer, .. } => out.push(buffer),
            Op::Convert { value } if source.class(value) == source.class(results[0]) => {
                out.push(value);
            }
            Op::Call { function, args } => out.extend(
                source
                    .values(args)
                    .iter()
                    .zip(taken(owned, function))
                    .filter(|&(_, &owned)| owned)
                    .map(|(&arg, _)| arg),
            ),
            Op::If {
                then_region,
                else_region,
                ..
            } => {
                consumed_in(source, then_region, owned, out);
                consumed_in(source, else_region, owned, out);
            }
            Op::Loop { initial, body } => {
                out.extend_from_slice(source.values(initial));
                consumed_in(source, body, owned, out);
            }
            _ => {}
        }
    }
    out.extend_from_slice(source.outgoing(region));
}

/// Whether each parameter of `function` is owned.
pub(super) fn taken(owned: &[Vec<bool>], function: FunctionId) -> &[bool] {
    &owned[function.index()]
}
