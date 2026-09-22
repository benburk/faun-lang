//! Dropping what a program works out and never reads.
//!
//! Lowering writes for one tier at a time, and a rewrite that redirects a
//! reader leaves what it read behind. Neither is worth complicating, so this
//! is where the leftovers go.
//!
//! What may go is what can be worked out again for nothing: a constant, a
//! width change, a comparison, an arithmetic step. A call may do something
//! while answering and a store does nothing else, so neither is ever
//! dropped, and an `if` holding one of them stays for what it holds rather
//! than for what it answers. A loop stays either way: this does not decide
//! whether one comes back.

use super::{Op, Program, RegionId, ValueId, rewrite};

/// Rebuild `source` without the instructions nothing reads.
#[must_use]
pub(super) fn prune(source: &Program) -> Program {
    let mut pass = Prune {
        read: Read::of(source),
    };
    rewrite::rebuild(source, &mut pass)
}

struct Prune {
    read: Read,
}

impl rewrite::Pass for Prune {
    fn op(
        &mut self,
        _: &rewrite::Rebuild<'_>,
        _: &mut super::Builder,
        op: Op,
        results: &[ValueId],
    ) -> bool {
        // Writing nothing and saying nothing about the old results is how
        // an instruction goes away: nothing left reads them.
        !self.read.wanted(&op, results)
    }
}

/// What a program reads, worked out by reading it backwards.
struct Read {
    values: Vec<bool>,
    regions: Vec<bool>,
}

impl Read {
    fn of(source: &Program) -> Self {
        let mut held = Self {
            values: vec![false; source.values_count()],
            regions: vec![false; source.regions.len()],
        };
        for function in source.functions() {
            if let Some(body) = function.body() {
                held.region(source, body);
            }
        }
        held
    }

    /// Whether an instruction is one the rebuild writes again.
    fn wanted(&self, op: &Op, results: &[ValueId]) -> bool {
        match *op {
            Op::Store { .. } | Op::Call { .. } | Op::Loop { .. } => true,
            Op::If { then_region, .. } => self.regions[then_region.index()],
            _ => results.iter().any(|value| self.values[value.index()]),
        }
    }

    /// Read one region backwards, which is the order a reader is known in:
    /// nothing names a value written after it, so by the time an
    /// instruction is reached, everything that could want it has spoken.
    fn region(&mut self, source: &Program, region: RegionId) {
        self.regions[region.index()] = true;
        let held = source.region(region);
        if let Some(terminator) = held.terminator {
            self.reads(source.values(terminator.values));
        }
        for (op, results) in source
            .walk(region)
            .map(|(op, results)| (*op, results))
            .rev()
        {
            if !self.needed(source, &op, results) {
                continue;
            }
            match op {
                Op::If {
                    condition,
                    then_region,
                    else_region,
                } => {
                    self.reads(&[condition]);
                    self.region(source, then_region);
                    self.region(source, else_region);
                }
                Op::Loop { initial, body } => {
                    self.reads(source.values(initial));
                    self.region(source, body);
                }
                _ => self.reads(&operands(source, &op)),
            }
        }
    }

    /// Whether this instruction stays. A container stays for what it holds
    /// as much as for what it answers: an arm that writes somewhere runs
    /// whether or not anybody wanted the answer.
    fn needed(&self, source: &Program, op: &Op, results: &[ValueId]) -> bool {
        let answered = || results.iter().any(|value| self.values[value.index()]);
        match *op {
            Op::Store { .. } | Op::Call { .. } | Op::Loop { .. } => true,
            Op::If {
                then_region,
                else_region,
                ..
            } => answered() || acts(source, then_region) || acts(source, else_region),
            _ => answered(),
        }
    }

    fn reads(&mut self, values: &[ValueId]) {
        for value in values {
            self.values[value.index()] = true;
        }
    }
}

/// Whether anything in a region, or in a region within it, does something
/// besides work out a value.
fn acts(source: &Program, region: RegionId) -> bool {
    source
        .every(region)
        .any(|op| matches!(*op, Op::Store { .. } | Op::Call { .. }))
}

/// What an instruction reads, for the ones that read a fixed few values.
/// Containers are handled where their regions are.
fn operands(source: &Program, op: &Op) -> Vec<ValueId> {
    match *op {
        Op::Constant { .. } | Op::NaturalConstant(_) | Op::AddressOf(_) => Vec::new(),
        Op::Binary { left, right, .. } | Op::Compare { left, right, .. } => vec![left, right],
        Op::Load { address, .. } => vec![address],
        Op::Store { address, value, .. } => vec![address, value],
        Op::Convert { value, .. } | Op::Shift { value, .. } => vec![value],
        Op::Call { args, .. } => source.values(args).to_vec(),
        Op::If { condition, .. } => vec![condition],
        Op::Loop { initial, .. } => source.values(initial).to_vec(),
    }
}
