//! Fitting what crosses a boundary to what a target carries across one.
//!
//! The IR lets a function take and answer any number of values, and a region
//! carry any number out. A target carries only so many: the 6502 passes four
//! parameters and answers one. Where more cross than fit, the last place
//! holds one cell carrying the rest, and the other side takes them back out.
//! A cell is the representation every target already legalizes, so this is
//! what keeps a program compilable everywhere: holding an aggregate as
//! several values is an optimization over boxing it, never a new requirement.
//!
//! The logical entry keeps its signature: nothing calls it, a target binds
//! its parameters from startup, and it answers one word. An external
//! declaration keeps its own too, since a provider reads what it reads.

use crate::index::append_range;

use super::rewrite::{self, Declarations, Rebuild};
use super::{Builder, Class, Exit, FunctionId, Op, Program, Terminator, ValueId};

/// How many values a target carries across each kind of boundary.
///
/// Every limit is at least one, since a packed run needs a place of its own.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Budget {
    params: usize,
    results: usize,
    transfers: usize,
}

impl Budget {
    /// A target that carries whatever the IR does.
    pub const UNLIMITED: Self = Self::new(usize::MAX, usize::MAX, usize::MAX);

    /// Parameters a function takes, results it answers, and values an `if`
    /// or a loop carries into or out of itself.
    ///
    /// # Panics
    /// If any limit is zero.
    #[must_use]
    pub const fn new(params: usize, results: usize, transfers: usize) -> Self {
        assert!(
            params > 0 && results > 0 && transfers > 0,
            "a boundary carries at least one value"
        );
        Self {
            params,
            results,
            transfers,
        }
    }
}

/// Rebuild `source` so nothing crosses a boundary in more values than
/// `budget` allows. A program already within it is returned as it stands.
///
/// Function IDs, names, data and globals are preserved. A packed parameter
/// run is named for the first parameter it holds.
#[must_use]
pub fn fit(source: &Program, budget: Budget) -> Program {
    if within(source, budget) {
        return source.clone();
    }
    let declared = declarations(source, budget);
    let mut pass = Fit {
        budget,
        entry: source.entry(),
        returns: budget.results,
    };
    rewrite::rebuild_declared(source, declared, &mut pass)
}

/// Whether every boundary already fits.
fn within(source: &Program, budget: Budget) -> bool {
    let entry = source.entry();
    source.functions.iter_enumerated().all(|(id, function)| {
        function.external().is_some()
            || id == entry
            || (function.params.len() <= budget.params
                && function.returns.classes().len() <= budget.results)
    }) && source
        .functions()
        .iter()
        .filter_map(super::Function::body)
        .all(|body| {
            source.walk_within(body).all(|(op, results)| match *op {
                Op::If { .. } => results.len() <= budget.transfers,
                Op::Loop { initial, .. } => {
                    initial.len() <= budget.transfers && results.len() <= budget.transfers
                }
                _ => true,
            })
        })
}

/// Every declaration, with defined functions other than the entry packed
/// to the budget. The pools are written afresh so no stale run survives.
fn declarations(source: &Program, budget: Budget) -> Declarations {
    let entry = source.entry();
    let mut declared = Declarations::of(source);
    declared.signature.clear();
    declared.parameters.clear();
    for id in source.functions.ids() {
        let function = &mut declared.functions[id];
        let params = source.signature(function.params);
        let names = &source.parameters[function.parameters.range()];
        let packs = function.external().is_none() && id != entry;
        let (params, names) = if packs && params.len() > budget.params {
            let kept = budget.params - 1;
            let mut classes = params[..kept].to_vec();
            classes.push(Class::Cell);
            (classes, names[..=kept].to_vec())
        } else {
            (params.to_vec(), names.to_vec())
        };
        function.params = append_range(&mut declared.signature, &params);
        function.parameters = append_range(&mut declared.parameters, &names);
        if let super::Returns::Values(returns) = function.returns {
            let returns = source.signature(returns);
            let returns = if packs {
                classes(returns, budget.results)
            } else {
                returns.to_vec()
            };
            function.returns =
                super::Returns::Values(append_range(&mut declared.signature, &returns));
        }
    }
    declared
}

struct Fit {
    budget: Budget,
    entry: FunctionId,
    /// How many results the function being rebuilt may answer.
    returns: usize,
}

impl Fit {
    /// A loop carrying more state in or more results out than fit: each
    /// side packed on the way in and read back on the way out.
    fn loop_(
        &mut self,
        rebuild: &Rebuild<'_>,
        b: &mut Builder,
        initial: super::Range,
        body: super::RegionId,
        results: &[ValueId],
    ) -> Vec<ValueId> {
        let limit = self.budget.transfers;
        let source = rebuild.source();
        let state: Vec<_> = source
            .values(initial)
            .iter()
            .map(|&value| source.class(value))
            .collect();
        let old = rebuild.classes(results);
        let initial = pack(b, &rebuild.args(initial), limit);
        let carried = b.loop_(&initial, &classes(&old, limit), |b, params| {
            let params = unpack(b, params, &state, limit);
            rebuild.region(b, body, &params, self);
        });
        unpack(b, &carried, &old, limit)
    }
}

impl rewrite::Pass for Fit {
    fn op(&mut self, rebuild: &Rebuild<'_>, b: &mut Builder, op: Op, results: &[ValueId]) -> bool {
        let limit = self.budget.transfers;
        let fresh = match op {
            Op::Call { function, args }
                if rebuild.source().function(function).external().is_none() =>
            {
                let args = pack(b, &rebuild.args(args), self.budget.params);
                let answered = b.call(function, &args);
                unpack(b, &answered, &rebuild.classes(results), self.budget.results)
            }
            Op::If {
                condition,
                then_region,
                else_region,
            } if results.len() > limit => {
                let old = rebuild.classes(results);
                let pass = std::cell::RefCell::new(self);
                let carried = b.if_(
                    rebuild.value(condition),
                    &classes(&old, limit),
                    |b| rebuild.region(b, then_region, &[], &mut **pass.borrow_mut()),
                    |b| rebuild.region(b, else_region, &[], &mut **pass.borrow_mut()),
                );
                unpack(b, &carried, &old, limit)
            }
            Op::Loop { initial, body } if initial.len() > limit || results.len() > limit => {
                self.loop_(rebuild, b, initial, body, results)
            }
            _ => return false,
        };
        for (&was, now) in results.iter().zip(fresh) {
            rebuild.stands_for(was, now);
        }
        true
    }

    fn enter(
        &mut self,
        rebuild: &Rebuild<'_>,
        b: &mut Builder,
        function: FunctionId,
        params: &[ValueId],
    ) -> Vec<ValueId> {
        let source = rebuild.source();
        let declared = source.function(function);
        if function == self.entry {
            self.returns = usize::MAX;
            return params.to_vec();
        }
        self.returns = self.budget.results;
        unpack(
            b,
            params,
            source.signature(declared.params),
            self.budget.params,
        )
    }

    fn exit(&mut self, rebuild: &Rebuild<'_>, b: &mut Builder, terminator: Terminator) -> bool {
        let limit = match terminator.exit {
            Exit::Return => self.returns,
            Exit::Yield | Exit::Continue | Exit::Break => self.budget.transfers,
        };
        if terminator.values.len() <= limit {
            return false;
        }
        let values = pack(b, &rebuild.args(terminator.values), limit);
        match terminator.exit {
            Exit::Return => b.ret(&values),
            Exit::Yield => b.yield_(&values),
            Exit::Continue => b.continue_(&values),
            Exit::Break => b.break_(&values),
        }
        true
    }
}

/// The classes a run takes once packed to `limit`.
fn classes(classes: &[Class], limit: usize) -> Vec<Class> {
    if classes.len() <= limit {
        return classes.to_vec();
    }
    let mut packed = classes[..limit - 1].to_vec();
    packed.push(Class::Cell);
    packed
}

/// A run as it crosses: all of it where it fits, and otherwise one short of
/// the limit followed by a cell holding the rest.
fn pack(b: &mut Builder, values: &[ValueId], limit: usize) -> Vec<ValueId> {
    if values.len() <= limit {
        return values.to_vec();
    }
    let (kept, rest) = values.split_at(limit - 1);
    let mut packed = kept.to_vec();
    packed.push(b.cell(0, rest));
    packed
}

/// The run `pack` was handed, read back from what crossed. `classes` are
/// the classes of the run before packing.
fn unpack(b: &mut Builder, crossed: &[ValueId], classes: &[Class], limit: usize) -> Vec<ValueId> {
    if classes.len() <= limit {
        return crossed.to_vec();
    }
    let (kept, cell) = crossed.split_at(limit - 1);
    let cell = cell[0];
    let mut values = kept.to_vec();
    for (index, &class) in (0u32..).zip(&classes[limit - 1..]) {
        values.push(b.cell_field(class, cell, index));
    }
    values
}
