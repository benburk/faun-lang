//! Dropping what a program works out and never reads.
//!
//! Lowering writes for one tier at a time, and a rewrite that redirects a
//! reader leaves what it read behind. Neither is worth complicating, so this
//! is where the leftovers go.
//!
//! What may go is what can be worked out again for nothing: a constant, a
//! width change, a comparison, an arithmetic step. A call may do something
//! while answering, so it is never dropped. A store does nothing else, so it
//! stays unless where it writes is a global nothing reads: one whose address
//! is only ever written through, never read through, handed on or kept.
//! A container holding a call or a store that stays, stays for what it
//! holds rather than for what it answers. So does an `if` an arm of which
//! leaves some other way than by answering: a loop's `break` or `continue`,
//! or a return; and a loop that returns.
//!
//! A loop that does none of that goes when nothing reads what it answers.
//! Every loop comes back: each is a total definition's tail call, or one
//! lowering writes over something it has counted, so dropping one never
//! takes away a program's failure to finish.
//!
//! A result of a function no call reads is not answered at all: the
//! function's signature loses it, and what worked it out is then read by
//! nothing. The entry answers what its target reads, and an external what
//! its provider writes, so neither changes.
//!
//! What no instruction left names any more is dropped from the data and
//! globals too, so an image carries only what the program reaches.

use crate::index::append_range;

use super::rewrite::Declarations;
use super::{
    Builder, DataId, Exit, FunctionId, Op, Origin, Program, RegionId, Returns, Terminator, ValueId,
    rewrite,
};

/// Rebuild `source` without the instructions nothing reads.
#[must_use]
pub(super) fn prune(source: &Program) -> Program {
    let read = Read::of(source);
    let declared = declarations(source, &read.answered);
    let mut pass = Prune {
        read,
        function: FunctionId::at(0),
        yields: Vec::new(),
        breaks: Vec::new(),
    };
    let mut pruned = rewrite::rebuild_declared(source, declared, &mut pass);
    pack(&mut pruned);
    pruned
}

/// The widest alignment a datum is kept at: wider than any word.
const ALIGNED: u32 = 16;

/// Lay the data and globals out again with only what an instruction names.
///
/// Every datum keeps its ID, so nothing naming one changes; one nothing
/// names is left holding nothing. A kept one keeps the alignment it was
/// laid out at, up to [`ALIGNED`], since what laid it out may have counted
/// on that.
fn pack(program: &mut Program) {
    let mut named = vec![false; program.spans.len()];
    for function in program.functions() {
        let Some(body) = function.body() else {
            continue;
        };
        for op in program.every(body) {
            if let Op::AddressOf(data) | Op::NaturalConstant(data) = *op {
                named[data.index()] = true;
            }
        }
    }
    if named.iter().all(|&named| named) {
        return;
    }
    let (mut data, mut globals) = (Vec::new(), Vec::new());
    for (span, named) in program.spans.iter_mut().zip(named) {
        let (from, to) = match span.origin {
            Origin::Data => (&program.data, &mut data),
            Origin::Globals => (&program.globals, &mut globals),
        };
        if !named {
            *span = super::Span {
                origin: span.origin,
                start: 0,
                len: 0,
            };
            continue;
        }
        let alignment = 1 << span.start.trailing_zeros().min(ALIGNED.trailing_zeros());
        to.resize(to.len().next_multiple_of(alignment), 0);
        let start = usize::try_from(span.start).expect("a validated datum offset");
        let len = usize::try_from(span.len).expect("a validated datum length");
        span.start = u32::try_from(to.len()).expect("no longer than it was");
        to.extend_from_slice(&from[start..start + len]);
    }
    program.data = data;
    program.globals = globals;
}

/// The declarations with every result nothing reads taken out.
///
/// The signature pool is written afresh, as `fit` writes it: a class only
/// an old signature held would otherwise still be found there by anything
/// asking what the program holds.
fn declarations(source: &Program, answered: &[Vec<bool>]) -> Declarations {
    let mut declared = Declarations::of(source);
    declared.signature.clear();
    for (id, kept) in answered.iter().enumerate() {
        let function = &mut declared.functions[FunctionId::at(id)];
        let params = source.signature(function.params);
        function.params = append_range(&mut declared.signature, params);
        let Returns::Values(returns) = function.returns else {
            continue;
        };
        let classes: Vec<_> = source
            .signature(returns)
            .iter()
            .zip(kept)
            .filter(|&(_, &kept)| kept)
            .map(|(&class, _)| class)
            .collect();
        function.returns = Returns::Values(append_range(&mut declared.signature, &classes));
    }
    declared
}

struct Prune {
    read: Read,
    /// The function whose body is being rebuilt.
    function: FunctionId,
    /// Which results each `if` and loop being rebuilt keeps, innermost
    /// last: what a `yield` and a `break` in it still hand over.
    yields: Vec<Vec<bool>>,
    breaks: Vec<Vec<bool>>,
}

impl rewrite::Pass for Prune {
    fn op(
        &mut self,
        rebuild: &rewrite::Rebuild<'_>,
        b: &mut Builder,
        op: Op,
        results: &[ValueId],
    ) -> bool {
        // Writing nothing and saying nothing about the old results is how
        // an instruction goes away: nothing left reads them.
        if !self.read.wanted(rebuild.source(), &op, results) {
            return true;
        }
        match op {
            Op::If { .. } | Op::Loop { .. } => {
                self.container(rebuild, b, op, results);
                true
            }
            _ => self.call(rebuild, b, op, results),
        }
    }

    fn enter(
        &mut self,
        _: &rewrite::Rebuild<'_>,
        _: &mut Builder,
        function: FunctionId,
        params: &[ValueId],
    ) -> Vec<ValueId> {
        self.function = function;
        params.to_vec()
    }

    fn exit(
        &mut self,
        rebuild: &rewrite::Rebuild<'_>,
        b: &mut Builder,
        terminator: Terminator,
    ) -> bool {
        let kept = match terminator.exit {
            Exit::Return => &self.read.answered[self.function.index()],
            Exit::Yield => self.yields.last().expect("a yield within an if"),
            Exit::Break => self.breaks.last().expect("a break within a loop"),
            Exit::Continue => return false,
        };
        let values: Vec<_> = rebuild
            .source()
            .values(terminator.values)
            .iter()
            .zip(kept)
            .filter(|&(_, &kept)| kept)
            .map(|(&value, _)| rebuild.value(value))
            .collect();
        match terminator.exit {
            Exit::Return => b.ret(&values),
            Exit::Yield => b.yield_(&values),
            Exit::Break => b.break_(&values),
            Exit::Continue => unreachable!("a continue is copied"),
        }
        true
    }
}

impl Prune {
    /// An `if` or a loop, answering only the results something reads.
    fn container(
        &mut self,
        rebuild: &rewrite::Rebuild<'_>,
        b: &mut Builder,
        op: Op,
        results: &[ValueId],
    ) {
        let kept: Vec<_> = results
            .iter()
            .filter(|value| self.read.values[value.index()])
            .copied()
            .collect();
        let mask = self.read.read_of(results);
        let fresh = match op {
            Op::If {
                condition,
                then_region,
                else_region,
            } => {
                self.yields.push(mask);
                let fresh = rebuild.if_(
                    b,
                    rebuild.value(condition),
                    &kept,
                    then_region,
                    else_region,
                    self,
                );
                self.yields.pop();
                fresh
            }
            Op::Loop { initial, body } => {
                self.breaks.push(mask);
                let classes = rebuild.classes(&kept);
                let fresh = b.loop_(&rebuild.args(initial), &classes, |b, params| {
                    rebuild.region(b, body, params, self);
                });
                self.breaks.pop();
                fresh
            }
            _ => unreachable!("only an if or a loop holds regions"),
        };
        for (&was, now) in kept.iter().zip(fresh) {
            rebuild.stands_for(was, now);
        }
    }

    /// A call, answering only the results its function still answers.
    fn call(
        &self,
        rebuild: &rewrite::Rebuild<'_>,
        b: &mut Builder,
        op: Op,
        results: &[ValueId],
    ) -> bool {
        let Op::Call { function, args } = op else {
            return false;
        };
        let kept = &self.read.answered[function.index()];
        if kept.iter().all(|&kept| kept) {
            return false;
        }
        let answered = b.call(function, &rebuild.args(args));
        let old = results.iter().zip(kept).filter(|&(_, &kept)| kept);
        for ((&was, _), now) in old.zip(answered) {
            rebuild.stands_for(was, now);
        }
        true
    }
}

/// What a region's `yield` and `break` hand their values to: the results of
/// the `if` and the loop around it.
#[derive(Clone, Copy, Default)]
struct Handing<'a> {
    yields: &'a [ValueId],
    breaks: &'a [ValueId],
}

/// What a program reads, worked out by reading it backwards.
struct Read {
    values: Vec<bool>,
    regions: Vec<bool>,
    unread: Unread,
    /// For each function, which of its results it answers: every one of the
    /// entry's and an external's, and of the rest, those some call reads.
    answered: Vec<Vec<bool>>,
}

impl Read {
    /// Read the program until what it reads settles: a load that goes can
    /// be the only reader of a global, whose stores then go too, and a
    /// result no call reads is not returned, so what worked it out may go.
    /// Either may have been the only reason something else stayed. Each
    /// round reads no more than the last, so this stops.
    fn of(source: &Program) -> Self {
        let every = source
            .functions()
            .iter()
            .map(|function| vec![true; source.signature(function.returns.classes()).len()])
            .collect();
        let mut read = Self::with(source, Unread::of(source, None), every);
        loop {
            let unread = Unread::of(source, Some(&read));
            let answered = read.called(source);
            if unread.read == read.unread.read && answered == read.answered {
                return read;
            }
            read = Self::with(source, unread, answered);
        }
    }

    fn with(source: &Program, unread: Unread, answered: Vec<Vec<bool>>) -> Self {
        let mut held = Self {
            values: vec![false; source.values_count()],
            regions: vec![false; source.regions.len()],
            unread,
            answered,
        };
        for (id, function) in source.functions().iter().enumerate() {
            if let Some(body) = function.body() {
                held.region(source, FunctionId::at(id), body, Handing::default());
            }
        }
        held
    }

    /// Which results each function answers, given what this reading read:
    /// those a call kept reads, and all of the entry's and an external's.
    fn called(&self, source: &Program) -> Vec<Vec<bool>> {
        let mut answered: Vec<Vec<bool>> = source
            .functions()
            .iter()
            .enumerate()
            .map(|(id, function)| {
                let kept = id == 0 || function.body().is_none();
                vec![kept; self.answered[id].len()]
            })
            .collect();
        for body in source.functions().iter().filter_map(super::Function::body) {
            self.calls(source, body, &mut answered);
        }
        answered
    }

    /// Mark each result a kept call in `region` reads.
    fn calls(&self, source: &Program, region: RegionId, answered: &mut [Vec<bool>]) {
        for (op, results) in source.walk(region) {
            if !self.wanted(source, op, results) {
                continue;
            }
            match *op {
                Op::Call { function, .. } => {
                    let kept = &mut answered[function.index()];
                    for (at, value) in results.iter().enumerate() {
                        kept[at] |= self.values[value.index()];
                    }
                }
                Op::If {
                    then_region,
                    else_region,
                    ..
                } => {
                    self.calls(source, then_region, answered);
                    self.calls(source, else_region, answered);
                }
                Op::Loop { body, .. } => self.calls(source, body, answered),
                _ => {}
            }
        }
    }

    /// Whether an instruction is one the rebuild writes again.
    fn wanted(&self, source: &Program, op: &Op, results: &[ValueId]) -> bool {
        match *op {
            Op::Call { function, .. } if source.function(function).inert => {
                results.iter().any(|value| self.values[value.index()])
            }
            Op::Store { address, .. } => !self.unread.written_through(address),
            Op::Call { .. } => true,
            Op::If { then_region, .. } => self.regions[then_region.index()],
            Op::Loop { body, .. } => self.regions[body.index()],
            _ => results.iter().any(|value| self.values[value.index()]),
        }
    }

    /// Read one region backwards, which is the order a reader is known in:
    /// nothing names a value written after it, so by the time an
    /// instruction is reached, everything that could want it has spoken.
    fn region(
        &mut self,
        source: &Program,
        function: FunctionId,
        region: RegionId,
        handing: Handing<'_>,
    ) {
        self.regions[region.index()] = true;
        if let Some(terminator) = source.region(region).terminator {
            self.leaves(source, function, terminator, handing);
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
                    let arms = Handing {
                        yields: results,
                        breaks: handing.breaks,
                    };
                    self.region(source, function, then_region, arms);
                    self.region(source, function, else_region, arms);
                }
                Op::Loop { initial, body } => {
                    self.reads(source.values(initial));
                    let body_handing = Handing {
                        yields: &[],
                        breaks: results,
                    };
                    self.region(source, function, body, body_handing);
                }
                _ => self.reads(&operands(source, &op)),
            }
        }
    }

    /// Read what a region leaves with where what it becomes is read.
    fn leaves(
        &mut self,
        source: &Program,
        function: FunctionId,
        terminator: Terminator,
        handing: Handing<'_>,
    ) {
        let values = source.values(terminator.values);
        let kept: Vec<_> = match terminator.exit {
            Exit::Return => self.answered[function.index()].clone(),
            Exit::Yield => self.read_of(handing.yields),
            Exit::Break => self.read_of(handing.breaks),
            Exit::Continue => vec![true; values.len()],
        };
        for (&value, kept) in values.iter().zip(kept) {
            self.values[value.index()] |= kept;
        }
    }

    fn read_of(&self, values: &[ValueId]) -> Vec<bool> {
        values
            .iter()
            .map(|value| self.values[value.index()])
            .collect()
    }

    /// Whether this instruction stays. A container stays for what it holds
    /// as much as for what it answers: an arm that writes somewhere runs
    /// whether or not anybody wanted the answer.
    fn needed(&self, source: &Program, op: &Op, results: &[ValueId]) -> bool {
        let answered = || results.iter().any(|value| self.values[value.index()]);
        match *op {
            Op::Call { function, .. } if source.function(function).inert => answered(),
            Op::Store { address, .. } => !self.unread.written_through(address),
            Op::Call { .. } => true,
            Op::If {
                then_region,
                else_region,
                ..
            } => {
                answered()
                    || self.acts(source, then_region)
                    || self.acts(source, else_region)
                    || leaves(source, then_region)
                    || leaves(source, else_region)
            }
            Op::Loop { body, .. } => answered() || self.acts(source, body) || returns(source, body),
            _ => answered(),
        }
    }

    /// Whether anything in a region, or in a region within it, does something
    /// besides work out a value.
    fn acts(&self, source: &Program, region: RegionId) -> bool {
        source.every(region).any(|op| match *op {
            Op::Store { address, .. } => !self.unread.written_through(address),
            Op::Call { .. } => true,
            _ => false,
        })
    }

    fn reads(&mut self, values: &[ValueId]) {
        for value in values {
            self.values[value.index()] = true;
        }
    }
}

/// The globals nothing reads, and the addresses that name one.
///
/// A global is read when its address goes anywhere but the address of a
/// store: a load reads it, a call may, and an address kept or worked on may
/// be read through later. Only an address written as `address d` directly
/// is followed, so anything cleverer keeps its global. Given what an earlier
/// reading kept, only what it kept is asked.
struct Unread {
    /// The global each value is the address of, where it is one.
    address_of: Vec<Option<DataId>>,
    read: Vec<bool>,
}

impl Unread {
    fn of(source: &Program, kept: Option<&Read>) -> Self {
        let mut unread = Self {
            address_of: vec![None; source.values_count()],
            read: Vec::new(),
        };
        let bodies = || source.functions().iter().filter_map(super::Function::body);
        for body in bodies() {
            for (op, results) in source.walk_within(body) {
                if let Op::AddressOf(data) = *op {
                    unread.address_of[results[0].index()] = Some(data);
                    if unread.read.len() <= data.index() {
                        unread.read.resize(data.index() + 1, false);
                    }
                }
            }
        }
        for body in bodies() {
            unread.uses(source, body, kept);
        }
        unread
    }

    /// Mark every global an address in `region` reaches other than as where
    /// a store writes.
    fn uses(&mut self, source: &Program, region: RegionId, kept: Option<&Read>) {
        self.reads(source.outgoing(region));
        for (op, results) in source.walk(region) {
            if kept.is_some_and(|read| !read.wanted(source, op, results)) {
                continue;
            }
            match *op {
                Op::Store { value, .. } => self.reads(&[value]),
                Op::If {
                    condition,
                    then_region,
                    else_region,
                } => {
                    self.reads(&[condition]);
                    self.uses(source, then_region, kept);
                    self.uses(source, else_region, kept);
                }
                Op::Loop { initial, body } => {
                    self.reads(source.values(initial));
                    self.uses(source, body, kept);
                }
                _ => self.reads(&operands(source, op)),
            }
        }
    }

    fn reads(&mut self, values: &[ValueId]) {
        for value in values {
            if let Some(data) = self.address_of[value.index()] {
                self.read[data.index()] = true;
            }
        }
    }

    /// Whether a store to `address` writes a global nothing reads.
    fn written_through(&self, address: ValueId) -> bool {
        self.address_of[address.index()].is_some_and(|data| !self.read[data.index()])
    }
}

/// Whether control can leave a region other than by its answer: by a
/// `break` or `continue` of a loop around it, or by returning.
fn leaves(source: &Program, region: RegionId) -> bool {
    let held = source.region(region);
    if held
        .terminator
        .is_some_and(|terminator| terminator.exit != Exit::Yield)
    {
        return true;
    }
    source.walk(region).any(|(op, _)| match *op {
        Op::If {
            then_region,
            else_region,
            ..
        } => leaves(source, then_region) || leaves(source, else_region),
        // A loop's own `break` and `continue` stay within it.
        Op::Loop { body, .. } => returns(source, body),
        _ => false,
    })
}

/// Whether a region, or one within it, returns from its function.
fn returns(source: &Program, region: RegionId) -> bool {
    let held = source.region(region);
    if held
        .terminator
        .is_some_and(|terminator| terminator.exit == Exit::Return)
    {
        return true;
    }
    source.walk(region).any(|(op, _)| match *op {
        Op::If {
            then_region,
            else_region,
            ..
        } => returns(source, then_region) || returns(source, else_region),
        Op::Loop { body, .. } => returns(source, body),
        _ => false,
    })
}

/// What an instruction reads, for the ones that read a fixed few values.
/// Containers are handled where their regions are.
pub(super) fn operands(source: &Program, op: &Op) -> Vec<ValueId> {
    match *op {
        Op::Constant { .. } | Op::NaturalConstant(_) | Op::AddressOf(_) | Op::BufferEmpty => {
            Vec::new()
        }
        Op::Cell { fields, .. } => source.values(fields).to_vec(),
        Op::CellTag { cell } | Op::CellField { cell, .. } => vec![cell],
        Op::BufferPush {
            buffer,
            len,
            fields,
            ..
        } => {
            let mut read = vec![buffer, len];
            read.extend_from_slice(source.values(fields));
            read
        }
        Op::BufferPrepend {
            buffer,
            len,
            from,
            from_len,
            ..
        } => vec![buffer, len, from, from_len],
        Op::Binary { left, right, .. }
        | Op::Compare { left, right, .. }
        | Op::BufferField {
            buffer: left,
            len: right,
            ..
        } => vec![left, right],
        Op::Load { address, .. } => vec![address],
        Op::Store { address, value, .. } => vec![address, value],
        Op::Convert { value, .. } | Op::Shift { value, .. } => vec![value],
        Op::Call { args, .. } | Op::Float { operands: args, .. } => source.values(args).to_vec(),
        Op::If { condition, .. } => vec![condition],
        Op::Loop { initial, .. } => source.values(initial).to_vec(),
    }
}
