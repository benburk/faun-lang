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
//! What no instruction left names any more is dropped from the data and
//! globals too, so an image carries only what the program reaches.

use super::{DataId, Exit, Op, Origin, Program, RegionId, ValueId, rewrite};

/// Rebuild `source` without the instructions nothing reads.
#[must_use]
pub(super) fn prune(source: &Program) -> Program {
    let mut pass = Prune {
        read: Read::of(source),
    };
    let mut pruned = rewrite::rebuild(source, &mut pass);
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

struct Prune {
    read: Read,
}

impl rewrite::Pass for Prune {
    fn op(
        &mut self,
        rebuild: &rewrite::Rebuild<'_>,
        _: &mut super::Builder,
        op: Op,
        results: &[ValueId],
    ) -> bool {
        // Writing nothing and saying nothing about the old results is how
        // an instruction goes away: nothing left reads them.
        !self.read.wanted(rebuild.source(), &op, results)
    }
}

/// What a program reads, worked out by reading it backwards.
struct Read {
    values: Vec<bool>,
    regions: Vec<bool>,
    unread: Unread,
}

impl Read {
    /// Read the program until what it reads settles: a load that goes can
    /// be the only reader of a global, whose stores then go too, and what
    /// they stored may have been the only reason something else stayed.
    /// Each round reads no more than the last, so this stops.
    fn of(source: &Program) -> Self {
        let mut read = Self::with(source, Unread::of(source, None));
        loop {
            let unread = Unread::of(source, Some(&read));
            if unread.read == read.unread.read {
                return read;
            }
            read = Self::with(source, unread);
        }
    }

    fn with(source: &Program, unread: Unread) -> Self {
        let mut held = Self {
            values: vec![false; source.values_count()],
            regions: vec![false; source.regions.len()],
            unread,
        };
        for function in source.functions() {
            if let Some(body) = function.body() {
                held.region(source, body);
            }
        }
        held
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
