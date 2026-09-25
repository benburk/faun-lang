//! Target-sized representation and reference-count placement for managed values.
//!
//! Every local managed result owns a claim, and so do loop parameters and the
//! parameters [`super::ownership`] finds owned; the rest borrow. A claim is
//! released right after its value's last use in its region. A use that takes
//! a claim -- an exit, a cell field, a loop's initial state, a same-class
//! conversion, an owned parameter -- moves the value's own claim where that
//! use is its last and retains a new one otherwise. A value whose last use is
//! an `if` hands its claim to both arms, and each releases it at its own last
//! use. An exit releases whatever the scopes it leaves still hold.

use crate::index::Pool;
use std::{cell::Cell, collections::BTreeMap};

use num_bigint::BigUint;

use super::cell::{self, Library as CellLibrary};
use super::natural::{self, Config, Helper, Inline, Library, Needs};
use super::ownership::{self, Liveness, managed};
use super::sequence::{self, Library as SequenceLibrary};
use super::{
    Binary, Builder, Class, DataId, Definition, Exit, Op, Origin, Program, Range, RegionId,
    Relation, Terminator, ValueId, Width, validate,
};

/// Rebuild a validated program with naturals represented by immutable objects.
///
/// Existing data, globals, names and function IDs are preserved, including
/// external declarations.
/// Runtime helpers are appended and are not passed through ownership placement.
/// Programs needing no representation change take an unchanged clone fast path.
///
/// Serialized headers bind the output to a little-endian layout at
/// `config.word_bits`. Re-legalization, target acceptance and interpretation
/// check this obligation. Relative size checks do not prove complete target
/// image/pool/frame placement.
///
/// # Errors
/// Rejects invalid IR, unsupported host/address conversions, wide fixed-width
/// values, invalid runtime configuration, and constants exceeding the layout.
/// Wide `Fixed` remains unsupported: it is a fit assertion, not a modulus.
pub fn legalize(source: &Program, config: Config) -> Result<Program, String> {
    validate(source)?;
    if !matches!(config.word_bits, 16 | 32 | 64) {
        return Err("natural representation needs a 16, 32, or 64 bit word".into());
    }
    source.check_layout(config.layout())?;
    let needs = inspect(source, config)?;
    let has_naturals = holds(source, Class::Natural);
    let has_cells = holds(source, Class::Cell) || holds(source, Class::Buffer);
    if !has_naturals && !has_cells {
        return Ok(source.clone());
    }

    let mut output = skeleton(source);
    output.runtime_cells |= has_cells;
    output.runtime_naturals |= has_naturals;
    let library = natural::append(&mut output, config, needs)?;
    let (cells, sequences) = managed_runtime(&mut output, source, &library, config);
    let constants = constants(source, &mut output, config)?;
    let pass = Pass {
        source,
        library,
        cells,
        word_bytes: u64::from(config.word_bits / 8),
        word_bits: config.word_bits,
        sequences,
        constants,
        values: vec![Cell::new(None); source.values_count()],
        owned: ownership::owned_parameters(source),
    };
    pass.define_bodies(&mut output);
    validate(&output).map_err(|error| format!("after natural legalization: {error}"))?;
    Ok(output)
}

/// The cell and sequence routines a program needs, beside its naturals'.
/// A program holding buffers has cells' too, since a buffer may hold one.
fn managed_runtime(
    output: &mut Program,
    source: &Program,
    library: &Library,
    config: Config,
) -> (Option<CellLibrary>, Option<SequenceLibrary>) {
    let has_buffers = holds(source, Class::Buffer);
    let has_cells = holds(source, Class::Cell) || has_buffers;
    let buffers = has_buffers.then(|| sequence::declare(output));
    let cells = has_cells.then(|| cell::append(output, library, buffers, config.word_bits));
    let prepends = source
        .functions()
        .iter()
        .filter_map(super::Function::body)
        .flat_map(|body| source.walk_within(body))
        .any(|(op, _)| matches!(op, Op::BufferPrepend { .. }));
    let sequences = buffers.zip(cells).map(|(release, cells)| {
        sequence::append(
            output,
            release,
            library,
            cells,
            layouts(source),
            (config.word_bits, prepends),
        )
    });
    (cells, sequences)
}

/// Whether any value or signature in `source` is held at `class`.
fn holds(source: &Program, class: Class) -> bool {
    source.classes.as_slice().contains(&class) || source.signature.contains(&class)
}

fn skeleton(source: &Program) -> Program {
    // Copy only preserved pools. Value/instruction/region arenas are rebuilt,
    // so neither their contents nor their old capacity belongs in the skeleton.
    let mut output = Program {
        layout: source.layout,
        runtime_cells: source.runtime_cells,
        runtime_naturals: source.runtime_naturals,
        data: source.data.clone(),
        globals: source.globals.clone(),
        spans: source.spans.clone(),
        functions: source.functions.clone(),
        classes: Pool::default(),
        signature: source
            .signature
            .iter()
            .copied()
            .map(representation)
            .collect(),
        parameters: source.parameters.clone(),
        ops: Vec::new(),
        results: Vec::new(),
        operands: Vec::new(),
        regions: Pool::default(),
        names: source.names.clone(),
        symbols: source.symbols.clone(),
    };
    for id in output.functions.ids() {
        if output.functions[id].body().is_some() {
            let params = output.mint_from(output.functions[id].params);
            let body = output.regions.push(super::Region {
                params,
                ops: Range::EMPTY,
                terminator: None,
            });
            output.functions[id].definition = Definition::Declared(body);
        }
    }
    output
}

/// The innermost scope, which is the region being walked.
const fn top(scopes: &mut [Scope]) -> &mut Scope {
    scopes.last_mut().expect("a region being walked")
}

/// The leaf kinds of every element a program pushes onto a buffer, each once.
fn layouts(source: &Program) -> std::collections::BTreeSet<Vec<u64>> {
    source
        .functions()
        .iter()
        .filter_map(super::Function::body)
        .flat_map(|body| source.walk_within(body))
        .filter_map(|(op, _)| match *op {
            Op::BufferPush { fields, .. } => Some(
                source
                    .values(fields)
                    .iter()
                    .map(|&field| cell::kind(source.class(field)))
                    .collect(),
            ),
            _ => None,
        })
        .collect()
}

const fn representation(class: Class) -> Class {
    if matches!(class, Class::Cell | Class::Buffer | Class::Natural) {
        Class::Address
    } else {
        class
    }
}

fn check_classes(source: &Program, config: Config) -> Result<(), String> {
    for class in source.classes.iter().chain(&source.signature) {
        if let Some(bits) = class.width()
            && bits > config.word_bits
        {
            return Err(format!(
                "natural legalization does not yet support Fixed {{ bits: {bits} }} on a {} bit target",
                config.word_bits
            ));
        }
    }
    for function in source.functions().iter().filter(|f| f.external().is_some()) {
        for &class in source
            .signature(function.params)
            .iter()
            .chain(source.signature(function.returns.classes()))
        {
            match class {
                Class::Cell | Class::Buffer => {
                    return Err("host signatures containing cells have no aggregate ABI".into());
                }
                Class::Natural => {
                    return Err("host signatures containing naturals have no bigint ABI".into());
                }
                _ => {}
            }
        }
    }
    Ok(())
}

#[expect(
    clippy::too_many_lines,
    reason = "one scan collects natural helpers and checks each abstract cell operation"
)]
fn inspect(source: &Program, config: Config) -> Result<Needs, String> {
    check_classes(source, config)?;
    let mut needs = Needs::default();
    if [Class::Cell, Class::Buffer]
        .iter()
        .any(|class| source.classes.as_slice().contains(class) || source.signature.contains(class))
    {
        needs.insert(Helper::Allocate);
    }
    for body in source.functions().iter().filter_map(super::Function::body) {
        for (op, results) in source.walk_within(body) {
            match *op {
                Op::Binary { op, left, .. } if source.class(left) == Class::Natural => {
                    needs.insert(Helper::arithmetic(op));
                }
                Op::Compare { left, .. } if source.class(left) == Class::Natural => {
                    needs.insert(Helper::Compare);
                }
                Op::Convert { value } => match (source.class(value), source.class(results[0])) {
                    (Class::Address, Class::Natural) | (Class::Natural, Class::Address) => {
                        return Err(
                            "addresses cannot be reinterpreted as naturals or vice versa".into(),
                        );
                    }
                    (Class::Natural, Class::Natural) => {}
                    (_, Class::Natural) => needs.insert(Helper::FromWord),
                    (Class::Natural, _) => needs.insert(Helper::ToWord),
                    _ => {}
                },
                Op::Store { value, .. } if managed(source.class(value)) => {
                    return Err(
                        "storing a managed value has no scalar memory representation".into(),
                    );
                }
                Op::Cell { fields, .. } => {
                    let arity = source.values(fields).len();
                    let words = arity
                        .checked_mul(2)
                        .and_then(|n| n.checked_add(1))
                        .ok_or_else(|| "cell payload size overflow".to_owned())?;
                    let bytes = words
                        .checked_mul(usize::from(config.word_bits / 8))
                        .ok_or_else(|| "cell payload size overflow".to_owned())?;
                    if u64::try_from(bytes).is_err()
                        || i32::try_from(arity.saturating_mul(2).saturating_add(5)).is_err()
                    {
                        return Err("cell payload does not fit the target".into());
                    }
                }
                _ => {}
            }
        }
    }
    Ok(needs)
}

/// How a natural constant is held: as an immediate where it is small, and
/// otherwise as an immortal object in the data.
#[derive(Clone, Copy)]
enum Known {
    Small(u64),
    Object(DataId),
}

#[expect(
    clippy::too_many_lines,
    reason = "the walk, the small numbers and the interned objects stay together"
)]
fn constants(
    source: &Program,
    output: &mut Program,
    config: Config,
) -> Result<BTreeMap<ValueId, Known>, String> {
    let mut interned = BTreeMap::new();
    let mut constants = BTreeMap::new();
    let mut pending: Vec<_> = source
        .functions()
        .iter()
        .filter_map(super::Function::body)
        .collect();
    while let Some(region) = pending.pop() {
        for (op, results) in source.walk(region) {
            if let Op::If {
                then_region,
                else_region,
                ..
            } = *op
            {
                pending.extend([then_region, else_region]);
                continue;
            }
            if let Op::Loop { body, .. } = *op {
                pending.push(body);
                continue;
            }
            // Only what writes a value can be a number worth placing.
            let Some(magnitude) = results
                .first()
                .and_then(|&held| magnitude(source, *op, source.class(held)))
            else {
                continue;
            };
            let small = u64::try_from(&magnitude)
                .ok()
                .filter(|&n| n < natural::half(config.word_bits));
            let known = if let Some(n) = small {
                Known::Small(n)
            } else if let Some(&data) = interned.get(&magnitude) {
                Known::Object(data)
            } else {
                let data = natural::constant(output, config, &magnitude)?;
                interned.insert(magnitude, data);
                Known::Object(data)
            };
            constants.insert(results[0], known);
        }
    }
    Ok(constants)
}

fn magnitude(source: &Program, op: Op, class: Class) -> Option<BigUint> {
    match op {
        Op::Constant { value } if class == Class::Natural => Some(BigUint::from(value)),
        Op::NaturalConstant(data) => {
            let span = source.datum(data);
            let bytes = match span.origin {
                Origin::Data => source.data(),
                Origin::Globals => source.globals(),
            };
            let start = usize::try_from(span.start).expect("validated datum offset");
            let len = usize::try_from(span.len).expect("validated datum length");
            Some(BigUint::from_bytes_le(&bytes[start..start + len]))
        }
        _ => None,
    }
}

struct Pass<'a> {
    source: &'a Program,
    library: Library,
    cells: Option<CellLibrary>,
    sequences: Option<SequenceLibrary>,
    word_bytes: u64,
    word_bits: u16,
    constants: BTreeMap<ValueId, Known>,
    // Validation establishes globally unique SSA definitions and lexical use.
    // Mapping is monotonic across functions and sibling regions, not path-local.
    // Cells let the builder's two sequential branch callbacks share this table
    // without cloning it or borrowing a whole Pass mutably.
    values: Vec<Cell<Option<ValueId>>>,
    /// Which parameters of each function own a claim.
    owned: Vec<Vec<bool>>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ScopeKind {
    Ordinary,
    /// Parameters own the claims carried by this iteration.
    Loop,
}

/// The claims a region holds at one point of its walk, by source value.
#[derive(Clone)]
struct Scope {
    held: Vec<ValueId>,
    kind: ScopeKind,
}

impl Pass<'_> {
    /// Rebuild every function body into `output`.
    fn define_bodies(&self, output: &mut Program) {
        for (id, function) in self.source.functions.iter_enumerated() {
            let Some(body) = function.body() else {
                continue;
            };
            let held = self.owned_parameters(id, body);
            output.define(id, |b, params| {
                self.region(b, body, &mut Vec::new(), ScopeKind::Ordinary, params, held);
            });
        }
    }

    /// The parameters of a function's body that arrive holding a claim.
    fn owned_parameters(&self, id: super::FunctionId, body: RegionId) -> Vec<ValueId> {
        self.source
            .values(self.source.region(body).params)
            .iter()
            .zip(ownership::taken(&self.owned, id))
            .filter(|&(_, &owned)| owned)
            .map(|(&param, _)| param)
            .collect()
    }

    fn value(&self, old: ValueId) -> ValueId {
        self.values[old.index()]
            .get()
            .expect("validated SSA operand has been rebuilt")
    }

    fn mapped(&self, old: ValueId, new: ValueId) {
        assert!(
            self.values[old.index()].replace(Some(new)).is_none(),
            "each SSA definition is rebuilt once"
        );
    }

    fn retained(&self, b: &mut Builder, class: Class, value: ValueId) -> ValueId {
        let function = match class {
            Class::Natural => return self.library.retain_value(b, value),
            Class::Cell | Class::Buffer => self.cells.expect("cell helpers were requested").retain,
            _ => return value,
        };
        b.call_one(function, &[value])
    }

    fn release(&self, b: &mut Builder, class: Class, value: ValueId) {
        let function = match class {
            Class::Natural => return self.library.release_value(b, value),
            Class::Cell => self.cells.expect("cell helpers were requested").release,
            Class::Buffer => {
                self.sequences
                    .as_ref()
                    .expect("buffer helpers were requested")
                    .release
            }
            _ => return,
        };
        b.call(function, &[value]);
    }

    /// Build one object from fields whose claims it takes.
    fn construct_cell(
        &self,
        b: &mut Builder,
        tag: u32,
        fields: Range,
        claimed: &[ValueId],
    ) -> ValueId {
        let fields = self.source.values(fields);
        let payload_words = fields.len() * 2 + 1;
        let payload_bytes =
            u64::try_from(payload_words).expect("checked cell payload") * self.word_bytes;
        let library = self.cells.expect("cell helpers were requested");
        let bytes = b.constant(Class::Word, payload_bytes);
        let object = b.call_one(library.allocate, &[bytes]);
        let tag = b.constant(Class::Word, u64::from(tag));
        b.store(Width::Word, object, super::Offset::Words(2), tag);
        let arity = b.constant(
            Class::Word,
            u64::try_from(fields.len()).expect("checked cell arity"),
        );
        b.store(Width::Word, object, super::Offset::Words(3), arity);
        for (index, (&old, &value)) in fields.iter().zip(claimed).enumerate() {
            let kind = b.constant(Class::Word, cell::kind(self.source.class(old)));
            let at = i32::try_from(index * 2 + 4).expect("checked cell field offset");
            b.store(Width::Word, object, super::Offset::Words(at), kind);
            b.store(Width::Word, object, super::Offset::Words(at + 1), value);
        }
        object
    }

    /// Push one element, whose leaves' claims it takes, onto a buffer whose
    /// claim it takes: make room in front of the sequence, then write there.
    fn push(
        &self,
        b: &mut Builder,
        buffer: ValueId,
        len: ValueId,
        fields: Range,
        claimed: &[ValueId],
    ) -> ValueId {
        let kinds: Vec<_> = self
            .source
            .values(fields)
            .iter()
            .map(|&old| cell::kind(self.source.class(old)))
            .collect();
        let sequences = self
            .sequences
            .as_ref()
            .expect("buffer helpers were requested");
        let len = if b.class(len) == Class::Word {
            len
        } else {
            b.convert(Class::Word, len)
        };
        let room = sequences.room(b, &kinds, buffer, len);
        let capacity = b.load(Width::Word, room, super::Offset::Words(2));
        let one = b.constant(Class::Word, 1);
        let after = b.binary(Binary::Sub, capacity, len);
        let slot = b.binary(Binary::Sub, after, one);
        let stride = b.constant(Class::Word, sequence::count(kinds.len()));
        let first = sequence::element_word(b, stride, slot);
        for (leaf, &value) in claimed.iter().enumerate() {
            let leaf = b.constant(Class::Word, sequence::count(leaf));
            let at = b.binary(Binary::Add, first, leaf);
            let value = if matches!(b.class(value), Class::Word | Class::Address) {
                value
            } else {
                b.convert(Class::Word, value)
            };
            sequence::store_word(b, room, at, value, self.word_bits);
        }
        room
    }

    /// Read one leaf of a sequence's first element, holding a claim to it.
    fn buffer_field(
        &self,
        b: &mut Builder,
        old_result: ValueId,
        buffer: ValueId,
        len: ValueId,
        index: u32,
    ) -> ValueId {
        let capacity = b.load(Width::Word, buffer, super::Offset::Words(2));
        let stride = b.load(Width::Word, buffer, super::Offset::Words(4));
        let len = if b.class(len) == Class::Word {
            len
        } else {
            b.convert(Class::Word, len)
        };
        let element = b.binary(Binary::Sub, capacity, len);
        let first = sequence::element_word(b, stride, element);
        let leaf = b.constant(Class::Word, u64::from(index));
        let at = b.binary(Binary::Add, first, leaf);
        let value = sequence::load_word(b, buffer, at, self.word_bits);
        let class = self.source.class(old_result);
        let represented = representation(class);
        let value = if represented == Class::Word {
            value
        } else {
            b.convert(represented, value)
        };
        self.retained(b, class, value)
    }

    fn cell_field(
        &self,
        b: &mut Builder,
        old_result: ValueId,
        cell: ValueId,
        index: u32,
    ) -> ValueId {
        let index = usize::try_from(index).expect("checked cell field index");
        let at = i32::try_from(index * 2 + 5).expect("checked cell field offset");
        let value = b.load(Width::Word, self.value(cell), super::Offset::Words(at));
        let class = self.source.class(old_result);
        let represented = representation(class);
        let value = if represented == Class::Word {
            value
        } else {
            b.convert(represented, value)
        };
        self.retained(b, class, value)
    }

    /// Walk one region holding `held` on entry: claims handed down by an
    /// enclosing `if`, owned parameters, or a loop's carried state.
    fn region(
        &self,
        b: &mut Builder,
        region: RegionId,
        scopes: &mut Vec<Scope>,
        kind: ScopeKind,
        params: &[ValueId],
        held: Vec<ValueId>,
    ) {
        let old = self.source.region(region);
        for (&old, &new) in self.source.values(old.params).iter().zip(params) {
            self.mapped(old, new);
        }
        let live = Liveness::of(self.source, region);
        scopes.push(Scope { held, kind });
        self.release_dead(b, scopes, &live, None);
        for (at, (op, results)) in self.source.walk(region).enumerate() {
            let fresh = self.op(b, *op, results, scopes, &live, at);
            for (&old, new) in results.iter().zip(fresh) {
                self.mapped(old, new);
                if managed(self.source.class(old)) {
                    top(scopes).held.push(old);
                }
            }
            self.release_dead(b, scopes, &live, Some(at));
        }
        // Terminal child transfers already cleaned their scopes. A Never
        // call must not be followed by cleanup at this region's end.
        if let Some(terminator) = old.terminator {
            self.exit(b, scopes, terminator);
        }
        scopes.pop();
    }

    /// Release what the innermost scope holds and nothing reads from `at` on.
    fn release_dead(
        &self,
        b: &mut Builder,
        scopes: &mut [Scope],
        live: &Liveness,
        at: Option<usize>,
    ) {
        let scope = top(scopes);
        let (dead, kept): (Vec<_>, Vec<_>) =
            scope.held.iter().partition(|&&value| live.dead(value, at));
        scope.held = kept;
        for &value in dead.iter().rev() {
            self.release(b, self.source.class(value), self.value(value));
        }
    }

    /// A claim to `old` for a use at `at` that takes one: its own, where
    /// this region holds it and this is its only and last reading, and a
    /// new one otherwise.
    fn take(
        &self,
        b: &mut Builder,
        scopes: &mut [Scope],
        live: &Liveness,
        at: usize,
        old: ValueId,
    ) -> ValueId {
        let class = self.source.class(old);
        let scope = top(scopes);
        if managed(class)
            && live.only_last(old, at)
            && let Some(held) = scope.held.iter().position(|&value| value == old)
        {
            scope.held.remove(held);
            return self.value(old);
        }
        self.retained(b, class, self.value(old))
    }

    fn exit(&self, b: &mut Builder, scopes: &mut [Scope], terminator: Terminator) {
        let start = match terminator.exit {
            Exit::Return => 0,
            Exit::Yield => scopes.len() - 1,
            Exit::Break | Exit::Continue => scopes
                .iter()
                .rposition(|s| s.kind == ScopeKind::Loop)
                .expect("validated loop exit"),
        };
        let leaving = self.source.values(terminator.values);
        let outgoing: Vec<_> = leaving
            .iter()
            .map(|&old| {
                // Everything the exited scopes hold dies here, so a claim
                // one of them holds moves out, unless it leaves twice.
                let once = leaving.iter().filter(|&&value| value == old).count() == 1;
                let held = scopes[start..].iter_mut().find_map(|scope| {
                    let at = scope.held.iter().position(|&value| value == old)?;
                    Some((scope, at))
                });
                match held {
                    Some((scope, at)) if once => {
                        scope.held.remove(at);
                        self.value(old)
                    }
                    _ => self.retained(b, self.source.class(old), self.value(old)),
                }
            })
            .collect();
        for scope in scopes[start..].iter().rev() {
            for &value in scope.held.iter().rev() {
                self.release(b, self.source.class(value), self.value(value));
            }
        }
        match terminator.exit {
            Exit::Yield => b.yield_(&outgoing),
            Exit::Return => b.ret(&outgoing),
            Exit::Continue => b.continue_(&outgoing),
            Exit::Break => b.break_(&outgoing),
        }
    }

    #[expect(
        clippy::too_many_lines,
        reason = "exhaustive operation dispatch keeps scalar cloning beside each representation rewrite"
    )]
    fn op(
        &self,
        b: &mut Builder,
        op: Op,
        results: &[ValueId],
        scopes: &mut [Scope],
        live: &Liveness,
        at: usize,
    ) -> Vec<ValueId> {
        let v = |old| self.value(old);
        let classes = || {
            results
                .iter()
                .map(|&old| representation(self.source.class(old)))
                .collect::<Vec<_>>()
        };
        let one = match op {
            Op::Constant { .. } | Op::NaturalConstant(_)
                if self.source.class(results[0]) == Class::Natural =>
            {
                match self.constants[&results[0]] {
                    Known::Small(n) => self.library.small(b, n).expect("a small constant"),
                    Known::Object(data) => b.address_of(data),
                }
            }
            Op::Constant { value } => b.constant(self.source.class(results[0]), value),
            Op::NaturalConstant(data) => b.kept_natural(data),
            Op::AddressOf(data) => b.address_of(data),
            Op::Cell { tag, fields } => {
                let claimed: Vec<_> = self
                    .source
                    .values(fields)
                    .iter()
                    .map(|&old| self.take(b, scopes, live, at, old))
                    .collect();
                self.construct_cell(b, tag, fields, &claimed)
            }
            Op::CellTag { cell } => b.load(Width::Word, v(cell), super::Offset::Words(2)),
            Op::CellField { cell, index } => self.cell_field(b, results[0], cell, index),
            Op::BufferEmpty => {
                let library = self.cells.expect("cell helpers were requested");
                let none = b.constant(Class::Word, 0);
                sequence::allocate(b, library.allocate, &[], none, self.word_bytes)
            }
            Op::BufferPush {
                buffer,
                len,
                fields,
            } => {
                let buffer = self.take(b, scopes, live, at, buffer);
                let claimed: Vec<_> = self
                    .source
                    .values(fields)
                    .iter()
                    .map(|&old| self.take(b, scopes, live, at, old))
                    .collect();
                self.push(b, buffer, v(len), fields, &claimed)
            }
            Op::BufferPrepend {
                buffer,
                len,
                from,
                from_len,
                reversed,
            } => {
                let buffer = self.take(b, scopes, live, at, buffer);
                let word = |b: &mut Builder, len| {
                    if b.class(len) == Class::Word {
                        len
                    } else {
                        b.convert(Class::Word, len)
                    }
                };
                let (len, from_len) = (word(b, v(len)), word(b, v(from_len)));
                let routine = self
                    .sequences
                    .as_ref()
                    .expect("buffer helpers were requested")
                    .prepend(reversed);
                b.call_one(routine, &[buffer, len, v(from), from_len])
            }
            Op::BufferField { buffer, len, index } => {
                self.buffer_field(b, results[0], v(buffer), v(len), index)
            }
            Op::Binary { op, left, right } if self.source.class(left) == Class::Natural => match op
            {
                Binary::Add => self.library.inline(b, Inline::Add, v(left), v(right)),
                Binary::Sub | Binary::Monus => {
                    self.library.inline(b, Inline::Monus, v(left), v(right))
                }
                _ => {
                    let function = self.library.require(Helper::arithmetic(op));
                    b.call_one(function, &[v(left), v(right)])
                }
            },
            Op::Binary { op, left, right } => {
                b.binary_at(self.source.class(results[0]), op, v(left), v(right))
            }
            // A shift is never over a natural, so there is no helper for it
            // and nothing to choose between here.
            Op::Shift {
                direction,
                value,
                by,
            } => b.shift(self.source.class(results[0]), direction, v(value), by),
            Op::Compare {
                relation,
                left,
                right,
            } if self.source.class(left) == Class::Natural => {
                let ordering = self.library.inline(b, Inline::Compare, v(left), v(right));
                let wanted = b.constant(Class::Word, u64::from(relation == Relation::Equal));
                b.compare(Relation::Equal, ordering, wanted)
            }
            Op::Compare {
                relation,
                left,
                right,
            } => b.compare(relation, v(left), v(right)),
            Op::Convert { value } => {
                let class = self.source.class(results[0]);
                match (self.source.class(value), class) {
                    (Class::Natural, Class::Natural) | (Class::Cell, Class::Cell) => {
                        self.take(b, scopes, live, at, value)
                    }
                    (_, Class::Natural) => {
                        b.call_one(self.library.require(Helper::FromWord), &[v(value)])
                    }
                    (Class::Natural, _) => {
                        let word = b.call_one(self.library.require(Helper::ToWord), &[v(value)]);
                        if class == Class::Word {
                            word
                        } else {
                            b.convert(class, word)
                        }
                    }
                    _ => b.convert(class, v(value)),
                }
            }
            Op::Load {
                width,
                address,
                offset,
            } => b.load(width, v(address), offset),
            Op::Store {
                width,
                address,
                offset,
                value,
            } => {
                b.store(width, v(address), offset, v(value));
                return Vec::new();
            }
            Op::Call {
                function,
                args: held,
            } => {
                let owned = ownership::taken(&self.owned, function);
                let args: Vec<_> = self
                    .source
                    .values(held)
                    .iter()
                    .zip(owned)
                    .map(|(&old, &owned)| {
                        if owned {
                            self.take(b, scopes, live, at, old)
                        } else {
                            v(old)
                        }
                    })
                    .collect();
                return b.call(function, &args);
            }
            Op::If {
                condition,
                then_region,
                else_region,
            } => {
                // What this region holds and reads last here is each arm's
                // to release, where that arm last reads it.
                let scope = top(scopes);
                let (handed, kept): (Vec<_>, Vec<_>) = scope
                    .held
                    .iter()
                    .partition(|&&value| live.dead(value, Some(at)));
                scope.held = kept;
                let arms: &[Scope] = scopes;
                return b.if_(
                    v(condition),
                    &classes(),
                    |b| {
                        let mut scopes = arms.to_vec();
                        let kind = ScopeKind::Ordinary;
                        self.region(b, then_region, &mut scopes, kind, &[], handed.clone());
                    },
                    |b| {
                        let mut scopes = arms.to_vec();
                        let kind = ScopeKind::Ordinary;
                        self.region(b, else_region, &mut scopes, kind, &[], handed.clone());
                    },
                );
            }
            Op::Loop { initial, body } => {
                let carried: Vec<_> = self
                    .source
                    .values(self.source.region(body).params)
                    .iter()
                    .copied()
                    .filter(|&param| managed(self.source.class(param)))
                    .collect();
                let initial: Vec<_> = self
                    .source
                    .values(initial)
                    .iter()
                    .zip(self.source.values(self.source.region(body).params))
                    .map(|(&old, &parameter)| {
                        let value = self.take(b, scopes, live, at, old);
                        // Builder derives loop parameter classes from initial
                        // values. Valid IR may initialize a wider carried slot
                        // from a narrower scalar, so preserve the declared slot.
                        let class = representation(self.source.class(parameter));
                        if b.class(value) == class {
                            value
                        } else {
                            b.convert(class, value)
                        }
                    })
                    .collect();
                let outer: &[Scope] = scopes;
                return b.loop_(&initial, &classes(), |b, params| {
                    let mut scopes = outer.to_vec();
                    self.region(b, body, &mut scopes, ScopeKind::Loop, params, carried);
                });
            }
        };
        vec![one]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn source() -> Program {
        let (mut p, main) = Program::new("main");
        p.intern(b"unaligned data");
        p.global(&[1, 2, 3]);
        crate::platform::Routines::builtin().declare(&mut p, "write!");
        p.symbol("unused name");
        let identity = p.declare("identity", &[Class::Natural], &[Class::Natural]);
        p.define(identity, |b, args| b.ret(&[args[0]]));
        p.define(main, |b, _| {
            let value = b.constant(Class::Natural, 7);
            let value = b.call_one(identity, &[value]);
            let value = b.convert(Class::Word, value);
            b.ret(&[value]);
        });
        p.bind_layout(
            Config {
                word_bits: 64,
                heap_bytes: 256,
                grows: false,
            }
            .layout(),
        )
        .unwrap();
        validate(&p).unwrap();
        p
    }

    #[test]
    fn skeleton_keeps_metadata_but_does_not_clone_discarded_instruction_storage() {
        let p = source();
        let out = skeleton(&p);
        assert_eq!(out.layout, p.layout);
        assert_eq!(out.names, p.names);
        assert_eq!(out.symbols, p.symbols);
        assert_eq!(out.data, p.data);
        assert_eq!(out.globals, p.globals);
        assert_eq!(out.spans, p.spans);
        assert_eq!(
            out.functions
                .iter()
                .filter_map(super::super::Function::external)
                .collect::<Vec<_>>(),
            p.functions
                .iter()
                .filter_map(super::super::Function::external)
                .collect::<Vec<_>>()
        );
        assert_eq!(
            out.signature[..p.signature.len()],
            p.signature
                .iter()
                .copied()
                .map(representation)
                .collect::<Vec<_>>()
        );
        assert!(!p.ops.is_empty());
        assert!(!p.results.is_empty());
        assert_eq!(out.ops.capacity(), 0);
        assert_eq!(out.results.capacity(), 0);
        assert!(out.regions.iter().all(|r| r.ops.is_empty()));
    }

    #[test]
    fn skeleton_preserves_function_ids_and_rebuilds_parameter_and_result_classes() {
        let p = source();
        let out = skeleton(&p);
        assert_eq!(out.functions.len(), p.functions.len());
        for (before, after) in p.functions.iter().zip(&out.functions) {
            assert_eq!(before.name, after.name);
            assert_eq!(
                p.signature(before.params)
                    .iter()
                    .copied()
                    .map(representation)
                    .collect::<Vec<_>>(),
                out.signature(after.params)
            );
            assert_eq!(
                p.signature(before.returns.classes())
                    .iter()
                    .copied()
                    .map(representation)
                    .collect::<Vec<_>>(),
                out.signature(after.returns.classes())
            );
        }
    }
}
