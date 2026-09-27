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
use super::packing::Packed;
use super::sequence::{self, Growth, Library as SequenceLibrary};
use super::{
    Binary, Builder, Class, DataId, Definition, Exit, Offset, Op, Origin, Program, Range, RegionId,
    Relation, ShapeId, Terminator, ValueId, Width, validate,
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
/// Rejects invalid IR, unsupported host/address conversions, fixed widths
/// wider than the word, invalid runtime configuration, and constants
/// exceeding the layout. A fixed width wider than the word is held as words,
/// which [`super::split`] makes it before this runs.
pub fn legalize(source: &Program, config: Config) -> Result<Program, String> {
    validate(source)?;
    if !matches!(config.word_bits, 16 | 32 | 64) {
        return Err("natural representation needs a 16, 32, or 64 bit word".into());
    }
    source.check_layout(config.layout())?;
    let divisors = word_divisors(source, config.word_bits);
    let needs = inspect(source, config, &divisors)?;
    let has_naturals = holds(source, Class::Natural);
    let has_cells = holds(source, Class::Cell) || holds(source, Class::Buffer);
    if !has_naturals && !has_cells {
        return Ok(source.clone());
    }

    let mut output = skeleton(source);
    output.runtime_cells |= has_cells;
    output.runtime_naturals |= has_naturals;
    let library = natural::append(&mut output, config, needs)?;
    let shapes = Shapes::of(source, &mut output, config.word_bits)?;
    let (cells, sequences) = managed_runtime(&mut output, source, &library, (config, &shapes));
    let constants = constants(source, &mut output, config)?;
    let pass = Pass {
        source,
        library,
        cells,
        shapes,
        word_bytes: u64::from(config.word_bits / 8),
        sequences,
        constants,
        divisors,
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
    (config, shapes): (Config, &Shapes),
) -> (Option<CellLibrary>, Option<SequenceLibrary>) {
    let has_buffers = holds(source, Class::Buffer);
    let has_cells = holds(source, Class::Cell) || has_buffers;
    let buffers = has_buffers.then(|| sequence::declare(output));
    let cells = has_cells.then(|| cell::append(output, library, buffers, config.word_bits));
    let sequences = buffers.zip(cells).map(|(release, cells)| {
        sequence::append(
            output,
            release,
            library,
            cells,
            growths(source).into_iter().map(|(growth, shape)| {
                (
                    growth,
                    shapes.packed[shape.index()].clone(),
                    shapes.descriptors[shape.index()],
                )
            }),
            config.word_bits,
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
        shapes: source.shapes.clone(),
        shaped: source.shaped.clone(),
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

/// An empty buffer of elements of `packed`, as the data holds it: an
/// immortal count, room for nothing, claims for nothing, and its stride. It
/// names no descriptor, since it holds nothing a descriptor would describe.
fn empty(packed: &Packed, word_bits: u16) -> Vec<u8> {
    known(packed, &[], word_bits)
}

/// A buffer laid out before the program runs, holding one element per byte
/// of `elements`, each that value in the element's one leaf: immortal, so
/// nothing writes it or frees it, as [`sequence`] lays out any buffer.
fn known(packed: &Packed, elements: &[u8], word_bits: u16) -> Vec<u8> {
    let word = usize::from(word_bits / 8);
    let immortal = u64::MAX >> (64 - word_bits);
    let count = u64::try_from(elements.len()).expect("a count fits 64 bits");
    let mut bytes: Vec<u8> = [0, immortal, count, 0, count, packed.size, 0]
        .iter()
        .flat_map(|value: &u64| value.to_le_bytes()[..word].to_vec())
        .collect();
    let stride = usize::try_from(packed.size).expect("a stride fits the host");
    let leaf = packed.leaves[..].first();
    for &element in elements {
        let mut laid = vec![0; stride];
        if let Some(&super::packing::Leaf {
            offset,
            width: Some(width),
            ..
        }) = leaf
        {
            let offset = usize::try_from(offset).expect("an offset fits the host");
            let width = usize::from(width.bytes(word_bits));
            laid[offset..offset + width]
                .copy_from_slice(&u64::from(element).to_le_bytes()[..width]);
        }
        bytes.extend_from_slice(&laid);
    }
    bytes
}

/// A count as a word, however narrow it was held.
fn word(b: &mut Builder, value: ValueId) -> ValueId {
    if b.class(value) == Class::Word {
        value
    } else {
        b.convert(Class::Word, value)
    }
}

/// The innermost scope, which is the region being walked.
const fn top(scopes: &mut [Scope]) -> &mut Scope {
    scopes.last_mut().expect("a region being walked")
}

/// Each way a program grows a sequence, and the shape of its elements, each
/// once.
fn growths(source: &Program) -> std::collections::BTreeSet<(Growth, ShapeId)> {
    shapes_of(source, |op| match op {
        Op::BufferPush { shape, .. } => Some((Growth::Push, shape)),
        Op::BufferPrepend { shape, .. } => Some((Growth::Prepend, shape)),
        Op::BufferExtend { shape, .. } => Some((Growth::Extend, shape)),
        _ => None,
    })
}

/// What `wanted` says of each instruction a program holds, each once.
fn shapes_of<T: Ord>(
    source: &Program,
    wanted: impl Fn(Op) -> Option<T>,
) -> std::collections::BTreeSet<T> {
    source
        .functions()
        .iter()
        .filter_map(super::Function::body)
        .flat_map(|body| source.walk_within(body))
        .filter_map(|(op, _)| wanted(*op))
        .collect()
}

/// Each known buffer a program makes, by its elements and shape, and where
/// it lies laid out.
type Knowns = BTreeMap<(DataId, ShapeId), DataId>;

/// The buffers a program knows before it runs, in the output's data: an
/// empty one of each shape it makes one of, and each known one it makes.
fn laid_out(
    source: &Program,
    output: &mut Program,
    packed: &[Packed],
    word_bits: u16,
) -> (Vec<Option<DataId>>, Knowns) {
    let made = shapes_of(source, |op| match op {
        Op::BufferEmpty { shape } => Some(shape),
        _ => None,
    });
    let empties = (0..packed.len())
        .map(|at| {
            made.contains(&ShapeId::at(at))
                .then(|| output.intern(&empty(&packed[at], word_bits)))
        })
        .collect();
    let knowns = shapes_of(source, |op| match op {
        Op::BufferKnown { elements, shape } => Some((elements, shape)),
        _ => None,
    })
    .into_iter()
    .map(|(elements, shape)| {
        let laid = known(
            &packed[shape.index()],
            source.datum_bytes(elements),
            word_bits,
        );
        ((elements, shape), output.intern(&laid))
    })
    .collect();
    (empties, knowns)
}

/// Every shape a program holds laid out, and the descriptor of each whose
/// leaves hold a claim, in the data.
struct Shapes {
    packed: Vec<Packed>,
    descriptors: Vec<Option<DataId>>,
    /// An empty buffer of each shape a program makes one of, in the data:
    /// immortal, so nothing ever writes it or frees it, and whatever is
    /// first put in it makes a buffer of its own.
    empties: Vec<Option<DataId>>,
    /// Each known buffer the program makes, of each shape, laid out.
    knowns: Knowns,
}

impl Shapes {
    fn of(source: &Program, output: &mut Program, word_bits: u16) -> Result<Self, String> {
        let packed: Vec<_> = source
            .shape_ids()
            .map(|shape| Packed::of(source.shaped(shape), word_bits))
            .collect();
        // What any object holds lies past a header of six words at most,
        // and what a target reaches from an address is an `i32` away.
        let header = 6 * u64::from(word_bits / 8);
        if packed
            .iter()
            .any(|packed| i32::try_from(packed.size + header).is_err())
        {
            return Err("an object's fields do not fit the target".into());
        }
        let descriptors = packed
            .iter()
            .map(|packed| {
                packed
                    .descriptor(word_bits)
                    .map(|bytes: Vec<u8>| output.intern(&bytes))
            })
            .collect();
        let (empties, knowns) = laid_out(source, output, &packed, word_bits);
        Ok(Self {
            packed,
            descriptors,
            empties,
            knowns,
        })
    }

    /// Where the known buffer of `elements`, each of `shape`, lies.
    fn known(&self, b: &mut Builder, elements: DataId, shape: ShapeId) -> ValueId {
        b.address_of(self.knowns[&(elements, shape)])
    }

    /// Where the empty buffer of `shape` lies.
    fn empty(&self, b: &mut Builder, shape: ShapeId) -> ValueId {
        let data = self.empties[shape.index()].expect("the program makes an empty buffer");
        b.address_of(data)
    }

    fn packed(&self, shape: ShapeId) -> &Packed {
        &self.packed[shape.index()]
    }

    /// Where `shape`'s descriptor lies, as a word, or nought where it has
    /// none.
    fn descriptor(&self, b: &mut Builder, shape: ShapeId) -> ValueId {
        match self.descriptors[shape.index()] {
            Some(data) => {
                let at = b.address_of(data);
                b.convert(Class::Word, at)
            }
            None => b.constant(Class::Word, 0),
        }
    }
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
                "a {bits}-bit number is held as words on a {}-bit target, which splitting does first",
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

/// A natural divisor known to fit a word, so that dividing by it is short
/// division: as the scalar it was converted from, or as a constant.
#[derive(Clone, Copy)]
enum Divisor {
    Scalar(ValueId),
    Constant(u64),
}

/// Every natural a program makes from a scalar or knows as a word-sized
/// constant, by the value that is it.
fn word_divisors(source: &Program, word_bits: u16) -> BTreeMap<ValueId, Divisor> {
    let mut divisors = BTreeMap::new();
    for body in source.functions().iter().filter_map(super::Function::body) {
        for (op, results) in source.walk_within(body) {
            let [result] = results[..] else {
                continue;
            };
            if source.class(result) != Class::Natural {
                continue;
            }
            match *op {
                Op::Convert { value }
                    if matches!(source.class(value), Class::Word | Class::Held(_)) =>
                {
                    divisors.insert(result, Divisor::Scalar(value));
                }
                Op::Constant { value } if value >> (word_bits - 1) >> 1 == 0 => {
                    divisors.insert(result, Divisor::Constant(value));
                }
                _ => {}
            }
        }
    }
    divisors
}

/// The helper a natural operation calls: one dividing by a word where the
/// divisor is known to be one.
fn helper_for(op: Binary, right: ValueId, divisors: &BTreeMap<ValueId, Divisor>) -> Helper {
    match op {
        Binary::Div if divisors.contains_key(&right) => Helper::DivWord,
        Binary::Mod if divisors.contains_key(&right) => Helper::ModWord,
        _ => Helper::arithmetic(op),
    }
}

fn inspect(
    source: &Program,
    config: Config,
    divisors: &BTreeMap<ValueId, Divisor>,
) -> Result<Needs, String> {
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
                Op::Binary { op, left, right } if source.class(left) == Class::Natural => {
                    needs.insert(helper_for(op, right, divisors));
                }
                Op::Compare { left, .. } if source.class(left) == Class::Natural => {
                    needs.insert(Helper::Compare);
                }
                Op::Convert { value } => {
                    let classes = (source.class(value), source.class(results[0]));
                    if let Some(helper) = conversion(classes, config.word_bits)? {
                        needs.insert(helper);
                    }
                }
                Op::Store { value, .. } if managed(source.class(value)) => {
                    return Err(
                        "storing a managed value has no scalar memory representation".into(),
                    );
                }
                _ => {}
            }
        }
    }
    Ok(needs)
}

/// The helper converting a value of one class to another asks for, if any.
fn conversion(classes: (Class, Class), word_bits: u16) -> Result<Option<Helper>, String> {
    Ok(match classes {
        (Class::Address, Class::Natural) | (Class::Natural, Class::Address) => {
            return Err("addresses cannot be reinterpreted as naturals or vice versa".into());
        }
        (Class::Natural, Class::Natural) => None,
        (from, Class::Natural) if !always_small(from, word_bits) => Some(Helper::FromWord),
        (Class::Natural, _) => Some(Helper::ToWord),
        _ => None,
    })
}

/// Whether every number of `class` is below half a word, and so is held as
/// a natural without asking whether it is an object.
fn always_small(class: Class, word_bits: u16) -> bool {
    matches!(class, Class::Held(_)) && class.width().is_some_and(|bits| bits < word_bits)
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
    shapes: Shapes,
    sequences: Option<SequenceLibrary>,
    word_bytes: u64,
    constants: BTreeMap<ValueId, Known>,
    divisors: BTreeMap<ValueId, Divisor>,
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
    fn word_bits(&self) -> u16 {
        u16::try_from(self.word_bytes * 8).expect("a word's bits fit u16")
    }

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
        shape: ShapeId,
        claimed: &[ValueId],
    ) -> ValueId {
        let packed = self.shapes.packed(shape);
        let library = self.cells.expect("cell helpers were requested");
        // The descriptor's word, then the fields.
        let bytes = b.constant(Class::Word, self.word_bytes + packed.size);
        let object = b.call_one(library.allocate, &[bytes]);
        let tag = b.constant(Class::Word, u64::from(tag));
        b.store(Width::Word, object, Offset::Words(cell::TAG), tag);
        let descriptor = self.shapes.descriptor(b, shape);
        b.store(
            Width::Word,
            object,
            Offset::Words(cell::DESCRIPTOR),
            descriptor,
        );
        let fields = self.fields_at();
        Self::store_leaves(b, (object, fields), packed, claimed);
        object
    }

    /// Where an object's fields begin, in bytes from its start.
    fn fields_at(&self) -> u64 {
        self.word_bytes * u64::from(cell::FIELDS.unsigned_abs())
    }

    /// Store each leaf of `packed` from `values`, the first `at` bytes past
    /// `object`.
    fn store_leaves(
        b: &mut Builder,
        (object, at): (ValueId, u64),
        packed: &Packed,
        values: &[ValueId],
    ) {
        for (leaf, &value) in packed.leaves.iter().zip(values) {
            let Some(width) = leaf.width else {
                continue;
            };
            let offset = i32::try_from(at + leaf.offset).expect("checked object layout");
            b.store(width, object, Offset::Bytes(offset), value);
        }
    }

    /// Load leaf `index` of `packed`, the first `at` bytes past `object`,
    /// as `old_result` is read, holding a claim to it.
    fn load_leaf(
        &self,
        b: &mut Builder,
        old_result: ValueId,
        (object, at): (ValueId, u64),
        (packed, index): (&Packed, u32),
    ) -> ValueId {
        let leaf = packed.leaves[usize::try_from(index).expect("checked leaf index")];
        let class = self.source.class(old_result);
        let represented = representation(class);
        let Some(width) = leaf.width else {
            // What takes no room can only be nought.
            return b.constant(represented, 0);
        };
        let offset = i32::try_from(at + leaf.offset).expect("checked object layout");
        let value = b.load(width, object, Offset::Bytes(offset));
        let value = if represented == Class::Word {
            value
        } else {
            b.convert(represented, value)
        };
        self.retained(b, class, value)
    }

    /// Push one element, whose leaves' claims it takes, onto a sequence
    /// whose buffer's claim it takes: make room in front of the sequence,
    /// then write there. The buffer and where the longer sequence starts.
    fn push(
        &self,
        b: &mut Builder,
        sequence: (ValueId, ValueId, ValueId),
        shape: ShapeId,
        claimed: &[ValueId],
    ) -> [ValueId; 2] {
        let packed = self.shapes.packed(shape);
        let sequences = self
            .sequences
            .as_ref()
            .expect("buffer helpers were requested");
        let [room, front] = sequences.room(b, packed, sequence);
        let element = sequences.element(b, room, packed.size, front);
        Self::store_leaves(b, (element, 0), packed, claimed);
        [room, front]
    }

    /// Read one leaf of element `start` of a buffer, holding a claim to it.
    fn buffer_field(
        &self,
        b: &mut Builder,
        old_result: ValueId,
        (buffer, start): (ValueId, ValueId),
        (shape, index): (ShapeId, u32),
    ) -> ValueId {
        let packed = self.shapes.packed(shape);
        let sequences = self
            .sequences
            .as_ref()
            .expect("buffer helpers were requested");
        let start = word(b, start);
        let element = sequences.element(b, buffer, packed.size, start);
        self.load_leaf(b, old_result, (element, 0), (packed, index))
    }

    fn cell_field(
        &self,
        b: &mut Builder,
        old_result: ValueId,
        cell: ValueId,
        (shape, index): (ShapeId, u32),
    ) -> ValueId {
        let packed = self.shapes.packed(shape);
        let fields = self.fields_at();
        self.load_leaf(b, old_result, (self.value(cell), fields), (packed, index))
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
            Op::Cell { tag, fields, shape } => {
                let claimed: Vec<_> = self
                    .source
                    .values(fields)
                    .iter()
                    .map(|&old| self.take(b, scopes, live, at, old))
                    .collect();
                self.construct_cell(b, tag, shape, &claimed)
            }
            Op::CellTag { cell } => b.load(Width::Word, v(cell), Offset::Words(cell::TAG)),
            Op::CellField { cell, index, shape } => {
                self.cell_field(b, results[0], cell, (shape, index))
            }
            Op::BufferEmpty { shape } => self.shapes.empty(b, shape),
            Op::BufferKnown { elements, shape } => self.shapes.known(b, elements, shape),
            Op::BufferRoom { count, shape } => {
                let library = self.cells.expect("cell helpers were requested");
                let stride = b.constant(Class::Word, self.shapes.packed(shape).size);
                let none = b.constant(Class::Word, 0);
                let count = word(b, v(count));
                sequence::allocate(b, library.allocate, (stride, none), count, self.word_bytes)
            }
            Op::BufferAt {
                buffer,
                start,
                shape,
            } => {
                let start = word(b, v(start));
                self.sequences
                    .as_ref()
                    .expect("buffer helpers were requested")
                    .element(b, v(buffer), self.shapes.packed(shape).size, start)
            }
            // What it holds is released after it, as after any last use.
            Op::Keep { .. } => return Vec::new(),
            Op::BufferPush { operands, shape } => {
                let operands = self.source.values(operands);
                let buffer = self.take(b, scopes, live, at, operands[0]);
                let (start, len) = (word(b, v(operands[1])), word(b, v(operands[2])));
                let claimed: Vec<_> = operands[3..]
                    .iter()
                    .map(|&old| self.take(b, scopes, live, at, old))
                    .collect();
                return self.push(b, (buffer, start, len), shape, &claimed).to_vec();
            }
            Op::BufferPrepend { operands, shape } => {
                let operands = self.source.values(operands);
                let buffer = self.take(b, scopes, live, at, operands[0]);
                let [start, len, from_start, count] =
                    [1, 2, 4, 5].map(|at| word(b, v(operands[at])));
                return self
                    .sequences
                    .as_ref()
                    .expect("buffer helpers were requested")
                    .prepend(
                        b,
                        self.shapes.packed(shape),
                        (buffer, start, len),
                        (v(operands[3]), from_start, count),
                    )
                    .to_vec();
            }
            Op::BufferExtend { operands, shape } => {
                let operands = self.source.values(operands);
                let first = self.take(b, scopes, live, at, operands[0]);
                let then = self.take(b, scopes, live, at, operands[3]);
                let [first_start, first_len, then_start, then_len] =
                    [1, 2, 4, 5].map(|at| word(b, v(operands[at])));
                return self
                    .sequences
                    .as_ref()
                    .expect("buffer helpers were requested")
                    .extend(
                        b,
                        self.shapes.packed(shape),
                        (first, first_start, first_len),
                        (then, then_start, then_len),
                    )
                    .to_vec();
            }
            Op::BufferField {
                buffer,
                start,
                index,
                shape,
            } => self.buffer_field(b, results[0], (v(buffer), v(start)), (shape, index)),
            Op::Binary { op, left, right } if self.source.class(left) == Class::Natural => match op
            {
                Binary::Add => self.library.inline(b, Inline::Add, v(left), v(right)),
                Binary::Sub | Binary::Monus => {
                    self.library.inline(b, Inline::Monus, v(left), v(right))
                }
                _ => {
                    let function = self.library.require(helper_for(op, right, &self.divisors));
                    let divisor = match self.divisors.get(&right) {
                        Some(&Divisor::Scalar(value))
                            if matches!(op, Binary::Div | Binary::Mod) =>
                        {
                            word(b, v(value))
                        }
                        Some(&Divisor::Constant(value))
                            if matches!(op, Binary::Div | Binary::Mod) =>
                        {
                            b.constant(Class::Word, value)
                        }
                        _ => v(right),
                    };
                    b.call_one(function, &[v(left), divisor])
                }
            },
            Op::Binary { op, left, right } => {
                b.binary_at(self.source.class(results[0]), op, v(left), v(right))
            }
            Op::Float { float, operands } => {
                let operands: Vec<_> = self
                    .source
                    .values(operands)
                    .iter()
                    .map(|&old| v(old))
                    .collect();
                b.float(float, &operands)
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
                    // A number narrower than half a word is an immediate.
                    (from, Class::Natural) if always_small(from, self.word_bits()) => {
                        let number = word(b, v(value));
                        self.library.small_word(b, number)
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
                inline_small: true,
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
