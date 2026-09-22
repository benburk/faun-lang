//! Target-sized representation and structured lifetimes for unbounded naturals.
//!
//! Function parameters borrow; every local natural result owns a claim. Region
//! exits retain outgoing values (including duplicates) before releasing exited
//! scopes. Loop parameters own their iteration's claims; ancestor captures do
//! not. This deliberately keeps dead locals until their region exits, trading
//! peak memory for a small, auditable schedule rather than a liveness analysis.

use crate::index::Pool;
use std::{cell::Cell, collections::BTreeMap};

use num_bigint::BigUint;

use super::cell::{self, Library as CellLibrary};
use super::natural::{self, Config, Helper, Library, Needs};
use super::{
    Builder, Class, DataId, Definition, Exit, Op, Origin, Program, Range, RegionId, Relation,
    Terminator, ValueId, Width, validate,
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
    let has_naturals = source.classes.as_slice().contains(&Class::Natural)
        || source.signature.contains(&Class::Natural);
    let has_cells =
        source.classes.as_slice().contains(&Class::Cell) || source.signature.contains(&Class::Cell);
    if !has_naturals && !has_cells {
        return Ok(source.clone());
    }

    let mut output = skeleton(source);
    output.runtime_cells |= has_cells;
    output.runtime_naturals |= has_naturals;
    let library = natural::append(&mut output, config, needs)?;
    let cells = has_cells.then(|| cell::append(&mut output, &library, config.word_bits));
    let constants = constants(source, &mut output, config)?;
    let pass = Pass {
        source,
        library,
        cells,
        word_bytes: u64::from(config.word_bits / 8),
        constants,
        values: vec![Cell::new(None); source.values_count()],
    };
    for (id, function) in source.functions.iter_enumerated() {
        let Some(body) = function.body() else {
            continue;
        };
        output.define(id, |b, params| {
            pass.region(b, body, &mut Vec::new(), ScopeKind::Ordinary, params);
        });
    }
    validate(&output).map_err(|error| format!("after natural legalization: {error}"))?;
    Ok(output)
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

const fn representation(class: Class) -> Class {
    if matches!(class, Class::Cell | Class::Natural) {
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
                Class::Cell => {
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
    if source.classes.as_slice().contains(&Class::Cell) || source.signature.contains(&Class::Cell) {
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
                Op::Store { value, .. }
                    if matches!(source.class(value), Class::Cell | Class::Natural) =>
                {
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

fn constants(
    source: &Program,
    output: &mut Program,
    config: Config,
) -> Result<BTreeMap<ValueId, DataId>, String> {
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
            let data = if let Some(&data) = interned.get(&magnitude) {
                data
            } else {
                let data = natural::constant(output, config, &magnitude)?;
                interned.insert(magnitude, data);
                data
            };
            constants.insert(results[0], data);
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
    word_bytes: u64,
    constants: BTreeMap<ValueId, DataId>,
    // Validation establishes globally unique SSA definitions and lexical use.
    // Mapping is monotonic across functions and sibling regions, not path-local.
    // Cells let the builder's two sequential branch callbacks share this table
    // without cloning it or borrowing a whole Pass mutably.
    values: Vec<Cell<Option<ValueId>>>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ScopeKind {
    Ordinary,
    /// Parameters own the claims carried by this iteration.
    Loop,
}

#[derive(Clone)]
struct Scope {
    owners: Vec<(Class, ValueId)>,
    kind: ScopeKind,
}

impl Pass<'_> {
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
            Class::Natural => self.library.retain,
            Class::Cell => self.cells.expect("cell helpers were requested").retain,
            _ => return value,
        };
        b.call_one(function, &[value])
    }

    fn release(&self, b: &mut Builder, class: Class, value: ValueId) {
        let function = match class {
            Class::Natural => self.library.release,
            Class::Cell => self.cells.expect("cell helpers were requested").release,
            _ => return,
        };
        b.call(function, &[value]);
    }

    fn construct_cell(&self, b: &mut Builder, tag: u32, fields: Range) -> ValueId {
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
        for (index, &old) in fields.iter().enumerate() {
            let class = self.source.class(old);
            let kind = match class {
                Class::Natural => cell::NATURAL,
                Class::Cell => cell::CELL,
                _ => cell::SCALAR,
            };
            let kind = b.constant(Class::Word, kind);
            let at = i32::try_from(index * 2 + 4).expect("checked cell field offset");
            b.store(Width::Word, object, super::Offset::Words(at), kind);
            let value = self.retained(b, class, self.value(old));
            b.store(Width::Word, object, super::Offset::Words(at + 1), value);
        }
        object
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

    fn region(
        &self,
        b: &mut Builder,
        region: RegionId,
        scopes: &mut Vec<Scope>,
        kind: ScopeKind,
        params: &[ValueId],
    ) {
        let old = self.source.region(region);
        let mut owners = Vec::new();
        for (&old, &new) in self.source.values(old.params).iter().zip(params) {
            self.mapped(old, new);
            if kind == ScopeKind::Loop
                && matches!(self.source.class(old), Class::Cell | Class::Natural)
            {
                owners.push((self.source.class(old), new));
            }
        }
        scopes.push(Scope { owners, kind });
        for (op, results) in self.source.walk(region) {
            let fresh = self.op(b, *op, results, scopes);
            for (&old, new) in results.iter().zip(fresh) {
                self.mapped(old, new);
                if matches!(self.source.class(old), Class::Cell | Class::Natural) {
                    scopes
                        .last_mut()
                        .expect("current scope")
                        .owners
                        .push((self.source.class(old), new));
                }
            }
        }
        // Terminal child transfers already cleaned their scopes. A Never
        // call must not be followed by cleanup at this region's end.
        if let Some(terminator) = old.terminator {
            self.exit(b, scopes, terminator);
        }
        scopes.pop();
    }

    fn exit(&self, b: &mut Builder, scopes: &[Scope], terminator: Terminator) {
        let outgoing: Vec<_> = self
            .source
            .values(terminator.values)
            .iter()
            .map(|&old| {
                let value = self.value(old);
                self.retained(b, self.source.class(old), value)
            })
            .collect();
        let start = match terminator.exit {
            Exit::Return => 0,
            Exit::Yield => scopes.len() - 1,
            Exit::Break | Exit::Continue => scopes
                .iter()
                .rposition(|s| s.kind == ScopeKind::Loop)
                .expect("validated loop exit"),
        };
        for scope in scopes[start..].iter().rev() {
            for &(class, value) in scope.owners.iter().rev() {
                self.release(b, class, value);
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
    fn op(&self, b: &mut Builder, op: Op, results: &[ValueId], scopes: &[Scope]) -> Vec<ValueId> {
        let v = |old| self.value(old);
        let args = |range| {
            self.source
                .values(range)
                .iter()
                .map(|&old| v(old))
                .collect::<Vec<_>>()
        };
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
                b.address_of(self.constants[&results[0]])
            }
            Op::Constant { value } => b.constant(self.source.class(results[0]), value),
            Op::NaturalConstant(data) => b.kept_natural(data),
            Op::AddressOf(data) => b.address_of(data),
            Op::Cell { tag, fields } => self.construct_cell(b, tag, fields),
            Op::CellTag { cell } => b.load(Width::Word, v(cell), super::Offset::Words(2)),
            Op::CellField { cell, index } => self.cell_field(b, results[0], cell, index),
            Op::Binary { op, left, right } if self.source.class(left) == Class::Natural => {
                let function = self.library.require(Helper::arithmetic(op));
                b.call_one(function, &[v(left), v(right)])
            }
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
                let ordering =
                    b.call_one(self.library.require(Helper::Compare), &[v(left), v(right)]);
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
                    (Class::Natural, Class::Natural) => self.retained(b, Class::Natural, v(value)),
                    (Class::Cell, Class::Cell) => self.retained(b, Class::Cell, v(value)),
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
            } => return b.call(function, &args(held)),
            Op::If {
                condition,
                then_region,
                else_region,
            } => {
                return b.if_(
                    v(condition),
                    &classes(),
                    |b| {
                        self.region(
                            b,
                            then_region,
                            &mut scopes.to_vec(),
                            ScopeKind::Ordinary,
                            &[],
                        );
                    },
                    |b| {
                        self.region(
                            b,
                            else_region,
                            &mut scopes.to_vec(),
                            ScopeKind::Ordinary,
                            &[],
                        );
                    },
                );
            }
            Op::Loop { initial, body } => {
                let initial: Vec<_> = self
                    .source
                    .values(initial)
                    .iter()
                    .zip(self.source.values(self.source.region(body).params))
                    .map(|(&old, &parameter)| {
                        let value = self.retained(b, self.source.class(old), v(old));
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
                return b.loop_(&initial, &classes(), |b, params| {
                    self.region(b, body, &mut scopes.to_vec(), ScopeKind::Loop, params);
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
        crate::platform::Routines::builtin().declare(&mut p, "write");
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
