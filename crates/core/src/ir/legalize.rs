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

use super::natural::{self, Config, Helper, Library, Needs};
use super::{
    Builder, Class, DataId, Definition, Exit, Op, Origin, Program, RegionId, Relation, Terminator,
    ValueId, validate,
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
    if !source.classes.as_slice().contains(&Class::Natural)
        && !source.signature.contains(&Class::Natural)
    {
        return Ok(source.clone());
    }

    let mut output = skeleton(source);
    let library = natural::append(&mut output, config, needs)?;
    let constants = constants(source, &mut output, config)?;
    let pass = Pass {
        source,
        library,
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
                ops: super::Range::EMPTY,
                terminator: None,
            });
            output.functions[id].definition = Definition::Declared(body);
        }
    }
    output
}

fn representation(class: Class) -> Class {
    if class == Class::Natural {
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
        if source
            .signature(function.params)
            .iter()
            .chain(source.signature(function.returns.classes()))
            .any(|&c| c == Class::Natural)
        {
            return Err("host signatures containing Natural have no bigint ABI".into());
        }
    }
    Ok(())
}

fn inspect(source: &Program, config: Config) -> Result<Needs, String> {
    check_classes(source, config)?;
    let mut needs = Needs::default();
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
                Op::Store { value, .. } if source.class(value) == Class::Natural => {
                    return Err("storing a Natural has no scalar memory representation".into());
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
    owners: Vec<ValueId>,
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

    fn retained(&self, b: &mut Builder, value: ValueId) -> ValueId {
        b.call_one(self.library.retain, &[value])
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
            if kind == ScopeKind::Loop && self.source.class(old) == Class::Natural {
                owners.push(new);
            }
        }
        scopes.push(Scope { owners, kind });
        for (op, results) in self.source.walk(region) {
            let fresh = self.op(b, *op, results, scopes);
            for (&old, new) in results.iter().zip(fresh) {
                self.mapped(old, new);
                if self.source.class(old) == Class::Natural {
                    scopes.last_mut().expect("current scope").owners.push(new);
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
                if self.source.class(old) == Class::Natural {
                    self.retained(b, value)
                } else {
                    value
                }
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
            for &value in scope.owners.iter().rev() {
                b.call(self.library.release, &[value]);
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
                    (Class::Natural, Class::Natural) => self.retained(b, v(value)),
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
                        let value = if self.source.class(old) == Class::Natural {
                            self.retained(b, v(old))
                        } else {
                            v(old)
                        };
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
