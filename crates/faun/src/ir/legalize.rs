//! Target-sized representation and structured lifetimes for unbounded naturals.
//!
//! Function parameters borrow; every local natural result owns a claim. Region
//! exits retain outgoing values (including duplicates) before releasing exited
//! scopes. Loop parameters own their iteration's claims; ancestor captures do
//! not. This deliberately keeps dead locals until their region exits, trading
//! peak memory for a small, auditable schedule rather than a liveness analysis.

use std::collections::BTreeMap;

use num_bigint::BigUint;

use super::natural::{self, Config, Library, Needs};
use super::{
    Binary, Builder, Class, DataId, Exit, FunctionId, Op, Origin, Program, RegionId, Relation,
    Terminator, ValueId, validate,
};

/// Rebuild a validated program with naturals represented by immutable objects.
///
/// Existing data, globals, names, platform IDs and function IDs are preserved.
/// Runtime helpers are appended and are not passed through ownership placement.
/// Programs needing no representation change take an unchanged clone fast path.
///
/// Serialized headers are target sized: `config.word_bits` MUST match the
/// subsequent backend or interpreter. This obligation cannot be detected from
/// the resulting ordinary Address IR. Relative size checks do not prove complete
/// target image/pool/frame placement.
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
    let needs = inspect(source, config)?;
    if !source.classes.contains(&Class::Natural) && !source.signature.contains(&Class::Natural) {
        return Ok(source.clone());
    }

    let mut output = skeleton(source);
    let library = natural::append(&mut output, config, needs)?;
    let constants = constants(source, &mut output, config)?;
    let pass = Pass {
        source,
        library,
        constants,
    };
    for (at, function) in source.functions().iter().enumerate() {
        output.define(FunctionId::at(at), |b, params| {
            let mut state = State {
                values: vec![None; source.values_count()],
                scopes: Vec::new(),
            };
            for (&old, &new) in source.values(function.params).iter().zip(params) {
                state.values[old.index()] = Some(new);
            }
            pass.region(b, function.body, &mut state, false, &[])
        });
    }
    validate(&output).map_err(|error| format!("after natural legalization: {error}"))?;
    Ok(output)
}

fn skeleton(source: &Program) -> Program {
    // Preserve the externally visible pools and IDs. Old value/region arenas
    // cannot survive: Builder appends contiguous regions in postorder.
    let mut output = source.clone();
    output.functions.clear();
    output.classes.clear();
    output.ops.clear();
    output.results.clear();
    output.operands.clear();
    output.regions.clear();
    for class in &mut output.signature {
        *class = representation(*class);
    }
    for function in source.functions() {
        let params: Vec<_> = source
            .values(function.params)
            .iter()
            .map(|&v| representation(source.class(v)))
            .collect();
        let returns: Vec<_> = source
            .signature(function.returns)
            .iter()
            .copied()
            .map(representation)
            .collect();
        output.declare(source.name(function.name), &params, &returns);
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
        if let Class::Fixed { bits } = *class
            && bits > config.word_bits
        {
            return Err(format!(
                "natural legalization does not yet support Fixed {{ bits: {bits} }} on a {} bit target",
                config.word_bits
            ));
        }
    }
    for platform in source.platforms() {
        if source
            .signature(platform.params)
            .iter()
            .chain(source.signature(platform.returns))
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
    for function in source.functions() {
        for op in source.every(function.body) {
            match *op {
                Op::Binary { op, left, .. } if source.class(left) == Class::Natural => match op {
                    Binary::Add => needs.add = true,
                    Binary::Sub => needs.sub = true,
                    Binary::Mul => needs.mul = true,
                    Binary::Div => needs.div = true,
                    Binary::Mod => needs.modulo = true,
                },
                Op::Compare { left, .. } if source.class(left) == Class::Natural => {
                    needs.compare = true;
                }
                Op::Convert { class, value } => match (source.class(value), class) {
                    (Class::Address, Class::Natural) | (Class::Natural, Class::Address) => {
                        return Err(
                            "addresses cannot be reinterpreted as naturals or vice versa".into(),
                        );
                    }
                    (Class::Natural, Class::Natural) => {}
                    (_, Class::Natural) => needs.from_word = true,
                    (Class::Natural, _) => needs.to_word = true,
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
    let mut pending: Vec<_> = source.functions().iter().map(|f| f.body).collect();
    while let Some(region) = pending.pop() {
        for (op, results) in source.walk(region) {
            let magnitude = match *op {
                Op::If {
                    then_region,
                    else_region,
                    ..
                } => {
                    pending.extend([then_region, else_region]);
                    continue;
                }
                Op::Loop { body, .. } => {
                    pending.push(body);
                    continue;
                }
                _ => match magnitude(source, *op) {
                    Some(value) => value,
                    None => continue,
                },
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

fn magnitude(source: &Program, op: Op) -> Option<BigUint> {
    match op {
        Op::Constant {
            class: Class::Natural,
            value,
        } => Some(BigUint::from(value)),
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
}

#[derive(Clone)]
struct Scope {
    owners: Vec<ValueId>,
    loop_: bool,
}

#[derive(Clone)]
struct State {
    values: Vec<Option<ValueId>>,
    scopes: Vec<Scope>,
}

impl State {
    fn value(&self, old: ValueId) -> ValueId {
        self.values[old.index()].expect("validated SSA operand has been rebuilt")
    }
}

impl Pass<'_> {
    fn retained(&self, b: &mut Builder, value: ValueId) -> ValueId {
        b.call(self.library.retain, &[value])[0]
    }

    fn region(
        &self,
        b: &mut Builder,
        region: RegionId,
        state: &mut State,
        loop_: bool,
        params: &[ValueId],
    ) -> Terminator {
        let old = self.source.region(region);
        let mut owners = Vec::new();
        for (&old, &new) in self.source.values(old.params).iter().zip(params) {
            state.values[old.index()] = Some(new);
            if loop_ && self.source.class(old) == Class::Natural {
                owners.push(new);
            }
        }
        state.scopes.push(Scope { owners, loop_ });
        for (op, results) in self.source.walk(region) {
            let fresh = self.op(b, *op, results, state);
            for (&old, new) in results.iter().zip(fresh) {
                state.values[old.index()] = Some(new);
                if self.source.class(old) == Class::Natural {
                    state
                        .scopes
                        .last_mut()
                        .expect("current scope")
                        .owners
                        .push(new);
                }
            }
        }
        self.exit(b, state, old.terminator)
    }

    fn exit(&self, b: &mut Builder, state: &State, terminator: Terminator) -> Terminator {
        // No operations may follow a nonreturning platform call. Unreachable
        // also follows constructs whose branches both leave this scope.
        if terminator.exit == Exit::Unreachable {
            return Terminator::UNREACHABLE;
        }
        let outgoing: Vec<_> = self
            .source
            .values(terminator.values)
            .iter()
            .map(|&old| {
                let value = state.value(old);
                if self.source.class(old) == Class::Natural {
                    self.retained(b, value)
                } else {
                    value
                }
            })
            .collect();
        let start = match terminator.exit {
            Exit::Return => 0,
            Exit::Yield => state.scopes.len() - 1,
            Exit::Break | Exit::Continue => state
                .scopes
                .iter()
                .rposition(|s| s.loop_)
                .expect("validated loop exit"),
            Exit::Unreachable => unreachable!(),
        };
        for scope in state.scopes[start..].iter().rev() {
            for &value in scope.owners.iter().rev() {
                b.call(self.library.release, &[value]);
            }
        }
        match terminator.exit {
            Exit::Yield => b.yield_(&outgoing),
            Exit::Return => b.ret(&outgoing),
            Exit::Continue => b.continue_(&outgoing),
            Exit::Break => b.break_(&outgoing),
            Exit::Unreachable => unreachable!(),
        }
    }

    #[expect(
        clippy::too_many_lines,
        reason = "exhaustive operation dispatch keeps scalar cloning beside each representation rewrite"
    )]
    fn op(&self, b: &mut Builder, op: Op, results: &[ValueId], state: &State) -> Vec<ValueId> {
        let v = |old| state.value(old);
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
            Op::Constant {
                class: Class::Natural,
                ..
            }
            | Op::NaturalConstant(_) => b.address_of(self.constants[&results[0]]),
            Op::Constant { class, value } => b.constant(class, value),
            Op::AddressOf(data) => b.address_of(data),
            Op::Binary { op, left, right } if self.source.class(left) == Class::Natural => {
                let function = match op {
                    Binary::Add => self.library.add,
                    Binary::Sub => self.library.sub,
                    Binary::Mul => self.library.mul,
                    Binary::Div => self.library.div,
                    Binary::Mod => self.library.modulo,
                }
                .expect("requested arithmetic helper");
                b.call(function, &[v(left), v(right)])[0]
            }
            Op::Binary { op, left, right } => {
                b.binary_at(self.source.class(results[0]), op, v(left), v(right))
            }
            Op::Compare {
                relation,
                left,
                right,
            } if self.source.class(left) == Class::Natural => {
                let ordering = b.call(
                    self.library.compare.expect("requested comparison"),
                    &[v(left), v(right)],
                )[0];
                let wanted = b.constant(Class::Word, u64::from(relation == Relation::Equal));
                b.compare(Relation::Equal, ordering, wanted)
            }
            Op::Compare {
                relation,
                left,
                right,
            } => b.compare(relation, v(left), v(right)),
            Op::Convert { class, value } => match (self.source.class(value), class) {
                (Class::Natural, Class::Natural) => self.retained(b, v(value)),
                (_, Class::Natural) => b.call(
                    self.library.from_word.expect("requested promotion"),
                    &[v(value)],
                )[0],
                (Class::Natural, _) => {
                    let word = b.call(
                        self.library.to_word.expect("requested narrowing"),
                        &[v(value)],
                    )[0];
                    if class == Class::Word {
                        word
                    } else {
                        b.convert(class, word)
                    }
                }
                _ => b.convert(class, v(value)),
            },
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
            Op::PlatformCall {
                platform,
                args: held,
            } => return b.platform_call(platform, &args(held)),
            Op::If {
                condition,
                then_region,
                else_region,
            } => {
                return b.if_(
                    v(condition),
                    &classes(),
                    |b| self.region(b, then_region, &mut state.clone(), false, &[]),
                    |b| self.region(b, else_region, &mut state.clone(), false, &[]),
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
                    self.region(b, body, &mut state.clone(), true, params)
                });
            }
        };
        vec![one]
    }
}
