//! Bounded evaluation over compact encodings, not unary constructor trees.

use num_bigint::BigUint;
use num_traits::{One, ToPrimitive, Zero};

use super::constant::{Shape, as_natural, read_natural, shape, write_natural};
use super::{Body, CtorId, Expr, ExprId, Operation, Program, TypeId};

/// A held value remains encoded even while taking a natural apart.
#[derive(Clone, Debug)]
pub(super) struct Held {
    pub owner: TypeId,
    pub bytes: Vec<u8>,
}

impl Held {
    fn number(owner: TypeId, n: &BigUint) -> Self {
        let mut bytes = Vec::new();
        write_natural(n, &mut bytes);
        Self { owner, bytes }
    }

    fn build(program: &Program, ctor: CtorId, fields: &[Self]) -> Option<Self> {
        let owner = program.ctor(ctor).owner;
        let mut bytes = Vec::new();
        match shape(program, owner) {
            Shape::Spine { nil, recursive, .. } => {
                if ctor == nil {
                    return Some(Self::number(owner, &BigUint::zero()));
                }
                let tail = &fields[recursive].bytes;
                let (count, took) = read_natural(tail);
                write_natural(&(count + BigUint::one()), &mut bytes);
                for (at, field) in fields.iter().enumerate() {
                    if at != recursive {
                        bytes.extend_from_slice(&field.bytes);
                    }
                }
                bytes.extend_from_slice(&tail[took..]);
            }
            Shape::Tagged => {
                if program.ctors(owner).len() > 1 {
                    write_natural(&BigUint::from(program.tag(ctor)), &mut bytes);
                }
                for field in fields {
                    bytes.extend_from_slice(&field.bytes);
                }
            }
        }
        (bytes.len() <= MAX_BYTES).then_some(Self { owner, bytes })
    }

    fn head(&self, program: &Program) -> Option<Head> {
        let (ctor, at, tail) = match shape(program, self.owner) {
            Shape::Spine {
                nil,
                cons,
                recursive,
            } => {
                let (count, took) = read_natural(&self.bytes);
                if count.is_zero() {
                    return Some(Head {
                        ctor: nil,
                        at: took,
                        tail: None,
                    });
                }
                (cons, took, Some((recursive, count - BigUint::one())))
            }
            Shape::Tagged => {
                let (tag, took) = if program.ctors(self.owner).len() > 1 {
                    let (n, took) = read_natural(&self.bytes);
                    (n.to_u32()?, took)
                } else {
                    (0, 0)
                };
                (program.ctor_at(self.owner, tag), took, None)
            }
        };
        Some(Head { ctor, at, tail })
    }

    fn parts(&self, program: &Program, fuel: &mut u32) -> Option<(CtorId, Vec<Self>)> {
        let Head { ctor, mut at, tail } = self.head(program)?;
        let mut fields = Vec::new();
        for (index, &owner) in program.fields(ctor).iter().enumerate() {
            if tail
                .as_ref()
                .is_some_and(|(recursive, _)| index == *recursive)
            {
                fields.push(Self {
                    owner,
                    bytes: Vec::new(),
                });
            } else {
                let took = length(program, owner, &self.bytes[at..], fuel)?;
                fields.push(Self {
                    owner,
                    bytes: self.bytes[at..at + took].to_vec(),
                });
                at += took;
            }
        }
        if let Some((recursive, count)) = tail {
            let mut rest = Self::number(self.owner, &count);
            rest.bytes.extend_from_slice(&self.bytes[at..]);
            fields[recursive] = rest;
        }
        Some((ctor, fields))
    }
}

struct Head {
    ctor: CtorId,
    at: usize,
    tail: Option<(usize, BigUint)>,
}

/// Resource limits are optimization limits, never language integer limits.
const MAX_BYTES: usize = 8192;

fn length(program: &Program, owner: TypeId, bytes: &[u8], fuel: &mut u32) -> Option<usize> {
    *fuel = fuel.checked_sub(1)?;
    let (ctor, mut at, repetitions, recursive) = match shape(program, owner) {
        Shape::Spine {
            cons, recursive, ..
        } => {
            let (count, took) = read_natural(bytes);
            if program.fields(cons).len() == 1 {
                return Some(took);
            }
            (cons, took, count.to_u32()?, Some(recursive))
        }
        Shape::Tagged => {
            let (tag, took) = if program.ctors(owner).len() > 1 {
                let (n, took) = read_natural(bytes);
                (n.to_u32()?, took)
            } else {
                (0, 0)
            };
            (program.ctor_at(owner, tag), took, 1, None)
        }
    };
    for _ in 0..repetitions {
        for (index, &field) in program.fields(ctor).iter().enumerate() {
            if recursive != Some(index) {
                at += length(program, field, &bytes[at..], fuel)?;
            }
        }
    }
    Some(at)
}

pub(super) struct Evaluator<'a> {
    pub program: &'a Program,
    pub operations: &'a [Option<Operation>],
}

impl Evaluator<'_> {
    pub(super) fn expr(&self, id: ExprId, env: &[Option<Held>], fuel: &mut u32) -> Option<Held> {
        *fuel = fuel.checked_sub(1)?;
        let args = |range| {
            self.program
                .atoms(range)
                .iter()
                .map(|a| env[a.0.index()].clone())
                .collect::<Option<Vec<_>>>()
        };
        match self.program.expr(id) {
            Expr::Atom(a) => env[a.0.index()].clone(),
            Expr::Static(owner, value) => {
                let bytes = self.program.known_bytes(value);
                (bytes.len() <= MAX_BYTES).then(|| Held {
                    owner,
                    bytes: bytes.to_vec(),
                })
            }
            Expr::Con(ctor, fields) => Held::build(self.program, ctor, &args(fields)?),
            Expr::Call(called, fields) => {
                let fields = args(fields)?;
                if let Some(op) = self.operations[called.index()] {
                    return self.arithmetic(op, self.program.function(called).result, &fields);
                }
                self.body(
                    self.program.function(called).body?,
                    fields.into_iter().map(Some).collect(),
                    fuel,
                )
            }
            Expr::Match(value, arms) => {
                let held = env[value.0.index()].as_ref()?;
                let (ctor, fields) = held.parts(self.program, fuel)?;
                let arm = self.program.arms(arms).iter().find(|a| a.ctor == ctor)?;
                let mut inner = env.to_vec();
                inner.extend(fields.into_iter().map(Some));
                self.body(arm.body, inner, fuel)
            }
        }
    }

    fn arithmetic(&self, op: Operation, result: TypeId, fields: &[Held]) -> Option<Held> {
        let a = as_natural(self.program, fields[0].owner, &fields[0].bytes)?;
        let b = as_natural(self.program, fields[1].owner, &fields[1].bytes)?;
        // A chain of squarings must not allocate without limit.
        if a.bits().saturating_add(b.bits()) > 7 * u64::try_from(MAX_BYTES).ok()? {
            return None;
        }
        if let Some(n) = op.calculate(&a, &b) {
            return Some(Held::number(result, &n));
        }
        Held::build(self.program, op.compare(&a, &b)?, &[])
    }

    pub(super) fn body(
        &self,
        body: Body,
        mut env: Vec<Option<Held>>,
        fuel: &mut u32,
    ) -> Option<Held> {
        for &binding in self.program.bindings(body.bindings) {
            let value = self.expr(binding, &env, fuel);
            env.push(value);
        }
        self.expr(body.tail, &env, fuel)
    }
}
