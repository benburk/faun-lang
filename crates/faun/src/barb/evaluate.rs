//! Bounded evaluation over compact encodings, not unary constructor trees.

use num_bigint::BigUint;
use num_traits::{One, ToPrimitive, Zero};

use super::constant::{Shape, as_natural, read_natural, shape, write_natural};
use super::{Body, CtorId, Expr, ExprId, Operation, Program, TypeId};

/// Resource limits for one whole folding pass, not language integer limits.
/// Work counts visits, copied bytes and conservative bigint word operations.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FoldLimits {
    pub work: u64,
    pub max_bytes: usize,
    pub max_depth: usize,
}

impl Default for FoldLimits {
    fn default() -> Self {
        Self {
            work: 1_000_000,
            max_bytes: 8192,
            max_depth: 128,
        }
    }
}

pub(super) struct Budget {
    pub remaining: u64,
    limits: FoldLimits,
    depth: usize,
}

impl Budget {
    pub(super) const fn new(limits: FoldLimits) -> Self {
        Self {
            remaining: limits.work,
            limits,
            depth: 0,
        }
    }

    const fn spend(&mut self, work: u64) -> Option<()> {
        if work > self.remaining {
            self.remaining = 0;
            return None;
        }
        self.remaining -= work;
        Some(())
    }

    fn bytes(&mut self, size: usize) -> Option<()> {
        if size > self.limits.max_bytes {
            return None;
        }
        self.spend(u64::try_from(size).ok()?)
    }
}

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

    fn build(
        program: &Program,
        ctor: CtorId,
        fields: &[Self],
        budget: &mut Budget,
    ) -> Option<Self> {
        let owner = program.ctor(ctor).owner;
        // Reserve the worst-case encoded size before concatenating fields or
        // incrementing a spine count. A refusal leaves the original term alone.
        let payload = fields
            .iter()
            .try_fold(0usize, |n, f| n.checked_add(f.bytes.len()))?;
        let overhead = if matches!(shape(program, owner), Shape::Spine { .. }) {
            1
        } else {
            5
        };
        budget.bytes(payload.checked_add(overhead)?)?;
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
        Some(Self { owner, bytes })
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

    fn parts(&self, program: &Program, budget: &mut Budget) -> Option<(CtorId, Vec<Self>)> {
        budget.bytes(self.bytes.len())?;
        let Head { ctor, mut at, tail } = self.head(program)?;
        budget.spend(u64::try_from(program.fields(ctor).len()).ok()?)?;
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
                let took = length(program, owner, &self.bytes[at..], budget)?;
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

fn length(program: &Program, owner: TypeId, bytes: &[u8], budget: &mut Budget) -> Option<usize> {
    budget.spend(1)?;
    if budget.depth >= budget.limits.max_depth {
        return None;
    }
    budget.depth += 1;
    let result = length_inner(program, owner, bytes, budget);
    budget.depth -= 1;
    result
}

fn length_inner(
    program: &Program,
    owner: TypeId,
    bytes: &[u8],
    budget: &mut Budget,
) -> Option<usize> {
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
                at += length(program, field, &bytes[at..], budget)?;
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
    pub(super) fn expr(
        &self,
        id: ExprId,
        env: &[Option<Held>],
        budget: &mut Budget,
    ) -> Option<Held> {
        budget.spend(1)?;
        if budget.depth >= budget.limits.max_depth {
            return None;
        }
        budget.depth += 1;
        let result = self.expr_inner(id, env, budget);
        budget.depth -= 1;
        result
    }

    fn args(
        &self,
        range: super::Range,
        env: &[Option<Held>],
        budget: &mut Budget,
    ) -> Option<Vec<Held>> {
        let atoms = self.program.atoms(range);
        budget.spend(u64::try_from(atoms.len()).ok()?)?;
        // Charge before allocating the argument vector or cloning values.
        for a in atoms {
            budget.bytes(env[a.0.index()].as_ref()?.bytes.len())?;
        }
        atoms.iter().map(|a| env[a.0.index()].clone()).collect()
    }

    fn expr_inner(&self, id: ExprId, env: &[Option<Held>], budget: &mut Budget) -> Option<Held> {
        match self.program.expr(id) {
            Expr::Atom(a) => {
                let value = env[a.0.index()].as_ref()?;
                budget.bytes(value.bytes.len())?;
                Some(value.clone())
            }
            Expr::Static(owner, value) => {
                let bytes = self.program.known_bytes(value);
                budget.bytes(bytes.len())?;
                Some(Held {
                    owner,
                    bytes: bytes.to_vec(),
                })
            }
            Expr::Con(ctor, fields) => {
                Held::build(self.program, ctor, &self.args(fields, env, budget)?, budget)
            }
            Expr::Call(called, fields) => {
                let fields = self.args(fields, env, budget)?;
                if let Some(op) = self.operations[called.index()] {
                    return self.arithmetic(
                        op,
                        self.program.function(called).result,
                        &fields,
                        budget,
                    );
                }
                self.body(
                    self.program.function(called).body()?,
                    fields.into_iter().map(Some).collect(),
                    budget,
                )
            }
            Expr::Match(value, arms) => {
                self.branch(env[value.0.index()].as_ref()?, arms, env, budget)
            }
        }
    }

    fn branch(
        &self,
        held: &Held,
        arms: super::Range,
        env: &[Option<Held>],
        budget: &mut Budget,
    ) -> Option<Held> {
        let (ctor, fields) = held.parts(self.program, budget)?;
        let arm = self.program.arms(arms).iter().find(|a| a.ctor == ctor)?;
        budget.spend(u64::try_from(env.len()).ok()?)?;
        for value in env.iter().flatten() {
            budget.bytes(value.bytes.len())?;
        }
        let mut inner = env.to_vec();
        inner.extend(fields.into_iter().map(Some));
        self.body(arm.body, inner, budget)
    }

    fn arithmetic(
        &self,
        op: Operation,
        result: TypeId,
        fields: &[Held],
        budget: &mut Budget,
    ) -> Option<Held> {
        // Decoding only sees already-size-checked arguments. Guard result size
        // and charge conservative word work BEFORE allocating a bigint result.
        let a = as_natural(self.program, fields[0].owner, &fields[0].bytes)?;
        let b = as_natural(self.program, fields[1].owner, &fields[1].bytes)?;
        let bits = a.bits().max(b.bits());
        let output = match op {
            Operation::Add => bits.saturating_add(1),
            Operation::Mul => a.bits().saturating_add(b.bits()),
            _ => bits,
        };
        let bytes = usize::try_from(output.div_ceil(7).max(1)).ok()?;
        budget.bytes(bytes)?;
        let words = |bits: u64| bits.div_ceil(64).max(1);
        let work = match op {
            Operation::Mul => words(a.bits()).saturating_mul(words(b.bits())),
            Operation::Div | Operation::Mod => words(bits).saturating_mul(words(bits)),
            _ => words(bits),
        };
        budget.spend(work)?;
        if let Some(n) = op.calculate(&a, &b) {
            return Some(Held::number(result, &n));
        }
        Held::build(self.program, op.compare(&a, &b)?, &[], budget)
    }

    pub(super) fn body(
        &self,
        body: Body,
        mut env: Vec<Option<Held>>,
        budget: &mut Budget,
    ) -> Option<Held> {
        for &binding in self.program.bindings(body.bindings) {
            // Eager evaluation: an unused unknown binding may perform effects
            // or fail to return. Never fold its enclosing call/match away.
            let value = self.expr(binding, &env, budget)?;
            env.push(Some(value));
        }
        self.expr(body.tail, &env, budget)
    }
}
