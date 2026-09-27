//! What a comparison says of the sizes it compared, carried to where its
//! answer is taken apart.
//!
//! A guard `i < n` reaches a match as a `Bool` some definition answered,
//! which answered it from an `Order` another answered, which answered from
//! the comparisons Barb recognizes by their equations: the less-than and the
//! equality of naturals. Nothing is known by name. A value of a type whose
//! constructors all carry nothing is followed here as a *verdict*: for each
//! constructor it can be, the facts about sizes that hold when it is. The
//! definitions between a recognized comparison and the match are evaluated
//! on verdicts, a few calls deep, so `lt(cmp(i, n))` being `True` says
//! `i < n` whatever spelled it.
//!
//! Every fact here holds of every run: a recognized comparison states its
//! own result, a match joins what its arms say by keeping only what all of
//! them say, and anything not followed says nothing. A fact is only ever
//! missing, never wrong.

use super::model::{Atom, Body, Expr, ExprId, FnId};
use super::program::Program;
use super::{CtorId, Operation, TypeId};

/// A set of the ways two sizes may stand: less, equal, greater.
pub(super) type Rel = u8;
pub(super) const LESS: Rel = 1;
pub(super) const EQUAL: Rel = 2;
pub(super) const GREATER: Rel = 4;
const ANY: Rel = LESS | EQUAL | GREATER;

/// `left` stands to `right` in one of the ways `rel` holds.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct Fact {
    pub left: usize,
    pub right: usize,
    pub rel: Rel,
}

impl Fact {
    /// The same fact with its sides in order, so one pair is one entry.
    const fn ordered(self) -> Self {
        if self.left <= self.right {
            self
        } else {
            Self {
                left: self.right,
                right: self.left,
                rel: flip(self.rel),
            }
        }
    }
}

/// What `rel` says read the other way round.
const fn flip(rel: Rel) -> Rel {
    (rel & EQUAL) | ((rel & LESS) << 2) | ((rel & GREATER) >> 2)
}

/// Facts that all hold.
pub(super) type Facts = Vec<Fact>;

/// Both conjunctions: what either says, and for a pair both speak of, what
/// both allow.
fn conj(a: &[Fact], b: &[Fact]) -> Facts {
    let mut held: Facts = a.to_vec();
    for fact in b {
        let fact = fact.ordered();
        match held
            .iter_mut()
            .find(|known| known.left == fact.left && known.right == fact.right)
        {
            Some(known) => known.rel &= fact.rel,
            None => held.push(fact),
        }
    }
    held
}

/// What holds whichever held: for each pair both speak of, either's way.
fn join(a: &[Fact], b: &[Fact]) -> Facts {
    a.iter()
        .filter_map(|fact| {
            let other = b
                .iter()
                .find(|known| known.left == fact.left && known.right == fact.right)?;
            let rel = fact.rel | other.rel;
            (rel != ANY).then_some(Fact { rel, ..*fact })
        })
        .collect()
}

/// Whether `facts` place `left` against `right` only in ways `within`
/// allows.
pub(super) fn holds(facts: &[Fact], left: usize, right: usize, within: Rel) -> bool {
    let (rel, left, right) = if left <= right {
        (within, left, right)
    } else {
        (flip(within), right, left)
    };
    facts
        .iter()
        .any(|fact| fact.left == left && fact.right == right && fact.rel & !rel == 0)
}

/// For each constructor of an enumeration, by tag, what holds when a value
/// is it, or nothing where it cannot be.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Verdict {
    pub outcomes: Vec<Option<Facts>>,
}

impl Verdict {
    fn only(program: &Program, ctor: CtorId) -> Self {
        let owner = program.ctor(ctor).owner;
        let mut outcomes = vec![None; program.ctors(owner).len()];
        outcomes[tag(program, ctor)] = Some(Vec::new());
        Self { outcomes }
    }

    /// Two ways of arriving at one value: what each outcome says either way.
    fn or(&self, other: &Self) -> Self {
        Self {
            outcomes: self
                .outcomes
                .iter()
                .zip(&other.outcomes)
                .map(|(a, b)| match (a, b) {
                    (None, None) => None,
                    (Some(facts), None) | (None, Some(facts)) => Some(facts.clone()),
                    (Some(a), Some(b)) => Some(join(a, b)),
                })
                .collect(),
        }
    }

    /// Every outcome with `facts` holding besides.
    fn given(&self, facts: &[Fact]) -> Self {
        Self {
            outcomes: self
                .outcomes
                .iter()
                .map(|outcome| outcome.as_ref().map(|held| conj(facts, held)))
                .collect(),
        }
    }
}

/// What a local is to this analysis: a size it can state facts of, a
/// verdict, or nothing it follows.
#[derive(Clone, Debug)]
pub(super) enum Value {
    Size(usize),
    Verdict(Verdict),
    Unknown,
}

/// How many definitions deep a verdict is followed through.
const DEPTH: usize = 4;

fn tag(program: &Program, ctor: CtorId) -> usize {
    usize::try_from(program.tag(ctor)).expect("a tag fits usize")
}

/// Whether values of `ty` are only which constructor they are.
fn enumerates(program: &Program, ty: TypeId) -> bool {
    let ctors = program.ctors(ty);
    ctors.len() >= 2
        && ctors
            .iter()
            .all(|ctor| program.types_of(ctor.fields).is_empty())
}

/// What calling `callee` on `args` answers, as a verdict where it can say.
pub(super) fn called(
    program: &Program,
    operations: &[Option<Operation>],
    callee: FnId,
    args: &[Value],
) -> Value {
    call(program, operations, callee, args, DEPTH)
}

/// What `expr`, in a body whose locals are `env`, answers.
pub(super) fn evaluated(
    program: &Program,
    operations: &[Option<Operation>],
    expr: ExprId,
    env: &mut Vec<Value>,
) -> Value {
    Evaluation {
        program,
        operations,
    }
    .expr(expr, env, DEPTH)
}

fn call(
    program: &Program,
    operations: &[Option<Operation>],
    callee: FnId,
    args: &[Value],
    depth: usize,
) -> Value {
    Evaluation {
        program,
        operations,
    }
    .call(callee, args, depth)
}

struct Evaluation<'a> {
    program: &'a Program,
    operations: &'a [Option<Operation>],
}

impl Evaluation<'_> {
    fn call(&self, callee: FnId, args: &[Value], depth: usize) -> Value {
        let comparison = match self.operations.get(callee.index()).copied().flatten() {
            Some(Operation::LessThan { yes, no }) => Some((yes, no, LESS, EQUAL | GREATER)),
            Some(Operation::Equals { yes, no }) => Some((yes, no, EQUAL, LESS | GREATER)),
            _ => None,
        };
        if let Some((yes, no, holds, fails)) = comparison {
            let (Some(Value::Size(left)), Some(Value::Size(right))) = (args.first(), args.get(1))
            else {
                return Value::Unknown;
            };
            let fact = |rel| Fact {
                left: *left,
                right: *right,
                rel,
            };
            let mut verdict = Verdict::only(self.program, yes);
            verdict.outcomes[tag(self.program, yes)] = Some(vec![fact(holds).ordered()]);
            verdict.outcomes[tag(self.program, no)] = Some(vec![fact(fails).ordered()]);
            return Value::Verdict(verdict);
        }
        let function = self.program.function(callee);
        if depth == 0 || !enumerates(self.program, function.result) {
            return Value::Unknown;
        }
        let Some(body) = function.body() else {
            return Value::Unknown;
        };
        let mut env = args.to_vec();
        self.body(body, &mut env, depth - 1)
    }

    fn body(&self, body: Body, env: &mut Vec<Value>, depth: usize) -> Value {
        let level = env.len();
        for &binding in self.program.bindings(body.bindings) {
            let value = self.expr(binding, env, depth);
            env.push(value);
        }
        let answer = self.expr(body.tail, env, depth);
        env.truncate(level);
        answer
    }

    fn expr(&self, id: ExprId, env: &mut Vec<Value>, depth: usize) -> Value {
        match self.program.expr(id) {
            Expr::Atom(Atom(local)) => env.get(local.index()).cloned().unwrap_or(Value::Unknown),
            Expr::Static(value) => {
                let ctor = self.program.constant(value).constructor();
                self.constant(ctor)
            }
            Expr::Con(ctor, args) if self.program.atoms(args).is_empty() => self.constant(ctor),
            Expr::Con(..) => Value::Unknown,
            Expr::Call(callee, args) => {
                let args: Vec<Value> = self
                    .program
                    .atoms(args)
                    .iter()
                    .map(|atom| env.get(atom.0.index()).cloned().unwrap_or(Value::Unknown))
                    .collect();
                self.call(callee, &args, depth)
            }
            Expr::Match(scrutinee, arms) => self.matched(scrutinee, arms, env, depth),
        }
    }

    fn constant(&self, ctor: CtorId) -> Value {
        if enumerates(self.program, self.program.ctor(ctor).owner) {
            Value::Verdict(Verdict::only(self.program, ctor))
        } else {
            Value::Unknown
        }
    }

    /// Each arm answers under what its constructor says of the scrutinee;
    /// an arm the scrutinee cannot reach answers nothing.
    fn matched(
        &self,
        scrutinee: Atom,
        arms: super::Range,
        env: &mut Vec<Value>,
        depth: usize,
    ) -> Value {
        let taken = env.get(scrutinee.0.index()).cloned();
        let mut answer: Option<Verdict> = None;
        for arm in self.program.arms(arms) {
            let given = match &taken {
                Some(Value::Verdict(verdict)) => {
                    match &verdict.outcomes[tag(self.program, arm.ctor)] {
                        Some(facts) => facts.clone(),
                        None => continue,
                    }
                }
                _ => Vec::new(),
            };
            let level = env.len();
            env.resize(level + self.program.fields(arm.ctor).len(), Value::Unknown);
            let arm_answer = self.body(arm.body, env, depth);
            env.truncate(level);
            let Value::Verdict(verdict) = arm_answer else {
                return Value::Unknown;
            };
            let verdict = verdict.given(&given);
            answer = Some(match answer {
                None => verdict,
                Some(before) => before.or(&verdict),
            });
        }
        answer.map_or(Value::Unknown, Value::Verdict)
    }
}
