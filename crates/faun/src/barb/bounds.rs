//! What a number can be, worked out from what a program does with it.
//!
//! A type says a value is a number and nothing about which numbers, so
//! deciding how wide to hold one is deciding what it could be. That is a
//! question about terms, not about storage: `Succ` is one more than what it
//! wraps, a match on `Zero` says which argument is nought in which arm, and
//! a call answers whatever the name it calls does. None of it needs a word
//! size, which is why it is worked out here and read below.
//!
//! What comes out is per term, since that is what the tier deciding
//! representation walks: every term has an answer, so how wide to hold what
//! it answers is a question with one. A term walked more than once -- an
//! arm reached at two widths, a definition gone round again -- holds what
//! it held at any of them.
//!
//! Nothing here is exact. A bound too wide costs a wider number and never a
//! wrong one, so where the walk cannot say -- a definition that counts up
//! without a last step, an argument from outside -- it says so and the
//! tiers below hold what they must.

use super::constant::{Shape, as_number, shape};
use super::ir::{Body, CtorId, Expr, FnId, Program};

/// The least and greatest a number can be. No greatest is a number counting
/// up without a last step, which is every `Nat` until something says less.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Bounds {
    pub low: u64,
    pub high: Option<u64>,
}

impl Bounds {
    /// Nothing is known, so anything is possible.
    pub const ANY: Self = Self { low: 0, high: None };

    /// And no number at all, which is where a walk starts: a name nothing
    /// has reached yet holds nothing, rather than holding anything. Starting
    /// at anything would be sound and would stay there, since what is known
    /// only ever grows.
    pub const NOTHING: Self = Self {
        low: 1,
        high: Some(0),
    };

    #[must_use]
    pub const fn is_nothing(self) -> bool {
        matches!(self.high, Some(high) if high < self.low)
    }

    /// Exactly this.
    #[must_use]
    pub const fn at(value: u64) -> Self {
        Self {
            low: value,
            high: Some(value),
        }
    }

    /// Either of two, which is what a match holds where its arms disagree.
    #[must_use]
    pub fn or(self, other: Self) -> Self {
        if self.is_nothing() {
            return other;
        }
        if other.is_nothing() {
            return self;
        }
        Self {
            low: self.low.min(other.low),
            high: self.high.zip(other.high).map(|(a, b)| a.max(b)),
        }
    }

    /// One more, which is what a constructor of a number answers.
    #[must_use]
    pub fn up(self) -> Self {
        if self.is_nothing() {
            return self;
        }
        Self {
            low: self.low.saturating_add(1),
            high: self.high.and_then(|high| high.checked_add(1)),
        }
    }

    /// One less, stopping at nought, which is what taking one apart holds.
    #[must_use]
    pub fn down(self) -> Self {
        if self.is_nothing() {
            return self;
        }
        Self {
            low: self.low.saturating_sub(1),
            high: self.high.map(|high| high.saturating_sub(1)),
        }
    }

    /// Both together, which is what adding them answers.
    #[must_use]
    pub fn plus(self, other: Self) -> Self {
        if self.is_nothing() || other.is_nothing() {
            return Self::NOTHING;
        }
        Self {
            low: self.low.saturating_add(other.low),
            high: self
                .high
                .zip(other.high)
                .and_then(|(a, b)| a.checked_add(b)),
        }
    }

    /// How many bits hold every number this could be, where anything does.
    #[must_use]
    pub fn width(self) -> Option<u32> {
        let high = self.high?;
        Some(u64::BITS - high.leading_zeros())
    }

    /// Whether this says less than `other` does, which is what says a walk
    /// has settled.
    const fn within(self, other: Self) -> bool {
        if self.is_nothing() {
            return true;
        }
        if other.is_nothing() {
            return false;
        }
        self.low >= other.low
            && match (self.high, other.high) {
                (_, None) => true,
                (None, Some(_)) => false,
                (Some(held), Some(other)) => held <= other,
            }
    }
}

/// Whether a value these bounds hold could be built with this constructor.
/// Nought is not a `Succ` of anything and nothing above nought is `Zero`,
/// and a tag is the one number it is.
fn reaches(program: &Program, held: Bounds, spine: Shape, ctor: CtorId) -> bool {
    match spine {
        Shape::Spine { nil, .. } if ctor == nil => held.low == 0,
        Shape::Spine { .. } => held.high != Some(0),
        Shape::Tagged => {
            let tag = u64::from(program.tag(ctor));
            held.low <= tag && held.high.is_none_or(|high| tag <= high)
        }
    }
}

/// How many times the walk goes round before it stops trying to be exact.
/// A definition that counts up without a last step grows every round, and
/// past this a growing bound is answered with no bound at all.
const WIDEN: usize = 8;

/// And how many times it goes round at all. Past widening a bound only ever
/// settles, so this is the room that takes rather than a guess.
const ROUNDS: usize = 24;

/// What every local of every function holds, by the level it takes.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(super) struct Known {
    /// What each term answers, by the term.
    pub terms: Vec<Bounds>,
    /// What each definition is handed, by definition.
    pub takes: Vec<Vec<Bounds>>,
    /// And what each answers.
    pub answers: Vec<Bounds>,
}

pub(super) fn walk(program: &Program, operations: &[Option<super::Operation>]) -> Known {
    let count = program.functions().len();
    let entry = program.entry();
    // A parameter nothing has handed anything to yet is a parameter nothing
    // is known of, which is not the same as one anything could be handed.
    let mut held = Held {
        params: (0..count)
            .map(|at| {
                let held = program.params(FnId::at(at)).len();
                let outside = entry == Some(FnId::at(at));
                vec![outside.then_some(Bounds::ANY); held]
            })
            .collect(),
        results: vec![None; count],
        terms: vec![Bounds::NOTHING; program.exprs_count()],
    };

    let mut settled = false;
    for round in 0..ROUNDS {
        let mut again = false;
        for at in 0..count {
            again |= once(program, operations, &mut held, (FnId::at(at), round));
        }
        if !again {
            settled = true;
            break;
        }
    }

    // A bound still on its way up is a bound too small, and a bound too
    // small is the one mistake this must not make: it would hold a value in
    // fewer bits than the value has. Widening settles what recursion leaves
    // growing, so reaching here means something grew in a way widening does
    // not reach -- and then nothing here is known.
    if !settled {
        held.terms.fill(Bounds::ANY);
        held.params.iter_mut().flatten().for_each(|held| {
            *held = Some(Bounds::ANY);
        });
        held.results.fill(Some(Bounds::ANY));
    }

    known(held)
}

/// What the walk worked out, as the tier below reads it.
fn known(held: Held) -> Known {
    // A term nothing reached is a term nothing knows, and so is a parameter
    // nothing was ever handed.
    Known {
        terms: held
            .terms
            .into_iter()
            .map(|held| anything(Some(held)))
            .collect(),
        takes: held
            .params
            .into_iter()
            .map(|held| held.into_iter().map(anything).collect())
            .collect(),
        answers: held.results.into_iter().map(anything).collect(),
    }
}

/// What nothing known comes out as. The walk starts at nothing so that one
/// name's ignorance does not spread to every name that calls it; what comes
/// out is read by a tier that has to hold something, and nothing known
/// there means anything at all.
const fn anything(held: Option<Bounds>) -> Bounds {
    match held {
        Some(held) if !held.is_nothing() => held,
        _ => Bounds::ANY,
    }
}

/// What the walk has worked out so far, which is what it goes round again
/// to add to.
struct Held {
    params: Vec<Vec<Option<Bounds>>>,
    results: Vec<Option<Bounds>>,
    terms: Vec<Bounds>,
}

/// One definition, once. Answers whether anything it worked out was more
/// than what was already known, which is what says to go round again.
fn once(
    program: &Program,
    operations: &[Option<super::Operation>],
    held: &mut Held,
    (id, round): (FnId, usize),
) -> bool {
    let at = id.index();
    let params: Option<Vec<Bounds>> = held.params[at].iter().copied().collect();
    let Some(params) = params else { return false };
    let Some(body) = program.function(id).body else {
        // Something outside answers, and nothing about a declaration can be
        // read, so what comes back from one is anything at all.
        return settle(&mut held.results[at], Bounds::ANY, round);
    };

    let results = held.results.clone();
    let mut walk = Walk {
        program,
        operations,
        results: &results,
        scope: params,
        terms: std::mem::take(&mut held.terms),
        calls: Vec::new(),
    };
    let answer = walk.body(body);
    held.terms = walk.terms;

    let mut again = settle(&mut held.results[at], answer, round);
    for (called, args) in walk.calls {
        for (at, bounds) in args.into_iter().enumerate() {
            again |= settle(&mut held.params[called.index()][at], bounds, round);
        }
    }
    again
}

/// Widen `held` by `found`, answering whether that changed it. Past the
/// rounds worth being exact for, a bound that grows is given no bound: a
/// definition counting up without a last step would otherwise be walked
/// once for every number it can reach.
fn settle(held: &mut Option<Bounds>, found: Bounds, round: usize) -> bool {
    let Some(before) = *held else {
        *held = Some(found);
        return true;
    };
    if found.within(before) {
        return false;
    }
    let after = before.or(found);
    *held = Some(if round < WIDEN {
        after
    } else {
        Bounds {
            low: after.low.min(before.low),
            high: None,
        }
    });
    *held != Some(before)
}

/// One walk over one definition, with what it hands to what it calls.
struct Walk<'a> {
    program: &'a Program,
    operations: &'a [Option<super::Operation>],
    results: &'a [Option<Bounds>],
    /// What each level holds here, which arms take back as they end.
    scope: Vec<Bounds>,
    /// And what each term answers, joined over every walk of it.
    terms: Vec<Bounds>,
    calls: Vec<(FnId, Vec<Bounds>)>,
}

impl Walk<'_> {
    fn body(&mut self, body: Body) -> Bounds {
        for binding in self.program.bindings(body.bindings).to_vec() {
            let held = self.expr(binding);
            self.scope.push(held);
        }
        self.expr(body.tail)
    }

    /// What a term answers, held against the term so that the tier below
    /// has it where it walks.
    fn expr(&mut self, id: super::ir::ExprId) -> Bounds {
        let held = self.worked(id);
        self.terms[id.index()] = self.terms[id.index()].or(held);
        held
    }

    fn worked(&mut self, id: super::ir::ExprId) -> Bounds {
        match self.program.expr(id) {
            Expr::Atom(atom) => self.scope[atom.0.index()],
            Expr::Static(owner, value) => {
                let bytes = self.program.known_bytes(value);
                as_number(self.program, owner, bytes).map_or(Bounds::ANY, Bounds::at)
            }
            Expr::Con(ctor, args) => self.built(ctor, args),
            Expr::Call(called, args) => {
                let held: Vec<Bounds> = self
                    .program
                    .atoms(args)
                    .iter()
                    .map(|atom| self.scope[atom.0.index()])
                    .collect();
                // An operation the tiers below have is one this knows the
                // answer of, which is what keeps a recursion exact.
                let answer = match self.operations.get(called.index()).copied().flatten() {
                    Some(super::Operation::Add) => held[0].plus(held[1]),
                    // A name nothing has worked out yet answers nothing yet.
                    None => self.results[called.index()].unwrap_or(Bounds::NOTHING),
                };
                self.calls.push((called, held));
                answer
            }
            Expr::Match(scrutinee, arms) => self.branch(scrutinee.0.index(), arms),
        }
    }

    /// A number's empty constructor is nought and its other one is one more
    /// than what it wraps. A tag is which constructor it is.
    fn built(&self, ctor: CtorId, args: super::ir::Range) -> Bounds {
        let owner = self.program.ctor(ctor).owner;
        let Shape::Spine { nil, cons, .. } = shape(self.program, owner) else {
            return Bounds::at(u64::from(self.program.tag(ctor)));
        };
        if self.program.fields(cons).len() != 1 {
            return Bounds::ANY;
        }
        if ctor == nil {
            return Bounds::at(0);
        }
        self.program
            .atoms(args)
            .first()
            .map_or(Bounds::ANY, |atom| self.scope[atom.0.index()].up())
    }

    /// Each arm in turn, with what the constructor it matched says of the
    /// value it took apart. What the match holds is what any arm holds.
    fn branch(&mut self, scrutinee: usize, arms: super::ir::Range) -> Bounds {
        let owner = self.program.ctor(self.program.arms(arms)[0].ctor).owner;
        let spine = shape(self.program, owner);
        let mut answer = None;
        for arm in self.program.arms(arms).to_vec() {
            let level = self.scope.len();
            let held = self.scope[scrutinee];
            let fields = self.program.fields(arm.ctor).len();
            // An arm the value cannot be is an arm nothing reaches, and what
            // it answers is not what the match answers.
            if !reaches(self.program, held, spine, arm.ctor) {
                continue;
            }
            match spine {
                Shape::Spine { nil, .. } if arm.ctor == nil => {
                    self.scope[scrutinee] = Bounds::at(0);
                }
                Shape::Spine { .. } => {
                    // One apart from what it wraps, and never nought here.
                    self.scope[scrutinee] = Bounds {
                        low: held.low.max(1),
                        high: held.high,
                    };
                    let inner = self.scope[scrutinee].down();
                    for _ in 0..fields {
                        self.scope.push(inner);
                    }
                }
                Shape::Tagged => {
                    self.scope[scrutinee] = Bounds::at(u64::from(self.program.tag(arm.ctor)));
                    for _ in 0..fields {
                        self.scope.push(Bounds::ANY);
                    }
                }
            }
            let found = self.body(arm.body);
            answer = Some(answer.map_or(found, |held: Bounds| held.or(found)));
            self.scope.truncate(level);
            self.scope[scrutinee] = held;
        }
        // Where no arm is reached, nothing is: a value nothing knows yet is
        // a value no constructor could have built.
        answer.unwrap_or(Bounds::NOTHING)
    }
}
