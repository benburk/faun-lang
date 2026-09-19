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

    /// The intersection is what a branch establishes in addition to its input.
    #[must_use]
    pub fn and(self, other: Self) -> Self {
        Self {
            low: self.low.max(other.low),
            high: match (self.high, other.high) {
                (Some(a), Some(b)) => Some(a.min(b)),
                (a, b) => a.or(b),
            },
        }
    }

    #[must_use]
    pub fn monus(self, other: Self) -> Self {
        if self.is_nothing() || other.is_nothing() {
            return Self::NOTHING;
        }
        Self {
            low: other.high.map_or(0, |b| self.low.saturating_sub(b)),
            high: self.high.map(|a| a.saturating_sub(other.low)),
        }
    }

    #[must_use]
    pub fn times(self, other: Self) -> Self {
        if self.is_nothing() || other.is_nothing() {
            return Self::NOTHING;
        }
        if self.high == Some(0) || other.high == Some(0) {
            return Self::at(0);
        }
        Self {
            low: self.low.saturating_mul(other.low),
            high: self
                .high
                .zip(other.high)
                .and_then(|(a, b)| a.checked_mul(b)),
        }
    }

    #[must_use]
    pub fn quotient(self, other: Self) -> Self {
        if self.is_nothing() || other.is_nothing() {
            return Self::NOTHING;
        }
        if other.high == Some(0) {
            return Self::at(0);
        }
        Self {
            low: if other.low == 0 {
                0
            } else {
                other.high.map_or(0, |b| self.low / b)
            },
            high: self.high.map(|a| a / other.low.max(1)),
        }
    }

    #[must_use]
    pub fn remainder(self, other: Self) -> Self {
        if self.is_nothing() || other.is_nothing() {
            return Self::NOTHING;
        }
        if other.high == Some(0) {
            return self;
        }
        let high = if other.low == 0 {
            self.high
        } else {
            match (self.high, other.high.map(|b| b.saturating_sub(1))) {
                (Some(a), Some(b)) => Some(a.min(b)),
                (a, b) => a.or(b),
            }
        };
        Self { low: 0, high }
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
    pub matched: Vec<Bounds>,
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
        matched: vec![Bounds::NOTHING; program.exprs_count()],
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
        held.matched.fill(Bounds::ANY);
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
        matched: held
            .matched
            .into_iter()
            .map(|held| anything(Some(held)))
            .collect(),
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
    matched: Vec<Bounds>,
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
    let Some(body) = program.function(id).body() else {
        // Something outside answers, and nothing about a declaration can be
        // read, so what comes back from one is anything at all.
        return settle(
            &mut held.results[at],
            program.function(id).bounds().unwrap_or(Bounds::ANY),
            round,
        );
    };

    // A recognized equation is evaluated as that operation, not walked as
    // unary recursion. Besides being cheaper, this avoids widening a huge
    // countdown one predecessor at a time.
    if let Some(op) = operations[at] {
        return settle(
            &mut held.results[at],
            operation(program, op, params[0], params[1]),
            round,
        );
    }

    let results = held.results.clone();
    let mut walk = Walk {
        program,
        operations,
        results: &results,
        predicates: vec![None; params.len()],
        scope: params,
        terms: std::mem::take(&mut held.terms),
        matched: std::mem::take(&mut held.matched),
        calls: Vec::new(),
    };
    let answer = walk.body(body);
    held.terms = walk.terms;
    held.matched = walk.matched;

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
    predicates: Vec<Option<(super::Operation, usize, usize)>>,
    /// And what each term answers, joined over every walk of it.
    terms: Vec<Bounds>,
    matched: Vec<Bounds>,
    calls: Vec<(FnId, Vec<Bounds>)>,
}

impl Walk<'_> {
    fn body(&mut self, body: Body) -> Bounds {
        for binding in self.program.bindings(body.bindings).to_vec() {
            let held = self.expr(binding);
            if let Expr::Call(called, _) = self.program.expr(binding)
                && self
                    .program
                    .ctors(self.program.function(called).result)
                    .is_empty()
            {
                return Bounds::NOTHING;
            }
            let predicate = match self.program.expr(binding) {
                Expr::Call(called, args) => {
                    let op = self.operations[called.index()];
                    match op {
                        Some(
                            op @ (super::Operation::Equals { .. }
                            | super::Operation::LessThan { .. }),
                        ) => {
                            let args = self.program.atoms(args);
                            Some((op, args[0].0.index(), args[1].0.index()))
                        }
                        _ => None,
                    }
                }
                Expr::Atom(a) => self.predicates[a.0.index()],
                _ => None,
            };
            self.scope.push(held);
            self.predicates.push(predicate);
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
                if let Some(number) = as_number(self.program, owner, bytes) {
                    return Bounds::at(number);
                }
                if self
                    .program
                    .ctors(owner)
                    .iter()
                    .all(|c| self.program.types_of(c.fields).is_empty())
                {
                    return Bounds::at(u64::from(
                        self.program
                            .tag(super::decode(self.program, owner, bytes).0.0),
                    ));
                }
                Bounds::ANY
            }
            Expr::Con(ctor, args) => self.built(ctor, args),
            Expr::Call(called, args) => self.call(called, args),
            Expr::Match(scrutinee, arms) => {
                self.matched[id.index()] =
                    self.matched[id.index()].or(self.scope[scrutinee.0.index()]);
                self.branch(scrutinee.0.index(), arms)
            }
        }
    }

    fn call(&mut self, called: FnId, args: super::Range) -> Bounds {
        let held: Vec<Bounds> = self
            .program
            .atoms(args)
            .iter()
            .map(|atom| self.scope[atom.0.index()])
            .collect();
        let answer = match self.operations.get(called.index()).copied().flatten() {
            Some(op) => operation(self.program, op, held[0], held[1]),
            None => self.results[called.index()].unwrap_or(Bounds::NOTHING),
        };
        self.calls.push((called, held));
        if self
            .program
            .ctors(self.program.function(called).result)
            .is_empty()
        {
            Bounds::NOTHING
        } else {
            answer
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
        let mut answer = None;
        let outer = self.scope.clone();
        let predicates = self.predicates.clone();
        let mut surviving: Option<Vec<Bounds>> = None;
        for arm in self.program.arms(arms).to_vec() {
            self.scope.clone_from(&outer);
            self.predicates.clone_from(&predicates);
            let level = self.scope.len();
            if !self.enter(scrutinee, arm.ctor) {
                continue;
            }
            let found = self.body(arm.body);
            answer = Some(answer.map_or(found, |held: Bounds| held.or(found)));
            if !found.is_nothing() {
                let inner = &self.scope[..level];
                if let Some(surviving) = &mut surviving {
                    for (held, found) in surviving.iter_mut().zip(inner) {
                        *held = held.or(*found);
                    }
                } else {
                    surviving = Some(inner.to_vec());
                }
            }
        }
        self.scope = surviving.unwrap_or(outer);
        self.predicates = predicates;
        // Where no arm is reached, nothing is: a value nothing knows yet is
        // a value no constructor could have built.
        answer.unwrap_or(Bounds::NOTHING)
    }

    fn enter(&mut self, scrutinee: usize, ctor: CtorId) -> bool {
        let held = self.scope[scrutinee];
        let spine = shape(self.program, self.program.ctor(ctor).owner);
        if !reaches(self.program, held, spine, ctor) {
            return false;
        }
        let field = match spine {
            Shape::Spine { nil, .. } if ctor == nil => {
                self.scope[scrutinee] = Bounds::at(0);
                Bounds::NOTHING
            }
            Shape::Spine { .. } => {
                self.scope[scrutinee] = Bounds {
                    low: held.low.max(1),
                    high: held.high,
                };
                self.scope[scrutinee].down()
            }
            Shape::Tagged => {
                self.scope[scrutinee] = Bounds::at(u64::from(self.program.tag(ctor)));
                Bounds::ANY
            }
        };
        self.scope
            .resize(self.scope.len() + self.program.fields(ctor).len(), field);
        if let Some((op, left, right)) = self.predicates[scrutinee] {
            let (a, b) = refine(op, ctor, self.scope[left], self.scope[right]);
            self.scope[left] = a;
            self.scope[right] = b;
            if a.is_nothing() || b.is_nothing() {
                return false;
            }
        }
        self.predicates.resize(self.scope.len(), None);
        true
    }
}

fn operation(program: &Program, op: super::Operation, a: Bounds, b: Bounds) -> Bounds {
    use super::Operation;
    if a.is_nothing() || b.is_nothing() {
        return Bounds::NOTHING;
    }
    let (yes, no, decided) = match op {
        Operation::Add => return a.plus(b),
        Operation::Monus => return a.monus(b),
        Operation::Mul => return a.times(b),
        Operation::Div => return a.quotient(b),
        Operation::Mod => return a.remainder(b),
        Operation::Equals { yes, no } => (
            yes,
            no,
            if a.high == Some(a.low) && b.high == Some(b.low) {
                Some(a.low == b.low)
            } else if a.high.is_some_and(|a| a < b.low) || b.high.is_some_and(|b| b < a.low) {
                Some(false)
            } else {
                None
            },
        ),
        Operation::LessThan { yes, no } => (
            yes,
            no,
            if a.high.is_some_and(|a| a < b.low) {
                Some(true)
            } else if b.high.is_some_and(|b| a.low >= b) {
                Some(false)
            } else {
                None
            },
        ),
    };
    let yes = Bounds::at(u64::from(program.tag(yes)));
    let no = Bounds::at(u64::from(program.tag(no)));
    decided.map_or_else(|| yes.or(no), |held| if held { yes } else { no })
}

fn exclude(held: Bounds, other: Bounds) -> Bounds {
    if other.high != Some(other.low) {
        return held;
    }
    if held.low == other.low {
        return held.and(Bounds {
            low: held.low.saturating_add(1),
            high: None,
        });
    }
    if held.high == Some(other.low) {
        return held.and(Bounds {
            low: 0,
            high: other.low.checked_sub(1),
        });
    }
    held
}

fn refine(op: super::Operation, ctor: CtorId, a: Bounds, b: Bounds) -> (Bounds, Bounds) {
    use super::Operation;
    match op {
        Operation::Equals { yes, .. } if ctor == yes => (a.and(b), b.and(a)),
        Operation::Equals { .. } => (exclude(a, b), exclude(b, a)),
        Operation::LessThan { yes, .. } if ctor == yes => {
            let a_limit = b.high.map_or(Bounds::ANY, |high| {
                high.checked_sub(1).map_or(Bounds::NOTHING, |high| Bounds {
                    low: 0,
                    high: Some(high),
                })
            });
            (
                a.and(a_limit),
                b.and(Bounds {
                    low: a.low.saturating_add(1),
                    high: None,
                }),
            )
        }
        Operation::LessThan { .. } => (
            a.and(Bounds {
                low: b.low,
                high: None,
            }),
            b.and(Bounds {
                low: 0,
                high: a.high,
            }),
        ),
        _ => (a, b),
    }
}
