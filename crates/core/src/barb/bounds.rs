//! What a number can be, worked out from what a program does with it.
//!
//! A type says a value is a number and nothing about which numbers, so
//! deciding how wide to hold one is deciding what it could be. That is a
//! question about terms, not about storage: `Succ` is one more than what it
//! wraps, a match on `Zero` says which argument is nought in which arm, and
//! a call answers whatever the name it calls does. None of it needs a word
//! size, which is why it is worked out here and read below.
//!
//! Every value has an interval, and values the program relates -- compares,
//! adds, steps, hands round a recursion -- have an octagon besides: what
//! holds between two of them, `i < len` or `count + rest <= 5`, so that a
//! bound found of one reaches the other (`notes/machine/ranges.md`). Which
//! values are related is read from each definition before it is walked
//! ([`super::packs`]).
//!
//! What comes out is per term, since that is what the tier deciding
//! representation walks: every term has an answer, so how wide to hold what
//! it answers is a question with one. A term walked more than once -- an
//! arm reached at two widths, a definition gone round again -- holds what
//! it held at any of them.
//!
//! A field is held the same way: every value built into one field of one
//! constructor, anywhere, is what reading that field back can answer. That
//! is what lets a number inside a product be held as narrowly as a number
//! outside one. A value no walk sees built -- handed in at the entry, or
//! answered by something outside -- could hold anything in any field it
//! reaches.
//!
//! Nothing here is exact. A bound too wide costs a wider number and never a
//! wrong one, so where the walk cannot say -- a definition that counts up
//! without a last step, an argument from outside -- it says so and the
//! tiers below hold what they must.

use std::cell::RefCell;
use std::collections::{BTreeSet, HashSet};
use std::rc::Rc;

use super::facts::{Recognised, SequenceOperation};
use super::model::{Body, CtorId, Expr, ExprId, FnId, Range, TypeId};
use super::octagon::{Bound, Constraint, INFINITE, Octagon, node};
use super::packs::{Layout, Place};
use super::program::Program;
use super::{Shape, shape, single_field};
pub use crate::facts::Facts as Bounds;

/// Whether a value these bounds hold could be built with this constructor.
/// Nought is not a `Succ` of anything and nothing above nought is `Zero`,
/// and a tag is the one number it is.
fn reaches(program: &Program, held: Bounds, spine: Shape, ctor: CtorId) -> bool {
    if single_field(program, program.ctor(ctor).owner).is_some() {
        return true;
    }
    match spine {
        Shape::Spine { nil, .. } if ctor == nil => held.low == 0,
        Shape::Spine { .. } => held.high != Some(0),
        Shape::Tagged => {
            let tag = u64::from(program.tag(ctor));
            held.low <= tag && held.high.is_none_or(|high| tag <= high)
        }
    }
}

/// How many times a value may grow before it is widened. A definition that
/// counts up without a last step grows every time it is walked, and past
/// this a growing bound jumps to the next machine width, and past the
/// widest to none, so that every value grows only a few more times and the
/// walk settles.
const WIDEN: usize = 8;

/// How many times the walk goes round afterwards to take back what widening
/// gave up. Each round carries a narrower bound one call further.
const NARROWINGS: usize = 8;

/// An entry of what a definition is handed that no call has said yet:
/// joining anything to it is that thing.
const UNSAID: Bound = -INFINITE;

/// Final conservative ranges consumed by lowering.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(super) struct Ranges {
    /// What each term answers, by the term.
    pub terms: Vec<Bounds>,
    pub matched: Vec<Bounds>,
    pub arguments: Vec<Vec<Bounds>>,
    /// What each definition is handed, by definition.
    pub takes: Vec<Vec<Bounds>>,
    /// And what each answers.
    pub answers: Vec<Bounds>,
    /// What each constructor field holds, by its place in the field pool.
    pub fields: Vec<Bounds>,
}

/// What stays the same while the walk goes round: each definition's packs,
/// and which definitions to walk again when something changes.
struct Plan {
    layouts: Vec<Layout>,
    /// The matches of each definition whose answer is matched again on its
    /// tag: see [`super::packs::told`].
    told: Vec<HashSet<ExprId>>,
    /// Where each definition comes in the order walked: callers first.
    rank: Vec<usize>,
    /// Who calls each definition.
    callers: Vec<Vec<usize>>,
    /// Who reads each field, by its place in the field pool.
    readers: Vec<Vec<usize>>,
    /// Where a growing bound is widened to.
    thresholds: Thresholds,
    /// What held where each definition's walk last started, and what it
    /// was handed then: a definition walked again for what something it
    /// calls answers, handed the same, starts the same, and closing what
    /// it is handed again would cost a cube of its packs each time.
    started: RefCell<Vec<Option<(Entry, State, bool)>>>,
}

/// Where a growing bound is widened to: the next width a machine holds a
/// number in, the most any sequence's length can be, or one less than a
/// number the program takes a remainder by, and no bound past the widest.
/// A value kept below a divisor by a remainder settles there rather than at
/// the next width, and so does a length below the most a length can be: a
/// field copied into itself, or an answer read back by the call that
/// answers it, keeps what it was widened to, which narrowing cannot take
/// back. What holds between two values is widened only to the widths.
struct Thresholds {
    bounds: Vec<Bound>,
    relations: Vec<Bound>,
}

/// One less than every constant `body` takes a remainder by, into `found`;
/// `known` is the constant each level in scope is, where it is one.
fn divisors(
    program: &Program,
    recognised: &Recognised,
    body: Body,
    known: &mut Vec<Option<u64>>,
    found: &mut Vec<Bound>,
) {
    let level = known.len();
    let exprs = program
        .bindings(body.bindings)
        .iter()
        .copied()
        .chain([body.tail]);
    for expr in exprs {
        let constant = match program.expr(expr) {
            Expr::Static(value) => match program.constant(value).view() {
                super::ConstantView::Natural(number) => number.try_u64().ok(),
                _ => None,
            },
            Expr::Atom(atom) => known[atom.0.index()],
            Expr::Call(called, args) => {
                if recognised.operations[called.index()] == Some(super::Operation::Mod)
                    && let Some(&Some(divisor)) = program
                        .atoms(args)
                        .get(1)
                        .map(|atom| &known[atom.0.index()])
                    && divisor > 0
                {
                    found.push(Bound::from(divisor) - 1);
                }
                None
            }
            Expr::Match(_, arms) => {
                for arm in program.arms(arms) {
                    let inner = known.len();
                    known.resize(inner + program.fields(arm.ctor).len(), None);
                    divisors(program, recognised, arm.body, known, found);
                    known.truncate(inner);
                }
                None
            }
            Expr::Con(..) => None,
        };
        known.push(constant);
    }
    known.truncate(level);
}

impl Thresholds {
    fn new(program: &Program, recognised: &Recognised, assumed: &Assumed) -> Self {
        let widths: Vec<Bound> = [
            0,
            Bound::from(u8::MAX),
            Bound::from(u16::MAX),
            Bound::from(u32::MAX),
            Bound::from(u64::MAX),
        ]
        .into();
        let mut relations = widths;
        relations.extend(
            assumed
                .length
                .and_then(|length| length.high)
                .map(Bound::from),
        );
        relations.sort_unstable();
        let mut bounds = relations.clone();
        for (at, function) in program.functions().iter().enumerate() {
            if let Some(body) = function.body() {
                let params = program.params(FnId::at(at)).len();
                divisors(
                    program,
                    recognised,
                    body,
                    &mut vec![None; params],
                    &mut bounds,
                );
            }
        }
        bounds.sort_unstable();
        bounds.dedup();
        Self { bounds, relations }
    }

    /// The least threshold for a bound at least `bound`, or no bound.
    fn above(&self, bound: Bound) -> Bound {
        Self::next(&self.bounds, bound)
    }

    /// The least threshold for a relation at least `bound`, or no bound.
    fn relation(&self, bound: Bound) -> Bound {
        Self::next(&self.relations, bound)
    }

    fn next(thresholds: &[Bound], bound: Bound) -> Bound {
        let at = thresholds.partition_point(|&threshold| threshold < bound);
        thresholds.get(at).copied().unwrap_or(INFINITE)
    }
}

impl Plan {
    #[expect(
        clippy::too_many_lines,
        reason = "what stays the same while the walk goes round, read off the program in one pass"
    )]
    fn new(program: &Program, recognised: &Recognised, assumed: &Assumed) -> Self {
        let count = program.functions().len();
        let calls = super::calls::graph(program);
        let rounds = super::calls::rounds(&calls);
        let mut round = vec![0; count];
        let mut rank = vec![0; count];
        // The rounds come callees first; walking callers first carries what
        // a caller hands down before what it is answered comes back.
        for (at, members) in rounds.iter().enumerate() {
            for id in members {
                round[id.index()] = at;
                rank[id.index()] = at;
            }
        }
        let recursive = super::calls::recursive(program);
        let layouts: Vec<Layout> = (0..count)
            .map(|at| super::packs::layout(program, recognised, FnId::at(at), &round, &recursive))
            .collect();
        let mut callers = vec![Vec::new(); count];
        for (at, callees) in calls.iter().enumerate() {
            for callee in callees {
                callers[callee.index()].push(at);
            }
        }
        let slots = field_slots(program);
        let mut readers = vec![Vec::new(); slots];
        for (at, function) in program.functions().iter().enumerate() {
            let Some(body) = function.body() else {
                continue;
            };
            for expr in super::walk::within(program, body) {
                if let Expr::Match(_, arms) = program.expr(expr) {
                    for arm in program.arms(arms) {
                        for place in program.ctor(arm.ctor).fields.range() {
                            readers[place].push(at);
                        }
                    }
                }
            }
        }
        let told = program
            .functions()
            .iter()
            .enumerate()
            .map(|(at, function)| {
                function.body().map_or_else(HashSet::new, |body| {
                    super::packs::told(program, body, program.params(FnId::at(at)).len())
                })
            })
            .collect();
        Self {
            layouts,
            told,
            rank,
            callers,
            readers,
            thresholds: Thresholds::new(program, recognised, assumed),
            started: RefCell::new(vec![None; count]),
        }
    }
}

pub(super) fn analyze(program: &Program, recognised: &Recognised, assumed: &Assumed) -> Ranges {
    let count = program.functions().len();
    let plan = Plan::new(program, recognised, assumed);
    let mut held = Propagation::start(program, assumed);

    // Walk every definition, and again each whose inputs grew, callers
    // first, until nothing grows. Every value is widened once it has grown
    // a few times, so this ends.
    let mut waiting: BTreeSet<(usize, usize)> = (0..count).map(|at| (plan.rank[at], at)).collect();
    // A sweep walks what is waiting in order, going on past each to the
    // next waiting after it, and the next sweep starts again from the first.
    let mut after = (0, 0);
    loop {
        let next = waiting.range(after..).next().copied();
        let Some(next) = next.or_else(|| {
            held.grown.sweep += 1;
            waiting.first().copied()
        }) else {
            break;
        };
        waiting.remove(&next);
        after = (next.0, next.1 + 1);
        let grown = once(
            program,
            recognised,
            assumed,
            &plan,
            &mut held,
            FnId::at(next.1),
        );
        waiting.extend(grown.into_iter().map(|at| (plan.rank[at], at)));
    }

    // Widening gives up more than recursion needs it to: a remainder of a
    // count that grew is still below its divisor, and what is handed that
    // remainder is too. Going round again from a bound that holds, without
    // widening, only takes away what nothing reaches.
    held.settled = true;
    for _ in 0..NARROWINGS {
        let next = narrowed(program, recognised, assumed, &plan, &held);
        if next == held {
            break;
        }
        held = next;
    }

    Ranges {
        arguments: argument_bounds(program, recognised, assumed, &plan, &held),
        ..finish(program, assumed, &plan, held)
    }
}

/// Read operand ranges under each branch from the settled analysis.
fn argument_bounds(
    program: &Program,
    recognised: &Recognised,
    assumed: &Assumed,
    plan: &Plan,
    held: &Propagation,
) -> Vec<Vec<Bounds>> {
    let mut arguments = vec![Vec::new(); program.exprs_count()];
    let mut terms = vec![Bounds::NOTHING; program.exprs_count()];
    let mut matched = terms.clone();
    for at in 0..program.functions().len() {
        walk(
            (program, recognised, assumed, plan),
            held,
            FnId::at(at),
            (&mut terms, &mut matched),
            Some(&mut arguments),
        );
    }
    for bound in arguments.iter_mut().flatten() {
        *bound = anything(Some(*bound));
    }
    arguments
}

/// What the tier lowering a program assumes of values that come from
/// outside it: what its routines answer and what its target hands the entry.
///
/// Barb works out what the program itself says and nothing about any
/// target; these are asked of an analysis by the tier that knows the target,
/// and what comes out belongs to that tier, never to the program.
#[derive(Clone, Debug, Default)]
pub struct Assumed {
    /// What a declaration with no body answers.
    pub results: Vec<(FnId, Bounds)>,
    /// What the entry's parameters are handed, by place.
    pub parameters: Vec<(usize, Bounds)>,
    /// What every value of a constructor holds in one field.
    pub fields: Vec<(CtorId, usize, Bounds)>,
    /// What any sequence's length can be, where anything says.
    pub length: Option<Bounds>,
    /// Whether a recognized float operation is answered by a machine rather
    /// than by its body. This selects native float lowering and range
    /// assumptions; semantic recognition still reads the operation.
    pub floats: bool,
}

impl Assumed {
    fn result(&self, id: FnId) -> Bounds {
        self.results
            .iter()
            .find(|(of, _)| *of == id)
            .map_or(Bounds::ANY, |(_, bounds)| *bounds)
    }

    fn parameter(&self, at: usize) -> Bounds {
        self.parameters
            .iter()
            .find(|(of, _)| *of == at)
            .map_or(Bounds::ANY, |(_, bounds)| *bounds)
    }

    fn field(&self, ctor: CtorId, at: usize) -> Bounds {
        self.fields
            .iter()
            .find(|(of, place, _)| *of == ctor && *place == at)
            .map_or(Bounds::ANY, |(_, _, bounds)| *bounds)
    }

    /// What a value of `ty` built outside is: anything, but for what is
    /// assumed of the one field of each wrapper it is held through. A wrapper
    /// is its field, so that bounds the value itself.
    fn value(&self, program: &Program, ty: TypeId) -> Bounds {
        let mut held = Bounds::ANY;
        let mut ty = ty;
        for _ in 0..program.types().len() {
            let Some((ctor, field)) = single_field(program, ty) else {
                break;
            };
            held = held.and(self.field(ctor, 0));
            ty = field;
        }
        held
    }
}

/// How many field places the program declares, end to end.
fn field_slots(program: &Program) -> usize {
    (0..program.types().len())
        .flat_map(|ty| program.ctors(TypeId::at(ty)))
        .map(|ctor| ctor.fields.range().end)
        .max()
        .unwrap_or(0)
}

/// The place one field of one constructor has in the field pool.
pub(super) fn slot(program: &Program, ctor: CtorId, at: usize) -> usize {
    program.ctor(ctor).fields.range().start + at
}

/// Say that every field reachable from `roots` could hold anything but what
/// is assumed of it: values of those types were built where nothing here
/// walks.
fn unknown(program: &Program, assumed: &Assumed, roots: &[TypeId], fields: &mut [Option<Bounds>]) {
    let mut seen = vec![false; program.types().len()];
    let mut waiting = roots.to_vec();
    while let Some(ty) = waiting.pop() {
        if std::mem::replace(&mut seen[ty.index()], true) {
            continue;
        }
        for (tag, ctor) in program.ctors(ty).iter().enumerate() {
            let id = program.ctor_at(ty, u32::try_from(tag).expect("a sane constructor count"));
            for (at, place) in fields[ctor.fields.range()].iter_mut().enumerate() {
                *place = Some(assumed.field(id, at));
            }
            waiting.extend_from_slice(program.types_of(ctor.fields));
        }
    }
}

/// What the walk worked out, as the tier below reads it.
#[expect(
    clippy::too_many_lines,
    reason = "every table the tier below reads, each from what the walk worked out"
)]
fn finish(program: &Program, assumed: &Assumed, plan: &Plan, held: Propagation) -> Ranges {
    // What a definition is handed is what holds where its walk starts: what
    // its callers handed it, each as tight as what they handed together
    // makes it, which is how a count is bounded by what it walks beside.
    let takes = held
        .entries
        .iter()
        .enumerate()
        .map(|(at, entry)| {
            let params = entry.values.len();
            match started(&plan.layouts[at], entry) {
                Some((state, true)) => state.values[..params]
                    .iter()
                    .map(|&held| anything(Some(held)))
                    .collect(),
                _ => vec![Bounds::ANY; params],
            }
        })
        .collect();
    let mut fields: Vec<_> = held.fields.into_iter().map(anything).collect();
    // A spine's rest is read as a step of its count, not as what was built
    // there, so nothing is said of that field.
    for ty in 0..program.types().len() {
        if let Shape::Spine {
            cons, recursive, ..
        } = shape(program, TypeId::at(ty))
        {
            fields[slot(program, cons, recursive)] = Bounds::ANY;
        }
    }
    // What is assumed of a field holds wherever the value was built.
    for &(ctor, at, bounds) in &assumed.fields {
        let place = slot(program, ctor, at);
        fields[place] = fields[place].and(bounds);
    }
    // A term nothing reached is a term nothing knows, and so is a parameter
    // nothing was ever handed.
    Ranges {
        arguments: Vec::new(),
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
        takes,
        answers: held.results.into_iter().map(anything).collect(),
        fields,
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

/// What every call so far has handed a definition: each parameter's bounds,
/// and what holds between any two of them, as an octagon's entries over the
/// parameters. An entry no call has said is [`UNSAID`].
#[derive(Clone, Debug, PartialEq, Eq)]
struct Entry {
    values: Vec<Option<Bounds>>,
    /// The side of `relations`: twice the parameters, where a pack relates
    /// two of them, and nought where none does.
    side: usize,
    relations: Vec<Bound>,
}

impl Entry {
    fn new(params: usize, relates: bool) -> Self {
        let side = if relates { 2 * params } else { 0 };
        Self {
            values: vec![None; params],
            side,
            relations: vec![UNSAID; side * side],
        }
    }

    fn relation(&self, from: usize, to: usize) -> Bound {
        self.relations[from * self.side + to]
    }

    /// Take in what one call hands, widened where `widen` says. Answers
    /// whether anything grew.
    fn hand(&mut self, handed: &Handed, widen: Option<&Thresholds>) -> bool {
        let mut grew = false;
        for (held, &found) in self.values.iter_mut().zip(&handed.values) {
            grew |= settle(held, found, widen);
        }
        let Some(relations) = &handed.relations else {
            return grew;
        };
        if self.side == 0 {
            return grew;
        }
        for from in 0..self.side {
            for to in 0..self.side {
                let (x, y) = (from / 2, to / 2);
                if x == y || handed.unknown[x] || handed.unknown[y] {
                    continue;
                }
                let found = relations.get(from, to);
                let held = &mut self.relations[from * self.side + to];
                if *held == UNSAID {
                    grew |= found != UNSAID;
                    *held = found;
                } else if found > *held {
                    *held = widen.map_or(found, |thresholds| thresholds.relation(found));
                    grew = true;
                }
            }
        }
        grew
    }
}

/// What one call hands the definition it calls: each argument's bounds, and
/// what holds between them where the caller relates them.
#[derive(Clone, Debug)]
struct Handed {
    values: Vec<Bounds>,
    relations: Option<Octagon>,
    /// Arguments nothing is known of yet, which say nothing of how they
    /// relate to the rest.
    unknown: Vec<bool>,
}

/// What the walk has worked out so far, which is what it goes round again
/// to add to.
#[derive(PartialEq, Eq)]
struct Propagation {
    entries: Vec<Entry>,
    results: Vec<Option<Bounds>>,
    terms: Vec<Bounds>,
    matched: Vec<Bounds>,
    /// What each field was built with, by its place in the field pool.
    fields: Vec<Option<Bounds>>,
    /// How many times each entry, result and field has grown, which says
    /// when to widen it.
    grown: Growth,
    /// Whether the walk has settled, so that a way nothing reaches is one
    /// nothing will: see [`FunctionWalk::sequence`].
    settled: bool,
}

/// How many sweeps each entry, result and field has grown in, and the
/// last it grew in: a value grows at most once a sweep, however many of
/// the definitions a sweep walks hand or build it more.
#[derive(Clone, PartialEq, Eq)]
struct Growth {
    entries: Vec<(usize, usize)>,
    results: Vec<(usize, usize)>,
    fields: Vec<(usize, usize)>,
    /// The sweep under way.
    sweep: usize,
}

/// Count one more sweep `grown` grew in, unless it already grew in this one.
const fn grew((count, last): &mut (usize, usize), sweep: usize) {
    if *last != sweep {
        *last = sweep;
        *count += 1;
    }
}

impl Propagation {
    /// Where the walk starts: nothing known of anything reached from inside,
    /// and anything at all in the fields of what comes in from outside; and
    /// what the tier above assumes of the entry's parameters.
    #[expect(
        clippy::too_many_lines,
        reason = "every table of the walk, as it starts"
    )]
    fn start(program: &Program, assumed: &Assumed) -> Self {
        let count = program.functions().len();
        let entry = program.entry();
        let entries = (0..count)
            .map(|at| {
                let id = FnId::at(at);
                let params = program.params(id);
                // Whether any pack relates two parameters is the walk's to
                // say; the entry records what every call hands either way,
                // so it is sized for it.
                let mut held = Entry::new(params.len(), params.len() > 1);
                if entry == id {
                    for (at, &ty) in params.iter().enumerate() {
                        held.values[at] =
                            Some(assumed.parameter(at).and(assumed.value(program, ty)));
                    }
                }
                held
            })
            .collect();
        let slots = field_slots(program);
        let mut held = Self {
            entries,
            results: vec![None; count],
            terms: vec![Bounds::NOTHING; program.exprs_count()],
            matched: vec![Bounds::NOTHING; program.exprs_count()],
            fields: vec![None; slots],
            grown: Growth {
                entries: vec![(0, usize::MAX); count],
                results: vec![(0, usize::MAX); count],
                fields: vec![(0, usize::MAX); slots],
                sweep: 0,
            },
            settled: false,
        };
        // What comes in from outside was built where no walk sees it.
        let mut outside: Vec<TypeId> = Vec::new();
        for (at, function) in program.functions().iter().enumerate() {
            if entry == FnId::at(at) {
                outside.extend_from_slice(program.params(FnId::at(at)));
            }
            if function.body().is_none() {
                outside.push(function.result);
            }
        }
        unknown(program, assumed, &outside, &mut held.fields);
        held
    }

    /// Take in what one walk found it built and called, answering which
    /// definitions to walk again for what grew: those reading a field that
    /// grew, and those handed more than before. `widen` says whether a
    /// value growing again may be widened, which narrowing never does.
    fn learn(
        &mut self,
        (program, assumed, plan): (&Program, &Assumed, &Plan),
        found: Found,
        widen: bool,
    ) -> Vec<usize> {
        let mut again = Vec::new();
        let mut grew_field = |held: &mut Self, place: usize, bounds: Bounds| {
            let wide = (widen && held.grown.fields[place].0 >= WIDEN).then_some(&plan.thresholds);
            if settle(&mut held.fields[place], bounds, wide) {
                grew(&mut held.grown.fields[place], held.grown.sweep);
                again.extend_from_slice(&plan.readers[place]);
            }
        };
        for (place, bounds) in found.built {
            grew_field(self, place, bounds);
        }
        if !found.outside.is_empty() {
            let before = self.fields.clone();
            unknown(program, assumed, &found.outside, &mut self.fields);
            for (place, (now, before)) in self.fields.iter().zip(before).enumerate() {
                if *now != before {
                    again.extend_from_slice(&plan.readers[place]);
                }
            }
        }
        for (called, handed) in found.calls {
            let at = called.index();
            let wide = (widen && self.grown.entries[at].0 >= WIDEN).then_some(&plan.thresholds);
            if self.entries[at].hand(&handed, wide) {
                grew(&mut self.grown.entries[at], self.grown.sweep);
                again.push(at);
            }
        }
        again
    }
}

/// One definition, once. Answers which definitions to walk again for what
/// it found grew.
fn once(
    program: &Program,
    recognised: &Recognised,
    assumed: &Assumed,
    plan: &Plan,
    held: &mut Propagation,
    id: FnId,
) -> Vec<usize> {
    // Results change only after this walk; borrowing retains the same
    // per-function snapshot without copying the whole table each round.
    let (mut terms, mut matched) = (
        std::mem::take(&mut held.terms),
        std::mem::take(&mut held.matched),
    );
    let walked = walk(
        (program, recognised, assumed, plan),
        held,
        id,
        (&mut terms, &mut matched),
        None,
    );
    held.terms = terms;
    held.matched = matched;
    let Some((answer, found)) = walked else {
        return Vec::new();
    };
    let mut again = held.learn((program, assumed, plan), found, true);
    let at = id.index();
    let wide = (held.grown.results[at].0 >= WIDEN).then_some(&plan.thresholds);
    if settle(&mut held.results[at], answer, wide) {
        grew(&mut held.grown.results[at], held.grown.sweep);
        again.extend_from_slice(&plan.callers[at]);
    }
    again
}

/// Every definition once more, reading only what `held` knows and building
/// what that says afresh. Where `held` already holds everything its walks
/// find, so does the answer, and it holds no more: a bound widened past
/// what the program reaches comes back down.
fn narrowed(
    program: &Program,
    recognised: &Recognised,
    assumed: &Assumed,
    plan: &Plan,
    held: &Propagation,
) -> Propagation {
    let mut next = Propagation::start(program, assumed);
    next.settled = true;
    for at in 0..program.functions().len() {
        let Some((answer, found)) = walk(
            (program, recognised, assumed, plan),
            held,
            FnId::at(at),
            (&mut next.terms, &mut next.matched),
            None,
        ) else {
            continue;
        };
        next.results[at] = Some(answer);
        next.learn((program, assumed, plan), found, false);
    }
    // Narrowing widens nothing, so how often anything grew is as it was.
    next.grown = held.grown.clone();
    next
}

/// What holds where a definition's walk starts, given what it is handed:
/// its parameters' bounds, and what holds between those its packs relate,
/// closed, and whether it can all hold at once. Nothing, while some
/// parameter has been handed nothing.
#[expect(
    clippy::too_many_lines,
    reason = "each pack built from what a definition is handed, and closed"
)]
fn started(layout: &Layout, entry: &Entry) -> Option<(State, bool)> {
    let values: Vec<Bounds> = entry.values.iter().copied().collect::<Option<_>>()?;
    let params = values.len();
    let places: Vec<Place> = (0..params).map(|at| layout.param(at)).collect();
    let mut members: Vec<Vec<usize>> = layout
        .sizes
        .iter()
        .map(|&size| vec![usize::MAX; size])
        .collect();
    for (level, place) in places.iter().enumerate() {
        if let Some((pack, at)) = *place {
            members[pack][at] = level;
        }
    }
    let mut packs = Vec::with_capacity(layout.sizes.len());
    let mut empty = false;
    for (pack, &size) in layout.sizes.iter().enumerate() {
        let mut octagon = Octagon::top(size);
        for (at, &level) in members[pack].iter().enumerate() {
            if level >= params || values[level].is_nothing() {
                continue;
            }
            octagon.bound(at, values[level]);
            if entry.side == 0 {
                continue;
            }
            for (other, &with) in members[pack].iter().enumerate() {
                if with >= params || with == level || values[with].is_nothing() {
                    continue;
                }
                for (from, to) in [(false, false), (false, true), (true, false), (true, true)] {
                    let bound = entry.relation(node(level, from), node(with, to));
                    if bound != UNSAID && bound < INFINITE {
                        octagon.assume(Constraint {
                            from: node(at, from),
                            to: node(other, to),
                            bound,
                        });
                    }
                }
            }
        }
        empty |= !octagon.close();
        packs.push(octagon);
    }
    let fresh = vec![false; values.len()];
    let mut state = State {
        values,
        places,
        packs,
        members,
        fresh,
    };
    let holds = !empty && (0..layout.sizes.len()).all(|pack| state.sync(pack));
    Some((state, holds))
}

/// What one definition answers and hands on, given what `held` knows, with
/// what each of its terms answers joined into `terms` and `matched`. Nothing,
/// while nothing has handed it anything.
#[expect(
    clippy::too_many_lines,
    reason = "the cases a definition is answered by before its body is walked, each short"
)]
fn walk(
    (program, recognised, assumed, plan): (&Program, &Recognised, &Assumed, &Plan),
    held: &Propagation,
    id: FnId,
    (terms, matched): (&mut [Bounds], &mut [Bounds]),
    arguments: Option<&mut [Vec<Bounds>]>,
) -> Option<(Bounds, Found)> {
    let layout = &plan.layouts[id.index()];
    let entry = &held.entries[id.index()];
    let cached = plan.started.borrow()[id.index()]
        .as_ref()
        .filter(|(from, _, _)| from == entry)
        .map(|(_, state, holds)| (state.clone(), *holds));
    let (state, holds) = if let Some(cached) = cached {
        cached
    } else {
        let (state, holds) = started(layout, entry)?;
        plan.started.borrow_mut()[id.index()] = Some((entry.clone(), state.clone(), holds));
        (state, holds)
    };
    // What it is handed cannot all hold at once: no call reaches it.
    if !holds {
        return Some((Bounds::NOTHING, Found::default()));
    }
    let params = &state.values;
    let Some(body) = program.function(id).body() else {
        // Something outside answers, and nothing about a declaration can be
        // read, so what comes back from one is what the tier above said.
        let result = program.function(id).result;
        let answered = assumed.result(id).and(assumed.value(program, result));
        return Some((answered, Found::default()));
    };

    // A recognized equation is evaluated as that operation, not walked as
    // unary recursion. Besides being cheaper, this avoids widening a huge
    // countdown one predecessor at a time.
    if let Some(op) = recognised.operations[id.index()] {
        let answer = operation(program, op, params[0], params[1]);
        return Some((answer, Found::default()));
    }
    // A sequence holds its length, so a count of one reads it; what it can
    // be is what the tier holding sequences says.
    if recognised.sequences[id.index()] == Some(SequenceOperation::Length) {
        return Some((assumed.length.unwrap_or(Bounds::ANY), Found::default()));
    }

    let count = params.len();
    let walk = FunctionWalk {
        id,
        program,
        assumed,
        operations: &recognised.operations,
        sequences: &recognised.sequences,
        layouts: &plan.layouts,
        layout,
        told: &plan.told[id.index()],
        results: &held.results,
        fields: &held.fields,
        built: Vec::new(),
        outside: Vec::new(),
        implied: vec![None; count],
        answered_implied: None,
        exact: vec![None; count],
        state,
        settled: held.settled,
        terms,
        matched,
        arguments,
        calls: Vec::new(),
    };
    Some(walk.finish(body))
}

/// Widen `held` by `found`, answering whether that changed it. Where
/// `widen` says, a bound that grows is widened in the direction it grew --
/// up to the next machine width, and past the widest to no bound at all: a
/// definition counting up without a last step, or down from a large
/// constant, would otherwise be walked once for every number it can reach.
fn settle(held: &mut Option<Bounds>, found: Bounds, widen: Option<&Thresholds>) -> bool {
    // Nothing yet, held or found, is no bound to have moved: the first
    // thing found is what is held, however late it is found.
    let before = match *held {
        Some(before) if !before.is_nothing() => before,
        _ => {
            let changed = *held != Some(found);
            *held = Some(found);
            return changed;
        }
    };
    if found.within(before) {
        return false;
    }
    let after = before.or(found);
    *held = Some(widen.map_or(after, |thresholds| {
        // A bound that moves is given up in the direction it moved: a count
        // going up has no greatest, and one counting down from a large
        // constant has nought as least.
        Bounds {
            low: if after.low < before.low {
                0
            } else {
                before.low
            },
            high: if after.high == before.high {
                before.high
            } else {
                after.high.and_then(|high| {
                    let wide = thresholds.above(Bound::from(high));
                    (wide < INFINITE).then(|| u64::try_from(wide).unwrap_or(u64::MAX))
                })
            },
        }
    }));
    *held != Some(before)
}

/// The most elements of a constant sequence read one by one for what its
/// fields hold; past this, its fields could hold anything.
const ELEMENTS_READ: u64 = 4096;

/// What holds of every level in scope: each one's bounds, and each pack's
/// octagon, kept closed and agreeing with the bounds of the levels in it.
#[derive(Clone, Debug)]
struct State {
    values: Vec<Bounds>,
    /// Where each level is in a pack, where it is in one.
    places: Vec<Place>,
    packs: Vec<Octagon>,
    /// Which level each place of each pack is, where one in scope is: a
    /// level past the scope, or one whose place is another, is not.
    members: Vec<Vec<usize>>,
    /// Whether each level is related to nothing yet, but by its bounds.
    fresh: Vec<bool>,
}

impl State {
    /// Narrow each level of `pack` in scope to what its octagon says of it.
    /// Answers whether every one can still be something.
    fn sync(&mut self, pack: usize) -> bool {
        for at in 0..self.members[pack].len() {
            let level = self.members[pack][at];
            let Some(&held) = self.values.get(level) else {
                continue;
            };
            if self.places[level] != Some((pack, at)) {
                continue;
            }
            if held.is_nothing() {
                continue;
            }
            let narrowed = held.and(self.packs[pack].bounds(at));
            if narrowed.is_nothing() {
                return false;
            }
            self.values[level] = narrowed;
        }
        true
    }

    /// What either of two states holds, of the levels both have.
    fn join(&mut self, other: &Self) {
        for (held, other) in self.values.iter_mut().zip(&other.values) {
            *held = held.or(*other);
        }
        for (held, other) in self.packs.iter_mut().zip(&other.packs) {
            held.join(other);
        }
    }
}

/// Something one term said of the levels before it, held to be said again
/// where the term's answer is matched.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Said {
    /// A constraint between two levels, or of one.
    Holds(Constraint),
    /// A level lies within bounds.
    Within(usize, Bounds),
    /// Two levels are not equal.
    Differ(usize, usize),
}

/// What a value being each of some tags says of the levels before it: for
/// each of a few ranges of tags, what held where one of them was answered.
/// A tag in several ranges holds what all of them say, joined; a tag in
/// none is one the value never is.
type Implications = Vec<(Bounds, Vec<Said>)>;

/// What either of two things said holds: each said by both, the looser.
fn join_said(first: &[Said], second: &[Said]) -> Vec<Said> {
    first
        .iter()
        .filter_map(|&said| match said {
            Said::Holds(constraint) => second.iter().find_map(|other| match *other {
                Said::Holds(other)
                    if other.from == constraint.from && other.to == constraint.to =>
                {
                    Some(Said::Holds(Constraint {
                        bound: constraint.bound.max(other.bound),
                        ..constraint
                    }))
                }
                _ => None,
            }),
            Said::Within(level, bounds) => second.iter().find_map(|other| match *other {
                Said::Within(other, held) if other == level => {
                    Some(Said::Within(level, bounds.or(held)))
                }
                _ => None,
            }),
            Said::Differ(..) => second.contains(&said).then_some(said),
        })
        .collect()
}

/// How a matched constructor's fields are bound: all alike, or each as what
/// was built into it, but for a spine's rest, which is its count less one.
#[derive(Clone, Copy)]
enum Binding {
    Whole(Bounds),
    Built(Option<(usize, Bounds)>),
}

/// What one walk hands on: the arguments it called with, what it built into
/// each field, and the types of values it met built out of sight.
#[derive(Default)]
struct Found {
    calls: Vec<(FnId, Handed)>,
    built: Vec<(usize, Bounds)>,
    outside: Vec<TypeId>,
}

/// One walk over one definition, with what it hands to what it calls.
struct FunctionWalk<'a> {
    /// The definition walked.
    id: FnId,
    program: &'a Program,
    assumed: &'a Assumed,
    operations: &'a [Option<super::Operation>],
    sequences: &'a [Option<SequenceOperation>],
    layouts: &'a [Layout],
    /// Which levels of this definition are related.
    layout: &'a Layout,
    /// Which of its matches are matched again on their tag.
    told: &'a HashSet<ExprId>,
    results: &'a [Option<Bounds>],
    /// What each field was built with so far, and what this walk builds.
    fields: &'a [Option<Bounds>],
    built: Vec<(usize, Bounds)>,
    /// Types of values this walk found built where it cannot see inside.
    outside: Vec<TypeId>,
    /// What holds here of every level, which arms take back as they end.
    state: State,
    /// Whether the walk has settled: see [`Propagation::settled`].
    settled: bool,
    /// What each level being one tag says of the levels before it: a
    /// comparison says what it compared, and a match answering tags what
    /// held in the arms answering each. A guard worked out into a `Bool`
    /// and matched on later narrows what it compared there, as one matched
    /// at once does.
    implied: Vec<Option<Rc<Implications>>>,
    /// What the term last worked out says, where it says anything.
    answered_implied: Option<Rc<Implications>>,
    /// The natural each level is known to be outright, where it is one a
    /// bound cannot say exactly: past what a `u64` holds, `2^64` among
    /// them, which a remainder below it needs to be known as.
    exact: Vec<Option<u128>>,
    /// And what each term answers, joined over every walk of it.
    terms: &'a mut [Bounds],
    arguments: Option<&'a mut [Vec<Bounds>]>,
    matched: &'a mut [Bounds],
    calls: Vec<(FnId, Handed)>,
}

impl FunctionWalk<'_> {
    fn finish(mut self, body: Body) -> (Bounds, Found) {
        let answer = self.body(body);
        (
            answer,
            Found {
                calls: self.calls,
                built: self.built,
                outside: self.outside,
            },
        )
    }

    fn body(&mut self, body: Body) -> Bounds {
        for &binding in self.program.bindings(body.bindings) {
            let held = self.term(binding);
            if let Expr::Call(called, _) = self.program.expr(binding)
                && self
                    .program
                    .ctors(self.program.function(called).result)
                    .is_empty()
            {
                self.record(binding, held);
                return Bounds::NOTHING;
            }
            let implied = self.answered_implied.take();
            let exact = self.exact(binding);
            let level = self.state.values.len();
            self.push(held, self.layout.binding(binding));
            self.implied.push(implied);
            self.exact.push(exact);
            self.relate(level, binding);
            let held = self.state.values[level];
            self.record(binding, held);
        }
        let held = self.term(body.tail);
        self.record(body.tail, held);
        held
    }

    /// Bind the next level to `held`, related to nothing yet.
    fn push(&mut self, held: Bounds, place: Place) {
        let level = self.state.values.len();
        self.state.values.push(held);
        self.state.places.push(place);
        self.state.fresh.push(true);
        if let Some((pack, at)) = place {
            self.state.members[pack][at] = level;
            let octagon = &mut self.state.packs[pack];
            octagon.forget(at);
            if !held.is_nothing() {
                octagon.introduce(at, held);
            }
        }
    }

    /// Narrow `level` to `bounds`, answering whether it can still be
    /// anything at all.
    fn narrow(&mut self, level: usize, bounds: Bounds) -> bool {
        let held = self.state.values[level];
        let narrowed = held.and(bounds);
        if narrowed.is_nothing() {
            return false;
        }
        if narrowed == held {
            return true;
        }
        self.state.values[level] = narrowed;
        let Some((pack, at)) = self.state.places[level] else {
            return true;
        };
        let octagon = &mut self.state.packs[pack];
        if !octagon.add(Constraint::least(at, Bound::from(narrowed.low))) {
            return false;
        }
        if let Some(high) = narrowed.high
            && !octagon.add(Constraint::most(at, Bound::from(high)))
        {
            return false;
        }
        self.state.sync(pack)
    }

    /// Say `constraint` of the levels it names, answering whether they can
    /// all still be something. Two levels in one pack are constrained
    /// there, and the pack closed; any others by their bounds alone.
    fn constrain(&mut self, constraint: Constraint) -> bool {
        // A level less itself is nought.
        if constraint.from == constraint.to {
            return constraint.bound >= 0;
        }
        let (x, y) = constraint.variables();
        self.state.fresh[x] = false;
        self.state.fresh[y] = false;
        let (first, second) = (self.state.values[x], self.state.values[y]);
        if first.is_nothing() || second.is_nothing() {
            return false;
        }
        if let (Some((pack, at)), Some((with, other))) =
            (self.state.places[x], self.state.places[y])
            && pack == with
        {
            if !self.state.packs[pack].add(constraint.renamed(at, other)) {
                return false;
            }
            return self.state.sync(pack);
        }
        let (first, second) = by_bounds(constraint, first, second);
        self.narrow(x, first) && self.narrow(y, second)
    }

    /// Say `x - y` lies between `least` and `most`, where each is said.
    fn between(&mut self, x: usize, y: usize, least: Option<Bound>, most: Option<Bound>) {
        if self.state.values[x].is_nothing() || self.state.values[y].is_nothing() {
            return;
        }
        // Between two values not in one pack, a value just worked out from
        // another by intervals says nothing of it intervals do not.
        let packed = matches!((self.state.places[x], self.state.places[y]),
            (Some((pack, _)), Some((with, _))) if pack == with);
        if !packed {
            return;
        }
        // A value just bound and related to nothing yet holds what the
        // other does, moved: its row is the other's, in time linear in the
        // pack, where closing after a constraint takes its square.
        if self.state.fresh.get(x).copied().unwrap_or(false)
            && let (Some((pack, at)), Some((with, other))) =
                (self.state.places[x], self.state.places[y])
            && pack == with
        {
            self.state.fresh[x] = false;
            if self.state.packs[pack].assign(at, other, least, most) {
                self.state.sync(pack);
            }
            return;
        }
        if let Some(most) = most {
            self.constrain(Constraint::difference(x, y, most));
        }
        if let Some(least) = least {
            self.constrain(Constraint::difference(y, x, -least));
        }
    }

    /// What a binding says of how it stands to the levels it was worked out
    /// from: an alias is what it names, a step one more than what it steps,
    /// a sum more than each operand by the other.
    #[expect(
        clippy::too_many_lines,
        reason = "one arm for each kind of term a binding relates to its operands"
    )]
    fn relate(&mut self, level: usize, binding: ExprId) {
        use super::Operation;
        if self.state.values[level].is_nothing() {
            return;
        }
        let low = |held: Bounds| Some(Bound::from(held.low));
        let high = |held: Bounds| held.high.map(Bound::from);
        match self.program.expr(binding) {
            Expr::Atom(atom) => self.between(level, atom.0.index(), Some(0), Some(0)),
            Expr::Con(ctor, args) => {
                let owner = self.program.ctor(ctor).owner;
                let atoms = self.program.atoms(args);
                if single_field(self.program, owner).is_some() {
                    self.between(level, atoms[0].0.index(), Some(0), Some(0));
                } else if let Shape::Spine { nil, recursive, .. } = shape(self.program, owner)
                    && ctor != nil
                {
                    self.between(level, atoms[recursive].0.index(), Some(1), Some(1));
                }
            }
            Expr::Call(called, args) => {
                let atoms: Vec<usize> = self
                    .program
                    .atoms(args)
                    .iter()
                    .map(|atom| atom.0.index())
                    .collect();
                let held = |at: usize| self.state.values[atoms[at]];
                match (
                    self.operations[called.index()],
                    self.sequences[called.index()],
                ) {
                    (Some(Operation::Add), _)
                    | (None, Some(SequenceOperation::Prepend | SequenceOperation::ReverseOnto)) => {
                        let (a, b) = (held(0), held(1));
                        self.between(level, atoms[0], low(b), high(b));
                        self.between(level, atoms[1], low(a), high(a));
                    }
                    (Some(Operation::Monus), _) | (None, Some(SequenceOperation::Drop)) => {
                        let b = held(1);
                        self.between(level, atoms[0], high(b).map(|high| -high), Some(0));
                    }
                    (None, Some(SequenceOperation::Length | SequenceOperation::Replace)) => {
                        self.between(level, atoms[0], Some(0), Some(0));
                    }
                    (None, Some(SequenceOperation::Append)) => {
                        self.between(level, atoms[0], Some(1), Some(1));
                    }
                    (None, Some(SequenceOperation::Take)) => {
                        self.between(level, atoms[0], None, Some(0));
                        self.between(level, atoms[1], None, Some(0));
                    }
                    _ => {}
                }
            }
            Expr::Static(_) | Expr::Match(..) => {}
        }
    }

    /// Say everything in `said`, answering whether the levels it names can
    /// all still be something.
    #[expect(
        clippy::too_many_lines,
        reason = "what each kind of thing said narrows, and closing each pack once"
    )]
    fn apply(&mut self, said: &[Said]) -> bool {
        // Constraints between two levels of one pack are said together, and
        // the pack closed once where they are many, rather than closed
        // again after each.
        let mut packed: Vec<Vec<Constraint>> = vec![Vec::new(); self.state.packs.len()];
        for &said in said {
            let holds = match said {
                Said::Holds(constraint) => {
                    let (x, y) = constraint.variables();
                    if constraint.from != constraint.to
                        && let (Some((pack, at)), Some((with, other))) =
                            (self.state.places[x], self.state.places[y])
                        && pack == with
                        && !self.state.values[x].is_nothing()
                        && !self.state.values[y].is_nothing()
                    {
                        self.state.fresh[x] = false;
                        self.state.fresh[y] = false;
                        packed[pack].push(constraint.renamed(at, other));
                        true
                    } else {
                        self.constrain(constraint)
                    }
                }
                Said::Within(level, bounds) => self.narrow(level, bounds),
                Said::Differ(a, b) => {
                    let (first, second) = (self.state.values[a], self.state.values[b]);
                    self.narrow(a, exclude(first, second)) && self.narrow(b, exclude(second, first))
                }
            };
            if !holds {
                return false;
            }
        }
        for (pack, constraints) in packed.into_iter().enumerate() {
            if constraints.is_empty() {
                continue;
            }
            let octagon = &mut self.state.packs[pack];
            let holds = if constraints.len() * 6 > 2 * octagon.variables() {
                for &constraint in &constraints {
                    octagon.assume(constraint);
                }
                octagon.close()
            } else {
                constraints
                    .iter()
                    .all(|&constraint| octagon.add(constraint))
            };
            if !holds || !self.state.sync(pack) {
                return false;
            }
        }
        true
    }

    /// What holds now of the first `level` levels beyond what held in
    /// `outer`: each level narrowed, and each constraint between two of
    /// them tightened.
    fn said_since(&self, outer: &State, level: usize) -> Vec<Said> {
        let mut said: Vec<Said> = (0..level)
            .filter(|&at| self.state.values[at] != outer.values[at])
            .map(|at| Said::Within(at, self.state.values[at]))
            .collect();
        for (pack, members) in outer.members.iter().enumerate() {
            let (now, before) = (&self.state.packs[pack], &outer.packs[pack]);
            if now == before {
                continue;
            }
            // The levels of the pack in scope before the match.
            let live: Vec<(usize, usize)> = members
                .iter()
                .enumerate()
                .filter(|&(at, &member)| member < level && outer.places[member] == Some((pack, at)))
                .map(|(at, &level)| (at, level))
                .collect();
            for (index, &(at, first)) in live.iter().enumerate() {
                for &(other, second) in &live[index + 1..] {
                    for (from, to) in [(false, false), (false, true), (true, false), (true, true)] {
                        let bound = now.get(node(at, from), node(other, to));
                        if bound < before.get(node(at, from), node(other, to)) {
                            said.push(Said::Holds(Constraint {
                                from: node(first, from),
                                to: node(second, to),
                                bound,
                            }));
                        }
                    }
                }
            }
        }
        said
    }

    /// What a call answers, beyond what its equations or its body say: a
    /// remainder is below its divisor, even one past what a bound can say
    /// exactly, so `n % 2^64` is a number a word holds; and a recognized float
    /// may be answered by a machine rather than its body, whose NaN need not
    /// be the body's -- any pattern of the format, built into each wrapper
    /// out of sight.
    fn answered(&mut self, called: FnId, args: Range, mut answer: Bounds) -> Bounds {
        if self.operations.get(called.index()).copied().flatten() == Some(super::Operation::Mod)
            && let Some(divisor) = self.exact[self.program.atoms(args)[1].0.index()]
            && let Ok(greatest) = u64::try_from(divisor.saturating_sub(1))
            && divisor > 0
        {
            answer = answer.and(Bounds {
                low: 0,
                high: Some(greatest),
            });
        }
        let function = self.program.function(called);
        if let Some(float) = function.float
            && let Some((wrappers, _)) = super::floats::wrapped(self.program, function.result)
        {
            let pattern = Bounds {
                low: 0,
                high: Some(float.format.greatest()),
            };
            for constructor in wrappers {
                self.built
                    .push((slot(self.program, constructor, 0), pattern));
            }
            answer = answer.or(pattern);
        }
        answer
    }

    /// The natural a binding is outright, where it is one.
    fn exact(&self, binding: ExprId) -> Option<u128> {
        match self.program.expr(binding) {
            Expr::Static(value) => match self.program.constant(value).view() {
                super::ConstantView::Natural(number) => u128::try_from(number.to_biguint()).ok(),
                _ => None,
            },
            Expr::Atom(a) => self.exact[a.0.index()],
            _ => None,
        }
    }

    /// What a term answers, with what each argument it hands holds where
    /// it is handed.
    fn term(&mut self, id: ExprId) -> Bounds {
        if let Some(arguments) = &mut self.arguments
            && let Expr::Call(_, args) | Expr::Con(_, args) = self.program.expr(id)
        {
            let found = &mut arguments[id.index()];
            found.resize(self.program.atoms(args).len(), Bounds::NOTHING);
            for (bound, atom) in found.iter_mut().zip(self.program.atoms(args)) {
                *bound = bound.or(self.state.values[atom.0.index()]);
            }
        }
        self.worked(id)
    }

    /// Hold what a term answers against the term, so that the tier below
    /// has it where it walks.
    fn record(&mut self, id: ExprId, held: Bounds) {
        self.terms[id.index()] = self.terms[id.index()].or(held);
    }

    fn worked(&mut self, id: ExprId) -> Bounds {
        self.answered_implied = None;
        match self.program.expr(id) {
            Expr::Atom(atom) => {
                self.answered_implied
                    .clone_from(&self.implied[atom.0.index()]);
                self.state.values[atom.0.index()]
            }
            Expr::Static(value) => {
                let value = self.program.constant(value);
                self.constant_fields(value);
                constant_bounds(self.program, value)
            }
            Expr::Con(ctor, args) => {
                for (at, atom) in self.program.atoms(args).iter().enumerate() {
                    let place = slot(self.program, ctor, at);
                    self.built.push((place, self.state.values[atom.0.index()]));
                }
                self.built(ctor, args)
            }
            Expr::Call(called, args) => self.call(called, args),
            Expr::Match(scrutinee, arms) => {
                self.matched[id.index()] =
                    self.matched[id.index()].or(self.state.values[scrutinee.0.index()]);
                self.branch(id, scrutinee.0.index(), arms)
            }
        }
    }

    fn call(&mut self, called: FnId, args: Range) -> Bounds {
        let atoms: Vec<usize> = self
            .program
            .atoms(args)
            .iter()
            .map(|atom| atom.0.index())
            .collect();
        let held: Vec<Bounds> = atoms.iter().map(|&at| self.state.values[at]).collect();
        let operation_of = self.operations.get(called.index()).copied().flatten();
        let sequence_of = self.sequences.get(called.index()).copied().flatten();
        let answer = match (operation_of, sequence_of) {
            (Some(op), _) => operation(self.program, op, held[0], held[1]),
            (None, Some(op)) => self.sequence(op, &held),
            (None, None) => self.results[called.index()].unwrap_or(Bounds::NOTHING),
        };
        let answer = self.answered(called, args, answer);
        if let Some(super::Operation::Equals { yes, no } | super::Operation::LessThan { yes, no }) =
            operation_of
        {
            self.answered_implied = Some(Rc::new(self.compared(operation_of, &atoms, yes, no)));
        }
        let handed = self.handed(called, &atoms, held);
        self.calls.push((called, handed));
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

    /// What a comparison of two levels says of them where it answers each
    /// of its tags.
    fn compared(
        &self,
        operation: Option<super::Operation>,
        atoms: &[usize],
        yes: CtorId,
        no: CtorId,
    ) -> Implications {
        let (a, b) = (atoms[0], atoms[1]);
        let (holds, fails) = match operation {
            Some(super::Operation::LessThan { .. }) => (
                vec![Said::Holds(Constraint::difference(a, b, -1))],
                vec![Said::Holds(Constraint::difference(b, a, 0))],
            ),
            _ => (
                vec![
                    Said::Holds(Constraint::difference(a, b, 0)),
                    Said::Holds(Constraint::difference(b, a, 0)),
                ],
                vec![Said::Differ(a, b)],
            ),
        };
        vec![
            (Bounds::at(u64::from(self.program.tag(yes))), holds),
            (Bounds::at(u64::from(self.program.tag(no))), fails),
        ]
    }

    /// What a call hands `called`: its arguments' bounds, and what holds
    /// between any two its packs relate, as the parameters they become. A
    /// definition handing itself one of its own parameters unchanged hands
    /// it nothing it was not already handed, so that bound is said as
    /// nothing: a parameter a walk passes on settles at what its callers
    /// hand it, and a bound widened while they settled comes back down
    /// when they do, rather than holding itself up for ever.
    fn handed(&self, called: FnId, atoms: &[usize], mut values: Vec<Bounds>) -> Handed {
        let unknown: Vec<bool> = values.iter().map(|held| held.is_nothing()).collect();
        let relates = self.layouts[called.index()].relates_parameters();
        let relations = relates.then(|| self.related(atoms, &values));
        if called == self.id {
            for (at, &atom) in atoms.iter().enumerate() {
                if atom == at {
                    values[at] = Bounds::NOTHING;
                } else if self.no_more(atom, at) && !values[at].is_nothing() {
                    // Handed no more than it was handed, a count going
                    // down hands on only how low it goes.
                    values[at] = Bounds::at(values[at].low);
                }
            }
        }
        Handed {
            values,
            relations,
            unknown,
        }
    }

    /// Whether level `first` is known to be no more than level `second`.
    fn no_more(&self, first: usize, second: usize) -> bool {
        match (self.state.places[first], self.state.places[second]) {
            (Some((pack, x)), Some((with, y))) if pack == with => {
                self.state.packs[pack].get(node(x, false), node(y, false)) <= 0
            }
            _ => false,
        }
    }

    /// What holds between any two of `atoms`, held as `values`, as an
    /// octagon over their places: what their pack says where one pack
    /// holds both, and what their bounds say in any case, so that two
    /// arguments known apart are related by what each is.
    #[expect(
        clippy::too_many_lines,
        reason = "the four constraints between each two arguments, from their pack and their bounds"
    )]
    fn related(&self, atoms: &[usize], values: &[Bounds]) -> Octagon {
        // The most a node, a level or its negation, can be.
        let most = |held: Bounds, negated: bool| -> Bound {
            if negated {
                -Bound::from(held.low)
            } else {
                held.high.map_or(INFINITE, Bound::from)
            }
        };
        let mut octagon = Octagon::top(atoms.len());
        let signs = [(false, false), (false, true), (true, false), (true, true)];
        for (at, &first) in atoms.iter().enumerate() {
            for (other, &second) in atoms.iter().enumerate().skip(at + 1) {
                if first == second {
                    octagon.assume(Constraint::difference(at, other, 0));
                    octagon.assume(Constraint::difference(other, at, 0));
                }
                let packed = match (self.state.places[first], self.state.places[second]) {
                    (Some((pack, x)), Some((with, y))) if pack == with => {
                        Some((&self.state.packs[pack], x, y))
                    }
                    _ => None,
                };
                for (from, to) in signs {
                    // `u - v` is no more than the most `u` and `-v` are.
                    let mut bound = {
                        let (u, v) = (most(values[at], from), most(values[other], !to));
                        if u >= INFINITE || v >= INFINITE {
                            INFINITE
                        } else {
                            u + v
                        }
                    };
                    if let Some((held, x, y)) = packed {
                        bound = bound.min(held.get(node(x, from), node(y, to)));
                    }
                    octagon.assume(Constraint {
                        from: node(at, from),
                        to: node(other, to),
                        bound,
                    });
                }
            }
        }
        octagon
    }

    /// How many elements a recognized sequence operation answers, or its
    /// length: worked out here from what its operands hold, as arithmetic
    /// is, rather than from its definition, which is answered for every
    /// call at once. Replacing keeps a length, appending adds one, putting
    /// one before another adds theirs, dropping takes the count away and
    /// taking keeps the fewer.
    fn sequence(&self, op: SequenceOperation, held: &[Bounds]) -> Bounds {
        let counted = match op {
            SequenceOperation::Length | SequenceOperation::Replace => held[0],
            SequenceOperation::Append => held[0].up(),
            SequenceOperation::ReverseOnto | SequenceOperation::Prepend => held[0].plus(held[1]),
            SequenceOperation::Drop => held[0].monus(held[1]),
            SequenceOperation::Take => fewer(held[0], held[1]),
        };
        let length = self.assumed.length.unwrap_or(Bounds::ANY);
        // On a way nothing reaches, what any length can be: a definition
        // handed only that is still handed a length, which a word holds.
        // Only once the walk has settled, though: before then, a way not
        // reached yet may be reached with a shorter one, and what is handed
        // only ever grows.
        if counted.is_nothing() {
            return if self.settled { length } else { counted };
        }
        counted.and(length)
    }

    /// Record what a known value holds in each field, all the way down. A
    /// spine is read as a count, not field by field, so what one holds is
    /// said to be anything.
    fn constant_fields(&mut self, value: super::Constant<'_>) {
        let super::ConstantView::Constructor(ctor) = value.view() else {
            if let super::ConstantView::Spine(spine) = value.view() {
                self.spine_fields(value.owner(), spine);
            }
            return;
        };
        let mut budget = super::Budget::new(super::FoldLimits {
            work: u64::MAX,
            work_per_function: u64::MAX,
            max_bytes: usize::MAX,
            max_depth: usize::MAX,
        });
        let fields = ctor
            .fields(&mut budget)
            .expect("validated constants can be revisited");
        for (at, field) in fields.into_iter().enumerate() {
            let place = slot(self.program, ctor.constructor(), at);
            self.built
                .push((place, constant_bounds(self.program, field)));
            self.constant_fields(field);
        }
    }

    /// A run of bytes holds each byte in its element field. A short spine
    /// of anything else is read element by element, as a constructor's
    /// fields are; a long one is not, so its fields could hold anything.
    fn spine_fields(&mut self, owner: TypeId, spine: super::SpineView<'_>) {
        let Shape::Spine {
            cons, recursive, ..
        } = shape(self.program, owner)
        else {
            self.outside.push(owner);
            return;
        };
        let Some(bytes) = spine.to_bytes() else {
            if spine.length() > ELEMENTS_READ.into() {
                self.outside.push(owner);
            } else {
                self.spine_elements(spine, cons, recursive);
            }
            return;
        };
        let (Some(&low), Some(&high)) = (bytes.iter().min(), bytes.iter().max()) else {
            return;
        };
        let element = usize::from(recursive == 0);
        self.built.push((
            slot(self.program, cons, element),
            Bounds {
                low: u64::from(low),
                high: Some(u64::from(high)),
            },
        ));
    }

    /// Each element's fields of a constant spine, built into `cons`.
    fn spine_elements(&mut self, spine: super::SpineView<'_>, cons: CtorId, recursive: usize) {
        let mut budget = super::Budget::new(super::FoldLimits {
            work: u64::MAX,
            work_per_function: u64::MAX,
            max_bytes: usize::MAX,
            max_depth: usize::MAX,
        });
        let elements = spine
            .elements(&mut budget)
            .expect("validated constants can be revisited");
        for fields in elements {
            for (at, field) in fields.into_iter().enumerate() {
                let at = if at >= recursive { at + 1 } else { at };
                self.built.push((
                    slot(self.program, cons, at),
                    constant_bounds(self.program, field),
                ));
                self.constant_fields(field);
            }
        }
    }

    /// A number's empty constructor is nought and its other one is one more
    /// than what it wraps. A tag is which constructor it is.
    fn built(&self, ctor: CtorId, args: Range) -> Bounds {
        let owner = self.program.ctor(ctor).owner;
        if single_field(self.program, owner).is_some() {
            let promised = self.assumed.field(ctor, 0);
            return self
                .program
                .atoms(args)
                .first()
                .map_or(Bounds::ANY, |atom| self.state.values[atom.0.index()])
                .and(promised);
        }
        let Shape::Spine { nil, recursive, .. } = shape(self.program, owner) else {
            return Bounds::at(u64::from(self.program.tag(ctor)));
        };
        if ctor == nil {
            return Bounds::at(0);
        }
        // A number, or how many elements a sequence holds: one more than
        // the rest.
        self.program
            .atoms(args)
            .get(recursive)
            .map_or(Bounds::ANY, |atom| self.state.values[atom.0.index()].up())
    }

    /// Each arm in turn, with what the constructor it matched says of the
    /// value it took apart. What the match holds is what any arm holds, and
    /// what holds after it is what held at the end of any arm that answers.
    fn branch(&mut self, matched: ExprId, scrutinee: usize, arms: Range) -> Bounds {
        let mut answer = None;
        let outer = self.state.clone();
        let level = outer.values.len();
        let told = self.told.contains(&matched);
        let mut surviving: Option<State> = None;
        // What each tag the match answers says of the levels before it.
        let mut implications: Implications = Vec::new();
        for (index, arm) in self.program.arms(arms).iter().enumerate() {
            // An arm only adds levels to these, and takes back what it
            // borrows, so what it added is all there is to take away.
            self.state.clone_from(&outer);
            self.implied.truncate(level);
            self.exact.truncate(level);
            if !self.enter(scrutinee, arm.ctor, (matched, index)) {
                continue;
            }
            let found = self.body(arm.body);
            let answered = self.answered_implied.take();
            answer = Some(answer.map_or(found, |held: Bounds| held.or(found)));
            if found.is_nothing() {
                continue;
            }
            if told {
                self.gather(&mut implications, found, answered, &outer, level);
            }
            self.state.values.truncate(level);
            self.state.places.truncate(level);
            self.state.fresh.truncate(level);
            if let Some(surviving) = &mut surviving {
                surviving.join(&self.state);
            } else {
                surviving = Some(self.state.clone());
            }
        }
        self.state = surviving.unwrap_or(outer);
        self.implied.truncate(level);
        self.exact.truncate(level);
        self.answered_implied = (!implications.is_empty()).then(|| Rc::new(implications));
        // Where no arm is reached, nothing is: a value nothing knows yet is
        // a value no constructor could have built.
        answer.unwrap_or(Bounds::NOTHING)
    }

    /// Add what the arm just walked, answering `found`, says of the levels
    /// before the match to what each tag says: what the arm narrowed them
    /// to, and what its own last term says besides, by the tag it answers.
    fn gather(
        &self,
        implications: &mut Implications,
        found: Bounds,
        answered: Option<Rc<Implications>>,
        outer: &State,
        level: usize,
    ) {
        let said = self.said_since(outer, level);
        let Some(answered) = answered else {
            implications.push((found, said));
            return;
        };
        // What the arm's last term says of each tag holds besides, of the
        // levels before the match.
        let before = |said: &Said| match *said {
            Said::Holds(constraint) => {
                let (x, y) = constraint.variables();
                x < level && y < level
            }
            Said::Within(at, _) => at < level,
            Said::Differ(a, b) => a < level && b < level,
        };
        for (tags, inner) in answered.iter() {
            let tags = tags.and(found);
            if tags.is_nothing() {
                continue;
            }
            let mut both = said.clone();
            both.extend(inner.iter().filter(|said| before(said)));
            implications.push((tags, both));
        }
    }

    #[expect(
        clippy::too_many_lines,
        reason = "one arm for each shape a matched constructor's type has"
    )]
    fn enter(&mut self, scrutinee: usize, ctor: CtorId, arm: (ExprId, usize)) -> bool {
        let held = self.state.values[scrutinee];
        let owner = self.program.ctor(ctor).owner;
        let spine = shape(self.program, owner);
        if !reaches(self.program, held, spine, ctor) {
            return false;
        }
        let level = self.state.values.len();
        if single_field(self.program, owner).is_some() {
            let promised = self.assumed.field(ctor, 0);
            self.bind_fields(ctor, Binding::Whole(held.and(promised)), arm);
            // A wrapper is its field.
            self.between(level, scrutinee, Some(0), Some(0));
        } else {
            match spine {
                Shape::Spine { nil, .. } if ctor == nil => {
                    if !self.narrow(scrutinee, Bounds::at(0)) {
                        return false;
                    }
                    self.bind_fields(ctor, Binding::Whole(Bounds::NOTHING), arm);
                }
                Shape::Spine { recursive, .. } => {
                    if !self.narrow(scrutinee, Bounds { low: 1, high: None }) {
                        return false;
                    }
                    let rest = self.state.values[scrutinee].down();
                    self.bind_fields(ctor, Binding::Built(Some((recursive, rest))), arm);
                    // The rest is one less than what it was taken from.
                    self.between(level + recursive, scrutinee, Some(-1), Some(-1));
                }
                Shape::Tagged => {
                    let tag = Bounds::at(u64::from(self.program.tag(ctor)));
                    if !self.narrow(scrutinee, tag) {
                        return false;
                    }
                    self.bind_fields(ctor, Binding::Built(None), arm);
                }
            }
        }
        self.implied.resize(self.state.values.len(), None);
        self.exact.resize(self.state.values.len(), None);
        // A wrapper's bound is what it wraps, not which constructor it is,
        // so only a value whose bound is its tag is told apart by one.
        !matches!(spine, Shape::Tagged)
            || single_field(self.program, owner).is_some()
            || self.take_implied(scrutinee, ctor)
    }

    /// Narrow the levels before `scrutinee` to what held where it was built as
    /// `ctor`, answering whether that arm can be reached at all. Every arm
    /// answering a tag said what it held, so a tag none answered is one the
    /// value is never.
    fn take_implied(&mut self, scrutinee: usize, ctor: CtorId) -> bool {
        let Some(implications) = self.implied[scrutinee].take() else {
            return true;
        };
        let tag = u64::from(self.program.tag(ctor));
        let mut chosen: Option<Vec<Said>> = None;
        for (tags, said) in implications.iter() {
            if tags.low <= tag && tags.high.is_none_or(|high| tag <= high) {
                chosen =
                    Some(chosen.map_or_else(|| said.clone(), |chosen| join_said(&chosen, said)));
            }
        }
        self.implied[scrutinee] = Some(implications);
        chosen.is_some_and(|said| self.apply(&said))
    }

    /// Bind a constructor's fields. A field holds what was built into it --
    /// nothing yet, where no walk has built one -- and one whose type is a
    /// run of bare tags is one of them besides: the type says that much
    /// alone. The rest of a spine is one step down its count instead.
    fn bind_fields(&mut self, ctor: CtorId, binding: Binding, (matched, arm): (ExprId, usize)) {
        for (at, &ty) in self.program.fields(ctor).iter().enumerate() {
            let counted = match binding {
                Binding::Whole(held) => Some(held),
                Binding::Built(Some((recursive, rest))) if recursive == at => Some(rest),
                Binding::Built(_) => None,
            };
            let place = self.layout.field(matched, arm, at);
            if let Some(held) = counted {
                self.push(held, place);
                continue;
            }
            let built = self.fields[slot(self.program, ctor, at)].unwrap_or(Bounds::NOTHING);
            let held = tag_count(self.program, ty).map_or(built, |count| {
                built.and(Bounds {
                    low: 0,
                    high: Some(count - 1),
                })
            });
            self.push(held, place);
        }
    }
}

/// What `constraint` says of the bounds of its two levels, held as `first`
/// and `second`, by those bounds alone.
fn by_bounds(constraint: Constraint, first: Bounds, second: Bounds) -> (Bounds, Bounds) {
    // Each node is a level or its negation: the least and most it can be,
    // where it has either.
    let span = |held: Bounds, negated: bool| -> (Option<Bound>, Option<Bound>) {
        let (low, high) = (Bound::from(held.low), held.high.map(Bound::from));
        if negated {
            (high.map(|high| -high), Some(-low))
        } else {
            (Some(low), high)
        }
    };
    // What a node no more than `most` says of its level.
    let at_most = |most: Option<Bound>, negated: bool| -> Bounds {
        match (most, negated) {
            (None, _) => Bounds::ANY,
            (Some(most), false) => bounds_of(None, Some(most)),
            (Some(most), true) => bounds_of(Some(-most), None),
        }
    };
    let (from_negated, to_negated) = (constraint.from % 2 == 1, constraint.to % 2 == 1);
    if constraint.own() {
        // `±2x <= c`.
        let half = constraint.bound.div_euclid(2);
        return if from_negated {
            let least = bounds_of(Some(-half), None);
            (first.and(least), second.and(least))
        } else {
            let most = bounds_of(None, Some(half));
            (first.and(most), second.and(most))
        };
    }
    let (from, to) = (span(first, from_negated), span(second, to_negated));
    // `u - v <= c`: `u <= c + v` and `v >= u - c`, that is `-v <= c - u`.
    let u_most = to.1.map(|most| constraint.bound + most);
    let minus_v_most = from.0.map(|least| constraint.bound - least);
    (
        first.and(at_most(u_most, from_negated)),
        second.and(at_most(minus_v_most, !to_negated)),
    )
}

/// The naturals from `least` to `most`, each where said.
fn bounds_of(least: Option<Bound>, most: Option<Bound>) -> Bounds {
    let low = least.map_or(0, |least| u64::try_from(least.max(0)).unwrap_or(u64::MAX));
    let high = match most {
        None => None,
        Some(most) if most < 0 => return Bounds::NOTHING,
        Some(most) => u64::try_from(most).ok(),
    };
    Bounds { low, high }
}

/// The fewer of two counts, each anywhere in its bounds.
fn fewer(a: Bounds, b: Bounds) -> Bounds {
    if a.is_nothing() || b.is_nothing() {
        return Bounds::NOTHING;
    }
    let high = match (a.high, b.high) {
        (Some(a), Some(b)) => Some(a.min(b)),
        (Some(high), None) | (None, Some(high)) => Some(high),
        (None, None) => None,
    };
    Bounds {
        low: a.low.min(b.low),
        high,
    }
}

/// How many tags a type has, where its constructors all carry nothing and
/// there are at least two of them: a value of one is a tag below this.
fn tag_count(program: &Program, ty: TypeId) -> Option<u64> {
    (super::type_shape(program, ty) == super::TypeShape::Enumeration)
        .then(|| u64::try_from(program.ctors(ty).len()).expect("a count of constructors"))
}

/// The values any of these constants can represent, using the same join as a
/// match. For a sequence or a transparent wrapper around one, this is its
/// element count. An empty set has no possible value.
#[must_use]
pub fn bounds_of_constants<'a>(
    program: &Program,
    values: impl IntoIterator<Item = super::Constant<'a>>,
) -> Bounds {
    values.into_iter().fold(Bounds::NOTHING, |held, value| {
        held.or(constant_bounds(program, value))
    })
}

fn constant_bounds(program: &Program, value: super::Constant<'_>) -> Bounds {
    let value = super::single_field_constant(program, value);
    match value.view() {
        super::ConstantView::Natural(number) => number.try_u64().map_or(Bounds::ANY, Bounds::at),
        super::ConstantView::Constructor(ctor)
            if program
                .ctors(value.owner())
                .iter()
                .all(|c| program.types_of(c.fields).is_empty()) =>
        {
            Bounds::at(u64::from(program.tag(ctor.constructor())))
        }
        super::ConstantView::Spine(spine) => {
            u64::try_from(spine.length()).map_or(Bounds::ANY, Bounds::at)
        }
        super::ConstantView::Constructor(_) => Bounds::ANY,
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
        Operation::And => return a.masked(b),
        Operation::Or => return a.merged(b, true),
        Operation::Xor => return a.merged(b, false),
        Operation::Pow => return a.power(b),
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
