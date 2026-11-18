//! What every value of a numeric program can be.
//!
//! The solver takes a [`Numeric`] program and answers, for every term it
//! records, what the term answers, what each match matched, what each call
//! and constructor was handed, what each definition is handed and answers,
//! and what each slot was built with ([`Solution`]). It knows nothing of
//! Barb: a numeric program says all it reads.
//!
//! Every value has an interval. Values a definition relates -- compares,
//! sums, steps, hands round a recursion ([`super::packs`]) -- also have a
//! relational domain `D`, an octagon or a zone, kept closed. The domain is
//! a type parameter, so the solver is written once over [`Domain`] and the
//! caller chooses; with [`Intervals`] it keeps intervals alone.
//!
//! Definitions are walked from a worklist in sweeps over the call graph's
//! rounds, callees first, and again when what they are handed, what they
//! call answers or a slot they read grows. A value that grows in more than
//! [`WIDEN`] sweeps is widened to a threshold; every value has finitely
//! many to pass, so the walk settles with no round limit. Narrowing then
//! walks every definition again without widening.
//!
//! [`Intervals`]: super::octagon::Intervals

use std::cell::RefCell;
use std::collections::BTreeSet;
use std::rc::Rc;

use super::facts::{Operation, SequenceOperation};
use super::numeric::{Answer, Arm, Block, Built, Field, Kind, Numeric, Term, Test, Var};
use super::octagon::{Bound, Constraint, Domain, INFINITE, node};
use super::packs::{Layout, Place};
use crate::facts::Facts as Bounds;

/// How many sweeps a value may grow in before it is widened.
const WIDEN: usize = 8;

/// How many times the walk goes round afterwards to take back what widening
/// gave up. Each round carries a narrower bound one call further.
const NARROWINGS: usize = 8;

/// An entry of what a definition is handed that no call has said yet:
/// joining anything to it is that thing.
const UNSAID: Bound = -INFINITE;

/// What the solver found, by the terms, definitions and slots of the
/// numeric program. Nothing, `None` or [`Bounds::NOTHING`], is what no walk
/// reached.
#[derive(Debug, Default)]
pub(super) struct Solution {
    /// What each term answers, by its Barb term.
    pub terms: Vec<Bounds>,
    /// What each match's value was, by its Barb term.
    pub matched: Vec<Bounds>,
    /// What each call's or constructor's arguments were where it was made,
    /// by its Barb term.
    pub arguments: Vec<Vec<Bounds>>,
    /// What each definition is handed, as its walk starts: `None` where
    /// nothing handed it all of them, or what it is handed cannot all hold.
    pub takes: Vec<Option<Vec<Bounds>>>,
    pub answers: Vec<Option<Bounds>>,
    pub slots: Vec<Option<Bounds>>,
}

/// Solve `numeric` over the relational domain `D`, relating values in every
/// definition.
#[must_use]
#[expect(
    clippy::too_many_lines,
    reason = "the climb, the narrowing and the walk reading what was handed, in order"
)]
pub(super) fn solve<D: Domain>(numeric: &Numeric) -> Solution {
    let plan = Plan::<D>::new(numeric, D::RELATES);
    let mut held = Propagation::<D>::start(numeric);
    let count = numeric.functions.len();

    // A sweep walks what is waiting in order, going on past each to the
    // next waiting after it, and the next sweep starts from the first.
    let mut waiting: BTreeSet<(usize, usize)> = (0..count).map(|at| (plan.rank[at], at)).collect();
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
        let grown = once(numeric, &plan, &mut held, next.1);
        waiting.extend(grown.into_iter().map(|at| (plan.rank[at], at)));
    }

    // Widening gives up more than recursion needs it to: a remainder of a
    // count that grew is still below its divisor, and what is handed that
    // remainder is too. Going round again from a bound that holds, without
    // widening, only takes away what nothing reaches.
    held.settled = true;
    for _ in 0..NARROWINGS {
        let next = narrowed(numeric, &plan, &held);
        if next == held {
            break;
        }
        held = next;
    }

    let mut arguments = vec![Vec::new(); numeric.terms];
    let (mut terms, mut matched) = (
        vec![Bounds::NOTHING; numeric.terms],
        vec![Bounds::NOTHING; numeric.terms],
    );
    for at in 0..count {
        walk(
            numeric,
            &plan,
            &held,
            at,
            (&mut terms, &mut matched),
            Some(&mut arguments),
        );
    }
    let takes = held
        .entries
        .iter()
        .enumerate()
        .map(|(at, entry)| {
            started::<D>(&plan.layouts[at], entry)
                .filter(|(_, holds)| *holds)
                .map(|(state, _)| state.values)
        })
        .collect();
    Solution {
        terms: held.terms,
        matched: held.matched,
        arguments,
        takes,
        answers: held.results,
        slots: held.fields,
    }
}

/// What a definition was handed, what held where its walk started, and
/// whether it could all hold.
type Start<D> = (Entry, State<D>, bool);

/// What stays the same while the walk goes round.
struct Plan<D> {
    layouts: Vec<Layout>,
    /// Where each definition comes in the order walked.
    rank: Vec<usize>,
    /// Who calls each definition.
    callers: Vec<Vec<usize>>,
    /// Who reads each slot.
    readers: Vec<Vec<usize>>,
    thresholds: Thresholds,
    /// What held where each definition's walk last started, and what it
    /// was handed then: a definition walked again for what something it
    /// calls answers, handed the same, starts the same, and closing what
    /// it is handed again would cost a cube of its packs each time.
    started: RefCell<Vec<Option<Start<D>>>>,
}

impl<D: Domain> Plan<D> {
    #[expect(
        clippy::too_many_lines,
        reason = "the call graph, its rounds, the readers of each slot and each definition's packs, in one pass"
    )]
    fn new(numeric: &Numeric, relates: bool) -> Self {
        let count = numeric.functions.len();
        let mut calls = vec![Vec::new(); count];
        let mut readers = vec![Vec::new(); numeric.slots];
        for (at, function) in numeric.functions.iter().enumerate() {
            if let Answer::Body(body) = &function.answer {
                visit(body, &mut |term| match &term.kind {
                    Kind::Call { callee, .. } => calls[at].push(super::FnId::at(*callee)),
                    Kind::Match { arms, .. } => {
                        for arm in arms {
                            for &(_, field) in &arm.fields {
                                if let Field::Slot { slot, .. } = field {
                                    readers[slot].push(at);
                                }
                            }
                        }
                    }
                    _ => {}
                });
            }
        }
        let rounds = super::calls::rounds(&calls);
        let mut rank = vec![0; count];
        let mut recursive = vec![false; count];
        for (at, members) in rounds.iter().enumerate() {
            for id in members {
                rank[id.index()] = at;
                recursive[id.index()] = members.len() > 1 || calls[id.index()].contains(id);
            }
        }
        let layouts = numeric
            .functions
            .iter()
            .enumerate()
            .map(|(at, function)| match &function.answer {
                Answer::Body(body) if relates => super::packs::layout(
                    function,
                    body,
                    (at, &rank, recursive[at]),
                    &numeric.functions,
                ),
                _ => Layout::default(),
            })
            .collect();
        let mut callers = vec![Vec::new(); count];
        for (at, callees) in calls.iter().enumerate() {
            for callee in callees {
                callers[callee.index()].push(at);
            }
        }
        Self {
            layouts,
            rank,
            callers,
            readers,
            thresholds: Thresholds::new(numeric),
            started: RefCell::new(vec![None; count]),
        }
    }
}

/// Every term of `block`, however deep, each before what its arms hold.
fn visit(block: &Block, each: &mut impl FnMut(&Term)) {
    for statement in &block.statements {
        visit_term(&statement.term, each);
    }
    visit_term(&block.tail, each);
}

fn visit_term(term: &Term, each: &mut impl FnMut(&Term)) {
    each(term);
    if let Kind::Match { arms, .. } = &term.kind {
        for arm in arms {
            visit(&arm.body, each);
        }
    }
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

impl Thresholds {
    fn new(numeric: &Numeric) -> Self {
        let mut relations: Vec<Bound> = vec![
            0,
            Bound::from(u8::MAX),
            Bound::from(u16::MAX),
            Bound::from(u32::MAX),
            Bound::from(u64::MAX),
        ];
        relations.extend(
            numeric
                .length
                .and_then(|length| length.high)
                .map(Bound::from),
        );
        relations.sort_unstable();
        let mut bounds = relations.clone();
        bounds.extend(numeric.divisors.iter().map(|&below| Bound::from(below)));
        bounds.sort_unstable();
        bounds.dedup();
        Self { bounds, relations }
    }

    fn above(&self, bound: Bound) -> Bound {
        Self::next(&self.bounds, bound)
    }

    fn relation(&self, bound: Bound) -> Bound {
        Self::next(&self.relations, bound)
    }

    fn next(thresholds: &[Bound], bound: Bound) -> Bound {
        let at = thresholds.partition_point(|&threshold| threshold < bound);
        thresholds.get(at).copied().unwrap_or(INFINITE)
    }
}

/// What every call so far has handed a definition: each parameter's bounds,
/// and what holds between any two of them, as a domain's entries over the
/// parameters. An entry no call has said is [`UNSAID`].
#[derive(Clone, Debug, PartialEq, Eq)]
struct Entry {
    values: Vec<Option<Bounds>>,
    /// The side of `relations`: twice the parameters, where there are two
    /// to relate, and nought otherwise.
    side: usize,
    relations: Vec<Bound>,
}

impl Entry {
    fn new(params: usize) -> Self {
        let side = if params > 1 { 2 * params } else { 0 };
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
    fn hand<D: Domain>(&mut self, handed: &Handed<D>, widen: Option<&Thresholds>) -> bool {
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

/// What one call hands the definition it calls.
#[derive(Clone, Debug)]
struct Handed<D> {
    values: Vec<Bounds>,
    relations: Option<D>,
    /// Arguments nothing is known of yet, which say nothing of how they
    /// relate to the rest.
    unknown: Vec<bool>,
}

/// What the walk has worked out so far.
#[derive(PartialEq, Eq)]
struct Propagation<D> {
    entries: Vec<Entry>,
    results: Vec<Option<Bounds>>,
    terms: Vec<Bounds>,
    matched: Vec<Bounds>,
    fields: Vec<Option<Bounds>>,
    grown: Growth,
    /// Whether the walk has settled, so that a way nothing reaches is one
    /// nothing will: see [`FunctionWalk::sequence`].
    settled: bool,
    marker: std::marker::PhantomData<D>,
}

/// How many sweeps each entry, result and field has grown in, and the last
/// it grew in.
#[derive(Clone, PartialEq, Eq)]
struct Growth {
    entries: Vec<(usize, usize)>,
    results: Vec<(usize, usize)>,
    fields: Vec<(usize, usize)>,
    sweep: usize,
}

const fn grew((count, last): &mut (usize, usize), sweep: usize) {
    if *last != sweep {
        *last = sweep;
        *count += 1;
    }
}

impl<D: Domain> Propagation<D> {
    fn start(numeric: &Numeric) -> Self {
        let count = numeric.functions.len();
        let entries = numeric
            .functions
            .iter()
            .map(|function| {
                let mut held = Entry::new(function.counts.len());
                if let Some(handed) = &function.handed {
                    for (at, &bounds) in handed.iter().enumerate() {
                        held.values[at] = Some(bounds);
                    }
                }
                held
            })
            .collect();
        let mut fields = vec![None; numeric.slots];
        for &(slot, bounds) in &numeric.outside {
            fields[slot] = Some(bounds);
        }
        Self {
            entries,
            results: vec![None; count],
            terms: vec![Bounds::NOTHING; numeric.terms],
            matched: vec![Bounds::NOTHING; numeric.terms],
            fields,
            grown: Growth {
                entries: vec![(0, usize::MAX); count],
                results: vec![(0, usize::MAX); count],
                fields: vec![(0, usize::MAX); numeric.slots],
                sweep: 0,
            },
            settled: false,
            marker: std::marker::PhantomData,
        }
    }

    /// Take in what one walk found, answering which definitions to walk
    /// again for what grew. `widen` says whether a value growing again may
    /// be widened, which narrowing never does.
    fn learn(&mut self, plan: &Plan<D>, found: Found<D>, widen: bool) -> Vec<usize> {
        let mut again = Vec::new();
        for (slot, bounds) in found.built {
            let wide = (widen && self.grown.fields[slot].0 >= WIDEN).then_some(&plan.thresholds);
            if settle(&mut self.fields[slot], bounds, wide) {
                grew(&mut self.grown.fields[slot], self.grown.sweep);
                again.extend_from_slice(&plan.readers[slot]);
            }
        }
        for (slot, bounds) in found.resets {
            if self.fields[slot] != Some(bounds) {
                self.fields[slot] = Some(bounds);
                again.extend_from_slice(&plan.readers[slot]);
            }
        }
        for (called, handed) in found.calls {
            let wide = (widen && self.grown.entries[called].0 >= WIDEN).then_some(&plan.thresholds);
            if self.entries[called].hand(&handed, wide) {
                grew(&mut self.grown.entries[called], self.grown.sweep);
                again.push(called);
            }
        }
        again
    }
}

/// One definition, once. Answers which definitions to walk again.
fn once<D: Domain>(
    numeric: &Numeric,
    plan: &Plan<D>,
    held: &mut Propagation<D>,
    at: usize,
) -> Vec<usize> {
    let (mut terms, mut matched) = (
        std::mem::take(&mut held.terms),
        std::mem::take(&mut held.matched),
    );
    let walked = walk(numeric, plan, held, at, (&mut terms, &mut matched), None);
    held.terms = terms;
    held.matched = matched;
    let Some((answer, found)) = walked else {
        return Vec::new();
    };
    let mut again = held.learn(plan, found, true);
    let wide = (held.grown.results[at].0 >= WIDEN).then_some(&plan.thresholds);
    if settle(&mut held.results[at], answer, wide) {
        grew(&mut held.grown.results[at], held.grown.sweep);
        again.extend_from_slice(&plan.callers[at]);
    }
    again
}

/// Every definition once more, reading only what `held` knows and building
/// what that says afresh.
fn narrowed<D: Domain>(numeric: &Numeric, plan: &Plan<D>, held: &Propagation<D>) -> Propagation<D> {
    let mut next = Propagation::start(numeric);
    next.settled = true;
    for at in 0..numeric.functions.len() {
        let Some((answer, found)) = walk(
            numeric,
            plan,
            held,
            at,
            (&mut next.terms, &mut next.matched),
            None,
        ) else {
            continue;
        };
        next.results[at] = Some(answer);
        next.learn(plan, found, false);
    }
    // Narrowing widens nothing, so how often anything grew is as it was.
    next.grown = held.grown.clone();
    next
}

/// What holds where a definition's walk starts, given what it is handed,
/// closed, and whether it can all hold at once. Nothing, while some
/// parameter has been handed nothing.
#[expect(
    clippy::too_many_lines,
    reason = "each pack built from what a definition is handed, and closed"
)]
fn started<D: Domain>(layout: &Layout, entry: &Entry) -> Option<(State<D>, bool)> {
    let values: Vec<Bounds> = entry.values.iter().copied().collect::<Option<_>>()?;
    let params = values.len();
    let places: Vec<Place> = (0..params).map(|at| layout.place(at)).collect();
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
        let mut domain = D::top(size);
        for (at, &level) in members[pack].iter().enumerate() {
            if level >= params || values[level].is_nothing() {
                continue;
            }
            domain.assume(Constraint::least(at, Bound::from(values[level].low)));
            if let Some(high) = values[level].high {
                domain.assume(Constraint::most(at, Bound::from(high)));
            }
            if entry.side == 0 {
                continue;
            }
            for (other, &with) in members[pack].iter().enumerate() {
                if with >= params || with == level || values[with].is_nothing() {
                    continue;
                }
                for (from, to) in SIGNS {
                    let bound = entry.relation(node(level, from), node(with, to));
                    if bound != UNSAID && bound < INFINITE {
                        domain.assume(Constraint {
                            from: node(at, from),
                            to: node(other, to),
                            bound,
                        });
                    }
                }
            }
        }
        empty |= !domain.close();
        packs.push(Rc::new(domain));
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

/// The four ways two values' nodes pair.
const SIGNS: [(bool, bool); 4] = [(false, false), (false, true), (true, false), (true, true)];

/// What one definition answers and hands on, given what `held` knows.
/// Nothing, while nothing has handed it anything.
#[expect(
    clippy::too_many_lines,
    reason = "the cached start and the answers a definition gives without its body, each short"
)]
fn walk<D: Domain>(
    numeric: &Numeric,
    plan: &Plan<D>,
    held: &Propagation<D>,
    at: usize,
    (terms, matched): (&mut [Bounds], &mut [Bounds]),
    arguments: Option<&mut [Vec<Bounds>]>,
) -> Option<(Bounds, Found<D>)> {
    let layout = &plan.layouts[at];
    let entry = &held.entries[at];
    let cached = plan.started.borrow()[at]
        .as_ref()
        .filter(|(from, _, _)| from == entry)
        .map(|(_, state, holds)| (state.clone(), *holds));
    let (state, holds) = if let Some(cached) = cached {
        cached
    } else {
        let (state, holds) = started::<D>(layout, entry)?;
        plan.started.borrow_mut()[at] = Some((entry.clone(), state.clone(), holds));
        (state, holds)
    };
    // What it is handed cannot all hold at once: no call reaches it.
    if !holds {
        return Some((Bounds::NOTHING, Found::default()));
    }
    let body = match &numeric.functions[at].answer {
        Answer::Known(bounds) => return Some((*bounds, Found::default())),
        Answer::Operation(op, tags) => {
            let answer = operation(*op, *tags, state.values[0], state.values[1]);
            return Some((answer, Found::default()));
        }
        Answer::Body(body) => body,
    };
    let count = state.values.len();
    let walk = FunctionWalk {
        id: at,
        length: numeric.length,
        layouts: &plan.layouts,
        results: &held.results,
        fields: &held.fields,
        found: Found::default(),
        implied: vec![None; count],
        answered_implied: None,
        exact: vec![None; count],
        state,
        settled: held.settled,
        terms,
        matched,
        arguments,
    };
    Some(walk.finish(body))
}

/// Widen `held` by `found`, answering whether that changed it. Where
/// `widen` says, a bound that grows is widened in the direction it grew.
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
    *held = Some(widen.map_or(after, |thresholds| Bounds {
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
    }));
    *held != Some(before)
}

/// What holds of every value in scope: each one's bounds, and each pack's
/// domain, kept closed and agreeing with the bounds of the values in it. A
/// pack is shared until an arm changes it, so taking a state into an arm
/// copies only what the arm says something of.
#[derive(Clone, Debug)]
struct State<D> {
    values: Vec<Bounds>,
    /// Where each value is in a pack, where it is in one.
    places: Vec<Place>,
    packs: Vec<Rc<D>>,
    /// Which value each place of each pack is, where one in scope is.
    members: Vec<Vec<usize>>,
    /// Whether each value is related to nothing yet, but by its bounds.
    fresh: Vec<bool>,
}

impl<D: Domain> State<D> {
    /// Narrow each value of `pack` in scope to what its domain says of it.
    /// Answers whether every one can still be something.
    fn sync(&mut self, pack: usize) -> bool {
        for at in 0..self.members[pack].len() {
            let level = self.members[pack][at];
            let Some(&held) = self.values.get(level) else {
                continue;
            };
            if self.places[level] != Some((pack, at)) || held.is_nothing() {
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

    /// What either of two states holds, of the values both have.
    fn join(&mut self, other: &Self) {
        for (held, other) in self.values.iter_mut().zip(&other.values) {
            *held = held.or(*other);
        }
        for (held, other) in self.packs.iter_mut().zip(&other.packs) {
            if !Rc::ptr_eq(held, other) {
                Rc::make_mut(held).join(other);
            }
        }
    }

    fn pack(&mut self, pack: usize) -> &mut D {
        Rc::make_mut(&mut self.packs[pack])
    }
}

/// Something one term said of the values before it, held to be said again
/// where the term's answer is matched.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Said {
    Holds(Constraint),
    Within(usize, Bounds),
    Differ(usize, usize),
}

/// What a value being each of some tags says of the values before it.
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

/// What one walk hands on.
struct Found<D> {
    calls: Vec<(usize, Handed<D>)>,
    built: Vec<(usize, Bounds)>,
    resets: Vec<(usize, Bounds)>,
}

impl<D> Default for Found<D> {
    fn default() -> Self {
        Self {
            calls: Vec::new(),
            built: Vec::new(),
            resets: Vec::new(),
        }
    }
}

/// One walk over one definition.
struct FunctionWalk<'a, D> {
    id: usize,
    length: Option<Bounds>,
    layouts: &'a [Layout],
    results: &'a [Option<Bounds>],
    fields: &'a [Option<Bounds>],
    found: Found<D>,
    state: State<D>,
    settled: bool,
    /// What each value being one tag says of the values before it.
    implied: Vec<Option<Rc<Implications>>>,
    /// What the term last worked out says, where it says anything.
    answered_implied: Option<Rc<Implications>>,
    /// The natural each value is outright, where past what a bound says.
    exact: Vec<Option<u128>>,
    terms: &'a mut [Bounds],
    matched: &'a mut [Bounds],
    arguments: Option<&'a mut [Vec<Bounds>]>,
}

impl<D: Domain> FunctionWalk<'_, D> {
    fn finish(mut self, body: &Block) -> (Bounds, Found<D>) {
        let answer = self.block(body);
        (answer, self.found)
    }

    fn layout(&self) -> &Layout {
        &self.layouts[self.id]
    }

    fn block(&mut self, block: &Block) -> Bounds {
        for statement in &block.statements {
            let term = &statement.term;
            let held = self.term(term);
            if matches!(term.kind, Kind::Call { never: true, .. }) {
                self.record(term.expr, held);
                return Bounds::NOTHING;
            }
            let implied = self.answered_implied.take();
            let exact = match term.kind {
                Kind::Const { exact, .. } => exact,
                Kind::Copy(from) => self.exact[from],
                _ => None,
            };
            let level = self.state.values.len();
            let place = self.layout().place(statement.site);
            self.push(held, place);
            self.implied.push(implied);
            self.exact.push(exact);
            self.relate(level, term);
            let held = self.state.values[level];
            self.record(term.expr, held);
        }
        let held = self.term(&block.tail);
        self.record(block.tail.expr, held);
        held
    }

    /// Bind the next value to `held`, related to nothing yet.
    fn push(&mut self, held: Bounds, place: Place) {
        let level = self.state.values.len();
        self.state.values.push(held);
        self.state.places.push(place);
        self.state.fresh.push(true);
        if let Some((pack, at)) = place {
            self.state.members[pack][at] = level;
            let domain = self.state.pack(pack);
            domain.forget(at);
            if !held.is_nothing() {
                domain.introduce(at, held);
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
        self.state.pack(pack).narrow(at, narrowed) && self.state.sync(pack)
    }

    /// Say `constraint` of the values it names, answering whether they can
    /// all still be something.
    fn constrain(&mut self, constraint: Constraint) -> bool {
        // A value less itself is nought.
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
            if !self.state.pack(pack).add(constraint.renamed(at, other)) {
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
        let (Some((pack, at)), Some((with, other))) = (self.state.places[x], self.state.places[y])
        else {
            return;
        };
        if pack != with {
            return;
        }
        // A value just bound and related to nothing yet holds what the
        // other does, moved: its row is the other's, in time linear in the
        // pack.
        if self.state.fresh.get(x).copied().unwrap_or(false) {
            self.state.fresh[x] = false;
            if self.state.pack(pack).assign(at, other, least, most) {
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

    /// What a statement says of how it stands to the values it was worked
    /// out from.
    #[expect(
        clippy::too_many_lines,
        reason = "one arm for each kind of term a statement relates to its operands"
    )]
    fn relate(&mut self, level: usize, term: &Term) {
        if self.state.values[level].is_nothing() {
            return;
        }
        let low = |held: Bounds| Some(Bound::from(held.low));
        let high = |held: Bounds| held.high.map(Bound::from);
        match &term.kind {
            Kind::Copy(from) => self.between(level, *from, Some(0), Some(0)),
            Kind::Build { args, built, .. } => match built {
                Built::Wrap(_) => self.between(level, args[0], Some(0), Some(0)),
                Built::Step(rest) => self.between(level, args[*rest], Some(1), Some(1)),
                Built::Empty | Built::Tag(_) => {}
            },
            Kind::Call {
                args,
                operation,
                sequence,
                ..
            } => {
                let held = |at: usize| self.state.values[args[at]];
                match (operation, sequence) {
                    (Some(Operation::Add), _)
                    | (None, Some(SequenceOperation::Prepend | SequenceOperation::ReverseOnto)) => {
                        let (a, b) = (held(0), held(1));
                        self.between(level, args[0], low(b), high(b));
                        self.between(level, args[1], low(a), high(a));
                    }
                    (Some(Operation::Monus), _) | (None, Some(SequenceOperation::Drop)) => {
                        let b = held(1);
                        self.between(level, args[0], high(b).map(|high| -high), Some(0));
                    }
                    (None, Some(SequenceOperation::Length | SequenceOperation::Replace)) => {
                        self.between(level, args[0], Some(0), Some(0));
                    }
                    (None, Some(SequenceOperation::Append)) => {
                        self.between(level, args[0], Some(1), Some(1));
                    }
                    (None, Some(SequenceOperation::Take)) => {
                        self.between(level, args[0], None, Some(0));
                        self.between(level, args[1], None, Some(0));
                    }
                    _ => {}
                }
            }
            Kind::Const { .. } | Kind::Match { .. } => {}
        }
    }

    /// Say everything in `said`, answering whether the values it names can
    /// all still be something. Constraints within one pack are said
    /// together, and the pack closed once where they are many.
    #[expect(
        clippy::too_many_lines,
        reason = "what each kind of thing said narrows, and closing each pack once"
    )]
    fn apply(&mut self, said: &[Said]) -> bool {
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
            let domain = self.state.pack(pack);
            let holds = if constraints.len() * 6 > 2 * domain.variables() {
                for &constraint in &constraints {
                    domain.assume(constraint);
                }
                domain.close()
            } else {
                constraints.iter().all(|&constraint| domain.add(constraint))
            };
            if !holds || !self.state.sync(pack) {
                return false;
            }
        }
        true
    }

    /// What holds now of the first `level` values beyond what held in
    /// `outer`: each value narrowed, and each constraint between two of
    /// them tightened.
    fn said_since(&self, outer: &State<D>, level: usize) -> Vec<Said> {
        let mut said: Vec<Said> = (0..level)
            .filter(|&at| self.state.values[at] != outer.values[at])
            .map(|at| Said::Within(at, self.state.values[at]))
            .collect();
        for (pack, members) in outer.members.iter().enumerate() {
            let (now, before) = (&self.state.packs[pack], &outer.packs[pack]);
            if Rc::ptr_eq(now, before) || now == before {
                continue;
            }
            let live: Vec<(usize, usize)> = members
                .iter()
                .enumerate()
                .filter(|&(at, &member)| member < level && outer.places[member] == Some((pack, at)))
                .map(|(at, &level)| (at, level))
                .collect();
            for (index, &(at, first)) in live.iter().enumerate() {
                for &(other, second) in &live[index + 1..] {
                    for (from, to) in SIGNS {
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

    /// Hold what a term answers against its Barb term.
    fn record(&mut self, expr: usize, held: Bounds) {
        self.terms[expr] = self.terms[expr].or(held);
    }

    /// What a term answers, with what each argument it hands holds where it
    /// is handed.
    #[expect(clippy::too_many_lines, reason = "one arm for each kind of term")]
    fn term(&mut self, term: &Term) -> Bounds {
        if let Some(arguments) = &mut self.arguments
            && let Kind::Call { args, .. } | Kind::Build { args, .. } = &term.kind
        {
            let found = &mut arguments[term.expr];
            found.resize(args.len(), Bounds::NOTHING);
            for (bound, &arg) in found.iter_mut().zip(args) {
                *bound = bound.or(self.state.values[arg]);
            }
        }
        self.answered_implied = None;
        match &term.kind {
            Kind::Copy(from) => {
                self.answered_implied.clone_from(&self.implied[*from]);
                self.state.values[*from]
            }
            Kind::Const {
                value,
                stores,
                resets,
                ..
            } => {
                self.found.built.extend_from_slice(stores);
                self.found.resets.extend_from_slice(resets);
                *value
            }
            Kind::Build { args, slots, built } => {
                for (at, &arg) in args.iter().enumerate() {
                    self.found.built.push((slots + at, self.state.values[arg]));
                }
                match *built {
                    Built::Wrap(promised) => args
                        .first()
                        .map_or(Bounds::ANY, |&arg| self.state.values[arg])
                        .and(promised),
                    Built::Empty => Bounds::at(0),
                    Built::Step(rest) => args
                        .get(rest)
                        .map_or(Bounds::ANY, |&arg| self.state.values[arg].up()),
                    Built::Tag(tag) => Bounds::at(tag),
                }
            }
            Kind::Call {
                callee,
                args,
                operation,
                tags,
                sequence,
                float,
                never,
            } => self.call(
                *callee,
                args,
                (*operation, *tags, *sequence),
                float.as_ref(),
                *never,
            ),
            Kind::Match { on, arms, told } => {
                self.matched[term.expr] = self.matched[term.expr].or(self.state.values[*on]);
                self.branch(*on, arms, *told)
            }
        }
    }

    fn call(
        &mut self,
        callee: usize,
        args: &[Var],
        (operation_of, tags, sequence_of): (
            Option<Operation>,
            (u64, u64),
            Option<SequenceOperation>,
        ),
        float: Option<&(Bounds, Vec<usize>)>,
        never: bool,
    ) -> Bounds {
        let held: Vec<Bounds> = args.iter().map(|&at| self.state.values[at]).collect();
        let mut answer = match (operation_of, sequence_of) {
            (Some(op), _) => operation(op, tags, held[0], held[1]),
            (None, Some(op)) => self.sequence(op, &held),
            (None, None) => self.results[callee].unwrap_or(Bounds::NOTHING),
        };
        // A remainder is below its divisor, even one past what a bound can
        // say exactly, so `n % 2^64` is a number a word holds.
        if operation_of == Some(Operation::Mod)
            && let Some(divisor) = self.exact[args[1]]
            && let Ok(greatest) = u64::try_from(divisor.saturating_sub(1))
            && divisor > 0
        {
            answer = answer.and(Bounds {
                low: 0,
                high: Some(greatest),
            });
        }
        // A machine's float operation may answer any pattern of the format,
        // built into each wrapper out of sight.
        if let Some((pattern, slots)) = float {
            for &slot in slots {
                self.found.built.push((slot, *pattern));
            }
            answer = answer.or(*pattern);
        }
        if let Some(compare @ (Operation::Equals { .. } | Operation::LessThan { .. })) =
            operation_of
        {
            self.answered_implied = Some(Rc::new(compared(compare, tags, args)));
        }
        let handed = self.handed(callee, args, held);
        self.found.calls.push((callee, handed));
        if never { Bounds::NOTHING } else { answer }
    }

    /// What a call hands `called`: its arguments' bounds, and what holds
    /// between any two its packs relate. A definition handing itself one
    /// of its own parameters unchanged hands it nothing it was not already
    /// handed, and one handing on no more than a parameter hands only how
    /// low it goes, so a bound widened while callers settled comes back
    /// down when they do.
    fn handed(&self, called: usize, atoms: &[usize], mut values: Vec<Bounds>) -> Handed<D> {
        let unknown: Vec<bool> = values.iter().map(|held| held.is_nothing()).collect();
        let relates = D::RELATES && self.layouts[called].relates_parameters(atoms.len());
        let relations = relates.then(|| self.related(atoms, &values));
        if called == self.id {
            for (at, &atom) in atoms.iter().enumerate() {
                if atom == at {
                    values[at] = Bounds::NOTHING;
                } else if self.no_more(atom, at) && !values[at].is_nothing() {
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

    /// Whether value `first` is known to be no more than value `second`.
    fn no_more(&self, first: usize, second: usize) -> bool {
        match (self.state.places[first], self.state.places[second]) {
            (Some((pack, x)), Some((with, y))) if pack == with => {
                self.state.packs[pack].get(node(x, false), node(y, false)) <= 0
            }
            _ => false,
        }
    }

    /// What holds between any two of `atoms`, held as `values`, over their
    /// places: what their pack says where one holds both, and what their
    /// bounds say in any case.
    fn related(&self, atoms: &[usize], values: &[Bounds]) -> D {
        let most = |held: Bounds, negated: bool| -> Bound {
            if negated {
                -Bound::from(held.low)
            } else {
                held.high.map_or(INFINITE, Bound::from)
            }
        };
        let mut domain = D::top(atoms.len());
        for (at, &first) in atoms.iter().enumerate() {
            for (other, &second) in atoms.iter().enumerate().skip(at + 1) {
                if first == second {
                    domain.assume(Constraint::difference(at, other, 0));
                    domain.assume(Constraint::difference(other, at, 0));
                }
                let packed = match (self.state.places[first], self.state.places[second]) {
                    (Some((pack, x)), Some((with, y))) if pack == with => {
                        Some((&self.state.packs[pack], x, y))
                    }
                    _ => None,
                };
                for (from, to) in SIGNS {
                    let (u, v) = (most(values[at], from), most(values[other], !to));
                    let mut bound = if u >= INFINITE || v >= INFINITE {
                        INFINITE
                    } else {
                        u + v
                    };
                    if let Some((held, x, y)) = packed {
                        bound = bound.min(held.get(node(x, from), node(y, to)));
                    }
                    domain.assume(Constraint {
                        from: node(at, from),
                        to: node(other, to),
                        bound,
                    });
                }
            }
        }
        domain
    }

    /// How many elements a sequence operation answers, from its operands.
    fn sequence(&self, op: SequenceOperation, held: &[Bounds]) -> Bounds {
        let counted = match op {
            SequenceOperation::Length | SequenceOperation::Replace => held[0],
            SequenceOperation::Append => held[0].up(),
            SequenceOperation::ReverseOnto | SequenceOperation::Prepend => held[0].plus(held[1]),
            SequenceOperation::Drop => held[0].monus(held[1]),
            SequenceOperation::Take => fewer(held[0], held[1]),
        };
        let length = self.length.unwrap_or(Bounds::ANY);
        // On a way nothing reaches, what any length can be: a definition
        // handed only that is still handed a length, which a word holds.
        // Only once the walk has settled: before then, a way not reached
        // yet may be reached with a shorter one, and what is handed only
        // ever grows.
        if counted.is_nothing() {
            return if self.settled { length } else { counted };
        }
        counted.and(length)
    }

    /// Each arm in turn, with what the constructor it matched says of the
    /// value it took apart. What the match holds is what any arm holds, and
    /// what holds after it is what held at the end of any arm that answers.
    fn branch(&mut self, on: Var, arms: &[Arm], told: bool) -> Bounds {
        let mut answer = None;
        let outer = self.state.clone();
        let level = outer.values.len();
        let mut surviving: Option<State<D>> = None;
        let mut implications: Implications = Vec::new();
        for arm in arms {
            // An arm only adds values to these, and takes back what it
            // borrows, so what it added is all there is to take away.
            self.state.clone_from(&outer);
            self.implied.truncate(level);
            self.exact.truncate(level);
            if !self.enter(on, arm) {
                continue;
            }
            let found = self.block(&arm.body);
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
        // Where no arm is reached, nothing is.
        answer.unwrap_or(Bounds::NOTHING)
    }

    /// Add what the arm just walked, answering `found`, says of the values
    /// before the match to what each tag says.
    fn gather(
        &self,
        implications: &mut Implications,
        found: Bounds,
        answered: Option<Rc<Implications>>,
        outer: &State<D>,
        level: usize,
    ) {
        let said = self.said_since(outer, level);
        let Some(answered) = answered else {
            implications.push((found, said));
            return;
        };
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

    /// Whether an arm can be reached, and if so what it says on entry: the
    /// value matched narrowed to what the constructor says, the fields
    /// bound, and what the value being that tag says of others.
    #[expect(
        clippy::too_many_lines,
        reason = "one arm for each test a constructor makes"
    )]
    fn enter(&mut self, on: Var, arm: &Arm) -> bool {
        let held = self.state.values[on];
        let reached = match arm.test {
            Test::Wrapper(_) => true,
            Test::Empty => held.low == 0,
            Test::Step(_) => held.high != Some(0),
            Test::Tag(tag) => held.low <= tag && held.high.is_none_or(|high| tag <= high),
        };
        if !reached {
            return false;
        }
        let level = self.state.values.len();
        match arm.test {
            Test::Wrapper(promised) => {
                self.bind_fields(arm, held.and(promised), Bounds::NOTHING);
                // A wrapper is its field.
                self.between(level, on, Some(0), Some(0));
            }
            Test::Empty => {
                if !self.narrow(on, Bounds::at(0)) {
                    return false;
                }
                self.bind_fields(arm, Bounds::NOTHING, Bounds::NOTHING);
            }
            Test::Step(rest) => {
                if !self.narrow(on, Bounds { low: 1, high: None }) {
                    return false;
                }
                let less = self.state.values[on].down();
                self.bind_fields(arm, Bounds::NOTHING, less);
                // The rest is one less than what it was taken from.
                self.between(level + rest, on, Some(-1), Some(-1));
            }
            Test::Tag(tag) => {
                if !self.narrow(on, Bounds::at(tag)) {
                    return false;
                }
                self.bind_fields(arm, Bounds::NOTHING, Bounds::NOTHING);
            }
        }
        self.implied.resize(self.state.values.len(), None);
        self.exact.resize(self.state.values.len(), None);
        // Only a value whose bound is its tag is told apart by one.
        match arm.test {
            Test::Tag(tag) => self.take_implied(on, tag),
            _ => true,
        }
    }

    /// Narrow the values before `on` to what held where it was built as
    /// `tag`, answering whether that arm can be reached at all.
    fn take_implied(&mut self, on: Var, tag: u64) -> bool {
        let Some(implications) = self.implied[on].clone() else {
            return true;
        };
        let mut chosen: Option<Vec<Said>> = None;
        for (tags, said) in implications.iter() {
            if tags.low <= tag && tags.high.is_none_or(|high| tag <= high) {
                chosen =
                    Some(chosen.map_or_else(|| said.clone(), |chosen| join_said(&chosen, said)));
            }
        }
        chosen.is_some_and(|said| self.apply(&said))
    }

    /// Bind an arm's fields: a whole field is `whole`, a rest `rest`, and
    /// any other what was built into its slot, below its tag count where
    /// its type is a run of bare tags.
    fn bind_fields(&mut self, arm: &Arm, whole: Bounds, rest: Bounds) {
        for &(site, field) in &arm.fields {
            let held = match field {
                Field::Whole => whole,
                Field::Rest => rest,
                Field::Slot { slot, tags } => {
                    let built = self.fields[slot].unwrap_or(Bounds::NOTHING);
                    tags.map_or(built, |count| {
                        built.and(Bounds {
                            low: 0,
                            high: Some(count - 1),
                        })
                    })
                }
            };
            let place = self.layout().place(site);
            self.push(held, place);
        }
    }
}

/// What a comparison of two values says of them where it answers each of
/// its tags.
fn compared(operation: Operation, (yes, no): (u64, u64), atoms: &[usize]) -> Implications {
    let (a, b) = (atoms[0], atoms[1]);
    let (holds, fails) = if matches!(operation, Operation::LessThan { .. }) {
        (
            vec![Said::Holds(Constraint::difference(a, b, -1))],
            vec![Said::Holds(Constraint::difference(b, a, 0))],
        )
    } else {
        (
            vec![
                Said::Holds(Constraint::difference(a, b, 0)),
                Said::Holds(Constraint::difference(b, a, 0)),
            ],
            vec![Said::Differ(a, b)],
        )
    };
    vec![(Bounds::at(yes), holds), (Bounds::at(no), fails)]
}

/// What `constraint` says of the bounds of its two values, by those bounds
/// alone.
fn by_bounds(constraint: Constraint, first: Bounds, second: Bounds) -> (Bounds, Bounds) {
    let span = |held: Bounds, negated: bool| -> (Option<Bound>, Option<Bound>) {
        let (low, high) = (Bound::from(held.low), held.high.map(Bound::from));
        if negated {
            (high.map(|high| -high), Some(-low))
        } else {
            (Some(low), high)
        }
    };
    let at_most = |most: Option<Bound>, negated: bool| -> Bounds {
        match (most, negated) {
            (None, _) => Bounds::ANY,
            (Some(most), false) => bounds_of(None, Some(most)),
            (Some(most), true) => bounds_of(Some(-most), None),
        }
    };
    let (from_negated, to_negated) = (constraint.from % 2 == 1, constraint.to % 2 == 1);
    if constraint.own() {
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

/// What a recognized operation answers of operands within `a` and `b`.
fn operation(op: Operation, (yes, no): (u64, u64), a: Bounds, b: Bounds) -> Bounds {
    if a.is_nothing() || b.is_nothing() {
        return Bounds::NOTHING;
    }
    let decided = match op {
        Operation::Add => return a.plus(b),
        Operation::Monus => return a.monus(b),
        Operation::Mul => return a.times(b),
        Operation::Div => return a.quotient(b),
        Operation::Mod => return a.remainder(b),
        Operation::And => return a.masked(b),
        Operation::Or => return a.merged(b, true),
        Operation::Xor => return a.merged(b, false),
        Operation::Pow => return a.power(b),
        Operation::Equals { .. } => {
            if a.high == Some(a.low) && b.high == Some(b.low) {
                Some(a.low == b.low)
            } else if a.high.is_some_and(|a| a < b.low) || b.high.is_some_and(|b| b < a.low) {
                Some(false)
            } else {
                None
            }
        }
        Operation::LessThan { .. } => {
            if a.high.is_some_and(|a| a < b.low) {
                Some(true)
            } else if b.high.is_some_and(|b| a.low >= b) {
                Some(false)
            } else {
                None
            }
        }
    };
    let (yes, no) = (Bounds::at(yes), Bounds::at(no));
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

#[cfg(test)]
pub(super) mod tests {
    use super::super::CtorId;
    use super::super::numeric::{Function, Site, Statement};
    use super::super::octagon::{Intervals, Octagon, Zone};
    use super::*;

    /// Whether `tight` proves at least what `loose` does: every bound it
    /// gives within the other's, nothing reached counting as no bound.
    pub(in super::super) fn proves_at_least(tight: &Solution, loose: &Solution) -> bool {
        let within = |tight: Bounds, loose: Bounds| {
            let known = |held: Bounds| if held.is_nothing() { Bounds::ANY } else { held };
            known(tight).within(known(loose))
        };
        let each = |tight: &[Bounds], loose: &[Bounds]| {
            tight
                .iter()
                .zip(loose)
                .all(|(&tight, &loose)| within(tight, loose))
        };
        let some = |tight: &[Option<Bounds>], loose: &[Option<Bounds>]| {
            tight.iter().zip(loose).all(|(tight, loose)| {
                within(tight.unwrap_or(Bounds::ANY), loose.unwrap_or(Bounds::ANY))
            })
        };
        each(&tight.terms, &loose.terms)
            && each(&tight.matched, &loose.matched)
            && tight
                .arguments
                .iter()
                .zip(&loose.arguments)
                .all(|(tight, loose)| each(tight, loose))
            && tight.takes.iter().zip(&loose.takes).all(|pair| match pair {
                (Some(tight), Some(loose)) => each(tight, loose),
                (_, None) => true,
                (None, Some(loose)) => loose.iter().all(|&held| within(Bounds::ANY, held)),
            })
            && some(&tight.answers, &loose.answers)
            && some(&tight.slots, &loose.slots)
    }

    /// Terms numbered as they are written, so each is recorded apart.
    struct Terms(usize);

    impl Terms {
        fn term(&mut self, kind: Kind) -> Term {
            self.0 += 1;
            Term {
                expr: self.0 - 1,
                kind,
            }
        }

        fn call(&mut self, callee: usize, args: Vec<Var>, operation: Option<Operation>) -> Term {
            self.term(Kind::Call {
                callee,
                args,
                operation,
                tags: (1, 0),
                sequence: None,
                float: None,
                never: false,
            })
        }

        fn constant(&mut self, value: u64) -> Term {
            self.term(Kind::Const {
                value: Bounds::at(value),
                exact: Some(u128::from(value)),
                stores: Vec::new(),
                resets: Vec::new(),
            })
        }
    }

    fn statements(terms: Vec<Term>, first: Site) -> Vec<Statement> {
        terms
            .into_iter()
            .enumerate()
            .map(|(at, term)| Statement {
                site: first + at,
                term,
            })
            .collect()
    }

    const ADD: usize = 1;
    const LESS: usize = 2;

    fn less() -> Operation {
        Operation::LessThan {
            yes: CtorId::at(1),
            no: CtorId::at(0),
        }
    }

    /// `walk(list, count)`: the count when the list is empty, and else the
    /// walk of the rest with one more counted, handed a list of at most
    /// `most` and a count of nought. With `ADD` and `LESS` recognized.
    #[expect(
        clippy::too_many_lines,
        reason = "a numeric program written out by hand"
    )]
    fn counting(most: u64) -> Numeric {
        let mut terms = Terms(0);
        // Values: 0 list, 1 count; the step arm binds 2 rest; then 3 one,
        // 4 count + 1.
        let one = terms.constant(1);
        let stepped = terms.call(ADD, vec![1, 3], Some(Operation::Add));
        let again = terms.call(0, vec![2, 4], None);
        let empty = terms.term(Kind::Copy(1));
        let walk = Block {
            statements: Vec::new(),
            tail: terms.term(Kind::Match {
                on: 0,
                arms: vec![
                    Arm {
                        test: Test::Empty,
                        fields: Vec::new(),
                        body: Block {
                            statements: Vec::new(),
                            tail: empty,
                        },
                    },
                    Arm {
                        test: Test::Step(0),
                        fields: vec![(2, Field::Rest)],
                        body: Block {
                            statements: statements(vec![one, stepped], 3),
                            tail: again,
                        },
                    },
                ],
                told: false,
            }),
        };
        let operation = |operation| Function {
            counts: vec![true, true],
            handed: None,
            answer: Answer::Operation(operation, (1, 0)),
        };
        Numeric {
            functions: vec![
                Function {
                    counts: vec![true, true],
                    handed: Some(vec![
                        Bounds {
                            low: 0,
                            high: Some(most),
                        },
                        Bounds::at(0),
                    ]),
                    answer: Answer::Body(walk),
                },
                operation(Operation::Add),
                operation(less()),
            ],
            terms: terms.0,
            ..Numeric::default()
        }
    }

    /// A count beside the list it walks is never more than the list was
    /// long: `count + rest` holds round the recursion, an octagon's sum.
    /// Neither intervals nor differences alone keep it.
    #[test]
    fn a_count_beside_a_walk_is_bounded_by_its_length() {
        let program = counting(1000);
        let (octagons, zones, intervals) = (
            solve::<Octagon>(&program),
            solve::<Zone>(&program),
            solve::<Intervals>(&program),
        );
        assert!(proves_at_least(&octagons, &zones) && proves_at_least(&octagons, &intervals));
        let takes = |solution: Solution| solution.takes[0].clone().expect("handed")[1];
        assert_eq!(takes(solve::<Octagon>(&program)).high, Some(1000));
        assert_ne!(takes(solve::<Intervals>(&program)).high, Some(1000));
        assert_ne!(takes(solve::<Zone>(&program)).high, Some(1000));
    }

    /// `walk(bit, total)`: while `bit + 9 < total`, the walk of `bit + 9`;
    /// handed a total of at most `most`. The guard on the sum bounds `bit`
    /// itself, with no walk back through the sum.
    #[test]
    #[expect(
        clippy::too_many_lines,
        reason = "a numeric program written out by hand"
    )]
    fn a_guard_on_a_sum_bounds_its_operand() {
        let mut terms = Terms(0);
        // Values: 0 bit, 1 total, 2 nine, 3 bit + 9, 4 sum < total.
        let nine = terms.constant(9);
        let sum = terms.call(ADD, vec![0, 2], Some(Operation::Add));
        let below = terms.call(LESS, vec![3, 1], Some(less()));
        let again = terms.call(0, vec![3, 1], None);
        let stop = terms.term(Kind::Copy(0));
        let body = Block {
            statements: statements(vec![nine, sum, below], 2),
            tail: terms.term(Kind::Match {
                on: 4,
                arms: vec![
                    Arm {
                        test: Test::Tag(0),
                        fields: Vec::new(),
                        body: Block {
                            statements: Vec::new(),
                            tail: stop,
                        },
                    },
                    Arm {
                        test: Test::Tag(1),
                        fields: Vec::new(),
                        body: Block {
                            statements: Vec::new(),
                            tail: again,
                        },
                    },
                ],
                told: false,
            }),
        };
        let operation = |operation| Function {
            counts: vec![true, true],
            handed: None,
            answer: Answer::Operation(operation, (1, 0)),
        };
        let program = Numeric {
            functions: vec![
                Function {
                    counts: vec![true, true],
                    handed: Some(vec![
                        Bounds::at(0),
                        Bounds {
                            low: 0,
                            high: Some(4096),
                        },
                    ]),
                    answer: Answer::Body(body),
                },
                operation(Operation::Add),
                operation(less()),
            ],
            terms: terms.0,
            ..Numeric::default()
        };
        let solution = solve::<Octagon>(&program);
        let bit = solution.takes[0].clone().expect("handed")[0];
        assert!(bit.high.is_some_and(|high| high <= 4096), "{bit:?}");
        // What the call going round is handed is below the total.
        assert!(
            solution.arguments[again_expr(&program)][0]
                .high
                .is_some_and(|high| high < 4096)
        );
    }

    /// The term the self-call of the guarded walk was recorded against.
    fn again_expr(program: &Numeric) -> usize {
        let Answer::Body(body) = &program.functions[0].answer else {
            unreachable!("a body")
        };
        let Kind::Match { arms, .. } = &body.tail.kind else {
            unreachable!("a match")
        };
        arms[1].body.tail.expr
    }
}
