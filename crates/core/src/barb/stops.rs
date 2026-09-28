//! Whether every definition stops.
//!
//! A definition may go round only on something it took apart, so each time
//! round is over something strictly smaller and the taking apart has an
//! end. What that takes is two things: knowing, of every value a body
//! holds, what it is against the parameters it came from; and knowing, of
//! every way round the call graph, that something gets smaller.
//!
//! What a call does to the sizes it carries is read into a matrix -- rows
//! are the parameters it was handed and columns are the arguments it hands
//! on. Size-change termination closes those matrices under composition. Every
//! idempotent path from a definition back to itself must have a strict
//! decrease on its diagonal; such a path can repeat, but its decreasing value
//! cannot do so forever.
//!
//! Where that finds a way round on which nothing gets smaller, a round may
//! still close a gap: a loop counting `i` up to `n`, a search moving `lo`
//! toward `hi`. The matrices then carry a measure besides each parameter,
//! `a ∸ b` for each ordered pair of natural parameters, which gets smaller
//! where the new pair lies within the old, one side has moved, and a guard
//! keeps them apart. What guards say is read in [`super::relations`].
//!
//! Where that still finds nothing, what calls answer is read too: each
//! definition's answer against its parameters, worked out as a greatest
//! fixpoint, and taken apart as its shape says, so a parser answering
//! `Ok((value, rest))` goes round on a `rest` no longer than its input. A
//! field of a parameter is then a size of its own, so an answer handed to a
//! definition that takes it apart carries what its fields are.
//!
//! Closure can be much larger than the source call graph. Barb keeps matrices
//! flat and indexes graphs by both endpoints, so a new graph is composed only
//! with graphs that can actually precede or follow it. A failing idempotent is
//! reported as soon as it appears rather than after the closure is complete.

use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use super::model::{Atom, Body, Expr, ExprId, FnId};
use super::program::Program;
use super::relations::{self, EQUAL, Facts, GREATER, LESS, Value, Verdict};
use super::{ConstantView, Operation, Refusal};

/// What a value is, against a parameter it came from.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Step {
    /// Taken out of it, and so strictly smaller than it.
    Smaller,
    /// It, or something else no bigger and no smaller.
    Same,
    /// Nothing that can be said. What a call answers is this, until
    /// something says what a call answers.
    Unknown,
}

/// A local's constructor depth relative to one parameter. Keeping the
/// distance until a call matrix is built lets `Succ(m)` retain one decrease
/// after `m` was taken through two constructors.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Bound {
    Unknown,
    /// No deeper than the parameter plus this signed distance.
    Offset(i64),
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct LocalFacts {
    bounds: Vec<Bound>,
    /// A proven lower bound for a natural, capped at two.
    minimum: u8,
    /// No shallower than each parameter plus this distance, where known:
    /// the other side of `bounds`, which a measure closing from below needs.
    lower: Vec<Option<i64>>,
    /// The local whose value this is, which facts are stated of.
    same: Option<usize>,
    /// What each constructor it may be says, where it is a verdict.
    verdict: Option<Verdict>,
    /// What it is taken apart as, where something says.
    shape: Shape,
}

/// What a value is taken apart as: for each constructor it may be, what its
/// fields are. A parser answering `Ok((value, rest))` says of `rest`, in
/// the `Ok` it answers, that it is no longer than what it was handed.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Shape {
    /// Nothing is known of which constructor it is.
    Unknown,
    /// As small as anything, which a summary not yet worked out assumes of
    /// a call, and what reading its body then weakens.
    Least,
    Known(Rc<Vec<(super::CtorId, Vec<LocalFacts>)>>),
}

impl Shape {
    /// What a value is, whichever of two it was: the constructors either
    /// may be, each with what both say of its fields where both say.
    fn join(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Least, held) | (held, Self::Least) => held.clone(),
            (Self::Unknown, _) | (_, Self::Unknown) => Self::Unknown,
            (Self::Known(a), Self::Known(b)) => {
                let mut joined: Vec<_> = a
                    .iter()
                    .map(|(ctor, fields)| {
                        let fields = b.iter().find(|(other, _)| other == ctor).map_or_else(
                            || fields.clone(),
                            |(_, others)| {
                                fields.iter().zip(others).map(|(a, b)| a.join(b)).collect()
                            },
                        );
                        (*ctor, fields)
                    })
                    .collect();
                joined.extend(
                    b.iter()
                        .filter(|(ctor, _)| !a.iter().any(|(held, _)| held == ctor))
                        .cloned(),
                );
                // In one order, so one shape is one value.
                joined.sort_by_key(|(ctor, _)| ctor.index());
                Self::Known(Rc::new(joined))
            }
        }
    }
}

/// The range a summary's distances are kept in, and how deep its shapes
/// go, so that working one out reaches an end.
const LEAST_OFFSET: i64 = -2;
const MOST_OFFSET: i64 = 4;
const SHAPE_DEPTH: usize = 3;

impl LocalFacts {
    fn unknown(params: usize) -> Self {
        Self {
            bounds: vec![Bound::Unknown; params],
            minimum: 0,
            lower: vec![None; params],
            same: None,
            verdict: None,
            shape: Shape::Unknown,
        }
    }

    /// What a summary not yet worked out assumes: as small as anything.
    fn least(params: usize) -> Self {
        Self {
            bounds: vec![Bound::Offset(LEAST_OFFSET); params],
            shape: Shape::Least,
            ..Self::unknown(params)
        }
    }

    /// What holds whichever of the two a body answered.
    fn join(&self, other: &Self) -> Self {
        Self {
            bounds: self
                .bounds
                .iter()
                .zip(&other.bounds)
                .map(|pair| match pair {
                    (Bound::Offset(a), Bound::Offset(b)) => Bound::Offset(*a.max(b)),
                    _ => Bound::Unknown,
                })
                .collect(),
            minimum: self.minimum.min(other.minimum),
            lower: self
                .lower
                .iter()
                .zip(&other.lower)
                .map(|(a, b)| a.zip(*b).map(|(a, b)| a.min(b)))
                .collect(),
            same: None,
            verdict: None,
            shape: self.shape.join(&other.shape),
        }
    }

    /// The same, kept to the range a summary holds and `depth` shapes deep.
    fn clamped(&self, depth: usize) -> Self {
        Self {
            bounds: self
                .bounds
                .iter()
                .map(|bound| match bound {
                    Bound::Offset(offset) if *offset <= MOST_OFFSET => {
                        Bound::Offset((*offset).max(LEAST_OFFSET))
                    }
                    _ => Bound::Unknown,
                })
                .collect(),
            minimum: self.minimum,
            lower: vec![None; self.lower.len()],
            same: None,
            verdict: None,
            shape: match &self.shape {
                Shape::Known(_) if depth == 0 => Shape::Unknown,
                Shape::Known(entries) => Shape::Known(Rc::new(
                    entries
                        .iter()
                        .map(|(ctor, fields)| {
                            (
                                *ctor,
                                fields
                                    .iter()
                                    .map(|field| field.clamped(depth - 1))
                                    .collect(),
                            )
                        })
                        .collect(),
                )),
                held => held.clone(),
            },
        }
    }

    /// A summary over a callee's parameters, read at a call: what is no
    /// deeper than a parameter there is no deeper than its argument here.
    fn instantiated(&self, args: &[&Self], params: usize) -> Self {
        let bounds = (0..params)
            .map(|row| {
                self.bounds
                    .iter()
                    .zip(args)
                    .filter_map(|(bound, arg)| match (bound, arg.bounds[row]) {
                        (Bound::Offset(a), Bound::Offset(b)) => Some(a + b),
                        _ => None,
                    })
                    .min()
                    .map_or(Bound::Unknown, Bound::Offset)
            })
            .collect();
        Self {
            bounds,
            minimum: self.minimum,
            shape: match &self.shape {
                Shape::Known(entries) => Shape::Known(Rc::new(
                    entries
                        .iter()
                        .map(|(ctor, fields)| {
                            let fields = fields
                                .iter()
                                .map(|field| field.instantiated(args, params))
                                .collect();
                            (*ctor, fields)
                        })
                        .collect(),
                )),
                held => held.clone(),
            },
            ..Self::unknown(params)
        }
    }

    /// Whichever says more of each row: both hold.
    fn meet(&self, other: &Self) -> Self {
        let mut met = self.clone();
        for (bound, other) in met.bounds.iter_mut().zip(&other.bounds) {
            *bound = match (*bound, *other) {
                (Bound::Offset(a), Bound::Offset(b)) => Bound::Offset(a.min(b)),
                (Bound::Unknown, known) | (known, Bound::Unknown) => known,
            };
        }
        met.minimum = met.minimum.max(other.minimum);
        if met.shape == Shape::Unknown {
            met.shape = other.shape.clone();
        }
        met
    }
}

impl Step {
    /// Compose two legs of a path. An unknown leg breaks the fact; otherwise
    /// one strict leg makes the whole path strict.
    const fn then(self, next: Self) -> Self {
        match (self, next) {
            (Self::Unknown, _) | (_, Self::Unknown) => Self::Unknown,
            (Self::Smaller, _) | (_, Self::Smaller) => Self::Smaller,
            (Self::Same, Self::Same) => Self::Same,
        }
    }

    /// Keep the strongest of several paths between the same two values.
    const fn stronger(self, other: Self) -> Self {
        match (self, other) {
            (Self::Smaller, _) | (_, Self::Smaller) => Self::Smaller,
            (Self::Same, _) | (_, Self::Same) => Self::Same,
            (Self::Unknown, Self::Unknown) => Self::Unknown,
        }
    }
}

/// One call or composed path, from caller parameters to callee parameters.
/// Flat cells avoid the allocation per row used by the more general Ori
/// checker; Barb has no synthesized measures or row labels to retain.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct Graph {
    caller: FnId,
    callee: FnId,
    rows: usize,
    columns: usize,
    cells: Vec<Step>,
}

impl Graph {
    fn at(&self, row: usize, column: usize) -> Step {
        self.cells[row * self.columns + column]
    }

    fn strict_diagonal(&self) -> bool {
        (0..self.rows.min(self.columns)).any(|at| self.at(at, at) == Step::Smaller)
    }

    fn idempotent(&self) -> bool {
        self.caller == self.callee && compose(self, self) == *self
    }
}

/// The definitions expanding a call of must not, so that expanding every
/// other one ends: in each round of calls, one that calls itself, and
/// enough of the rest that no way round is left among the others. Each of
/// the others can then be copied into its caller, which is how two
/// definitions calling each other become one that calls itself, and a call
/// of itself in tail position becomes a loop below.
pub(super) fn breakers(program: &Program) -> Vec<bool> {
    let calls = graph(program);
    let mut breaker = vec![false; calls.len()];
    for round in rounds(&calls) {
        for &id in &round {
            if calls[id.index()].contains(&id) {
                breaker[id.index()] = true;
            }
        }
        if round.len() == 1 {
            continue;
        }
        // Among the rest, break each way round still left, one definition
        // at a time, until none is.
        loop {
            let left: Vec<Vec<FnId>> = calls
                .iter()
                .enumerate()
                .map(|(at, callees)| {
                    if breaker[at] || !round.contains(&FnId::at(at)) {
                        return Vec::new();
                    }
                    callees
                        .iter()
                        .copied()
                        .filter(|callee| round.contains(callee) && !breaker[callee.index()])
                        .collect()
                })
                .collect();
            let cycles: Vec<_> = rounds(&left)
                .into_iter()
                .filter(|within| within.len() > 1)
                .collect();
            if cycles.is_empty() {
                break;
            }
            for within in cycles {
                let first = within.iter().min().expect("a round has a member");
                breaker[first.index()] = true;
            }
        }
    }
    breaker
}

/// Refuse a definition nothing shows stops, naming the call that begins a
/// way round on which nothing gets smaller.
pub(super) fn stops(program: &Program) -> Result<(), Refusal> {
    let calls = graph(program);
    let operations = super::arithmetic::recognise(program);
    let mut summaries = None;
    for round in rounds(&calls) {
        // One definition on its own goes round only if it calls itself.
        if round.len() == 1 && !calls[round[0].index()].contains(&round[0]) {
            continue;
        }
        // What guards say, and the gaps they keep, are read only for a round
        // nothing else shows stops, and what definitions answer only for
        // one that still is not.
        let none = HashMap::new();
        if descends(program, &round, &operations, Tier::plain(&none)).is_ok()
            || descends(program, &round, &operations, Tier::measured(&none)).is_ok()
        {
            continue;
        }
        let summaries = summaries.get_or_insert_with(|| summaries_of(program, &operations));
        descends(program, &round, &operations, Tier::answered(summaries))?;
    }
    Ok(())
}

/// What each definition answers against its parameters, as far as its
/// body shows: the greatest fixpoint, each round assumed to answer as
/// little as anything and weakened until what its bodies answer under the
/// assumption is what was assumed. What a call answers is only said of a
/// call that answers, which is all a proof of stopping reads it for: the
/// facts of one step round, where the rest has already come back.
fn summaries_of(program: &Program, operations: &[Option<Operation>]) -> HashMap<FnId, LocalFacts> {
    let calls = graph(program);
    let mut summaries = HashMap::new();
    let within = HashSet::new();
    for round in rounds(&calls) {
        let bodied: Vec<FnId> = round
            .into_iter()
            .filter(|id| program.function(*id).body().is_some())
            .collect();
        for &id in &bodied {
            summaries.insert(id, LocalFacts::least(program.params(id).len()));
        }
        let mut settled = false;
        for _ in 0..64 {
            let mut changed = false;
            for &id in &bodied {
                let answered =
                    Reader::new(program, id, &within, operations, Tier::measured(&summaries))
                        .answer()
                        .clamped(SHAPE_DEPTH);
                if summaries.get(&id) != Some(&answered) {
                    summaries.insert(id, answered);
                    changed = true;
                }
            }
            if !changed {
                settled = true;
                break;
            }
        }
        // Only a fixpoint says anything.
        if !settled {
            for id in &bodied {
                summaries.remove(id);
            }
        }
    }
    summaries
}

/// Every definition, each after everything it calls, but for those calling
/// each other, which come together in no particular order.
pub(super) fn callees_first(program: &Program) -> Vec<FnId> {
    rounds(&graph(program)).into_iter().flatten().collect()
}

/// The rounds a program's calls make: every definition in one reaches every
/// other in it, and comes back.
///
/// Which is what a strongly connected component is, so it is found the way
/// one is: a single walk that gives every definition a number as it is
/// first reached, and closes a round when it finds one that reaches no
/// further back than itself. Asking instead whether each definition reaches
/// each other was a search per pair, and the pairs are the square of the
/// program.
fn rounds(calls: &[Vec<FnId>]) -> Vec<Vec<FnId>> {
    let mut state = Rounds {
        calls,
        reached: vec![usize::MAX; calls.len()],
        lowest: vec![usize::MAX; calls.len()],
        within: vec![false; calls.len()],
        stack: Vec::new(),
        next: 0,
        held: Vec::new(),
    };
    for at in 0..calls.len() {
        if state.reached[at] == usize::MAX {
            state.walk(FnId::at(at));
        }
    }
    state.held
}

/// The walk that finds them, with its own stack rather than the machine's:
/// a program may call deeper than there is room to recurse.
struct Rounds<'a> {
    calls: &'a [Vec<FnId>],
    /// When each definition was first reached, and the earliest anything it
    /// reaches was.
    reached: Vec<usize>,
    lowest: Vec<usize>,
    /// Which are on the stack, since only those can close a round.
    within: Vec<bool>,
    stack: Vec<FnId>,
    next: usize,
    held: Vec<Vec<FnId>>,
}

impl Rounds<'_> {
    fn walk(&mut self, from: FnId) {
        // Where the walk is, and which call out of it comes next.
        let mut going = vec![(from, 0)];
        self.enter(from);

        while let Some(&mut (at, ref mut step)) = going.last_mut() {
            let called = self.calls[at.index()].get(*step).copied();
            *step += 1;
            let Some(called) = called else {
                going.pop();
                self.close(at);
                if let Some(&mut (before, _)) = going.last_mut() {
                    self.lowest[before.index()] =
                        self.lowest[before.index()].min(self.lowest[at.index()]);
                }
                continue;
            };
            if self.reached[called.index()] == usize::MAX {
                self.enter(called);
                going.push((called, 0));
            } else if self.within[called.index()] {
                self.lowest[at.index()] = self.lowest[at.index()].min(self.reached[called.index()]);
            }
        }
    }

    fn enter(&mut self, at: FnId) {
        self.reached[at.index()] = self.next;
        self.lowest[at.index()] = self.next;
        self.next += 1;
        self.within[at.index()] = true;
        self.stack.push(at);
    }

    /// A definition reaching no further back than itself is where a round
    /// ends, and everything above it on the stack is in that round.
    fn close(&mut self, at: FnId) {
        if self.lowest[at.index()] != self.reached[at.index()] {
            return;
        }
        let mut round = Vec::new();
        while let Some(held) = self.stack.pop() {
            self.within[held.index()] = false;
            round.push(held);
            if held == at {
                break;
            }
        }
        // In the order they were written, which is the order a round reads
        // in and the order its matrices are built in.
        round.sort_unstable_by_key(|held| held.index());
        self.held.push(round);
    }
}

/// Close the call matrices and require every repeatable path to descend.
/// How much a round is read for: plainly; with the gaps between its
/// parameters measured and its guards read; and besides that with what its
/// calls answer, taken apart where their answers are handed on.
#[derive(Clone, Copy)]
struct Tier<'a> {
    measured: bool,
    pathed: bool,
    summaries: &'a HashMap<FnId, LocalFacts>,
}

impl<'a> Tier<'a> {
    const fn plain(summaries: &'a HashMap<FnId, LocalFacts>) -> Self {
        Self {
            measured: false,
            pathed: false,
            summaries,
        }
    }

    const fn measured(summaries: &'a HashMap<FnId, LocalFacts>) -> Self {
        Self {
            measured: true,
            pathed: false,
            summaries,
        }
    }

    const fn answered(summaries: &'a HashMap<FnId, LocalFacts>) -> Self {
        Self {
            measured: true,
            pathed: true,
            summaries,
        }
    }
}

fn descends(
    program: &Program,
    round: &[FnId],
    operations: &[Option<Operation>],
    measured: Tier<'_>,
) -> Result<(), Refusal> {
    let within: HashSet<FnId> = round.iter().copied().collect();
    let direct = round.iter().flat_map(|id| {
        program.function(*id).body().map_or_else(Vec::new, |_| {
            let mut reader = Reader::new(program, *id, &within, operations, measured);
            reader.answer();
            reader.held
        })
    });
    let Err((function, call)) = Closure::new().proves(direct) else {
        return Ok(());
    };

    let named: Vec<&str> = round
        .iter()
        .map(|id| program.name(program.function(*id).name))
        .collect();
    Err(Refusal {
        message: format!(
            "nothing here shows `{}` stops: it goes round on what it was handed rather than on a part of it",
            named.join("`, `")
        ),
        function: Some(function),
        call: Some(call),
    })
}

/// The finite closure of one component's size-change graphs.
///
/// The endpoint indexes are authoritative only for entries in `graphs`; an
/// insertion updates all three together. IDs in each index are increasing,
/// which lets `products` pair a graph only with earlier entries and avoid
/// recomputing every ordered pair as the closure grows.
struct Closure {
    graphs: Vec<Graph>,
    /// The direct call each graph's path begins with, by graph.
    first_calls: Vec<ExprId>,
    seen: HashSet<Graph>,
    by_caller: HashMap<FnId, Vec<usize>>,
    by_callee: HashMap<FnId, Vec<usize>>,
}

impl Closure {
    fn new() -> Self {
        Self {
            graphs: Vec::new(),
            first_calls: Vec::new(),
            seen: HashSet::new(),
            by_caller: HashMap::new(),
            by_callee: HashMap::new(),
        }
    }

    /// Close the direct graphs, each beside the call it was read from, or
    /// answer where a path with no descent begins: its definition and call.
    fn proves(
        mut self,
        direct: impl IntoIterator<Item = (Graph, ExprId)>,
    ) -> Result<(), (FnId, ExprId)> {
        for (graph, call) in direct {
            self.insert(graph, call)?;
        }

        let mut at = 0;
        while at < self.graphs.len() {
            for (product, call) in self.products(at) {
                self.insert(product, call)?;
            }
            at += 1;
        }
        Ok(())
    }

    /// Add one unique graph whose path begins with `call`, or report an
    /// idempotent path with no descent by where it begins.
    fn insert(&mut self, graph: Graph, call: ExprId) -> Result<(), (FnId, ExprId)> {
        if !self.seen.insert(graph.clone()) {
            return Ok(());
        }
        if !graph.strict_diagonal() && graph.idempotent() {
            return Err((graph.caller, call));
        }

        let at = self.graphs.len();
        self.by_caller.entry(graph.caller).or_default().push(at);
        self.by_callee.entry(graph.callee).or_default().push(at);
        self.graphs.push(graph);
        self.first_calls.push(call);
        Ok(())
    }

    /// Compose `at` in both orders with compatible graphs already processed.
    fn products(&self, at: usize) -> Vec<(Graph, ExprId)> {
        let graph = &self.graphs[at];
        let mut products = Vec::new();

        for &before in self.by_callee.get(&graph.caller).into_iter().flatten() {
            if before > at {
                break;
            }
            products.push((
                compose(&self.graphs[before], graph),
                self.first_calls[before],
            ));
        }
        for &after in self.by_caller.get(&graph.callee).into_iter().flatten() {
            if after >= at {
                break;
            }
            products.push((compose(graph, &self.graphs[after]), self.first_calls[at]));
        }
        products
    }
}

/// Compose paths `a → b` and `b → c`.
fn compose(first: &Graph, second: &Graph) -> Graph {
    debug_assert_eq!(first.callee, second.caller);
    debug_assert_eq!(first.columns, second.rows);

    let mut cells = vec![Step::Unknown; first.rows * second.columns];
    for row in 0..first.rows {
        for column in 0..second.columns {
            let mut best = Step::Unknown;
            for middle in 0..first.columns {
                best = best.stronger(first.at(row, middle).then(second.at(middle, column)));
            }
            cells[row * second.columns + column] = best;
        }
    }
    Graph {
        caller: first.caller,
        callee: second.callee,
        rows: first.rows,
        columns: second.columns,
        cells,
    }
}

/// A field of a parameter, as a size of its own: what a callee takes apart
/// of its argument, where the caller built or was answered that argument.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Path {
    param: usize,
    ctor: super::CtorId,
    field: usize,
}

/// How many fields of its parameters a definition is read as having.
const MOST_PATHS: usize = 16;

/// The fields of a definition's parameters of sums that do not hold
/// themselves, where they are read: `Found(text, rest)` handed in, `rest`
/// is a size of its own.
fn paths(program: &Program, id: FnId, pathed: bool) -> Vec<Path> {
    if !pathed {
        return Vec::new();
    }
    let mut held = Vec::new();
    for (param, &ty) in program.params(id).iter().enumerate() {
        if !matches!(
            super::type_shape(program, ty),
            super::TypeShape::Sum
                | super::TypeShape::Product { .. }
                | super::TypeShape::Wrapper { .. }
        ) {
            continue;
        }
        let owner = program.ctors(ty);
        let recursive = owner
            .iter()
            .any(|ctor| program.types_of(ctor.fields).contains(&ty));
        if recursive {
            continue;
        }
        for tag in 0..owner.len() {
            let ctor = program.ctor_at(ty, u32::try_from(tag).expect("a tag fits"));
            for field in 0..program.fields(ctor).len() {
                held.push(Path { param, ctor, field });
            }
        }
    }
    held.truncate(MOST_PATHS);
    held
}

/// The top of a measured gap: a natural parameter, or a number a body binds
/// before anything else, which is the same every time round.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Top {
    Parameter(usize),
    Number { value: u64, local: usize },
}

/// The gaps `top ∸ bottom` a round may close in a definition, where it is
/// measured: between each two of its natural parameters, and from each number
/// its body first binds down to each natural parameter. A parameter every
/// call hands one value is that value inside, once optimized, and a guard
/// then compares with the number rather than the parameter.
fn measures(program: &Program, id: FnId, measured: bool) -> Vec<(Top, usize)> {
    if !measured {
        return Vec::new();
    }
    let params = program.params(id);
    let naturals: Vec<usize> = params
        .iter()
        .enumerate()
        .filter(|(_, ty)| super::arithmetic::natural(program, **ty).is_some())
        .map(|(at, _)| at)
        .collect();
    let numbers = program.function(id).body().map_or_else(Vec::new, |body| {
        program
            .bindings(body.bindings)
            .iter()
            .enumerate()
            .filter_map(|(at, &binding)| {
                let Expr::Static(value) = program.expr(binding) else {
                    return None;
                };
                let ConstantView::Natural(value) = program.constant(value).view() else {
                    return None;
                };
                Some(Top::Number {
                    value: value.try_u64().ok()?,
                    local: params.len() + at,
                })
            })
            .collect()
    });
    let tops = naturals.iter().map(|&at| Top::Parameter(at)).chain(numbers);
    tops.flat_map(|top| {
        naturals
            .iter()
            .filter(move |&&bottom| top != Top::Parameter(bottom))
            .map(move |&bottom| (top, bottom))
    })
    .collect()
}

/// What one definition's body says of the sizes it hands on: a graph per
/// call it makes to one it goes round with, beside that call, and what it
/// answers.
struct Reader<'a> {
    program: &'a Program,
    from: FnId,
    within: &'a HashSet<FnId>,
    operations: &'a [Option<Operation>],
    /// Whether gaps between parameters are measured, and guards read.
    measured: bool,
    /// What each definition answers, where that has been worked out.
    summaries: &'a HashMap<FnId, LocalFacts>,
    params: usize,
    /// The fields of parameters read as sizes of their own, which follow
    /// the parameters among the rows every bound is kept over.
    paths: Vec<Path>,
    rows: usize,
    /// Whether any definition's fields are read so.
    pathed: bool,
    locals: Vec<LocalFacts>,
    held: Vec<(Graph, ExprId)>,
    /// What the guards around the part being read say.
    facts: Facts,
}

impl<'a> Reader<'a> {
    fn new(
        program: &'a Program,
        from: FnId,
        within: &'a HashSet<FnId>,
        operations: &'a [Option<Operation>],
        tier: Tier<'a>,
    ) -> Self {
        let params = program.params(from).len();
        let paths = paths(program, from, tier.pathed);
        let rows = params + paths.len();
        // A parameter starts at distance zero from itself. Distances are
        // kept through local construction and become the three-valued
        // matrix only at an in-round call.
        let locals = (0..params)
            .map(|at| {
                let mut facts = LocalFacts::unknown(rows);
                facts.bounds[at] = Bound::Offset(0);
                facts.lower[at] = Some(0);
                facts.same = Some(at);
                facts
            })
            .collect();
        Self {
            program,
            from,
            within,
            operations,
            measured: tier.measured,
            summaries: tier.summaries,
            params,
            paths,
            rows,
            pathed: tier.pathed,
            locals,
            held: Vec::new(),
            facts: Vec::new(),
        }
    }

    /// What the body answers, reading it whole.
    fn answer(&mut self) -> LocalFacts {
        let body = self
            .program
            .function(self.from)
            .body()
            .expect("a definition read has a body");
        self.read(body)
    }
}

impl Reader<'_> {
    /// Each binding takes the next level, and what an arm takes apart is
    /// one constructor smaller than its scrutinee. What it answers.
    fn read(&mut self, body: Body) -> LocalFacts {
        for &binding in self.program.bindings(body.bindings) {
            let mut facts = self.term(binding);
            if facts.same.is_none() {
                facts.same = Some(self.locals.len());
            }
            self.locals.push(facts);
        }
        self.term(body.tail)
    }

    fn term(&mut self, id: ExprId) -> LocalFacts {
        let unknown = LocalFacts::unknown(self.rows);
        match self.program.expr(id) {
            Expr::Atom(atom) => self.locals.get(atom.0.index()).cloned().unwrap_or(unknown),
            Expr::Static(value) => {
                // A value known outright is its constructor, whatever its
                // fields are.
                let ctor = self.program.constant(value).constructor();
                let fields = self.program.fields(ctor).len();
                LocalFacts {
                    minimum: natural_minimum(self.program, value),
                    shape: Shape::Known(Rc::new(vec![(
                        ctor,
                        vec![LocalFacts::unknown(self.rows); fields],
                    )])),
                    ..unknown
                }
            }
            Expr::Con(ctor, args) => {
                let args = self.program.atoms(args);
                let mut built = constructed(self.program, ctor, args, &self.locals, unknown);
                // A constructor of nothing is as small as a value is, so no
                // bigger than any parameter.
                if self.measured && args.is_empty() {
                    built.bounds = vec![Bound::Offset(0); self.rows];
                }
                built
            }
            Expr::Call(to, args) => self.call(id, to, self.program.atoms(args)),
            Expr::Match(scrutinee, arms) => {
                let answered = self.arms(scrutinee, arms);
                let mut matched = self.matched(id);
                if let Some(answered) = answered {
                    let verdict = matched.verdict.take();
                    matched = LocalFacts {
                        verdict,
                        ..answered
                    };
                }
                matched
            }
        }
    }

    /// A call: a graph where it goes round, what recognized arithmetic says
    /// of its answer, and the verdict it answers where it answers one.
    fn call(&mut self, id: ExprId, to: FnId, args: &[Atom]) -> LocalFacts {
        if self.within.contains(&to) {
            let graph = self.matrix(to, args);
            self.held.push((graph, id));
        }
        let unknown = LocalFacts::unknown(self.rows);
        let mut result = match self.operations[to.index()] {
            Some(operation) => self.arithmetic(operation, args, unknown),
            None => self.summaries.get(&to).map_or(unknown, |summary| {
                let args: Vec<&LocalFacts> =
                    args.iter().map(|arg| &self.locals[arg.0.index()]).collect();
                summary.instantiated(&args, self.rows)
            }),
        };
        if self.measured {
            let values = self.values(args);
            if let Value::Verdict(verdict) =
                relations::called(self.program, self.operations, to, &values)
            {
                result.verdict = Some(verdict);
            }
        }
        result
    }

    /// What a match answers, which is a verdict where its arms answer them.
    fn matched(&self, id: ExprId) -> LocalFacts {
        let unknown = LocalFacts::unknown(self.rows);
        if !self.measured {
            return unknown;
        }
        let mut env: Vec<Value> = (0..self.locals.len()).map(|at| self.value(at)).collect();
        match relations::evaluated(self.program, self.operations, id, &mut env) {
            Value::Verdict(verdict) => LocalFacts {
                verdict: Some(verdict),
                ..unknown
            },
            Value::Size(_) | Value::Unknown => unknown,
        }
    }

    /// Each arm read under what its constructor says of the scrutinee, and
    /// an arm the scrutinee's verdict or shape cannot reach not read at all.
    /// What the arms answer, whichever answered.
    fn arms(&mut self, scrutinee: Atom, arms: super::Range) -> Option<LocalFacts> {
        let at = scrutinee.0.index();
        let mut answered: Option<LocalFacts> = None;
        for arm in self.program.arms(arms) {
            let Some((shaped, given)) = self.reached(at, arm.ctor) else {
                continue;
            };
            let (level, facts) = (self.locals.len(), self.facts.len());
            let previous_minimum = self.locals[at].minimum;
            self.bind_fields(at, arm.ctor, shaped.as_deref());
            self.facts.extend(given);
            let arm_answer = self.read(arm.body);
            self.facts.truncate(facts);
            self.locals.truncate(level);
            self.locals[at].minimum = previous_minimum;
            answered = Some(match answered {
                None => arm_answer,
                Some(before) => before.join(&arm_answer),
            });
        }
        answered
    }

    /// Whether an arm for `ctor` can be reached from what local `at` is,
    /// and if so, what its shape says of the fields and its verdict of the
    /// sizes around.
    fn reached(&self, at: usize, ctor: super::CtorId) -> Option<(Option<Vec<LocalFacts>>, Facts)> {
        let count = self.program.fields(ctor).len();
        let shaped = match &self.locals[at].shape {
            Shape::Unknown => None,
            Shape::Least => Some(vec![LocalFacts::least(self.rows); count]),
            Shape::Known(entries) => Some(
                entries
                    .iter()
                    .find(|(held, _)| *held == ctor)
                    .map(|(_, fields)| fields.clone())?,
            ),
        };
        let given = match &self.locals[at].verdict {
            Some(verdict) if self.measured => {
                let tag = usize::try_from(self.program.tag(ctor)).expect("a tag fits");
                verdict.outcomes[tag].clone()?
            }
            _ => Vec::new(),
        };
        Some((shaped, given))
    }

    /// The fields an arm for `ctor` binds of local `at`: one constructor
    /// smaller than it, what its shape says besides, and a field of a
    /// parameter read as a size of its own that size.
    fn bind_fields(&mut self, at: usize, ctor: super::CtorId, shaped: Option<&[LocalFacts]>) {
        let level = self.locals.len();
        let successor = natural_successor(self.program, ctor);
        if successor {
            self.locals[at].minimum = self.locals[at].minimum.max(1);
        }
        let field = taken(&self.locals[at], successor);
        self.locals
            .resize(level + self.program.fields(ctor).len(), field);
        let param = self.locals[at].same.filter(|&same| same < self.params);
        for (offset, local) in self.locals[level..].iter_mut().enumerate() {
            if let Some(shaped) = shaped.and_then(|fields| fields.get(offset)) {
                *local = local.meet(shaped);
            }
            if let Some(row) = param.and_then(|param| {
                self.paths.iter().position(|path| {
                    path.param == param && path.ctor == ctor && path.field == offset
                })
            }) {
                local.bounds[self.params + row] = Bound::Offset(0);
            }
            local.same = Some(level + offset);
        }
    }

    /// Whose value a local is.
    fn same(&self, at: usize) -> usize {
        self.locals[at].same.unwrap_or(at)
    }

    fn value(&self, at: usize) -> Value {
        self.locals[at]
            .verdict
            .clone()
            .map_or_else(|| Value::Size(self.same(at)), Value::Verdict)
    }

    fn values(&self, args: &[Atom]) -> Vec<Value> {
        args.iter().map(|atom| self.value(atom.0.index())).collect()
    }

    /// The least a natural is: what built it says, or a guard placing it
    /// above something, since no size is below nought.
    fn minimum(&self, at: usize) -> u8 {
        let same = self.same(at);
        let above = self.facts.iter().any(|fact| {
            (fact.left == same && fact.rel == GREATER) || (fact.right == same && fact.rel == LESS)
        });
        self.locals[at].minimum.max(u8::from(above))
    }

    /// Bounds guaranteed by structurally recognized natural arithmetic.
    /// These are semantic properties of the recognized equations, not
    /// source-level names.
    fn arithmetic(
        &self,
        operation: Operation,
        args: &[Atom],
        mut result: LocalFacts,
    ) -> LocalFacts {
        let argument = |at: usize| &self.locals[args[at].0.index()];
        let minimum = |at: usize| self.minimum(args[at].0.index());
        let candidates: &[(&LocalFacts, bool)] = match operation {
            Operation::Monus => &[(argument(0), minimum(0) > 0 && minimum(1) > 0)],
            Operation::Div => &[(argument(0), minimum(0) > 0 && minimum(1) >= 2)],
            Operation::Mod => &[(argument(0), false), (argument(1), minimum(1) > 0)],
            Operation::And => &[(argument(0), false), (argument(1), false)],
            Operation::Add | Operation::Mul => {
                result.lower = self.grown(operation, args);
                return result;
            }
            Operation::Or
            | Operation::Xor
            | Operation::Pow
            | Operation::Equals { .. }
            | Operation::LessThan { .. } => return result,
        };
        for row in 0..result.bounds.len() {
            result.bounds[row] = candidates
                .iter()
                .filter_map(|(argument, strict)| match argument.bounds[row] {
                    Bound::Unknown => None,
                    Bound::Offset(offset) => Some(offset - i64::from(*strict)),
                })
                .min()
                .map_or(Bound::Unknown, Bound::Offset);
        }
        result
    }

    /// How far a sum or a product is above each parameter: a sum is at
    /// least either side and the other's least, and a product at least a
    /// side whose other is no less than one.
    fn grown(&self, operation: Operation, args: &[Atom]) -> Vec<Option<i64>> {
        let (left, right) = (args[0].0.index(), args[1].0.index());
        let from = |side: usize, other: usize, row: usize| {
            let lower = self.locals[side].lower[row]?;
            match operation {
                Operation::Add => Some(lower + i64::from(self.minimum(other))),
                _ => (self.minimum(other) >= 1).then_some(lower),
            }
        };
        (0..self.rows)
            .map(
                |row| match (from(left, right, row), from(right, left, row)) {
                    (Some(a), Some(b)) => Some(a.max(b)),
                    (a, b) => a.or(b),
                },
            )
            .collect()
    }

    /// What one call hands on, read off the bounds of what it hands.
    fn matrix(&self, to: FnId, args: &[Atom]) -> Graph {
        let ours = measures(self.program, self.from, self.measured);
        let theirs = measures(self.program, to, self.measured);
        let their_paths = paths(self.program, to, self.pathed);
        let rows = self.rows + ours.len();
        let columns = args.len() + their_paths.len() + theirs.len();
        let mut cells = vec![Step::Unknown; rows * columns];
        for (column, arg) in args.iter().enumerate() {
            let Some(facts) = self.locals.get(arg.0.index()) else {
                continue;
            };
            for (row, bound) in facts.bounds.iter().enumerate() {
                cells[row * columns + column] = step(*bound);
            }
        }
        for (at, path) in their_paths.iter().enumerate() {
            if let Some(field) = self.handed_field(args, path) {
                for (row, bound) in field.bounds.iter().enumerate().take(self.rows) {
                    cells[row * columns + args.len() + at] = step(*bound);
                }
            }
        }
        let past = args.len() + their_paths.len();
        for (row, &(top, bottom)) in ours.iter().enumerate() {
            for (column, &(handed, under)) in theirs.iter().enumerate() {
                let handed = match handed {
                    Top::Parameter(at) => Top::Parameter(args[at].0.index()),
                    number @ Top::Number { .. } => number,
                };
                cells[(self.rows + row) * columns + past + column] =
                    self.closes((top, bottom), (handed, args[under].0.index()), &ours);
            }
        }
        Graph {
            caller: self.from,
            callee: to,
            rows,
            columns,
            cells,
        }
    }

    /// A field the callee reads of its argument, as the argument's shape
    /// says it is.
    fn handed_field(&self, args: &[Atom], path: &Path) -> Option<&LocalFacts> {
        let Shape::Known(entries) = &self.locals[args[path.param].0.index()].shape else {
            return None;
        };
        entries
            .iter()
            .find(|(ctor, _)| *ctor == path.ctor)
            .and_then(|(_, fields)| fields.get(path.field))
    }

    /// What the gap `upper ∸ lower` handed on is against this definition's
    /// gap `top ∸ bottom`: no wider where `upper` is at most `top` and
    /// `lower` at least `bottom`, and narrower besides where one of them
    /// moved and a guard keeps the pair apart, so the old gap was not nought.
    /// A handed `upper` is a local here where it is a parameter's argument,
    /// and a number where it is the callee's own.
    fn closes(
        &self,
        (top, bottom): (Top, usize),
        (upper, lower): (Top, usize),
        own: &[(Top, usize)],
    ) -> Step {
        let lower_same = self.same(lower);
        let upper_same = self.holding(upper, own);
        let top_local = match top {
            Top::Parameter(at) => at,
            Top::Number { local, .. } => local,
        };
        let below = self.below(top, upper, upper_same);
        let built = match self.locals[lower].lower[bottom] {
            Some(offset) if offset >= 1 => Some(true),
            Some(0) => Some(false),
            _ => None,
        };
        let above = stronger(built, self.placed(bottom, lower_same));
        let (Some(below), Some(above)) = (below, above) else {
            return Step::Unknown;
        };
        let apart = upper_same
            .is_some_and(|upper| relations::holds(&self.facts, lower_same, upper, LESS))
            || relations::holds(&self.facts, bottom, top_local, LESS);
        if (below || above) && apart {
            Step::Smaller
        } else {
            Step::Same
        }
    }

    /// The local here holding what a handed gap's top is: the argument, or
    /// a number this body binds too.
    fn holding(&self, upper: Top, own: &[(Top, usize)]) -> Option<usize> {
        match upper {
            Top::Parameter(local) => Some(self.same(local)),
            Top::Number { value, .. } => own.iter().find_map(|(held, _)| match held {
                Top::Number { value: here, local } if *here == value => Some(*local),
                _ => None,
            }),
        }
    }

    /// Whether a handed top is no more than this gap's top, and if so
    /// whether it is less.
    fn below(&self, top: Top, upper: Top, upper_same: Option<usize>) -> Option<bool> {
        match (top, upper) {
            (Top::Parameter(a), Top::Parameter(local)) => {
                let built = match self.locals[local].bounds[a] {
                    Bound::Offset(offset) if offset < 0 => Some(true),
                    Bound::Offset(0) => Some(false),
                    _ => None,
                };
                stronger(built, upper_same.and_then(|upper| self.placed(upper, a)))
            }
            (Top::Number { value, .. }, Top::Number { value: handed, .. }) => {
                (handed <= value).then_some(handed < value)
            }
            (Top::Number { local, .. }, Top::Parameter(_)) => self.placed(upper_same?, local),
            (Top::Parameter(_), Top::Number { .. }) => None,
        }
    }

    /// Whether the guards place `left` at most `right`, and if so whether
    /// below it.
    fn placed(&self, left: usize, right: usize) -> Option<bool> {
        if relations::holds(&self.facts, left, right, LESS) {
            Some(true)
        } else if relations::holds(&self.facts, left, right, LESS | EQUAL) {
            Some(false)
        } else {
            None
        }
    }
}

/// Of two ways of placing one value against another, each "no more"
/// or "less" where it places it at all, the one saying more.
const fn stronger(a: Option<bool>, b: Option<bool>) -> Option<bool> {
    match (a, b) {
        (Some(a), Some(b)) => Some(a || b),
        (held, None) | (None, held) => held,
    }
}

const fn step(bound: Bound) -> Step {
    match bound {
        Bound::Offset(offset) if offset < 0 => Step::Smaller,
        Bound::Offset(0) => Step::Same,
        Bound::Unknown | Bound::Offset(_) => Step::Unknown,
    }
}

/// What an arm binds of its scrutinee: one constructor smaller, and a
/// natural's predecessor exactly one below it.
fn taken(value: &LocalFacts, predecessor: bool) -> LocalFacts {
    LocalFacts {
        bounds: value
            .bounds
            .iter()
            .map(|bound| match bound {
                Bound::Unknown => Bound::Unknown,
                Bound::Offset(offset) => Bound::Offset(offset - 1),
            })
            .collect(),
        minimum: 0,
        lower: value
            .lower
            .iter()
            .map(|lower| lower.filter(|_| predecessor).map(|lower| lower - 1))
            .collect(),
        same: None,
        verdict: None,
        shape: Shape::Unknown,
    }
}

/// A constructor adds one to the deepest field. A nullary constructor has no
/// useful bound against an arbitrary parameter.
fn constructed(
    program: &Program,
    ctor: super::CtorId,
    args: &[Atom],
    locals: &[LocalFacts],
    mut result: LocalFacts,
) -> LocalFacts {
    result.shape = Shape::Known(Rc::new(vec![(
        ctor,
        args.iter()
            .map(|arg| locals[arg.0.index()].clamped(SHAPE_DEPTH - 1))
            .collect(),
    )]));
    if args.is_empty() {
        return result;
    }
    for row in 0..result.bounds.len() {
        let deepest = args
            .iter()
            .map(|arg| locals[arg.0.index()].bounds[row])
            .try_fold(i64::MIN, |deepest, bound| match bound {
                Bound::Unknown => None,
                Bound::Offset(offset) => Some(deepest.max(offset)),
            });
        if let Some(deepest) = deepest {
            result.bounds[row] = Bound::Offset(deepest + 1);
        }
    }
    if natural_successor(program, ctor) {
        let taken = &locals[args[0].0.index()];
        result.minimum = taken.minimum.saturating_add(1).min(2);
        result.lower = taken
            .lower
            .iter()
            .map(|lower| lower.map(|lower| lower + 1))
            .collect();
    }
    result
}

fn natural_successor(program: &Program, ctor: super::CtorId) -> bool {
    super::arithmetic::natural(program, program.ctor(ctor).owner)
        .is_some_and(|(_, successor)| successor == ctor)
}

fn natural_minimum(program: &Program, value: super::ConstId) -> u8 {
    let ConstantView::Natural(value) = program.constant(value).view() else {
        return 0;
    };
    value.try_u64().map_or(2, |value| {
        u8::try_from(value.min(2)).expect("a value capped at two")
    })
}

/// Which definitions each one calls.
fn graph(program: &Program) -> Vec<Vec<FnId>> {
    fn within(program: &Program, body: Body, held: &mut Vec<FnId>) {
        for expr in program
            .bindings(body.bindings)
            .iter()
            .chain([&body.tail])
            .copied()
        {
            match program.expr(expr) {
                Expr::Call(called, _) => held.push(called),
                Expr::Match(_, arms) => {
                    for arm in program.arms(arms) {
                        within(program, arm.body, held);
                    }
                }
                Expr::Atom(_) | Expr::Con(..) | Expr::Static(..) => {}
            }
        }
    }
    (0..program.functions().len())
        .map(|at| {
            let id = FnId::at(at);
            let mut held = Vec::new();
            if let Some(body) = program.function(id).body() {
                within(program, body, &mut held);
            }
            held
        })
        .collect()
}
