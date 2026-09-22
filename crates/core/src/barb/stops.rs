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
//! Closure can be much larger than the source call graph. Barb keeps matrices
//! flat and indexes graphs by both endpoints, so a new graph is composed only
//! with graphs that can actually precede or follow it. A failing idempotent is
//! reported as soon as it appears rather than after the closure is complete.

use std::collections::{HashMap, HashSet};

use super::model::{Atom, Body, Expr, ExprId, FnId};
use super::program::Program;
use super::{ConstantView, Operation};

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

#[derive(Clone, Debug)]
struct LocalFacts {
    bounds: Vec<Bound>,
    /// A proven lower bound for a natural, capped at two.
    minimum: u8,
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

pub(super) fn recursive(program: &Program) -> Vec<bool> {
    let calls = graph(program);
    let mut found = vec![false; calls.len()];
    for round in rounds(&calls) {
        if round.len() > 1 || calls[round[0].index()].contains(&round[0]) {
            for id in round {
                found[id.index()] = true;
            }
        }
    }
    found
}

/// Refuse a definition nothing shows stops.
pub(super) fn stops(program: &Program) -> Result<(), String> {
    let calls = graph(program);
    let operations = super::arithmetic::recognise(program);
    for round in rounds(&calls) {
        // One definition on its own goes round only if it calls itself.
        if round.len() == 1 && !calls[round[0].index()].contains(&round[0]) {
            continue;
        }
        descends(program, &round, &operations)?;
    }
    Ok(())
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
fn descends(
    program: &Program,
    round: &[FnId],
    operations: &[Option<Operation>],
) -> Result<(), String> {
    let within: HashSet<FnId> = round.iter().copied().collect();
    let direct = round
        .iter()
        .flat_map(|id| matrices(program, *id, &within, operations));
    if Closure::new().proves(direct) {
        return Ok(());
    }

    let named: Vec<&str> = round
        .iter()
        .map(|id| program.name(program.function(*id).name))
        .collect();
    Err(format!(
        "nothing here shows `{}` stops: it goes round on what it was handed rather than on a part of it",
        named.join("`, `")
    ))
}

/// The finite closure of one component's size-change graphs.
///
/// The endpoint indexes are authoritative only for entries in `graphs`; an
/// insertion updates all three together. IDs in each index are increasing,
/// which lets `products` pair a graph only with earlier entries and avoid
/// recomputing every ordered pair as the closure grows.
struct Closure {
    graphs: Vec<Graph>,
    seen: HashSet<Graph>,
    by_caller: HashMap<FnId, Vec<usize>>,
    by_callee: HashMap<FnId, Vec<usize>>,
}

impl Closure {
    fn new() -> Self {
        Self {
            graphs: Vec::new(),
            seen: HashSet::new(),
            by_caller: HashMap::new(),
            by_callee: HashMap::new(),
        }
    }

    fn proves(mut self, direct: impl IntoIterator<Item = Graph>) -> bool {
        for graph in direct {
            if self.insert(graph).is_err() {
                return false;
            }
        }

        let mut at = 0;
        while at < self.graphs.len() {
            for product in self.products(at) {
                if self.insert(product).is_err() {
                    return false;
                }
            }
            at += 1;
        }
        true
    }

    /// Add one unique graph, or report an idempotent path with no descent.
    fn insert(&mut self, graph: Graph) -> Result<(), ()> {
        if !self.seen.insert(graph.clone()) {
            return Ok(());
        }
        if !graph.strict_diagonal() && graph.idempotent() {
            return Err(());
        }

        let at = self.graphs.len();
        self.by_caller.entry(graph.caller).or_default().push(at);
        self.by_callee.entry(graph.callee).or_default().push(at);
        self.graphs.push(graph);
        Ok(())
    }

    /// Compose `at` in both orders with compatible graphs already processed.
    fn products(&self, at: usize) -> Vec<Graph> {
        let graph = &self.graphs[at];
        let mut products = Vec::new();

        for &before in self.by_callee.get(&graph.caller).into_iter().flatten() {
            if before > at {
                break;
            }
            products.push(compose(&self.graphs[before], graph));
        }
        for &after in self.by_caller.get(&graph.callee).into_iter().flatten() {
            if after >= at {
                break;
            }
            products.push(compose(graph, &self.graphs[after]));
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

/// A graph per call this definition makes to one it goes round with.
fn matrices(
    program: &Program,
    id: FnId,
    within: &HashSet<FnId>,
    operations: &[Option<Operation>],
) -> Vec<Graph> {
    let params = program.params(id).len();
    let mut held = Vec::new();
    let Some(body) = program.function(id).body() else {
        return held;
    };
    // A parameter starts at distance zero from itself. Distances are kept
    // through local construction and become the three-valued matrix only at
    // an in-round call.
    let mut locals: Vec<LocalFacts> = (0..params)
        .map(|at| {
            let mut bounds = vec![Bound::Unknown; params];
            bounds[at] = Bound::Offset(0);
            LocalFacts { bounds, minimum: 0 }
        })
        .collect();
    read(
        program,
        body,
        id,
        within,
        operations,
        (&mut locals, &mut held, params),
    );
    held
}

/// Each binding takes the next level, and what an arm takes apart is one
/// constructor smaller than its scrutinee.
fn read(
    program: &Program,
    body: Body,
    from: FnId,
    within: &HashSet<FnId>,
    operations: &[Option<Operation>],
    (locals, held, params): (&mut Vec<LocalFacts>, &mut Vec<Graph>, usize),
) {
    for &binding in program.bindings(body.bindings) {
        let facts = term(
            program,
            binding,
            from,
            within,
            operations,
            (locals, held, params),
        );
        locals.push(facts);
    }
    let _ = term(
        program,
        body.tail,
        from,
        within,
        operations,
        (locals, held, params),
    );
}

fn term(
    program: &Program,
    id: ExprId,
    from: FnId,
    within: &HashSet<FnId>,
    operations: &[Option<Operation>],
    (locals, held, params): (&mut Vec<LocalFacts>, &mut Vec<Graph>, usize),
) -> LocalFacts {
    let unknown = || LocalFacts {
        bounds: vec![Bound::Unknown; params],
        minimum: 0,
    };
    match program.expr(id) {
        Expr::Atom(atom) => locals.get(atom.0.index()).cloned().unwrap_or_else(unknown),
        Expr::Static(value) => LocalFacts {
            minimum: natural_minimum(program, value),
            ..unknown()
        },
        Expr::Con(ctor, args) => constructed(program, ctor, program.atoms(args), locals, unknown()),
        Expr::Call(to, args) => {
            let args = program.atoms(args);
            if within.contains(&to) {
                held.push(matrix(from, to, locals, args, params));
            }
            operations[to.index()].map_or_else(unknown, |operation| {
                arithmetic_result(operation, args, locals, unknown())
            })
        }
        Expr::Match(scrutinee, arms) => {
            read_arms(
                program,
                scrutinee,
                arms,
                from,
                within,
                operations,
                (locals, held, params),
            );
            unknown()
        }
    }
}

fn read_arms(
    program: &Program,
    scrutinee: Atom,
    arms: super::Range,
    from: FnId,
    within: &HashSet<FnId>,
    operations: &[Option<Operation>],
    (locals, held, params): (&mut Vec<LocalFacts>, &mut Vec<Graph>, usize),
) {
    for arm in program.arms(arms) {
        let at = scrutinee.0.index();
        let level = locals.len();
        let previous_minimum = locals[at].minimum;
        if natural_successor(program, arm.ctor) {
            locals[at].minimum = locals[at].minimum.max(1);
        }
        let field = taken(&locals[at]);
        locals.resize(level + program.fields(arm.ctor).len(), field);
        read(
            program,
            arm.body,
            from,
            within,
            operations,
            (locals, held, params),
        );
        locals.truncate(level);
        locals[at].minimum = previous_minimum;
    }
}

const fn step(bound: Bound) -> Step {
    match bound {
        Bound::Offset(offset) if offset < 0 => Step::Smaller,
        Bound::Offset(0) => Step::Same,
        Bound::Unknown | Bound::Offset(_) => Step::Unknown,
    }
}

fn taken(value: &LocalFacts) -> LocalFacts {
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
        result.minimum = locals[args[0].0.index()].minimum.saturating_add(1).min(2);
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

/// Bounds guaranteed by structurally recognized natural arithmetic. These are
/// semantic properties of the recognized equations, not source-level names.
fn arithmetic_result(
    operation: Operation,
    args: &[Atom],
    locals: &[LocalFacts],
    mut result: LocalFacts,
) -> LocalFacts {
    let argument = |at: usize| &locals[args[at].0.index()];
    let candidates: &[(&LocalFacts, bool)] = match operation {
        Operation::Monus => &[(argument(0), false)],
        Operation::Div => &[(
            argument(0),
            argument(0).minimum > 0 && argument(1).minimum >= 2,
        )],
        Operation::Mod => &[(argument(0), false), (argument(1), argument(1).minimum > 0)],
        Operation::Add | Operation::Mul | Operation::Equals { .. } | Operation::LessThan { .. } => {
            return result;
        }
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

/// What one call hands on, read off the bounds of what it hands.
fn matrix(from: FnId, to: FnId, locals: &[LocalFacts], args: &[Atom], params: usize) -> Graph {
    let mut cells = vec![Step::Unknown; params * args.len()];
    for (column, arg) in args.iter().enumerate() {
        let Some(facts) = locals.get(arg.0.index()) else {
            continue;
        };
        for (row, bound) in facts.bounds.iter().enumerate() {
            cells[row * args.len() + column] = step(*bound);
        }
    }
    Graph {
        caller: from,
        callee: to,
        rows: params,
        columns: args.len(),
        cells,
    }
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
