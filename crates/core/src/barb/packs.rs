//! Which values of a definition range analysis relates to each other.
//!
//! An octagon over every value a body binds would cost a cube of the body's
//! length to close, and most values are never compared with anything. So
//! before a definition is walked, this reads which values the program
//! itself relates -- the two sides of a comparison, a sum and its operands,
//! a step and what it steps, the rest a match takes apart and what it took
//! it from, the arguments a recursive call hands round -- and groups them.
//! Each group, a pack, is one octagon; a value in none is an interval.
//!
//! Only a value that reaches a comparison or a recursive call through such
//! relations is grouped at all: a sum nothing compares tells nothing a
//! sum's interval does not.

use std::collections::{HashMap, HashSet};

use super::facts::{Operation, Recognised, SequenceOperation};
use super::model::{Body, CtorId, Expr, ExprId, FnId};
use super::program::Program;
use super::{Shape, shape, single_field};

/// The most values one pack relates: a closure costs the cube of this.
/// Past it, a value is left out of the pack it would join, and what it
/// says of the pack's values is said of their intervals instead.
const PACK: usize = 96;

/// Which relations range analysis keeps, chosen by `FAUN_RANGES` for
/// measuring what each costs and earns; octagons in loops where nothing
/// says. Octagons in every definition cost twice the compiling of a program
/// reaching the software float routines, whose long bodies relate dozens of
/// values a pack, for a few hundredths of the naturals held as words.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Relations {
    /// Intervals alone: no value is related to another.
    Intervals,
    /// Differences `x - y <= c` alone, in every definition: zones.
    Zones,
    /// Octagons only in definitions that call themselves, the loops, and
    /// intervals elsewhere.
    Loops,
    /// Octagons in every definition.
    Octagons,
}

impl Relations {
    pub(crate) fn chosen() -> Self {
        static CHOSEN: std::sync::OnceLock<Relations> = std::sync::OnceLock::new();
        *CHOSEN.get_or_init(|| match std::env::var("FAUN_RANGES").as_deref() {
            Ok("intervals") => Self::Intervals,
            Ok("zones") => Self::Zones,
            Ok("octagons") => Self::Octagons,
            _ => Self::Loops,
        })
    }
}

/// Where a value of a definition is in a pack, by place.
pub(super) type Place = Option<(usize, usize)>;

/// Which pack each value of a definition is in, and where. A value is a
/// parameter, a binding or a field an arm binds: a level of a body names a
/// different value in each of two arms side by side, so what is related is
/// the value, by where it is made.
#[derive(Clone, Debug, Default)]
pub(super) struct Layout {
    /// For each parameter, its pack and place.
    params: Vec<Place>,
    /// For each binding related to anything, by the term it binds.
    bindings: HashMap<ExprId, (usize, usize)>,
    /// For each field an arm binds that is related to anything, by the
    /// match, the arm's place in it and the field's.
    fields: HashMap<(ExprId, usize, usize), (usize, usize)>,
    /// How many values each pack relates.
    pub sizes: Vec<usize>,
}

impl Layout {
    /// Where parameter `at` is.
    pub(super) fn param(&self, at: usize) -> Place {
        self.params.get(at).copied().flatten()
    }

    /// Where the value `binding` binds is.
    pub(super) fn binding(&self, binding: ExprId) -> Place {
        self.bindings.get(&binding).copied()
    }

    /// Where field `field` of arm `arm` of match `matched` is.
    pub(super) fn field(&self, matched: ExprId, arm: usize, field: usize) -> Place {
        self.fields.get(&(matched, arm, field)).copied()
    }

    /// Whether any pack relates two of the definition's parameters: what a
    /// call hands it relates them too.
    pub(super) fn relates_parameters(&self) -> bool {
        let mut seen = vec![false; self.sizes.len()];
        self.params
            .iter()
            .flatten()
            .any(|&(pack, _)| std::mem::replace(&mut seen[pack], true))
    }
}

/// The packs of definition `id`, whose round of calls is `round[id]`.
pub(super) fn layout(
    program: &Program,
    recognised: &Recognised,
    id: FnId,
    round: &[usize],
    recursive: &[bool],
) -> Layout {
    let Some(body) = program.function(id).body() else {
        return Layout::default();
    };
    if recognised.operations[id.index()].is_some()
        || recognised.sequences[id.index()] == Some(SequenceOperation::Length)
    {
        return Layout::default();
    }
    match Relations::chosen() {
        Relations::Intervals => return Layout::default(),
        Relations::Loops if !recursive[id.index()] => return Layout::default(),
        _ => {}
    }
    let params = program.params(id).len();
    let mut found = Relating {
        program,
        recognised,
        id,
        round,
        recursive,
        constant: vec![false; params],
        scope: (0..params).collect(),
        made: vec![Made::Param; params],
        edges: Vec::new(),
        groups: Vec::new(),
        events: Vec::new(),
    };
    found.body(body);
    found.packs(params)
}

/// Where a value is made.
#[derive(Clone, Copy)]
enum Made {
    Param,
    Binding(ExprId),
    Field(ExprId, usize, usize),
}

struct Relating<'a> {
    program: &'a Program,
    recognised: &'a Recognised,
    id: FnId,
    round: &'a [usize],
    recursive: &'a [bool],
    /// Whether each level in scope is a value known outright, which a
    /// constraint takes as a number rather than as a value to relate.
    constant: Vec<bool>,
    /// Which value each level in scope is.
    scope: Vec<usize>,
    /// Where each value is made, by value.
    made: Vec<Made>,
    /// Each value worked out from another: what it is worked out from says
    /// something of it, and is worth relating if it is.
    edges: Vec<(usize, usize)>,
    /// Values that are related among themselves wherever they are read:
    /// the two sides of a comparison and a recursive call's arguments.
    groups: Vec<Vec<usize>>,
    /// The values made in the order they come into scope, and where scopes
    /// end: two values never in scope at once can share a place.
    events: Vec<Event>,
}

/// A value coming into scope, or every value since the last mark going.
#[derive(Clone, Copy)]
enum Event {
    Made(usize),
    Mark,
    Release,
}

impl Relating<'_> {
    fn bind(&mut self, made: Made, constant: bool) {
        self.events.push(Event::Made(self.made.len()));
        self.scope.push(self.made.len());
        self.made.push(made);
        self.constant.push(constant);
    }

    fn body(&mut self, body: Body) {
        self.events.push(Event::Mark);
        let level = self.constant.len();
        for &binding in self.program.bindings(body.bindings) {
            let constant = self.expr(binding, true);
            self.bind(Made::Binding(binding), constant);
        }
        self.expr(body.tail, false);
        self.constant.truncate(level);
        self.scope.truncate(level);
        self.events.push(Event::Release);
    }

    /// The value at `level`, unless it is known outright.
    fn value(&self, level: usize) -> Option<usize> {
        (!self.constant[level]).then(|| self.scope[level])
    }

    fn edge(&mut self, derived: usize, from: usize) {
        if let Some(from) = self.value(from) {
            self.edges.push((derived, from));
        }
    }

    fn group(&mut self, levels: &[usize]) {
        let group: Vec<usize> = levels
            .iter()
            .filter_map(|&level| self.value(level))
            .collect();
        if !group.is_empty() {
            self.groups.push(group);
        }
    }

    /// Read one term, about to be bound to the next level where `bound`
    /// says. Answers whether it is a value known outright.
    #[expect(
        clippy::too_many_lines,
        reason = "one arm for each kind of term, each saying what it relates"
    )]
    fn expr(&mut self, id: ExprId, bound: bool) -> bool {
        // The value it is bound to is the next one made.
        let at = self.made.len();
        match self.program.expr(id) {
            Expr::Atom(atom) => {
                if bound {
                    self.edge(at, atom.0.index());
                }
                self.constant[atom.0.index()]
            }
            Expr::Static(_) => true,
            Expr::Con(ctor, args) => {
                if let (true, Some(from)) = (bound, self.stepped(ctor)) {
                    let from = self.program.atoms(args)[from].0.index();
                    self.edge(at, from);
                }
                false
            }
            Expr::Call(called, args) => {
                self.call(called, args, bound.then_some(at));
                false
            }
            Expr::Match(scrutinee, arms) => {
                let scrutinee = scrutinee.0.index();
                for (index, arm) in self.program.arms(arms).iter().enumerate() {
                    self.events.push(Event::Mark);
                    let level = self.constant.len();
                    let fields = self.program.fields(arm.ctor).len();
                    let first = self.made.len();
                    for field in 0..fields {
                        self.bind(Made::Field(id, index, field), false);
                    }
                    if let Some(rest) = self.stepped(arm.ctor)
                        && let Some(from) = self.value(scrutinee)
                    {
                        self.edges.push((first + rest, from));
                    }
                    self.body(arm.body);
                    self.constant.truncate(level);
                    self.scope.truncate(level);
                    self.events.push(Event::Release);
                }
                false
            }
        }
    }

    /// Which field of `ctor` a value built with it is a step of: a
    /// wrapper's one field, which it is, or a spine's rest, one less.
    fn stepped(&self, ctor: CtorId) -> Option<usize> {
        let owner = self.program.ctor(ctor).owner;
        if single_field(self.program, owner).is_some() {
            return Some(0);
        }
        match shape(self.program, owner) {
            Shape::Spine { nil, recursive, .. } if ctor != nil => Some(recursive),
            _ => None,
        }
    }

    #[expect(
        clippy::too_many_lines,
        reason = "what each recognized operation relates, and a call going round"
    )]
    fn call(&mut self, called: FnId, args: super::Range, binding: Option<usize>) {
        let args: Vec<usize> = self
            .program
            .atoms(args)
            .iter()
            .map(|atom| atom.0.index())
            .collect();
        let operation = self.recognised.operations[called.index()];
        let sequence = self.recognised.sequences[called.index()];
        match (operation, sequence, binding) {
            (Some(Operation::Equals { .. } | Operation::LessThan { .. }), _, _) => {
                self.group(&args);
            }
            (Some(Operation::Add), _, Some(at))
            | (
                None,
                Some(
                    SequenceOperation::Prepend
                    | SequenceOperation::ReverseOnto
                    | SequenceOperation::Take,
                ),
                Some(at),
            ) => {
                self.edge(at, args[0]);
                self.edge(at, args[1]);
            }
            (Some(Operation::Monus), _, Some(at))
            | (
                None,
                Some(
                    SequenceOperation::Length
                    | SequenceOperation::Replace
                    | SequenceOperation::Append
                    | SequenceOperation::Drop,
                ),
                Some(at),
            ) => self.edge(at, args[0]),
            _ => {}
        }
        // A call going round hands its arguments on to be compared, or
        // stepped and handed round again: what holds between them is what
        // holds between the parameters they become.
        if self.recursive[self.id.index()]
            && self.round[called.index()] == self.round[self.id.index()]
        {
            // Only a number, or what a length counts, is worth relating:
            // a record or a tag is held whatever it holds.
            let types = self.program.params(called);
            let counted: Vec<usize> = args
                .iter()
                .zip(types)
                .filter(|&(_, &ty)| counts(self.program, ty))
                .map(|(&arg, _)| arg)
                .collect();
            self.group(&counted);
        }
    }

    /// Group what is worth relating into packs.
    #[expect(
        clippy::too_many_lines,
        reason = "which values matter, grouping them, and placing each"
    )]
    fn packs(self, params: usize) -> Layout {
        let values = self.made.len();
        let mut relevant = vec![false; values];
        for group in &self.groups {
            for &value in group {
                relevant[value] = true;
            }
        }
        loop {
            let mut changed = false;
            for &(derived, from) in &self.edges {
                if relevant[derived] && !relevant[from] {
                    relevant[from] = true;
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        let mut packs = Packing::new(values, PACK);
        for group in &self.groups {
            for pair in group.windows(2) {
                packs.union(pair[0], pair[1]);
            }
        }
        // A definition's parameters together, where a recursion keeps a
        // relation between them that no one value carries: a count and the
        // rest of what it walks.
        let types = self.program.params(self.id);
        let related: Vec<usize> = (0..params)
            .filter(|&at| relevant[at] && counts(self.program, types[at]))
            .collect();
        for pair in related.windows(2) {
            packs.union(pair[0], pair[1]);
        }
        for &(derived, from) in &self.edges {
            if relevant[derived] {
                packs.union(derived, from);
            }
        }
        let (pack_of, count) = packs.packs();
        let (place, sizes) = placed(&pack_of, count, params, &self.events);
        let mut layout = Layout {
            params: place[..params].to_vec(),
            sizes,
            ..Layout::default()
        };
        for (value, made) in self.made.iter().enumerate() {
            let Some(place) = place[value] else {
                continue;
            };
            match *made {
                Made::Param => {}
                Made::Binding(binding) => {
                    layout.bindings.insert(binding, place);
                }
                Made::Field(matched, arm, field) => {
                    layout.fields.insert((matched, arm, field), place);
                }
            }
        }
        layout
    }
}

/// Whether a value of `ty` is a count: a number or a sequence, whose
/// bounds are how many steps it takes, or a wrapper of one.
fn counts(program: &Program, ty: super::TypeId) -> bool {
    let mut ty = ty;
    for _ in 0..program.types().len() {
        match single_field(program, ty) {
            Some((_, field)) => ty = field,
            None => break,
        }
    }
    matches!(shape(program, ty), Shape::Spine { .. })
}

/// Union and find over values, each set no larger than [`PACK`].
struct Packing {
    parent: Vec<usize>,
    size: Vec<usize>,
    most: usize,
}

impl Packing {
    fn new(levels: usize, most: usize) -> Self {
        Self {
            parent: (0..levels).collect(),
            size: vec![1; levels],
            most,
        }
    }

    fn find(&mut self, mut at: usize) -> usize {
        while self.parent[at] != at {
            self.parent[at] = self.parent[self.parent[at]];
            at = self.parent[at];
        }
        at
    }

    fn union(&mut self, a: usize, b: usize) {
        let (a, b) = (self.find(a), self.find(b));
        if a == b || self.size[a] + self.size[b] > self.most {
            return;
        }
        let (keep, join) = if self.size[a] >= self.size[b] {
            (a, b)
        } else {
            (b, a)
        };
        self.parent[join] = keep;
        self.size[keep] += self.size[join];
    }

    /// Each value's pack, a value alone being in none, and how many
    /// packs there are.
    fn packs(mut self) -> (Vec<Option<usize>>, usize) {
        let values = self.parent.len();
        let mut pack_of = vec![None; values];
        let mut numbered = vec![usize::MAX; values];
        let mut count = 0;
        for (value, pack) in pack_of.iter_mut().enumerate() {
            let root = self.find(value);
            if self.size[root] < 2 {
                continue;
            }
            if numbered[root] == usize::MAX {
                numbered[root] = count;
                count += 1;
            }
            *pack = Some(numbered[root]);
        }
        (pack_of, count)
    }
}

/// Each value's place in its pack, and each pack's size: the next place
/// not taken by a value of the pack still in scope, so that values of two
/// arms side by side share places, and a pack is as large as the most of
/// its values ever in scope at once.
fn placed(
    pack_of: &[Option<usize>],
    count: usize,
    params: usize,
    events: &[Event],
) -> (Vec<Place>, Vec<usize>) {
    let mut place = vec![None; pack_of.len()];
    let mut live = vec![0; count];
    let mut sizes = vec![0; count];
    let mut take = |value: usize, live: &mut Vec<usize>| {
        if let Some(pack) = pack_of[value] {
            place[value] = Some((pack, live[pack]));
            live[pack] += 1;
            sizes[pack] = sizes[pack].max(live[pack]);
        }
    };
    for value in 0..params {
        take(value, &mut live);
    }
    let mut marks: Vec<Vec<usize>> = Vec::new();
    for &event in events {
        match event {
            Event::Made(value) => take(value, &mut live),
            Event::Mark => marks.push(live.clone()),
            Event::Release => live = marks.pop().expect("a mark for each release"),
        }
    }
    (place, sizes)
}

/// The matches and comparisons of a body whose answer is matched again on
/// its tag, where what each tag says of the values before it is worth
/// gathering: a match whose answer is bound and matched later as a tag, or
/// handed through a binding or as the last term of an arm of one that is.
/// Gathering it for every other match would cost a walk of every level at
/// every arm for nothing.
pub(super) fn told(program: &Program, body: Body, params: usize) -> HashSet<ExprId> {
    let mut found = Told {
        program,
        scope: vec![None; params],
        aliases: HashMap::new(),
        wanted: Vec::new(),
    };
    found.body(body);
    let mut told = HashSet::new();
    while let Some(expr) = found.wanted.pop() {
        if !told.insert(expr) {
            continue;
        }
        match program.expr(expr) {
            Expr::Atom(_) => found.wanted.extend(found.aliases.get(&expr)),
            Expr::Match(_, arms) => {
                found
                    .wanted
                    .extend(program.arms(arms).iter().map(|arm| arm.body.tail));
            }
            _ => {}
        }
    }
    told
}

struct Told<'a> {
    program: &'a Program,
    /// The binding each level in scope is, where it is one.
    scope: Vec<Option<ExprId>>,
    /// The binding each atom read as a term names, where it names one.
    aliases: HashMap<ExprId, ExprId>,
    wanted: Vec<ExprId>,
}

impl Told<'_> {
    fn body(&mut self, body: Body) {
        let level = self.scope.len();
        for &binding in self.program.bindings(body.bindings) {
            self.expr(binding);
            self.scope.push(Some(binding));
        }
        self.expr(body.tail);
        self.scope.truncate(level);
    }

    fn expr(&mut self, id: ExprId) {
        match self.program.expr(id) {
            Expr::Atom(atom) => {
                if let Some(binding) = self.scope[atom.0.index()] {
                    self.aliases.insert(id, binding);
                }
            }
            Expr::Match(scrutinee, arms) => {
                let arms = self.program.arms(arms);
                if let Some(arm) = arms.first() {
                    let owner = self.program.ctor(arm.ctor).owner;
                    if single_field(self.program, owner).is_none()
                        && matches!(shape(self.program, owner), Shape::Tagged)
                        && let Some(binding) = self.scope[scrutinee.0.index()]
                    {
                        self.wanted.push(binding);
                    }
                }
                for arm in arms {
                    let level = self.scope.len();
                    self.scope
                        .resize(level + self.program.fields(arm.ctor).len(), None);
                    self.body(arm.body);
                    self.scope.truncate(level);
                }
            }
            _ => {}
        }
    }
}
