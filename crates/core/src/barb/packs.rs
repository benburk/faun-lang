//! Which values of a numeric definition range analysis relates.
//!
//! A relational domain over every value a body binds would cost a cube of
//! the body's length to close, and most values are never compared with
//! anything. So before a definition is solved, this reads which values its
//! numeric program relates -- the two sides of a comparison, a sum and its
//! operands, a step and what it steps, the rest a match takes apart and
//! what it took it from, the counts a recursive call hands round -- and
//! groups them. Each group, a pack, is one octagon; a value in none is an
//! interval.
//!
//! Only a value that reaches a comparison or a recursive call through such
//! relations is grouped at all: a sum nothing compares tells nothing a
//! sum's interval does not.

use super::facts::{Operation, SequenceOperation};
use super::numeric::{Arm, Block, Built, Field, Function, Kind, Site, Statement, Term, Test, Var};

/// The most values one pack relates. Past it, a value is left out of the
/// pack it would join, and what it says of the pack's values is said of
/// their intervals instead.
const PACK: usize = 96;

/// Where a value of a definition is in a pack, by place.
pub(super) type Place = Option<(usize, usize)>;

/// Which pack each value of a definition is in, and where, by the site
/// that makes it.
#[derive(Clone, Debug, Default)]
pub(super) struct Layout {
    places: Vec<Place>,
    /// How many places each pack has.
    pub sizes: Vec<usize>,
}

impl Layout {
    /// Where the value made at `site` is.
    pub(super) fn place(&self, site: Site) -> Place {
        self.places.get(site).copied().flatten()
    }

    /// Whether any pack relates two of the first `params` sites, the
    /// parameters: what a call hands the definition relates them too.
    pub(super) fn relates_parameters(&self, params: usize) -> bool {
        let mut seen = vec![false; self.sizes.len()];
        self.places
            .iter()
            .take(params)
            .flatten()
            .any(|&(pack, _)| std::mem::replace(&mut seen[pack], true))
    }
}

/// The packs of `function`, numbered `id`, whose round of calls is
/// `round[id]`, given whether it goes round and each definition's counts.
pub(super) fn layout(
    function: &Function,
    body: &Block,
    (id, round, recursive): (usize, &[usize], bool),
    functions: &[Function],
) -> Layout {
    let params = function.counts.len();
    let mut found = Relating {
        id,
        round,
        recursive,
        functions,
        constant: vec![false; params],
        scope: (0..params).collect(),
        sites: params,
        edges: Vec::new(),
        groups: Vec::new(),
        events: Vec::new(),
    };
    found.block(body);
    found.packs(params, &function.counts)
}

struct Relating<'a> {
    id: usize,
    round: &'a [usize],
    recursive: bool,
    functions: &'a [Function],
    /// Whether each value in scope is known outright, which a constraint
    /// takes as a number rather than as a value to relate.
    constant: Vec<bool>,
    /// The site of each value in scope.
    scope: Vec<Site>,
    /// How many sites there are.
    sites: usize,
    /// Each value worked out from another: what it is worked out from says
    /// something of it, and is worth relating if it is.
    edges: Vec<(Site, Site)>,
    /// Values related among themselves wherever they are read.
    groups: Vec<Vec<Site>>,
    /// The values made in the order they come into scope, and where scopes
    /// end: two values never in scope at once can share a place.
    events: Vec<Event>,
}

/// A value coming into scope, or every value since the last mark going.
#[derive(Clone, Copy)]
enum Event {
    Made(Site),
    Mark,
    Release,
}

impl Relating<'_> {
    fn bind(&mut self, site: Site, constant: bool) {
        self.events.push(Event::Made(site));
        self.scope.push(site);
        self.constant.push(constant);
        self.sites = self.sites.max(site + 1);
    }

    fn block(&mut self, block: &Block) {
        self.events.push(Event::Mark);
        let level = self.constant.len();
        for Statement { site, term } in &block.statements {
            let constant = self.term(term, Some(*site));
            self.bind(*site, constant);
        }
        self.term(&block.tail, None);
        self.constant.truncate(level);
        self.scope.truncate(level);
        self.events.push(Event::Release);
    }

    /// The site of the value at `var`, unless it is known outright.
    fn value(&self, var: Var) -> Option<Site> {
        (!self.constant[var]).then(|| self.scope[var])
    }

    fn edge(&mut self, derived: Site, from: Var) {
        if let Some(from) = self.value(from) {
            self.edges.push((derived, from));
        }
    }

    fn group(&mut self, vars: impl IntoIterator<Item = Var>) {
        let group: Vec<Site> = vars.into_iter().filter_map(|var| self.value(var)).collect();
        if !group.is_empty() {
            self.groups.push(group);
        }
    }

    /// Read one term, bound to `site` where it is a statement. Answers
    /// whether it is a value known outright.
    fn term(&mut self, term: &Term, site: Option<Site>) -> bool {
        match &term.kind {
            Kind::Copy(from) => {
                if let Some(site) = site {
                    self.edge(site, *from);
                }
                self.constant[*from]
            }
            Kind::Const { .. } => true,
            Kind::Build { args, built, .. } => {
                let from = match built {
                    Built::Wrap(_) => Some(0),
                    Built::Step(rest) => Some(*rest),
                    Built::Empty | Built::Tag(_) => None,
                };
                if let (Some(site), Some(from)) = (site, from) {
                    self.edge(site, args[from]);
                }
                false
            }
            Kind::Call {
                callee,
                args,
                operation,
                sequence,
                ..
            } => {
                self.call(*callee, args, (*operation, *sequence), site);
                false
            }
            Kind::Match { on, arms, .. } => {
                for arm in arms {
                    self.arm(*on, arm);
                }
                false
            }
        }
    }

    fn arm(&mut self, on: Var, arm: &Arm) {
        self.events.push(Event::Mark);
        let level = self.constant.len();
        for &(site, field) in &arm.fields {
            self.bind(site, false);
            let stepped = matches!(field, Field::Rest)
                || matches!((arm.test, field), (Test::Wrapper(_), Field::Whole));
            if stepped && let Some(from) = self.value(on) {
                self.edges.push((site, from));
            }
        }
        self.block(&arm.body);
        self.constant.truncate(level);
        self.scope.truncate(level);
        self.events.push(Event::Release);
    }

    fn call(
        &mut self,
        callee: usize,
        args: &[Var],
        recognized: (Option<Operation>, Option<SequenceOperation>),
        site: Option<Site>,
    ) {
        let (operation, sequence) = recognized;
        if matches!(
            operation,
            Some(Operation::Equals { .. } | Operation::LessThan { .. })
        ) {
            self.group(args.iter().copied());
        }
        let Some(site) = site else {
            return self.goes_round(callee, args);
        };
        let both = matches!(operation, Some(Operation::Add))
            || matches!(
                sequence,
                Some(
                    SequenceOperation::Prepend
                        | SequenceOperation::ReverseOnto
                        | SequenceOperation::Take
                )
            );
        let first = matches!(operation, Some(Operation::Monus))
            || matches!(
                sequence,
                Some(
                    SequenceOperation::Length
                        | SequenceOperation::Replace
                        | SequenceOperation::Append
                        | SequenceOperation::Drop
                )
            );
        if both || first {
            self.edge(site, args[0]);
        }
        if both {
            self.edge(site, args[1]);
        }
        self.goes_round(callee, args);
    }

    /// A call going round hands its counts on to be compared, or stepped
    /// and handed round again: what holds between them is what holds
    /// between the parameters they become. A record or a tag is held
    /// whatever it holds.
    fn goes_round(&mut self, callee: usize, args: &[Var]) {
        if self.recursive && self.round[callee] == self.round[self.id] {
            let counts = &self.functions[callee].counts;
            self.group(
                args.iter()
                    .zip(counts)
                    .filter(|&(_, &counts)| counts)
                    .map(|(&arg, _)| arg),
            );
        }
    }

    /// Group what is worth relating into packs.
    fn packs(self, params: usize, counts: &[bool]) -> Layout {
        let made = self.sites;
        let mut relevant = vec![false; made];
        for group in &self.groups {
            for &site in group {
                relevant[site] = true;
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
        let mut packing = Packing::new(made);
        for group in &self.groups {
            for pair in group.windows(2) {
                packing.union(pair[0], pair[1]);
            }
        }
        // A definition's counts together, where a recursion keeps a
        // relation between them that no one value carries: a count and the
        // rest of what it walks.
        let related: Vec<Site> = (0..params)
            .filter(|&at| relevant[at] && counts[at])
            .collect();
        for pair in related.windows(2) {
            packing.union(pair[0], pair[1]);
        }
        for &(derived, from) in &self.edges {
            if relevant[derived] {
                packing.union(derived, from);
            }
        }
        let (pack_of, count) = packing.packs();
        let (places, sizes) = placed(&pack_of, count, params, &self.events);
        Layout { places, sizes }
    }
}

/// Union and find over sites, each set no larger than [`PACK`].
struct Packing {
    parent: Vec<usize>,
    size: Vec<usize>,
}

impl Packing {
    fn new(sites: usize) -> Self {
        Self {
            parent: (0..sites).collect(),
            size: vec![1; sites],
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
        if a == b || self.size[a] + self.size[b] > PACK {
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

    /// Each site's pack, a site alone being in none, and how many packs
    /// there are.
    fn packs(mut self) -> (Vec<Option<usize>>, usize) {
        let sites = self.parent.len();
        let mut pack_of = vec![None; sites];
        let mut numbered = vec![usize::MAX; sites];
        let mut count = 0;
        for (site, pack) in pack_of.iter_mut().enumerate() {
            let root = self.find(site);
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

/// Each site's place in its pack, and each pack's size: the next place not
/// taken by a value of the pack still in scope, so that values of two arms
/// side by side share places, and a pack is as large as the most of its
/// values ever in scope at once.
fn placed(
    pack_of: &[Option<usize>],
    count: usize,
    params: usize,
    events: &[Event],
) -> (Vec<Place>, Vec<usize>) {
    let mut place = vec![None; pack_of.len()];
    let mut live = vec![0; count];
    let mut sizes = vec![0; count];
    let mut take = |site: usize, live: &mut Vec<usize>| {
        if let Some(pack) = pack_of[site] {
            place[site] = Some((pack, live[pack]));
            live[pack] += 1;
            sizes[pack] = sizes[pack].max(live[pack]);
        }
    };
    for site in 0..params {
        take(site, &mut live);
    }
    let mut marks: Vec<Vec<usize>> = Vec::new();
    for &event in events {
        match event {
            Event::Made(site) => take(site, &mut live),
            Event::Mark => marks.push(live.clone()),
            Event::Release => live = marks.pop().expect("a mark for each release"),
        }
    }
    (place, sizes)
}
