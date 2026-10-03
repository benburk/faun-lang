//! Which buffers nothing else holds, known before the program runs.
//!
//! Replacing an element asks, every time, whether anything else holds the
//! buffer: if so it is copied first, so that nothing else sees it change.
//! Where the answer is known, nothing need ask it. A buffer is known to be
//! held by nothing else where it was answered by a replacement, a push or an
//! append, each of which writes into a buffer nothing else holds or into a
//! fresh copy, and has been handed on since only by being moved: given up by
//! its last use, rather than kept beside whatever took it.
//!
//! A loop carrying a buffer it rewrites every time round carries one nothing
//! else holds after the first time; what it was handed on entry may be held
//! elsewhere. Made one nothing else holds there, once -- copied if it is
//! shared, as the first replacement would have -- the loop's every
//! replacement writes in place without asking. That is only done where the
//! loop does rewrite it: a loop going round on the buffer it was handed only
//! reads it, and copying that would be work for nothing.
//!
//! Only buffers of elements holding no claims take part. Replacing one of
//! those gives up nothing the element held, so writing it is all there is.

use std::collections::{HashMap, HashSet};

use super::ownership;
use super::{Class, Exit, Op, Program, RegionId, ShapeId, ValueId};

/// What legalization may write without asking.
#[derive(Default)]
pub(super) struct Unique {
    /// Replacements writing a buffer nothing else holds, by the buffer each
    /// answers.
    pub(super) replaced: HashSet<ValueId>,
    /// Loops whose buffer is made one nothing else holds on entry: by the
    /// loop's body, the place of the buffer among what it carries -- its
    /// start and length the two after -- and its elements' shape.
    pub(super) owned: HashMap<RegionId, Vec<(usize, ShapeId)>>,
}

/// Work it out for every function of `source`, where `owned` says which
/// parameters own a claim and `plain` which element shapes hold none.
pub(super) fn unique(
    source: &Program,
    owned: &[Vec<bool>],
    plain: &dyn Fn(ShapeId) -> bool,
) -> Unique {
    // Making a buffer one nothing else holds copies it as replacing an
    // element would, with the routine a replacement of that layout has.
    let replaced: HashSet<ShapeId> = source
        .functions()
        .iter()
        .filter_map(super::Function::body)
        .flat_map(|body| source.walk_within(body))
        .filter_map(|(op, _)| match *op {
            Op::BufferReplace { shape, .. } => Some(shape),
            _ => None,
        })
        .collect();
    let ownable = |shape: ShapeId| plain(shape) && replaced.contains(&shape);
    let mut found = Unique::default();
    for function in source.functions() {
        if let Some(body) = function.body() {
            let mut walk = Walk::new(source, owned);
            walk.region(body, (None, None), 0);
            walk.decide((plain, &ownable), &mut found);
        }
    }
    found
}

/// Where something is read: its position in the order read, the innermost
/// loop it is in, by its body, and the arms it is in, as a path.
#[derive(Clone, Copy, PartialEq, Eq)]
struct Site {
    position: usize,
    inside: Option<RegionId>,
    path: usize,
}

/// One reading of a value, and whether it takes a claim to it.
#[derive(Clone, Copy)]
struct Use {
    site: Site,
    claim: bool,
}

/// Where a value comes from.
#[derive(Clone, Copy)]
enum Def {
    /// Result `at` of the instruction at a position.
    Result(usize, usize),
    /// Parameter `at` of a loop's body.
    Carried(RegionId, usize),
}

/// One function's body, read once: each instruction, what it answers and
/// where it was read; where each value comes from and each reading of it;
/// and where each `if` and loop is left.
struct Walk<'a> {
    source: &'a Program,
    owned: &'a [Vec<bool>],
    ops: Vec<(Op, Vec<ValueId>, Site)>,
    defs: HashMap<ValueId, Def>,
    /// The innermost loop each value is made in, by its body: a value made
    /// outside one is read every time round it, so nothing in it can move
    /// the value on.
    homes: HashMap<ValueId, Option<RegionId>>,
    uses: HashMap<ValueId, Vec<Use>>,
    /// Each path, as the arms it takes: by each `if`'s instruction, whether
    /// the first.
    paths: Vec<Vec<(usize, bool)>>,
    position: usize,
    /// What each `if`, by its instruction, is left with by each arm.
    yields: HashMap<usize, Vec<(Vec<ValueId>, Site)>>,
    /// What each loop, by its body, goes round with, and leaves with.
    continues: HashMap<RegionId, Vec<(Vec<ValueId>, Site)>>,
    breaks: HashMap<RegionId, Vec<(Vec<ValueId>, Site)>>,
    /// Each loop's instruction, by its body.
    loops: HashMap<RegionId, usize>,
}

impl<'a> Walk<'a> {
    fn new(source: &'a Program, owned: &'a [Vec<bool>]) -> Self {
        Self {
            source,
            owned,
            ops: Vec::new(),
            defs: HashMap::new(),
            homes: HashMap::new(),
            uses: HashMap::new(),
            paths: vec![Vec::new()],
            position: 0,
            yields: HashMap::new(),
            continues: HashMap::new(),
            breaks: HashMap::new(),
            loops: HashMap::new(),
        }
    }

    /// The path `path` goes on to by taking an arm of the `if` at `at`.
    fn arm(&mut self, path: usize, at: usize, first: bool) -> usize {
        let mut arms = self.paths[path].clone();
        arms.push((at, first));
        self.paths.push(arms);
        self.paths.len() - 1
    }

    /// Whether two paths part at some `if`, so no run takes both.
    fn exclusive(&self, a: usize, b: usize) -> bool {
        for (x, y) in self.paths[a].iter().zip(&self.paths[b]) {
            if x.0 != y.0 {
                return false;
            }
            if x.1 != y.1 {
                return true;
            }
        }
        false
    }

    fn read(&mut self, value: ValueId, site: Site, claim: bool) {
        self.uses
            .entry(value)
            .or_default()
            .push(Use { site, claim });
    }

    /// Read `region`, on `path`, left by a yield to the `if` at `within`,
    /// where it is an arm of one, and by going round or leaving the loop
    /// whose body `inside` is.
    fn region(
        &mut self,
        region: RegionId,
        (within, inside): (Option<usize>, Option<RegionId>),
        path: usize,
    ) {
        let ops: Vec<(Op, Vec<ValueId>)> = self
            .source
            .walk(region)
            .map(|(op, results)| (*op, results.to_vec()))
            .collect();
        for (op, results) in ops {
            self.instruction(op, results, (inside, path));
        }
        self.position += 1;
        let site = Site {
            position: self.position,
            inside,
            path,
        };
        if let Some(terminator) = self.source.region(region).terminator {
            self.leave(terminator, site, (within, inside));
        }
    }

    /// Read one instruction, inside the loop whose body is `inside` and on
    /// `path`, and the regions it holds.
    fn instruction(
        &mut self,
        op: Op,
        results: Vec<ValueId>,
        (inside, path): (Option<RegionId>, usize),
    ) {
        let source = self.source;
        let at = self.ops.len();
        self.position += 1;
        let site = Site {
            position: self.position,
            inside,
            path,
        };
        let mut taken = Vec::new();
        ownership::taken_by(source, &op, &results, self.owned, &mut taken);
        for operand in source.operands(&op) {
            let claim = taken.contains(&operand);
            self.read(operand, site, claim);
        }
        for (index, &result) in results.iter().enumerate() {
            self.defs.insert(result, Def::Result(at, index));
            self.homes.insert(result, inside);
        }
        self.ops.push((op, results, site));
        self.held(op, at, (inside, path));
    }

    /// Read the regions the instruction at `at` holds: an `if`'s arms, each
    /// a path of its own, and a loop's body, whose parameters it makes.
    fn held(&mut self, op: Op, at: usize, (inside, path): (Option<RegionId>, usize)) {
        let source = self.source;
        match op {
            Op::If {
                then_region,
                else_region,
                ..
            } => {
                let first = self.arm(path, at, true);
                self.region(then_region, (Some(at), inside), first);
                let second = self.arm(path, at, false);
                self.region(else_region, (Some(at), inside), second);
            }
            Op::Loop { body, .. } => {
                self.loops.insert(body, at);
                let params = source.values(source.region(body).params);
                for (index, &param) in params.iter().enumerate() {
                    self.defs.insert(param, Def::Carried(body, index));
                    self.homes.insert(param, Some(body));
                }
                self.region(body, (None, Some(body)), path);
            }
            _ => {}
        }
    }

    /// Read how a region is left, at `site`: each value leaving takes a
    /// claim, and goes to the `if` or loop it leaves for.
    fn leave(
        &mut self,
        terminator: super::Terminator,
        site: Site,
        (within, inside): (Option<usize>, Option<RegionId>),
    ) {
        let leaving = self.source.values(terminator.values).to_vec();
        for &value in &leaving {
            self.read(value, site, true);
        }
        let exit = (leaving, site);
        match terminator.exit {
            Exit::Yield => {
                if let Some(at) = within {
                    self.yields.entry(at).or_default().push(exit);
                }
            }
            Exit::Continue => {
                if let Some(body) = inside {
                    self.continues.entry(body).or_default().push(exit);
                }
            }
            Exit::Break => {
                if let Some(body) = inside {
                    self.breaks.entry(body).or_default().push(exit);
                }
            }
            Exit::Return => {}
        }
    }

    /// Whether `value` is handed on by its use at `site` alone: read there
    /// once, in the loop it is made in, and on any run through `site`
    /// claimed nowhere else and read nowhere after.
    fn moved(&self, value: ValueId, site: Site) -> bool {
        let Some(uses) = self.uses.get(&value) else {
            return false;
        };
        self.homes.get(&value) == Some(&site.inside)
            && uses
                .iter()
                .filter(|reading| reading.site.position == site.position)
                .count()
                == 1
            && uses.iter().all(|reading| {
                reading.site.position == site.position
                    || self.exclusive(reading.site.path, site.path)
                    || (!reading.claim && reading.site.position < site.position)
            })
    }

    /// Whether `value` is a buffer nothing else holds where it is made,
    /// where `carried` says which loop parameters are taken to be.
    fn fresh(&self, value: ValueId, carried: &HashSet<(RegionId, usize)>) -> bool {
        match self.defs.get(&value) {
            Some(&Def::Result(at, 0))
                if matches!(
                    self.ops[at].0,
                    Op::BufferReplace { .. } | Op::BufferPush { .. } | Op::BufferAppend { .. }
                ) =>
            {
                true
            }
            Some(&Def::Result(at, index)) => {
                let exits = match self.ops[at].0 {
                    Op::If { .. } => self.yields.get(&at),
                    Op::Loop { body, .. } => self.breaks.get(&body),
                    _ => return false,
                };
                exits.is_some_and(|exits| {
                    exits.iter().all(|(values, site)| {
                        self.fresh(values[index], carried) && self.moved(values[index], *site)
                    })
                })
            }
            Some(&Def::Carried(body, index)) => carried.contains(&(body, index)),
            None => false,
        }
    }

    /// The position of the loop whose body is `body`, and its initial
    /// state.
    fn initial(&self, body: RegionId) -> (Site, Vec<ValueId>) {
        let (op, _, site) = &self.ops[self.loops[&body]];
        let Op::Loop { initial, .. } = *op else {
            unreachable!("a loop's body belongs to a loop");
        };
        (*site, self.source.values(initial).to_vec())
    }

    /// The shape of the elements a carried buffer is read or written at,
    /// where its loop does either.
    fn shape(&self, buffer: ValueId) -> Option<ShapeId> {
        self.ops.iter().find_map(|(op, _, _)| match *op {
            Op::BufferField {
                buffer: read,
                shape,
                ..
            } if read == buffer => Some(shape),
            Op::BufferReplace { operands, shape } if self.source.values(operands)[0] == buffer => {
                Some(shape)
            }
            _ => None,
        })
    }

    /// Settle which loop parameters are buffers nothing else holds, then
    /// say which replacements write one and which loops make theirs so.
    /// `plain` says which element shapes hold no claims, and `ownable`
    /// which of those a buffer can be made one nothing else holds at.
    fn decide(
        &self,
        (plain, ownable): (&dyn Fn(ShapeId) -> bool, &dyn Fn(ShapeId) -> bool),
        found: &mut Unique,
    ) {
        // Every carried buffer is taken to be one nothing else holds, and
        // those it cannot be are given up until none is.
        let shapes = self.candidates(ownable);
        let mut carried: HashSet<(RegionId, usize)> = shapes.keys().copied().collect();
        loop {
            let kept: HashSet<_> = carried
                .iter()
                .copied()
                .filter(|&(body, index)| self.carries_its_own(body, index, &carried))
                .collect();
            if kept == carried {
                break;
            }
            carried = kept;
        }
        for &(body, index) in &carried {
            let (site, initial) = self.initial(body);
            let entered = initial[index];
            if !(self.fresh(entered, &carried) && self.moved(entered, site)) {
                found
                    .owned
                    .entry(body)
                    .or_default()
                    .push((index, shapes[&(body, index)]));
            }
        }
        for (op, results, site) in &self.ops {
            if let Op::BufferReplace { operands, shape } = *op {
                let buffer = self.source.values(operands)[0];
                if plain(shape) && self.fresh(buffer, &carried) && self.moved(buffer, *site) {
                    found.replaced.insert(results[0]);
                }
            }
        }
    }

    /// Every loop parameter that is a sequence's buffer, its start and
    /// length the two after, whose elements are read or written at a shape
    /// it can be made one nothing else holds at: by loop and place, that
    /// shape.
    fn candidates(&self, ownable: &dyn Fn(ShapeId) -> bool) -> HashMap<(RegionId, usize), ShapeId> {
        let source = self.source;
        let mut shapes = HashMap::new();
        for &body in self.loops.keys() {
            let params = source.values(source.region(body).params);
            for (index, &param) in params.iter().enumerate() {
                let sequence = params.get(index..index + 3).is_some_and(|run| {
                    source.class(run[0]) == Class::Buffer
                        && run[1..]
                            .iter()
                            .all(|&leaf| source.class(leaf).fits(Class::Word))
                });
                if sequence && let Some(shape) = self.shape(param).filter(|&shape| ownable(shape)) {
                    shapes.insert((body, index), shape);
                }
            }
        }
        shapes
    }

    /// Whether the loop parameter goes round as a buffer nothing else
    /// holds, and is rewritten each time round rather than only read.
    fn carries_its_own(
        &self,
        body: RegionId,
        index: usize,
        carried: &HashSet<(RegionId, usize)>,
    ) -> bool {
        let param = self.source.values(self.source.region(body).params)[index];
        self.continues.get(&body).is_none_or(|rounds| {
            rounds.iter().all(|(values, site)| {
                values[index] != param
                    && self.fresh(values[index], carried)
                    && self.moved(values[index], *site)
            })
        })
    }
}
