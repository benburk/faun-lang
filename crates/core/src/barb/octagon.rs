//! Octagons: what holds between two numbers, as well as of each.
//!
//! An interval says what one number can be. Where a program compares two
//! numbers, adds one to another or counts one down beside another, what it
//! knows is a relation between them -- `i < len`, `bit + 9 <= total`,
//! `count + rest <= 5` -- and an interval of each forgets it, so that a
//! bound found later of one never reaches the other. An octagon keeps
//! every constraint of the form `±x ±y <= c` (Miné, "The octagon abstract
//! domain", 2006), and a bound on one side of one reaches the other side
//! when the octagon is closed.
//!
//! Each variable `x` is two nodes, `+x` and `-x`, and the matrix holds, for
//! every two nodes `u` and `v`, the most `u - v` can be. `x - y <= c` is the
//! entry from `+x` to `+y`, `x + y <= c` the entry from `+x` to `-y`, and
//! `x <= c` the entry from `+x` to `-x`, at twice `c`. Every constraint is
//! held twice, once each way round, which keeps the matrix coherent.
//!
//! Closing the matrix makes every entry the tightest its others imply:
//! shortest paths, then each variable's own bound rounded down to an even
//! number since every value here is an integer, then each entry tightened
//! by the two variables' own bounds (Bagnara, Hill and Zaffanella, 2008).
//! A closed octagon answers a question by reading one entry.

use crate::facts::Facts as Bounds;

/// A bound in the matrix. Naturals here are below `2^64`, and a matrix
/// entry is at most two of them summed or doubled, so an `i128` holds any
/// with room to add three without overflow.
pub(super) type Bound = i128;

/// No bound at all.
pub(super) const INFINITE: Bound = i128::MAX / 8;

/// The node of a variable, `+x` or `-x`.
pub(super) const fn node(variable: usize, negated: bool) -> usize {
    2 * variable + if negated { 1 } else { 0 }
}

/// The node standing for the negation of `node`.
const fn bar(node: usize) -> usize {
    node ^ 1
}

/// Two bounds added, no bound where either is none.
const fn plus(a: Bound, b: Bound) -> Bound {
    if a >= INFINITE || b >= INFINITE {
        INFINITE
    } else {
        a + b
    }
}

/// The greatest even number no more than `bound`.
const fn even(bound: Bound) -> Bound {
    if bound >= INFINITE {
        bound
    } else {
        bound - bound.rem_euclid(2)
    }
}

/// Where a growing entry is widened to: the next width a machine holds a
/// number in, which a remainder keeps a value below, and no bound past
/// the widest. Each variable's own bound is held doubled, and so are its
/// thresholds.
#[cfg(test)]
fn threshold(bound: Bound, own: bool) -> Bound {
    let scale = if own { 2 } else { 1 };
    [
        0,
        Bound::from(u8::MAX),
        Bound::from(u16::MAX),
        Bound::from(u32::MAX),
        Bound::from(u64::MAX),
    ]
    .into_iter()
    .map(|width| width * scale)
    .find(|&width| width >= bound)
    .unwrap_or(INFINITE)
}

/// A constraint between two nodes: `u - v <= bound`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(super) struct Constraint {
    pub from: usize,
    pub to: usize,
    pub bound: Bound,
}

impl Constraint {
    /// `x - y <= bound`.
    pub(super) const fn difference(x: usize, y: usize, bound: Bound) -> Self {
        Self {
            from: node(x, false),
            to: node(y, false),
            bound,
        }
    }

    /// `x + y <= bound`.
    #[cfg(test)]
    const fn sum(x: usize, y: usize, bound: Bound) -> Self {
        Self {
            from: node(x, false),
            to: node(y, true),
            bound,
        }
    }

    /// `x <= bound`.
    pub(super) const fn most(x: usize, bound: Bound) -> Self {
        Self {
            from: node(x, false),
            to: node(x, true),
            bound: 2 * bound,
        }
    }

    /// `x >= bound`.
    pub(super) const fn least(x: usize, bound: Bound) -> Self {
        Self {
            from: node(x, true),
            to: node(x, false),
            bound: -2 * bound,
        }
    }

    /// The same constraint, the other way round: `-v - -u <= bound`.
    const fn turned(self) -> Self {
        Self {
            from: bar(self.to),
            to: bar(self.from),
            bound: self.bound,
        }
    }

    /// The variables it constrains.
    pub(super) const fn variables(self) -> (usize, usize) {
        (self.from / 2, self.to / 2)
    }

    /// The same constraint over other variables, `x` and `y` standing
    /// where its first and second were.
    pub(super) const fn renamed(self, x: usize, y: usize) -> Self {
        Self {
            from: node(x, self.from % 2 == 1),
            to: node(y, self.to % 2 == 1),
            bound: self.bound,
        }
    }

    /// Whether it says something of one variable alone.
    pub(super) const fn own(self) -> bool {
        self.from / 2 == self.to / 2
    }
}

/// Constraints `±x ±y <= c` over a fixed number of variables.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Octagon {
    /// Twice the variables: the side of the matrix.
    side: usize,
    entries: Vec<Bound>,
}

impl Octagon {
    /// Nothing known of `variables` numbers.
    pub(super) fn top(variables: usize) -> Self {
        let side = 2 * variables;
        let mut entries = vec![INFINITE; side * side];
        for at in 0..side {
            entries[at * side + at] = 0;
        }
        Self { side, entries }
    }

    /// How many variables it relates.
    pub(super) const fn variables(&self) -> usize {
        self.side / 2
    }

    /// The most `from - to` can be.
    pub(super) fn get(&self, from: usize, to: usize) -> Bound {
        self.entries[from * self.side + to]
    }

    fn put(&mut self, from: usize, to: usize, bound: Bound) {
        self.entries[from * self.side + to] = bound;
    }

    /// Say `constraint` without closing: for building a matrix to close.
    pub(super) fn assume(&mut self, constraint: Constraint) {
        for Constraint { from, to, bound } in [constraint, constraint.turned()] {
            if bound < self.get(from, to) {
                self.put(from, to, bound);
            }
        }
    }

    /// What a variable can be, by its own bounds, which a closed matrix
    /// holds as tight as anything implies. Nothing, where it can be nothing.
    pub(super) fn bounds(&self, variable: usize) -> Bounds {
        let (plus, minus) = (node(variable, false), node(variable, true));
        let (high, low) = (self.get(plus, minus), self.get(minus, plus));
        let least = if low >= INFINITE {
            0
        } else {
            // The least is minus half the entry, rounded up.
            let least = (-low).div_euclid(2) + Bound::from((-low).rem_euclid(2) != 0);
            u64::try_from(least.max(0)).unwrap_or(u64::MAX)
        };
        let greatest = if high >= INFINITE {
            None
        } else if high < 0 {
            return Bounds::NOTHING;
        } else {
            u64::try_from(high.div_euclid(2)).ok()
        };
        let bounds = Bounds {
            low: least,
            high: greatest,
        };
        if bounds.is_nothing() {
            Bounds::NOTHING
        } else {
            bounds
        }
    }

    /// Say that a variable lies within `bounds`, without closing.
    #[cfg(test)]
    fn bound(&mut self, variable: usize, bounds: Bounds) {
        self.assume(Constraint::least(variable, Bound::from(bounds.low)));
        if let Some(high) = bounds.high {
            self.assume(Constraint::most(variable, Bound::from(high)));
        }
    }

    /// Forget everything said of a variable, as for a new value taking its
    /// place. A closed matrix stays closed.
    pub(super) fn forget(&mut self, variable: usize) {
        for own in [node(variable, false), node(variable, true)] {
            for other in 0..self.side {
                if other != own {
                    self.put(own, other, INFINITE);
                    self.put(other, own, INFINITE);
                }
            }
        }
        self.put(node(variable, false), node(variable, true), INFINITE);
        self.put(node(variable, true), node(variable, false), INFINITE);
    }

    /// Say that a variable just forgotten lies within `bounds`, keeping the
    /// matrix closed, in time linear in its side: a forgotten variable is
    /// on no path but through its own bounds, so only the entries between
    /// it and each other variable, which those bounds and the other's
    /// tighten, can change.
    pub(super) fn introduce(&mut self, variable: usize, bounds: Bounds) {
        let (plus, minus) = (node(variable, false), node(variable, true));
        self.put(minus, plus, -2 * Bound::from(bounds.low));
        if let Some(high) = bounds.high {
            self.put(plus, minus, 2 * Bound::from(high));
        }
        for own in [plus, minus] {
            let mine = self.get(own, bar(own));
            for other in 0..self.side {
                if other / 2 == variable {
                    continue;
                }
                let theirs = self.get(bar(other), other);
                if mine < INFINITE && theirs < INFINITE {
                    let halves = mine.midpoint(theirs);
                    if halves < self.get(own, other) {
                        self.put(own, other, halves);
                        self.put(bar(other), bar(own), halves);
                    }
                }
            }
        }
    }

    /// Say that `fresh`, a variable just introduced with bounds of its own
    /// and related to nothing, less `from` lies between `least` and `most`
    /// where each is said, keeping the matrix closed. What holds of `fresh`
    /// is what holds of `from` moved by that much, in time linear in the
    /// side; only where its own bounds are tighter than that does it tell
    /// `from` and the rest anything, and then it is closed as any added
    /// constraint is. Answers whether any value still meets them all.
    #[expect(
        clippy::too_many_lines,
        reason = "the row moved, the bounds moved, the row tightened, then the bounds of its own"
    )]
    pub(super) fn assign(
        &mut self,
        fresh: usize,
        from: usize,
        least: Option<Bound>,
        most: Option<Bound>,
    ) -> bool {
        let (up, down) = (node(fresh, false), node(fresh, true));
        let (above, below) = (node(from, false), node(from, true));
        let own = (self.get(up, down), self.get(down, up));
        self.forget(fresh);
        // `fresh <= from + most`, so its row is `from`'s moved up by `most`,
        // and `-fresh <= -from - least`.
        for other in 0..self.side {
            if other / 2 == fresh {
                continue;
            }
            if let Some(most) = most {
                let through = plus(most, self.get(above, other));
                self.put(up, other, through);
                self.put(bar(other), down, through);
            }
            if let Some(least) = least {
                let through = plus(-least, self.get(below, other));
                self.put(down, other, through);
                self.put(bar(other), up, through);
            }
        }
        if let Some(most) = most {
            self.put(up, down, even(plus(2 * most, self.get(above, below))));
        }
        if let Some(least) = least {
            self.put(down, up, even(plus(-2 * least, self.get(below, above))));
        }
        // Tighten its row by its own bounds and each other's.
        for mine in [up, down] {
            let own = self.get(mine, bar(mine));
            if own >= INFINITE {
                continue;
            }
            for other in 0..self.side {
                if other / 2 == fresh {
                    continue;
                }
                let theirs = self.get(bar(other), other);
                if theirs < INFINITE {
                    let halves = own.midpoint(theirs);
                    if halves < self.get(mine, other) {
                        self.put(mine, other, halves);
                        self.put(bar(other), bar(mine), halves);
                    }
                }
            }
        }
        // Its own bounds, as introduced, where tighter than `from` moved
        // says: they bound `from`, and through it the rest.
        self.add(Constraint {
            from: up,
            to: down,
            bound: own.0,
        }) && self.add(Constraint {
            from: down,
            to: up,
            bound: own.1,
        })
    }

    /// Whether some value of every variable meets every constraint, which
    /// a closed matrix says of itself.
    pub(super) fn is_empty(&self) -> bool {
        (0..self.side).any(|at| self.get(at, at) < 0)
    }

    /// Make every entry as tight as the others imply. Answers whether any
    /// value meets them all; where none does, the matrix is left empty.
    pub(super) fn close(&mut self) -> bool {
        let side = self.side;
        for via in 0..side {
            for from in 0..side {
                let first = self.get(from, via);
                if first >= INFINITE {
                    continue;
                }
                for to in 0..side {
                    let through = plus(first, self.get(via, to));
                    if through < self.get(from, to) {
                        self.put(from, to, through);
                    }
                }
            }
        }
        self.tighten()
    }

    /// Say `constraint` of a closed matrix and close it again, in time
    /// square in its side rather than cube: a path the new constraint
    /// shortens goes through its ends, so only they need be gone through.
    /// Answers whether any value still meets every constraint.
    pub(super) fn add(&mut self, constraint: Constraint) -> bool {
        if constraint.bound >= self.get(constraint.from, constraint.to) {
            return !self.is_empty();
        }
        self.assume(constraint);
        let mut through = [
            constraint.from,
            constraint.to,
            bar(constraint.from),
            bar(constraint.to),
        ];
        through.sort_unstable();
        let side = self.side;
        for (at, &via) in through.iter().enumerate() {
            if at > 0 && through[at - 1] == via {
                continue;
            }
            for from in 0..side {
                let first = self.get(from, via);
                if first >= INFINITE {
                    continue;
                }
                for to in 0..side {
                    let through = plus(first, self.get(via, to));
                    if through < self.get(from, to) {
                        self.put(from, to, through);
                    }
                }
            }
        }
        self.tighten()
    }

    /// Say a variable of a closed matrix lies within `bounds`, closing again
    /// once for both its ends: the two constraints go through the same two
    /// nodes. Answers whether any value still meets every constraint.
    pub(super) fn narrow(&mut self, variable: usize, bounds: Bounds) -> bool {
        let (up, down) = (node(variable, false), node(variable, true));
        let least = -2 * Bound::from(bounds.low);
        let most = bounds.high.map_or(INFINITE, |high| 2 * Bound::from(high));
        if least >= self.get(down, up) && most >= self.get(up, down) {
            return !self.is_empty();
        }
        self.assume(Constraint::least(variable, Bound::from(bounds.low)));
        if let Some(high) = bounds.high {
            self.assume(Constraint::most(variable, Bound::from(high)));
        }
        let side = self.side;
        for via in [up, down] {
            for from in 0..side {
                let first = self.get(from, via);
                if first >= INFINITE {
                    continue;
                }
                for to in 0..side {
                    let through = plus(first, self.get(via, to));
                    if through < self.get(from, to) {
                        self.put(from, to, through);
                    }
                }
            }
        }
        self.tighten()
    }

    /// The integer half of closing, after shortest paths: each variable's
    /// own bound made even, then every entry tightened by its two
    /// variables' own bounds.
    fn tighten(&mut self) -> bool {
        let side = self.side;
        if self.is_empty() {
            return false;
        }
        for at in 0..side {
            let own = even(self.get(at, bar(at)));
            self.put(at, bar(at), own);
        }
        for at in (0..side).step_by(2) {
            if plus(self.get(at, bar(at)), self.get(bar(at), at)) < 0 {
                self.put(at, at, -1);
                return false;
            }
        }
        for from in 0..side {
            let own = self.get(from, bar(from));
            if own >= INFINITE {
                continue;
            }
            for to in 0..side {
                let other = self.get(bar(to), to);
                if other >= INFINITE {
                    continue;
                }
                let halves = own.midpoint(other);
                if halves < self.get(from, to) {
                    self.put(from, to, halves);
                }
            }
        }
        for at in 0..side {
            self.put(at, at, 0);
        }
        true
    }

    /// What either of two closed octagons holds: the looser of each entry,
    /// which is closed again.
    pub(super) fn join(&mut self, other: &Self) {
        for (held, other) in self.entries.iter_mut().zip(&other.entries) {
            *held = (*held).max(*other);
        }
    }

    /// Widen `self`, what was held, by `newer`, what was found: an entry
    /// that loosened jumps to the next threshold, and one that held is
    /// kept. The result is not closed, and must not be before widening it
    /// again, or a dropped constraint could come back and go round for
    /// ever.
    #[cfg(test)]
    fn widen(&mut self, newer: &Self) {
        let side = self.side;
        for from in 0..side {
            for to in 0..side {
                let found = newer.get(from, to);
                if found > self.get(from, to) {
                    self.put(from, to, threshold(found, to == bar(from)));
                }
            }
        }
    }
}

/// What range analysis needs of a relational domain: constraints between
/// two values, or of one, said, closed, joined and read. The solver is
/// written over this, so the domain is a choice made where it is called.
pub(super) trait Domain: Clone + std::fmt::Debug + PartialEq {
    /// Whether it relates anything at all; where not, the solver keeps
    /// intervals alone and never builds one.
    const RELATES: bool = true;
    /// Nothing known of `variables` values.
    fn top(variables: usize) -> Self;
    fn variables(&self) -> usize;
    /// The most `from - to` can be, nodes as [`node`] names them.
    fn get(&self, from: usize, to: usize) -> Bound;
    /// What a value can be by its own bounds.
    fn bounds(&self, variable: usize) -> Bounds;
    fn forget(&mut self, variable: usize);
    fn introduce(&mut self, variable: usize, bounds: Bounds);
    fn assign(
        &mut self,
        fresh: usize,
        from: usize,
        least: Option<Bound>,
        most: Option<Bound>,
    ) -> bool;
    fn add(&mut self, constraint: Constraint) -> bool;
    /// Say a value lies within `bounds`, and close.
    fn narrow(&mut self, variable: usize, bounds: Bounds) -> bool {
        self.add(Constraint::least(variable, Bound::from(bounds.low)))
            && bounds
                .high
                .is_none_or(|high| self.add(Constraint::most(variable, Bound::from(high))))
    }
    fn assume(&mut self, constraint: Constraint);
    fn close(&mut self) -> bool;
    fn join(&mut self, other: &Self);
}

impl Domain for Octagon {
    fn top(variables: usize) -> Self {
        Self::top(variables)
    }
    fn variables(&self) -> usize {
        Self::variables(self)
    }
    fn get(&self, from: usize, to: usize) -> Bound {
        Self::get(self, from, to)
    }
    fn bounds(&self, variable: usize) -> Bounds {
        Self::bounds(self, variable)
    }
    fn forget(&mut self, variable: usize) {
        Self::forget(self, variable);
    }
    fn introduce(&mut self, variable: usize, bounds: Bounds) {
        Self::introduce(self, variable, bounds);
    }
    fn assign(
        &mut self,
        fresh: usize,
        from: usize,
        least: Option<Bound>,
        most: Option<Bound>,
    ) -> bool {
        Self::assign(self, fresh, from, least, most)
    }
    fn add(&mut self, constraint: Constraint) -> bool {
        Self::add(self, constraint)
    }
    fn narrow(&mut self, variable: usize, bounds: Bounds) -> bool {
        Self::narrow(self, variable, bounds)
    }
    fn assume(&mut self, constraint: Constraint) {
        Self::assume(self, constraint);
    }
    fn close(&mut self) -> bool {
        Self::close(self)
    }
    fn join(&mut self, other: &Self) {
        Self::join(self, other);
    }
}

/// Differences `x - y <= c` alone: an octagon whose sums are forgotten
/// after every step, for testing what sums earn.
#[cfg(test)]
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Zone(Octagon);

#[cfg(test)]
impl Zone {
    /// Forget every constraint on a sum or a difference of negations.
    fn differences(&mut self) {
        let side = 2 * self.0.variables();
        for from in 0..side {
            for to in 0..side {
                if from / 2 != to / 2 && from % 2 != to % 2 {
                    self.0.put(from, to, INFINITE);
                }
            }
        }
    }
}

#[cfg(test)]
impl Domain for Zone {
    fn top(variables: usize) -> Self {
        Self(Octagon::top(variables))
    }
    fn variables(&self) -> usize {
        self.0.variables()
    }
    fn get(&self, from: usize, to: usize) -> Bound {
        self.0.get(from, to)
    }
    fn bounds(&self, variable: usize) -> Bounds {
        self.0.bounds(variable)
    }
    fn forget(&mut self, variable: usize) {
        self.0.forget(variable);
    }
    fn introduce(&mut self, variable: usize, bounds: Bounds) {
        self.0.introduce(variable, bounds);
        self.differences();
    }
    fn assign(
        &mut self,
        fresh: usize,
        from: usize,
        least: Option<Bound>,
        most: Option<Bound>,
    ) -> bool {
        let holds = self.0.assign(fresh, from, least, most);
        self.differences();
        holds
    }
    fn add(&mut self, constraint: Constraint) -> bool {
        let holds = self.0.add(constraint);
        self.differences();
        holds
    }
    fn narrow(&mut self, variable: usize, bounds: Bounds) -> bool {
        let holds = self.0.narrow(variable, bounds);
        self.differences();
        holds
    }
    fn assume(&mut self, constraint: Constraint) {
        self.0.assume(constraint);
    }
    fn close(&mut self) -> bool {
        let holds = self.0.close();
        self.differences();
        holds
    }
    fn join(&mut self, other: &Self) {
        self.0.join(&other.0);
    }
}

/// No relations: intervals alone, for testing what relations earn.
#[cfg(test)]
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Intervals;

#[cfg(test)]
impl Domain for Intervals {
    const RELATES: bool = false;
    fn top(_: usize) -> Self {
        Self
    }
    fn variables(&self) -> usize {
        0
    }
    fn get(&self, _: usize, _: usize) -> Bound {
        INFINITE
    }
    fn bounds(&self, _: usize) -> Bounds {
        Bounds::ANY
    }
    fn forget(&mut self, _: usize) {}
    fn introduce(&mut self, _: usize, _: Bounds) {}
    fn assign(&mut self, _: usize, _: usize, _: Option<Bound>, _: Option<Bound>) -> bool {
        true
    }
    fn add(&mut self, _: Constraint) -> bool {
        true
    }
    fn assume(&mut self, _: Constraint) {}
    fn close(&mut self) -> bool {
        true
    }
    fn join(&mut self, _: &Self) {}
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Every point of `0..=limit` in each of `variables` dimensions.
    fn points(variables: usize, limit: i128) -> Vec<Vec<i128>> {
        let mut all = vec![Vec::new()];
        for _ in 0..variables {
            all = all
                .into_iter()
                .flat_map(|point| {
                    (0..=limit).map(move |value| {
                        let mut point = point.clone();
                        point.push(value);
                        point
                    })
                })
                .collect();
        }
        all
    }

    fn value(point: &[i128], node: usize) -> i128 {
        if node.is_multiple_of(2) {
            point[node / 2]
        } else {
            -point[node / 2]
        }
    }

    fn meets(point: &[i128], constraints: &[Constraint]) -> bool {
        constraints.iter().all(|constraint| {
            value(point, constraint.from) - value(point, constraint.to) <= constraint.bound
        })
    }

    /// A small generator, so the cases are the same every run.
    struct Lcg(u64);
    impl Lcg {
        fn next(&mut self, below: u64) -> u64 {
            self.0 = self
                .0
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            (self.0 >> 33) % below
        }
    }

    fn random_constraints(random: &mut Lcg, variables: usize, count: usize) -> Vec<Constraint> {
        (0..count)
            .map(|_| {
                let from =
                    usize::try_from(random.next(2 * u64::try_from(variables).unwrap())).unwrap();
                let to =
                    usize::try_from(random.next(2 * u64::try_from(variables).unwrap())).unwrap();
                let bound = i128::from(random.next(13)) - 6;
                Constraint { from, to, bound }
            })
            .filter(|constraint| constraint.from != constraint.to)
            .collect()
    }

    /// Closing is exact over the integers: every point meeting the
    /// constraints meets the closed matrix, every entry is reached by one
    /// of them, and the matrix is empty just where no point is.
    #[test]
    fn closing_is_exact_over_small_integers() {
        let mut random = Lcg(7);
        let (variables, limit) = (3, 5);
        let space = points(variables, limit);
        for _ in 0..400 {
            let constraints = random_constraints(&mut random, variables, 4);
            let mut octagon = Octagon::top(variables);
            for variable in 0..variables {
                octagon.bound(
                    variable,
                    Bounds {
                        low: 0,
                        high: Some(u64::try_from(limit).unwrap()),
                    },
                );
            }
            for &c in &constraints {
                octagon.assume(c);
            }
            let inside: Vec<_> = space
                .iter()
                .filter(|point| meets(point, &constraints))
                .collect();
            let feasible = octagon.close();
            assert_eq!(feasible, !inside.is_empty(), "{constraints:?}");
            if !feasible {
                continue;
            }
            for from in 0..2 * variables {
                for to in 0..2 * variables {
                    let most = inside
                        .iter()
                        .map(|point| value(point, from) - value(point, to))
                        .max()
                        .unwrap();
                    assert_eq!(octagon.get(from, to), most, "{constraints:?} {from} {to}");
                }
            }
        }
    }

    /// Adding a constraint to a closed matrix and closing in square time
    /// gives what closing it all afresh does.
    #[test]
    fn adding_one_constraint_closes_as_closing_afresh_does() {
        let mut random = Lcg(11);
        let variables = 4;
        for _ in 0..400 {
            let constraints = random_constraints(&mut random, variables, 6);
            let mut stepped = Octagon::top(variables);
            let mut afresh = Octagon::top(variables);
            for variable in 0..variables {
                let bounds = Bounds {
                    low: 0,
                    high: Some(9),
                };
                stepped.bound(variable, bounds);
                afresh.bound(variable, bounds);
            }
            let mut feasible = stepped.close();
            for &constraint in &constraints {
                feasible = feasible && stepped.add(constraint);
                afresh.assume(constraint);
            }
            assert_eq!(feasible, afresh.close(), "{constraints:?}");
            if feasible {
                assert_eq!(stepped, afresh, "{constraints:?}");
            }
        }
    }

    /// `i < len`, then `len <= 10` found later: the bound reaches `i`.
    #[test]
    fn a_bound_found_later_reaches_through_a_guard() {
        let (i, len) = (0, 1);
        let mut octagon = Octagon::top(2);
        octagon.bound(i, Bounds::ANY);
        octagon.bound(len, Bounds::ANY);
        assert!(octagon.close());
        assert!(octagon.add(Constraint::difference(i, len, -1)));
        assert_eq!(octagon.bounds(i), Bounds::ANY);
        assert!(octagon.add(Constraint::most(len, 10)));
        assert_eq!(
            octagon.bounds(i),
            Bounds {
                low: 0,
                high: Some(9)
            }
        );
        assert_eq!(
            octagon.bounds(len),
            Bounds {
                low: 1,
                high: Some(10)
            }
        );
    }

    /// `s = bit + 9` and `s <= total`, `total <= 100`: `bit <= 91`, with no
    /// walk back through the sum.
    #[test]
    fn a_guard_on_a_sum_bounds_its_operand() {
        let (bit, sum, total) = (0, 1, 2);
        let mut octagon = Octagon::top(3);
        for variable in 0..3 {
            octagon.bound(variable, Bounds::ANY);
        }
        octagon.bound(total, Bounds::at(100).or(Bounds::at(0)));
        assert!(octagon.close());
        assert!(octagon.add(Constraint::difference(sum, bit, 9)));
        assert!(octagon.add(Constraint::difference(bit, sum, -9)));
        assert!(octagon.add(Constraint::difference(sum, total, 0)));
        assert_eq!(
            octagon.bounds(bit),
            Bounds {
                low: 0,
                high: Some(91)
            }
        );
        // And a guard no sum can meet leaves nothing.
        assert!(!octagon.add(Constraint::least(bit, 92)));
        assert_eq!(octagon.bounds(bit), Bounds::NOTHING);
    }

    /// Joining keeps what both said, as tight as either allows.
    #[test]
    fn a_join_holds_both() {
        let mut first = Octagon::top(2);
        first.bound(0, Bounds::at(0));
        first.bound(1, Bounds::at(5));
        assert!(first.close());
        let mut second = Octagon::top(2);
        second.bound(0, Bounds::at(1));
        second.bound(1, Bounds::at(4));
        assert!(second.close());
        first.join(&second);
        assert_eq!(
            first.bounds(0),
            Bounds {
                low: 0,
                high: Some(1)
            }
        );
        // The sum is five on both sides, and stays so.
        assert_eq!(first.get(node(0, false), node(1, true)), 5);
        assert_eq!(first.get(node(0, true), node(1, false)), -5);
        let mut closed = first.clone();
        assert!(closed.close());
        assert_eq!(closed, first);
    }

    /// A count beside the rest of a list it walks, `count + rest` five
    /// where it comes in. Going round adds one to the count and takes one
    /// from the rest, so the sum holds: widening leaves it, and with it the
    /// count's bound, while the count's own bound grows to a threshold.
    #[test]
    fn a_count_beside_a_walk_survives_widening() {
        let (count, rest) = (0, 1);
        let mut entry = Octagon::top(2);
        entry.bound(count, Bounds::at(0));
        entry.bound(
            rest,
            Bounds {
                low: 0,
                high: Some(5),
            },
        );
        // What comes in is closed; only what widening makes of it is not.
        assert!(entry.close());
        let mut held = entry.clone();
        for _ in 0..8 {
            let mut walked = held.clone();
            assert!(walked.close());
            // The round's step: the rest is at least one, and each moves.
            assert!(walked.add(Constraint::least(rest, 1)));
            let mut stepped = Octagon::top(2);
            let (low, high) = (walked.bounds(count), walked.bounds(rest));
            stepped.bound(count, low.up());
            stepped.bound(rest, high.down());
            let sum = walked.get(node(count, false), node(rest, true));
            stepped.assume(Constraint::sum(count, rest, sum));
            assert!(stepped.close());
            let mut next = entry.clone();
            next.join(&stepped);
            let previous = held.clone();
            held.widen(&next);
            if held == previous {
                break;
            }
        }
        let mut closed = held.clone();
        assert!(closed.close());
        assert_eq!(
            closed.bounds(count),
            Bounds {
                low: 0,
                high: Some(5)
            }
        );
    }

    /// A growing bound widens to the next machine width, and past the
    /// widest to none; a least that falls goes to nought.
    #[test]
    fn widening_goes_to_machine_widths() {
        let mut held = Octagon::top(1);
        held.bound(0, Bounds::at(300));
        let mut found = Octagon::top(1);
        found.bound(
            0,
            Bounds {
                low: 299,
                high: Some(301),
            },
        );
        held.widen(&found);
        assert_eq!(
            held.bounds(0),
            Bounds {
                low: 0,
                high: Some(u64::from(u16::MAX))
            }
        );
        let mut beyond = Octagon::top(1);
        beyond.bound(0, Bounds::at(u64::MAX));
        held.widen(&beyond);
        assert_eq!(held.bounds(0).high, Some(u64::MAX));
        let mut endless = Octagon::top(1);
        endless.bound(0, Bounds::ANY);
        held.widen(&endless);
        assert_eq!(held.bounds(0), Bounds::ANY);
    }

    /// Introducing a forgotten variable's bounds closes as adding them does.
    #[test]
    fn introducing_a_variable_closes_as_adding_its_bounds_does() {
        let mut random = Lcg(5);
        for _ in 0..200 {
            let constraints = random_constraints(&mut random, 3, 4);
            let mut octagon = Octagon::top(3);
            for variable in 0..3 {
                octagon.bound(
                    variable,
                    Bounds {
                        low: 0,
                        high: Some(9),
                    },
                );
            }
            for &c in &constraints {
                octagon.assume(c);
            }
            if !octagon.close() {
                continue;
            }
            octagon.forget(1);
            let bounds = Bounds {
                low: random.next(4),
                high: Some(4 + random.next(4)),
            };
            let mut added = octagon.clone();
            assert!(added.add(Constraint::least(1, Bound::from(bounds.low))));
            assert!(added.add(Constraint::most(1, Bound::from(bounds.high.unwrap()))));
            octagon.introduce(1, bounds);
            assert_eq!(octagon, added, "{constraints:?}");
        }
    }

    /// Assigning a fresh variable from another, moved by an interval,
    /// closes as adding the two constraints does.
    #[test]
    fn assigning_closes_as_adding_does() {
        let mut random = Lcg(17);
        for _ in 0..400 {
            let constraints = random_constraints(&mut random, 3, 4);
            let mut octagon = Octagon::top(3);
            for variable in 0..3 {
                octagon.bound(
                    variable,
                    Bounds {
                        low: 0,
                        high: Some(9),
                    },
                );
            }
            for &c in &constraints {
                octagon.assume(c);
            }
            if !octagon.close() {
                continue;
            }
            octagon.forget(2);
            let own = Bounds {
                low: random.next(5),
                high: Some(5 + random.next(10)),
            };
            octagon.introduce(2, own);
            let least = Bound::from(random.next(5)) - 2;
            let most = least + Bound::from(random.next(4));
            let mut added = octagon.clone();
            let feasible = added.add(Constraint::difference(2, 0, most))
                && added.add(Constraint::difference(0, 2, -least));
            assert_eq!(octagon.assign(2, 0, Some(least), Some(most)), feasible);
            if feasible {
                assert_eq!(octagon, added, "{constraints:?} {own:?} {least} {most}");
            }
        }
    }

    /// Narrowing a variable to bounds closes as adding each end does.
    #[test]
    fn narrowing_closes_as_adding_both_ends_does() {
        let mut random = Lcg(23);
        for _ in 0..300 {
            let constraints = random_constraints(&mut random, 3, 4);
            let mut octagon = Octagon::top(3);
            for variable in 0..3 {
                octagon.bound(
                    variable,
                    Bounds {
                        low: 0,
                        high: Some(9),
                    },
                );
            }
            for &constraint in &constraints {
                octagon.assume(constraint);
            }
            if !octagon.close() {
                continue;
            }
            let bounds = Bounds {
                low: random.next(5),
                high: Some(3 + random.next(7)),
            };
            let mut added = octagon.clone();
            let feasible = added.add(Constraint::least(1, Bound::from(bounds.low)))
                && added.add(Constraint::most(1, Bound::from(bounds.high.unwrap())));
            assert_eq!(octagon.narrow(1, bounds), feasible);
            if feasible {
                assert_eq!(octagon, added, "{constraints:?} {bounds:?}");
            }
        }
    }

    /// Forgetting a variable keeps what the others say, closed.
    #[test]
    fn forgetting_keeps_the_rest() {
        let mut octagon = Octagon::top(3);
        octagon.bound(0, Bounds::at(2));
        octagon.assume(Constraint::difference(1, 0, 3));
        octagon.assume(Constraint::difference(2, 1, 0));
        assert!(octagon.close());
        assert_eq!(octagon.bounds(2).high, Some(5));
        octagon.forget(1);
        assert_eq!(octagon.bounds(2).high, Some(5));
        assert_eq!(octagon.bounds(1), Bounds::ANY);
        let mut closed = octagon.clone();
        assert!(closed.close());
        assert_eq!(closed, octagon);
    }
}
