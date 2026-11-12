//! What the comparison an arm sits under says about a value.
//!
//! A class says what a value can be anywhere it is read. Under `v < 4`, `v`
//! can be less than its class says, and a conversion of it to two bits
//! there takes nothing off. A class cannot say that, since the same value
//! is read outside the arm too, so each target would have to find it out
//! for itself; this finds it once.

use super::{Class, Op, Program, RegionId, Relation, ValueId};

/// Which conversions take nothing off, indexed by what each writes.
///
/// A conversion is one where every value reaching it, on the path to it,
/// is already below what it keeps: a target may read its value where it
/// stands. Only a bound that an enclosing `if` puts on the value converted
/// counts, along with what its class already says.
#[must_use]
pub fn conversions_taking_nothing(program: &Program) -> Vec<bool> {
    let mut walk = Walk {
        program,
        constants: vec![None; program.values_count()],
        comparisons: vec![None; program.values_count()],
        bounds: Vec::new(),
        whole: vec![false; program.values_count()],
    };
    for function in program.functions() {
        let Some(body) = function.body() else {
            continue;
        };
        for (op, results) in program.walk_within(body) {
            match *op {
                Op::Constant { value } => walk.constants[results[0].index()] = Some(value),
                Op::Compare {
                    relation,
                    left,
                    right,
                } => walk.comparisons[results[0].index()] = Some((relation, left, right)),
                _ => {}
            }
        }
    }
    for function in program.functions() {
        if let Some(body) = function.body() {
            walk.region(body);
        }
    }
    walk.whole
}

struct Walk<'a> {
    program: &'a Program,
    constants: Vec<Option<u64>>,
    comparisons: Vec<Option<(Relation, ValueId, ValueId)>>,
    /// The greatest each value can be, along the path being walked.
    bounds: Vec<(ValueId, u64)>,
    whole: Vec<bool>,
}

impl Walk<'_> {
    fn region(&mut self, region: RegionId) {
        for (op, results) in self.program.walk(region) {
            match *op {
                Op::Convert { value } => {
                    self.whole[results[0].index()] =
                        self.below(value, self.program.class(results[0]));
                }
                Op::If {
                    condition,
                    then_region,
                    else_region,
                } => {
                    let [then_bound, else_bound] = self.arm_bounds(condition);
                    self.region_under(then_region, then_bound);
                    self.region_under(else_region, else_bound);
                }
                Op::Loop { body, .. } => self.region(body),
                _ => {}
            }
        }
    }

    fn region_under(&mut self, region: RegionId, bound: Option<(ValueId, u64)>) {
        let depth = self.bounds.len();
        self.bounds.extend(bound);
        self.region(region);
        self.bounds.truncate(depth);
    }

    /// What each arm of an `if` on `condition` knows about a value: under
    /// `v < c`, `v` is at most one below `c` where it holds, and under
    /// `c < v`, at most `c` where it does not.
    fn arm_bounds(&self, condition: ValueId) -> [Option<(ValueId, u64)>; 2] {
        let Some((Relation::Less, left, right)) = self.comparisons[condition.index()] else {
            return [None, None];
        };
        let under = self.constants[right.index()]
            .and_then(|limit| limit.checked_sub(1))
            .map(|high| (left, high));
        let over = self.constants[left.index()].map(|limit| (right, limit));
        [under, over]
    }

    /// Whether `value` is below what `class` keeps, on the path walked.
    fn below(&self, value: ValueId, class: Class) -> bool {
        let Some(kept) = class.width() else {
            return false;
        };
        let declared = self
            .program
            .class(value)
            .facts()
            .and_then(|facts| facts.high);
        let high = self
            .bounds
            .iter()
            .filter(|&&(bounded, _)| bounded == value)
            .map(|&(_, high)| high)
            .chain(declared)
            .min();
        high.is_some_and(|high| kept >= 64 || high >> kept == 0)
    }
}
