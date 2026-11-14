//! Pass word-sized natural arguments directly through comparisons.
//! An internal function can use a word parameter if every call supplies an
//! exact word and all its uses compare it with other proven words. Naturals
//! used anywhere else still keep their original arbitrary-precision form.

use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};

use super::rewrite::{self, Declarations, Rebuild};
use super::{Builder, Class, Op, Program, ValueId};
use crate::index::append_range;

/// The scalar or literal that exactly represents a natural.
#[derive(Clone, Copy)]
pub(super) enum Word {
    Scalar(ValueId),
    Constant(u64),
}

/// Every natural a program makes from a scalar or knows as a word-sized
/// constant, by the value that is it.
pub(super) fn word_values(source: &Program, word_bits: u16) -> BTreeMap<ValueId, Word> {
    let mut words = BTreeMap::new();
    for body in source.functions().iter().filter_map(super::Function::body) {
        for (op, results) in source.walk_within(body) {
            let [result] = results[..] else {
                continue;
            };
            if source.class(result) != Class::Natural {
                continue;
            }
            match *op {
                Op::Convert { value }
                    if source.class(value) == Class::Word
                        || source
                            .class(value)
                            .width()
                            .is_some_and(|bits| bits <= word_bits) =>
                {
                    words.insert(result, Word::Scalar(value));
                }
                Op::Constant { value }
                    if u64::BITS - value.leading_zeros() <= u32::from(word_bits) =>
                {
                    words.insert(result, Word::Constant(value));
                }
                _ => {}
            }
        }
    }
    words
}

impl Word {
    fn emit(self, rebuild: &Rebuild, b: &mut Builder) -> ValueId {
        match self {
            Self::Scalar(v) => rebuild.value(v),
            Self::Constant(n) => b.constant(Class::Word, n),
        }
    }
}

/// A parameter may change representation only if every caller agrees.
fn word_params(p: &Program, words: &BTreeMap<ValueId, Word>) -> HashSet<ValueId> {
    let mut candidates = HashSet::new();
    let mut wide = HashSet::new();
    for op in &p.ops {
        let Op::Call { function, args } = *op else {
            continue;
        };
        if function == p.entry() {
            continue;
        }
        let Some(body) = p.function(function).body() else {
            continue;
        };
        for (&param, &arg) in p.values(p.region(body).params).iter().zip(p.values(args)) {
            if p.class(param) == Class::Natural {
                if words.contains_key(&arg) {
                    candidates.insert(param);
                } else {
                    wide.insert(param);
                }
            }
        }
    }
    candidates.retain(|v| !wide.contains(v));
    candidates
}

/// A comparison can change when both operands have word representations.
/// If both are parameters they must change together: propagate an escape
/// through those comparisons so no comparison ever mixes representations.
fn compared_params(p: &Program, words: &BTreeMap<ValueId, Word>) -> HashSet<ValueId> {
    let mut params = word_params(p, words);
    if params.is_empty() {
        return params;
    }
    let mut peers = HashMap::<ValueId, Vec<ValueId>>::new();
    let mut rejected = VecDeque::new();
    let mut compared = HashSet::new();
    for r in p.regions.ids() {
        for op in p.ops(r) {
            if let Op::Compare { left, right, .. } = *op {
                for (param, other) in [(left, right), (right, left)] {
                    if !params.contains(&param) {
                        continue;
                    }
                    compared.insert(param);
                    if params.contains(&other) {
                        peers.entry(other).or_default().push(param);
                    } else if !words.contains_key(&other) {
                        rejected.push_back(param);
                    }
                }
            } else {
                rejected.extend(p.operands(op).filter(|v| params.contains(v)));
            }
        }
        rejected.extend(p.outgoing(r).iter().filter(|v| params.contains(v)));
    }
    while let Some(v) = rejected.pop_front() {
        if params.remove(&v)
            && let Some(others) = peers.remove(&v)
        {
            rejected.extend(others);
        }
    }
    params.retain(|v| compared.contains(v));
    params
}

pub(crate) fn lower(p: &Program, bits: u16) -> Option<Program> {
    if !p.signature.contains(&Class::Natural)
        || !p
            .ops
            .iter()
            .any(|op| matches!(op, Op::Compare {left, ..} if p.class(*left) == Class::Natural))
    {
        return None;
    }
    let words = word_values(p, bits);
    let params = compared_params(p, &words);
    if params.is_empty() {
        return None;
    }
    let mut declared = Declarations::of(p);
    for (id, f) in p.functions.iter_enumerated() {
        let Some(body) = f.body() else { continue };
        let values = p.values(p.region(body).params);
        if values.iter().any(|v| params.contains(v)) {
            let classes: Vec<_> = values
                .iter()
                .map(|&v| {
                    if params.contains(&v) {
                        Class::Word
                    } else {
                        p.class(v)
                    }
                })
                .collect();
            declared.functions[id].params = append_range(&mut declared.signature, &classes);
        }
    }
    let mut pass = Lower { words, params };
    let lowered = rewrite::rebuild_declared(p, declared, &mut pass);
    // Drop conversions whose last reader now takes their scalar source.
    Some(super::prune::prune(&lowered))
}

struct Lower {
    words: BTreeMap<ValueId, Word>,
    params: HashSet<ValueId>,
}

impl Lower {
    fn value(&self, r: &Rebuild, b: &mut Builder, v: ValueId) -> ValueId {
        self.words
            .get(&v)
            .map_or_else(|| r.value(v), |w| w.emit(r, b))
    }
}

impl rewrite::Pass for Lower {
    fn op(&mut self, r: &Rebuild, b: &mut Builder, op: Op, results: &[ValueId]) -> bool {
        match op {
            Op::Compare {
                relation,
                left,
                right,
            } if self.params.contains(&left) || self.params.contains(&right) => {
                let left = self.value(r, b, left);
                let right = self.value(r, b, right);
                r.stands_for(results[0], b.compare(relation, left, right));
                true
            }
            Op::Call { function, args } => {
                let p = r.source();
                let Some(body) = p.function(function).body() else {
                    return false;
                };
                let params = p.values(p.region(body).params);
                if !params.iter().any(|v| self.params.contains(v)) {
                    return false;
                }
                let args: Vec<_> = params
                    .iter()
                    .zip(p.values(args))
                    .map(|(param, &v)| {
                        if self.params.contains(param) {
                            self.words[&v].emit(r, b)
                        } else {
                            r.value(v)
                        }
                    })
                    .collect();
                for (&old, new) in results.iter().zip(b.call(function, &args)) {
                    r.stands_for(old, new);
                }
                true
            }
            _ => false,
        }
    }
}
