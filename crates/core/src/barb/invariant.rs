//! A parameter every caller hands the same known value is that value.
//!
//! A definition calling itself goes round with some of its parameters
//! changing and others passed on as they came. Where each of those passed on
//! is a value known before the program runs, the same one at every call from
//! outside, the definition may as well hold it itself:
//!
//! ```text
//! f(k, n) = ... f(k, n') ...        called as f(K, a), f(K, b)
//! f(k, n) = k' = K; ... f(k', n') ...
//! ```
//!
//! Everything reading it inside then reads something known: its length
//! folds, and a tier below can hand out known bytes where they lie rather
//! than build them. The parameter stays, read by nothing, so no caller or
//! signature changes; a tier holding only what is read holds none of it.
//!
//! Only known values are followed, and one call from outside with anything
//! else leaves the parameter as it is. Constants are compared by identity,
//! so two interned apart count as two.

use super::copy::{self, Scope};
use super::{Atom, Body, ConstId, Expr, FnId, Local, Program};

/// Give every such definition the values its callers all hand it.
pub(crate) fn invariant(program: &mut Program) {
    let found = Handed::of(program);
    let mut bodies = Vec::new();
    for (at, handed) in found.params.iter().enumerate() {
        let id = FnId::at(at);
        let Some(body) = program.function(id).body() else {
            continue;
        };
        if !handed.iter().any(|param| matches!(param, Param::Known(_))) {
            continue;
        }
        bodies.push((id, held(program, body, handed)));
    }
    program.replace_bodies(bodies);
}

/// What a parameter is at every call seen so far.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Param {
    /// No call from outside has been seen.
    Unseen,
    /// Every call from outside hands this, and every call from inside
    /// passes the parameter on.
    Known(ConstId),
    /// Something else, somewhere.
    Varies,
}

impl Param {
    fn meet(self, other: Self) -> Self {
        match (self, other) {
            (Self::Unseen, other) | (other, Self::Unseen) => other,
            (Self::Known(a), Self::Known(b)) if a == b => self,
            _ => Self::Varies,
        }
    }
}

struct Handed {
    params: Vec<Vec<Param>>,
}

impl Handed {
    fn of(program: &mut Program) -> Self {
        let recognised = program.recognised().clone();
        let entry = program.entry();
        let params = (0..program.functions().len())
            .map(|at| {
                let id = FnId::at(at);
                // A recognised definition is answered rather than walked, and
                // the entry is called by nothing here.
                let fixed = recognised.answered(id)
                    || entry == Some(id)
                    || program.function(id).body().is_none();
                let param = if fixed { Param::Varies } else { Param::Unseen };
                vec![param; program.params(id).len()]
            })
            .collect();
        // Only a caller the entry reaches is ever a caller: one it does not
        // is swept away, whatever it hands.
        let reached = entry.map_or_else(
            || vec![true; program.functions().len()],
            |entry| super::sweep::reached(program, entry).0,
        );
        let mut handed = Self { params };
        for (at, &reached) in reached.iter().enumerate() {
            let id = FnId::at(at);
            if !reached {
                continue;
            }
            if let Some(body) = program.function(id).body() {
                let mut known = vec![None; program.params(id).len()];
                handed.body(program, id, body, &mut known);
            }
        }
        handed
    }

    /// Read the calls in `body` of `within`, where `known` says which
    /// locals so far hold a known value.
    fn body(
        &mut self,
        program: &Program,
        within: FnId,
        body: Body,
        known: &mut Vec<Option<ConstId>>,
    ) {
        let depth = known.len();
        for &expr in program.bindings(body.bindings).iter().chain([&body.tail]) {
            let value = match program.expr(expr) {
                Expr::Static(value) => Some(value),
                Expr::Atom(atom) => known[atom.0.index()],
                Expr::Con(..) => None,
                Expr::Call(callee, args) => {
                    let handed = &mut self.params[callee.index()];
                    for (at, atom) in program.atoms(args).iter().enumerate() {
                        let seen = if callee == within {
                            // Passed on as it came, it says nothing new.
                            if atom.0.index() == at {
                                continue;
                            }
                            Param::Varies
                        } else {
                            known[atom.0.index()].map_or(Param::Varies, Param::Known)
                        };
                        handed[at] = handed[at].meet(seen);
                    }
                    None
                }
                Expr::Match(_, arms) => {
                    for arm in program.arms(arms) {
                        let fields = program.fields(arm.ctor).len();
                        known.extend(std::iter::repeat_n(None, fields));
                        self.body(program, within, arm.body, known);
                        known.truncate(known.len() - fields);
                    }
                    None
                }
            };
            known.push(value);
        }
        known.truncate(depth);
    }
}

/// `body` with each parameter every caller hands a known value read as
/// that value, bound first.
fn held(program: &mut Program, body: Body, handed: &[Param]) -> Body {
    let arity = handed.len();
    let mut scope = Scope::at(arity);
    let locals: Vec<_> = handed
        .iter()
        .enumerate()
        .map(|(at, param)| match *param {
            Param::Known(value) => copy::push(program, &mut scope, Expr::Static(value)),
            Param::Unseen | Param::Varies => Atom(Local::at(at)),
        })
        .collect();
    let answer = copy::into(program, body, locals, &mut scope, None);
    copy::close(program, scope, answer)
}
