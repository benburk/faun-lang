//! A loop handed different known values by different callers is copied for
//! each, where knowing one decides something.
//!
//! [`super::invariant`] binds a parameter every caller hands the same known
//! value. Where callers hand different ones, no single definition can hold
//! it, so each value gets a copy of its own, which holds it and goes round
//! with itself:
//!
//! ```text
//! f(k, n) = ... f(k, n') ...        called as f(K, a), f(L, b)
//! f.1(k, n) = k' = K; ... f.1(k', n') ...     called as f.1(K, a)
//! f.2(k, n) = k' = L; ... f.2(k', n') ...     called as f.2(L, b)
//! ```
//!
//! A copy is kept only where folding it decides a match between two or more
//! arms: a way the loop could go that, for that value, it never does. A
//! copy that decides nothing is the same loop twice, which is what a
//! program writing many known strings through one loop must not become.
//! One kept takes over the calls handing its values; one refused is called
//! by nothing, and the sweep takes it away.
//!
//! Only parameters every call of the definition by itself passes on as they
//! came are followed, and constants are compared by identity, as there.

use super::copy::{self, Scope};
use super::{Atom, Body, ConstId, Expr, ExprId, FnId, Local, Program};

/// The most copies made of one definition.
const COPIES: usize = 4;
/// The largest definition copied, in what copying it allocates.
const LARGEST: usize = 4096;

/// Copy each such definition for the values its callers hand it, and send
/// each call handing them to its folded copy.
pub(crate) fn specialize(program: &mut Program) {
    let sites = Sites::of(program);
    for (at, calls) in sites.calls.iter().enumerate() {
        let id = FnId::at(at);
        let Some(body) = program.function(id).body() else {
            continue;
        };
        let passed = &sites.passed[at];
        let mut keys: Vec<Key> = Vec::new();
        for call in calls {
            let key = call.key(passed);
            if !keys.contains(&key) {
                keys.push(key);
            }
        }
        // One value everywhere is the invariant pass's to bind.
        if keys.len() < 2 || super::inline::cost(program, body) > LARGEST {
            continue;
        }
        let before = decided(program, body, program.params(id).len());
        for key in keys.into_iter().filter(Key::known).take(COPIES) {
            let copied = copied(program, id, body, &key);
            super::fold::refold(program, &[copied]);
            let body = program.function(copied).body().expect("a copy has a body");
            if decided(program, body, program.params(copied).len()) <= before {
                continue;
            }
            for call in calls.iter().filter(|call| call.key(passed) == key) {
                let Expr::Call(_, args) = program.expr(call.expr) else {
                    unreachable!("a call site is a call");
                };
                program.write(call.expr, Expr::Call(copied, args));
            }
        }
    }
}

/// The known values a call hands the parameters a definition passes on.
#[derive(Clone, PartialEq, Eq)]
struct Key(Vec<Option<ConstId>>);

impl Key {
    fn known(&self) -> bool {
        self.0.iter().any(Option::is_some)
    }
}

/// One call of a definition from outside it.
struct Call {
    expr: ExprId,
    /// What each argument is, where it is known.
    handed: Vec<Option<ConstId>>,
}

impl Call {
    fn key(&self, passed: &[bool]) -> Key {
        Key(self
            .handed
            .iter()
            .zip(passed)
            .map(|(&value, &passed)| value.filter(|_| passed))
            .collect())
    }
}

/// Every definition's calls from outside it, and which of its parameters it
/// passes on to itself as they came.
struct Sites {
    calls: Vec<Vec<Call>>,
    passed: Vec<Vec<bool>>,
}

impl Sites {
    fn of(program: &mut Program) -> Self {
        let recognised = program.recognised().clone();
        let entry = program.entry();
        let count = program.functions().len();
        let mut sites = Self {
            calls: (0..count).map(|_| Vec::new()).collect(),
            passed: (0..count)
                .map(|at| vec![true; program.params(FnId::at(at)).len()])
                .collect(),
        };
        let reached = entry.map_or_else(
            || vec![true; count],
            |entry| super::sweep::reached(program, entry).0,
        );
        for (at, &reached) in reached.iter().enumerate() {
            let id = FnId::at(at);
            if let Some(body) = program.function(id).body()
                && reached
            {
                let mut known = vec![None; program.params(id).len()];
                sites.body(program, id, body, &mut known);
            }
        }
        // A recognised definition is answered rather than walked, and the
        // entry is called by nothing here.
        for (at, calls) in sites.calls.iter_mut().enumerate() {
            let id = FnId::at(at);
            if recognised.answered(id) || entry == Some(id) {
                calls.clear();
            }
        }
        sites
    }

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
                    let atoms = program.atoms(args);
                    if callee == within {
                        for (at, atom) in atoms.iter().enumerate() {
                            if atom.0.index() != at {
                                self.passed[callee.index()][at] = false;
                            }
                        }
                    } else {
                        self.calls[callee.index()].push(Call {
                            expr,
                            handed: atoms.iter().map(|atom| known[atom.0.index()]).collect(),
                        });
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

/// A copy of `id`, whose body is `body`, holding the values `key` knows and
/// calling itself where `id` called itself.
fn copied(program: &mut Program, id: FnId, body: Body, key: &Key) -> FnId {
    let function = program.function(id);
    let (name, result) = (function.name, function.result);
    let params: Vec<_> = program
        .parameter_names(id)
        .map(str::to_owned)
        .zip(program.params(id).to_vec())
        .collect();
    let named: Vec<_> = params
        .iter()
        .map(|(name, ty)| (name.as_str(), *ty))
        .collect();
    let name = format!("{}.{}", program.name(name), program.functions().len());
    let copy = program.declare_named(&name, &named, result);
    let mut scope = Scope::at(params.len());
    let locals: Vec<_> = key
        .0
        .iter()
        .enumerate()
        .map(|(at, value)| {
            value.map_or_else(
                || Atom(Local::at(at)),
                |value| copy::push(program, &mut scope, Expr::Static(value)),
            )
        })
        .collect();
    let answer = copy::into(program, body, locals, &mut scope, None);
    let body = copy::close(program, scope, answer);
    renamed(program, body, id, copy);
    program.replace_bodies(vec![(copy, body)]);
    copy
}

/// Send the calls of `from` in `body`, which nothing else shares, to `to`.
fn renamed(program: &mut Program, body: Body, from: FnId, to: FnId) {
    let mut pending = vec![body];
    while let Some(body) = pending.pop() {
        for &expr in program
            .bindings(body.bindings)
            .to_vec()
            .iter()
            .chain([&body.tail])
        {
            match program.expr(expr) {
                Expr::Call(callee, args) if callee == from => {
                    program.write(expr, Expr::Call(to, args));
                }
                Expr::Match(_, arms) => pending.extend(program.arms(arms).iter().map(|a| a.body)),
                _ => {}
            }
        }
    }
}

/// How many matches between two or more arms in `body` are on a value
/// known before the program runs.
fn decided(program: &Program, body: Body, params: usize) -> usize {
    let mut known = vec![false; params];
    decided_in(program, body, &mut known)
}

fn decided_in(program: &Program, body: Body, known: &mut Vec<bool>) -> usize {
    let depth = known.len();
    let mut count = 0;
    for &expr in program.bindings(body.bindings).iter().chain([&body.tail]) {
        let value = match program.expr(expr) {
            Expr::Static(_) => true,
            Expr::Atom(atom) => known[atom.0.index()],
            Expr::Con(..) | Expr::Call(..) => false,
            Expr::Match(on, arms) => {
                let arms = program.arms(arms);
                if arms.len() > 1 && known[on.0.index()] {
                    count += 1;
                }
                for arm in arms {
                    let fields = program.fields(arm.ctor).len();
                    known.extend(std::iter::repeat_n(false, fields));
                    count += decided_in(program, arm.body, known);
                    known.truncate(known.len() - fields);
                }
                false
            }
        };
        known.push(value);
    }
    known.truncate(depth);
    count
}
