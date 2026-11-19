//! Parameters nothing reads, no longer worked out.
//!
//! A definition calling itself may hand on a parameter that nothing else
//! reads: a walk over a range fused with a fold keeps the index it counts,
//! though the step it folds with ignores it, and works out the next one at
//! every step for the call that hands it on.
//!
//! ```text
//! f(i, n, acc) = match n { Zero -> acc; Succ(m) -> i' = i + 1; f(i', m, step(acc)) }
//! ```
//!
//! A parameter is read where its value reaches the answer, a match, a call
//! with an effect, or a parameter of another definition that is read;
//! handing it to a parameter nothing reads, or working out from it a value
//! that only goes there, is not reading it. Every parameter of a definition
//! without a body, of a recognized one, and of the entry is read. The rest
//! start unread, and a definition's are read once its body reads them, until
//! nothing more is: a parameter only handed round to itself stays unread.
//!
//! A call handing a value to a parameter nothing reads hands it the caller's
//! own parameter of that type in its place, which is the same one where a
//! definition calls itself:
//!
//! ```text
//! f(i, n, acc) = match n { Zero -> acc; Succ(m) -> f(i, m, step(acc)) }
//! ```
//!
//! Cleanup then leaves out the work that went only there, and lowering, which
//! takes a parameter only where it is read, gives the definition none.
//! Signatures stay as they were, so no caller changes otherwise. Whatever a
//! parameter nothing reads is handed is pure work nothing needs, which a pass
//! may leave out even where it would not have come back.

use rustc_hash::FxHashMap as HashMap;

use super::copy::{self, Scope};
use super::{Atom, Body, Expr, ExprId, FnId, Local, Program};

/// Hand each parameter nothing reads its caller's own in place of the value
/// worked out for it.
pub(crate) fn unread(program: &mut Program) {
    let read = read(program);
    let mut bodies = Vec::new();
    for at in 0..program.functions().len() {
        let id = FnId::at(at);
        let Some(body) = program.function(id).body() else {
            continue;
        };
        if !super::walk::within(program, body).any(|expr| replaces(program, &read, id, expr)) {
            continue;
        }
        let params = program.params(id).len();
        let locals = (0..params).map(|at| Atom(Local::at(at))).collect();
        let mut edit = |program: &mut Program, _: &mut Scope, _: ExprId, expr: Expr| match expr {
            Expr::Call(callee, args) => {
                let handed = handed(program, &read, id, callee, program.atoms(args));
                Expr::Call(callee, program.terms.hold_atoms(handed.into_iter()))
            }
            other => other,
        };
        bodies.push((
            id,
            copy::body(program, body, locals, params, Some(&mut edit)),
        ));
    }
    program.replace_bodies(bodies);
}

/// What a call from `within` hands `callee` in place of `args`.
fn handed(
    program: &Program,
    read: &[Vec<bool>],
    within: FnId,
    callee: FnId,
    args: &[Atom],
) -> Vec<Atom> {
    args.iter()
        .enumerate()
        .map(|(at, &atom)| replacement(program, read, within, callee, at).unwrap_or(atom))
        .collect()
}

/// Whether `expr`, in `within`'s body, is a call handing a parameter nothing
/// reads something other than what it would be handed in its place.
fn replaces(program: &Program, read: &[Vec<bool>], within: FnId, expr: ExprId) -> bool {
    let Expr::Call(callee, args) = program.expr(expr) else {
        return false;
    };
    program.atoms(args).iter().enumerate().any(|(at, &atom)| {
        replacement(program, read, within, callee, at).is_some_and(|by| by != atom)
    })
}

/// What a call from `within` hands `callee`'s parameter `at` where nothing
/// reads it: the caller's parameter in the same place where it calls itself,
/// and otherwise its first of that type, if it has one.
fn replacement(
    program: &Program,
    read: &[Vec<bool>],
    within: FnId,
    callee: FnId,
    at: usize,
) -> Option<Atom> {
    if read[callee.index()][at] {
        return None;
    }
    if callee == within {
        return Some(Atom(Local::at(at)));
    }
    let ty = program.params(callee)[at];
    program
        .params(within)
        .iter()
        .position(|&own| own == ty)
        .map(|own| Atom(Local::at(own)))
}

/// Which parameters of each definition are read, by definition.
fn read(program: &mut Program) -> Vec<Vec<bool>> {
    let recognised = program.recognised().clone();
    let program = &*program;
    let entry = program.entry();
    let mut reader = Reader {
        program,
        pure: super::calls::pure(program, &recognised),
        read: program
            .functions()
            .iter()
            .enumerate()
            .map(|(at, function)| {
                let id = FnId::at(at);
                let given = function.body().is_none() || recognised.answered(id) || id == entry;
                vec![given; program.params(id).len()]
            })
            .collect(),
        inert: HashMap::default(),
    };
    loop {
        let mut changed = false;
        for at in 0..program.functions().len() {
            if reader.read[at].iter().all(|&read| read) {
                continue;
            }
            let Some(body) = program.function(FnId::at(at)).body() else {
                continue;
            };
            let mut locals = vec![false; reader.read[at].len()];
            reader.body(body, true, &mut locals);
            for (read, found) in reader.read[at].iter_mut().zip(locals) {
                if found && !*read {
                    *read = true;
                    changed = true;
                }
            }
        }
        if !changed {
            return reader.read;
        }
    }
}

struct Reader<'a> {
    program: &'a Program,
    /// Indexed by definition: see [`super::calls::pure`].
    pure: Vec<bool>,
    /// Indexed by definition, then parameter: whether it is read so far.
    read: Vec<Vec<bool>>,
    /// Which matches may go unevaluated where nothing reads them.
    inert: HashMap<ExprId, bool>,
}

impl Reader<'_> {
    /// Mark the locals in scope, `locals`, that `body` reads, where its
    /// answer is `needed`.
    fn body(&mut self, body: Body, needed: bool, locals: &mut Vec<bool>) {
        let base = locals.len();
        let bindings = self.program.bindings(body.bindings);
        locals.resize(base + bindings.len(), false);
        self.expr(body.tail, needed, locals);
        for &id in bindings.iter().rev() {
            let needed = locals.pop().expect("one local per binding");
            self.expr(id, needed, locals);
        }
    }

    fn expr(&mut self, id: ExprId, needed: bool, locals: &mut Vec<bool>) {
        let program = self.program;
        match program.expr(id) {
            Expr::Atom(atom) => {
                if needed {
                    locals[atom.0.index()] = true;
                }
            }
            Expr::Static(_) => {}
            Expr::Con(_, fields) => {
                if needed {
                    for atom in program.atoms(fields) {
                        locals[atom.0.index()] = true;
                    }
                }
            }
            Expr::Call(callee, args) => {
                if needed || !self.pure[callee.index()] {
                    for (atom, &read) in program.atoms(args).iter().zip(&self.read[callee.index()])
                    {
                        if read {
                            locals[atom.0.index()] = true;
                        }
                    }
                }
            }
            Expr::Match(on, arms) => {
                if needed || !self.inert(id) {
                    locals[on.0.index()] = true;
                    for arm in program.arms(arms) {
                        let fields = program.fields(arm.ctor).len();
                        let scope = locals.len();
                        locals.resize(scope + fields, false);
                        self.body(arm.body, needed, locals);
                        locals.truncate(scope);
                    }
                }
            }
        }
    }

    /// Whether `id` may go unevaluated where nothing reads it, as cleanup
    /// decides.
    fn inert(&mut self, id: ExprId) -> bool {
        if let Some(&known) = self.inert.get(&id) {
            return known;
        }
        let program = self.program;
        let inert = match program.expr(id) {
            Expr::Call(called, _) => self.pure[called.index()],
            Expr::Match(_, arms) => program.arms(arms).iter().all(|arm| {
                program
                    .bindings(arm.body.bindings)
                    .iter()
                    .chain([&arm.body.tail])
                    .all(|&inner| self.inert(inner))
            }),
            Expr::Atom(..) | Expr::Static(..) | Expr::Con(..) => true,
        };
        self.inert.insert(id, inert);
        inert
    }
}
