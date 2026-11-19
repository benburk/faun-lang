//! A counted walk handed numbers the target holds in half a word, split
//! from the same walk handed any.
//!
//! A walk taking a count down to nought while it counts another number up,
//! or counting a number up while it is below one it keeps, goes round as
//! often as its count says:
//!
//! ```text
//! w(i, n, total) = match n             w(i, n, total) = match i < n
//!   zero => total                        false => total
//!   succ(m) => w(i + 1, m, ...)          true => w(i + 1, n, ...)
//! ```
//!
//! What it counts up is no more than where it started and its count
//! together, which range analysis works out, so where both are small the
//! numbers worked out of them are small too. A walk over a list, as
//! `List.range(n).map(f)` was before fusing made it one walk, had the
//! list's length bound its count, since no list is longer than a target
//! can hold. Fused, the list is gone, and with it the bound: what the walk
//! counts up, and everything worked out of it, is a natural of any size.
//! On the 6502 a product of two of them past half a word is a natural on
//! the heap, made and freed every step.
//!
//! So every call of such a walk from outside it asks whether each number
//! it hands that the walk counts with is at most `most`, and calls a copy
//! of the walk where every one is: the copy is handed nothing larger, so
//! its numbers are as narrow as analysis can then make them. Where one is
//! not, the walk itself runs, and takes any count. A call handing a known
//! number asks nothing of it, and one handing a known number past `most`
//! calls the walk as it did. Where analysis finds a question answers yes
//! however the program runs, lowering takes only that arm, so a walk whose
//! numbers were already that narrow is the copy alone.
//!
//! Only an innermost walk is split, one calling no other walk: it is where
//! the steps are. And this trades work for time, a comparison a call for
//! narrower numbers every step, against a bound that is the target's, so
//! the tier lowering a program for a target asks for it.

use super::copy::{self, Scope};
use super::facts::Recognised;
use super::{
    Arm, Atom, Body, ConstId, ConstantView, CtorId, Expr, ExprId, FnId, Local, Operation, Program,
    TypeId, TypeShape, type_shape, walk,
};

/// `program` with each counted walk split, where it has one.
///
/// Every call of a counted walk from outside it asks whether the numbers
/// it counts with are at most `most`, and calls a copy of the walk where
/// they are; nothing comes back where there is no such walk.
#[must_use]
pub fn counted(program: &Program, most: u64, lists: bool) -> Option<Program> {
    let below = most.checked_add(1)?;
    let recognised = program.recognition();
    let found: Vec<(FnId, Vec<usize>)> = (0..program.functions().len())
        .map(FnId::at)
        .filter(|&id| id != program.entry())
        .filter_map(|id| Some((id, guarded(program, &recognised, id, lists)?)))
        .collect();
    if found.is_empty() {
        return None;
    }
    let mut split = program.clone();
    let walks: Vec<Walk> = found
        .into_iter()
        .filter_map(|(id, positions)| declared(&mut split, &recognised, id, &positions, below))
        .collect();
    let bodies = asking(&mut split, &recognised, &walks, most);
    if bodies.is_empty() {
        return None;
    }
    split.replace_bodies(bodies);
    let copies = walks
        .iter()
        .flat_map(|walk| [copied(&mut split, walk), asker(&mut split, walk)])
        .collect();
    split.replace_bodies(copies);
    debug_assert!(super::validate(&split).is_ok(), "a split program validates");
    Some(split)
}

/// The copy of walk `id` and the definition asking for it, declared, where
/// every number at `positions` can be asked whether it is below `below`.
fn declared(
    split: &mut Program,
    recognised: &Recognised,
    id: FnId,
    positions: &[usize],
    below: u64,
) -> Option<Walk> {
    let tests: Vec<Test> = positions
        .iter()
        .map(|&at| {
            let ty = split.params(id)[at];
            let less = less_than(split, recognised, ty)?;
            let bound = split.intern_number(ty, below).ok()?;
            Some(Test { at, less, bound })
        })
        .collect::<Option<_>>()?;
    let name = format!("{}.counted", split.name(split.function(id).name));
    let params = split.params(id).to_vec();
    let result = split.function(id).result;
    let copy = split.declare(&name, &params, result);
    let asker = split.declare(&format!("{name}.asked"), &params, result);
    Some(Walk {
        id,
        copy,
        asker,
        tests,
    })
}

/// Every body calling a walk from outside it, each call sent to the copy,
/// to the definition asking for it, or left. The bodies are all read
/// before any is replaced.
fn asking(
    split: &mut Program,
    recognised: &Recognised,
    walks: &[Walk],
    most: u64,
) -> Vec<(FnId, Body)> {
    let mut bodies = Vec::new();
    for at in 0..split.functions().len() {
        let id = FnId::at(at);
        let Some(body) = split.function(id).body() else {
            continue;
        };
        if recognised.answered(id) || !calls_a_walk(split, body, id, walks) {
            continue;
        }
        let arity = split.params(id).len();
        let known = known_arguments(split, body, arity);
        let locals = (0..arity).map(|at| Atom(Local::at(at))).collect();
        let mut edit = |program: &mut Program, _: &mut Scope, from: ExprId, expr: Expr| {
            let Expr::Call(callee, args) = expr else {
                return expr;
            };
            let Some(walk) = walks.iter().find(|walk| walk.id == callee && callee != id) else {
                return expr;
            };
            let handed = known
                .iter()
                .find(|(call, _)| *call == from)
                .map(|(_, known)| known.as_slice());
            match asked(program, walk, handed, most) {
                Some(true) => Expr::Call(walk.asker, args),
                Some(false) => Expr::Call(walk.copy, args),
                None => expr,
            }
        };
        bodies.push((id, copy::body(split, body, locals, arity, Some(&mut edit))));
    }
    bodies
}

/// The copy of a walk: its body, going round on itself.
fn copied(split: &mut Program, walk: &Walk) -> (FnId, Body) {
    let arity = split.params(walk.id).len();
    let locals = (0..arity).map(|at| Atom(Local::at(at))).collect();
    let mut edit = |_: &mut Program, _: &mut Scope, _: ExprId, expr: Expr| match expr {
        Expr::Call(callee, args) if callee == walk.id => Expr::Call(walk.copy, args),
        Expr::Call(..) | Expr::Atom(_) | Expr::Con(..) | Expr::Static(_) | Expr::Match(..) => expr,
    };
    let body = split.function(walk.id).body().expect("a walk has a body");
    (
        walk.copy,
        copy::body(split, body, locals, arity, Some(&mut edit)),
    )
}

/// The definition asking of what it is handed, and calling the copy or
/// the walk.
fn asker(split: &mut Program, walk: &Walk) -> (FnId, Body) {
    let arity = split.params(walk.id).len();
    let params: Vec<Atom> = (0..arity).map(|at| Atom(Local::at(at))).collect();
    let tests: Vec<&Test> = walk.tests.iter().collect();
    let mut scope = Scope::at(arity);
    let answer = ask(split, &mut scope, walk, &tests, &params);
    let answer = copy::push(split, &mut scope, answer);
    (walk.asker, copy::close(split, scope, answer))
}

/// A walk split, its copy, and what a call of it asks.
struct Walk {
    id: FnId,
    copy: FnId,
    /// What a call asking of what it hands calls: a definition asking, so
    /// that the copy is handed its own parameters, which it reads as narrow
    /// as they are rather than working out again what made them.
    asker: FnId,
    tests: Vec<Test>,
}

/// One number a call hands a walk, asked whether it is below `bound`.
struct Test {
    at: usize,
    less: (FnId, CtorId, CtorId),
    bound: ConstId,
}

/// Whether a call must ask, handing what `known` says of each argument,
/// where it may call the copy at all: not where every number is known and
/// at most `most`, and no call where one is known and past it.
fn asked(
    program: &Program,
    walk: &Walk,
    known: Option<&[Option<ConstId>]>,
    most: u64,
) -> Option<bool> {
    let mut asked = false;
    for test in &walk.tests {
        match known.and_then(|known| known[test.at]) {
            Some(value) => {
                let ConstantView::Natural(natural) = program.constant(value).view() else {
                    return None;
                };
                if !natural.try_u64().is_ok_and(|value| value <= most) {
                    return None;
                }
            }
            None => asked = true,
        }
    }
    Some(asked)
}

/// A call of `walk` with `args` that calls its copy where every test asked
/// holds, and the walk where one does not.
fn ask(
    program: &mut Program,
    scope: &mut Scope,
    walk: &Walk,
    asked: &[&Test],
    args: &[Atom],
) -> Expr {
    let held = program.terms.hold_atoms(args.iter().copied());
    let Some((test, rest)) = asked.split_first() else {
        return Expr::Call(walk.copy, held);
    };
    let bound = copy::push(program, scope, Expr::Static(test.bound));
    let (less, yes, no) = test.less;
    let compared = program.terms.hold_atoms([args[test.at], bound].into_iter());
    let below = copy::push(program, scope, Expr::Call(less, compared));
    // The arms bind nothing, and begin where the match is bound.
    let mut inner = Scope::at(scope.level);
    let answer = ask(program, &mut inner, walk, rest, args);
    let answer = copy::push(program, &mut inner, answer);
    let yes_body = copy::close(program, inner, answer);
    let tail = program.terms.push(Expr::Call(walk.id, held));
    let no_body = program.terms.hold_body(&[], tail);
    let mut arms = [
        Arm {
            ctor: yes,
            body: yes_body,
        },
        Arm {
            ctor: no,
            body: no_body,
        },
    ];
    arms.sort_by_key(|arm| program.tag(arm.ctor));
    let arms = program.terms.hold_arms(&arms);
    Expr::Match(below, arms)
}

/// Whether `body`, of `id`, calls any walk but itself.
fn calls_a_walk(program: &Program, body: Body, id: FnId, walks: &[Walk]) -> bool {
    walk::within(program, body).any(|expr| {
        matches!(program.expr(expr), Expr::Call(callee, _)
            if callee != id && walks.iter().any(|walk| walk.id == callee))
    })
}

/// Each call in `body`, with each of its arguments that is a known value:
/// what a body of `arity` parameters binds it to.
fn known_arguments(
    program: &Program,
    body: Body,
    arity: usize,
) -> Vec<(ExprId, Vec<Option<ConstId>>)> {
    let mut found = Vec::new();
    scoped(program, body, &mut vec![None; arity], &mut |expr, bound| {
        if let Expr::Call(_, args) = program.expr(expr) {
            let known = program
                .atoms(args)
                .iter()
                .map(|atom| match bound.get(atom.0.index()) {
                    Some(Some(binding)) => match program.expr(*binding) {
                        Expr::Static(value) => Some(value),
                        _ => None,
                    },
                    _ => None,
                })
                .collect();
            found.push((expr, known));
        }
    });
    found
}

/// Visit every binding and tail in `body`, however deep, with what bound
/// each level in scope there: the expression, or nothing for a parameter or
/// a field.
pub(super) fn scoped(
    program: &Program,
    body: Body,
    bound: &mut Vec<Option<ExprId>>,
    visit: &mut impl FnMut(ExprId, &[Option<ExprId>]),
) {
    let depth = bound.len();
    for &expr in program.bindings(body.bindings).iter().chain([&body.tail]) {
        visit(expr, bound);
        if let Expr::Match(_, arms) = program.expr(expr) {
            for arm in program.arms(arms) {
                let fields = program.fields(arm.ctor).len();
                bound.extend(std::iter::repeat_n(None, fields));
                scoped(program, arm.body, bound, visit);
                bound.truncate(bound.len() - fields);
            }
        }
        bound.push(Some(expr));
    }
    bound.truncate(depth);
}

/// The definition recognized as less-than over two numbers of `ty`, and
/// its two answers.
fn less_than(
    program: &Program,
    recognised: &Recognised,
    ty: TypeId,
) -> Option<(FnId, CtorId, CtorId)> {
    (0..program.functions().len()).map(FnId::at).find_map(|id| {
        let Some(Operation::LessThan { yes, no }) = recognised.operations[id.index()] else {
            return None;
        };
        (program.params(id) == [ty, ty]).then_some((id, yes, no))
    })
}

/// How a walk hands a number on to itself.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Role {
    /// As it came.
    Kept,
    /// One less, as the field of the step its top match took apart.
    Down,
    /// A constant more.
    Up,
}

/// What a walk hands itself in one place.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum Handed {
    /// The local at this level.
    Local(usize),
    /// The parameter at this level, plus a known number.
    Step(usize),
    Other,
}

/// Which numbers a call of `id` must hand at most the bound for its copy
/// to count narrowly, where `id` is an innermost counted walk.
fn guarded(
    program: &Program,
    recognised: &Recognised,
    id: FnId,
    lists: bool,
) -> Option<Vec<usize>> {
    if recognised.answered(id) {
        return None;
    }
    let body = program.function(id).body()?;
    if walks_within(program, recognised, id, body) {
        return None;
    }
    let params = program.params(id);
    let arity = params.len();
    let calls = self_calls(program, recognised, id, body);
    if calls.is_empty() {
        return None;
    }
    // A walk reading a sequence it keeps counts positions in it, which
    // the sequence's length bounds where it is read, and the copy would
    // copy all it does with it.
    // And where `lists` is false, a walk holding a list at all is left: its
    // count is bounded by that list's length, and narrower than that is
    // worth less than its copy.
    let keeps_a_sequence = (0..arity).any(|at| {
        matches!(type_shape(program, params[at]), TypeShape::Sequence { .. })
            && (!lists || calls.iter().all(|call| call[at] == Handed::Local(at)))
    });
    if keeps_a_sequence {
        return None;
    }
    let down = counted_down(program, id, body, &calls);
    let roles = roles(program, id, down, &calls);
    if !roles.contains(&Some(Role::Up)) {
        return None;
    }
    let mut guarded: Vec<usize> = (0..arity)
        .filter(|&at| matches!(roles[at], Some(Role::Up | Role::Down)))
        .collect();
    if down.is_none() {
        // Without a count, a number counted up is compared with one kept.
        let kept = compared(program, recognised, body, arity, &roles);
        if kept.is_empty() {
            return None;
        }
        guarded.extend(kept);
        guarded.sort_unstable();
        guarded.dedup();
    }
    Some(guarded)
}

/// Whether `body`, of `id`, calls another walk: only an innermost walk
/// goes round often enough for its own numbers to tell, and one calling
/// another spends its steps in that one.
fn walks_within(program: &Program, recognised: &Recognised, id: FnId, body: Body) -> bool {
    walk::within(program, body).any(|expr| {
        matches!(program.expr(expr), Expr::Call(callee, _) if callee != id
            && !recognised.answered(callee)
            && program.function(callee).body().is_some_and(|inner| walk::calls(program, inner, callee)))
    })
}

/// Each call `id`'s body makes of itself, each argument as it hands it on.
pub(super) fn self_calls(
    program: &Program,
    recognised: &Recognised,
    id: FnId,
    body: Body,
) -> Vec<Vec<Handed>> {
    let mut calls = Vec::new();
    let arity = program.params(id).len();
    scoped(program, body, &mut vec![None; arity], &mut |expr, bound| {
        if let Expr::Call(callee, args) = program.expr(expr)
            && callee == id
        {
            let handed = program
                .atoms(args)
                .iter()
                .map(|&atom| handed(program, recognised, bound, atom))
                .collect();
            calls.push(handed);
        }
    });
    calls
}

/// The count `id`'s top match takes down, where it has one: a number each
/// call of itself hands one less, and none where it is nought.
fn counted_down(program: &Program, id: FnId, body: Body, calls: &[Vec<Handed>]) -> Option<usize> {
    let params = program.params(id);
    let (on, arms) = walk::top_match(program, body)?;
    let TypeShape::Natural { empty, push, .. } = type_shape(program, params[on]) else {
        return None;
    };
    let [zero, _] = walk::split_arms(program, arms, empty, push)?;
    let again = walk::calls(program, zero.body, id);
    let stepped = calls
        .iter()
        .all(|call| call[on] == Handed::Local(params.len()));
    (!again && stepped).then_some(on)
}

/// How `id` hands each of its numbers on to itself.
fn roles(
    program: &Program,
    id: FnId,
    down: Option<usize>,
    calls: &[Vec<Handed>],
) -> Vec<Option<Role>> {
    let params = program.params(id);
    (0..params.len())
        .map(|at| {
            if !matches!(type_shape(program, params[at]), TypeShape::Natural { .. }) {
                None
            } else if down == Some(at) {
                Some(Role::Down)
            } else if calls.iter().all(|call| call[at] == Handed::Local(at)) {
                Some(Role::Kept)
            } else if calls.iter().all(|call| call[at] == Handed::Step(at)) {
                Some(Role::Up)
            } else {
                None
            }
        })
        .collect()
}

/// What `atom` is, as a walk hands it on.
fn handed(
    program: &Program,
    recognised: &Recognised,
    bound: &[Option<ExprId>],
    atom: Atom,
) -> Handed {
    let level = atom.0.index();
    let Some(Some(expr)) = bound.get(level) else {
        return Handed::Local(level);
    };
    let Expr::Call(callee, args) = program.expr(*expr) else {
        return Handed::Other;
    };
    if recognised.operations[callee.index()] != Some(Operation::Add) {
        return Handed::Other;
    }
    let constant = |atom: Atom| {
        matches!(bound.get(atom.0.index()), Some(Some(expr))
            if matches!(program.expr(*expr), Expr::Static(_)))
    };
    // A level nothing bound is a parameter or a field; only a parameter's
    // level is ever compared with what a parameter is handed.
    let param =
        |atom: Atom| matches!(bound.get(atom.0.index()), Some(None)).then_some(atom.0.index());
    match *program.atoms(args) {
        [a, b] if constant(b) => param(a).map_or(Handed::Other, Handed::Step),
        [a, b] if constant(a) => param(b).map_or(Handed::Other, Handed::Step),
        _ => Handed::Other,
    }
}

/// The numbers a walk keeps that it compares with one it counts up.
fn compared(
    program: &Program,
    recognised: &Recognised,
    body: Body,
    arity: usize,
    roles: &[Option<Role>],
) -> Vec<usize> {
    let mut kept = Vec::new();
    for expr in walk::within(program, body) {
        let Expr::Call(callee, args) = program.expr(expr) else {
            continue;
        };
        if !matches!(
            recognised.operations[callee.index()],
            Some(Operation::LessThan { .. })
        ) {
            continue;
        }
        let &[a, b] = program.atoms(args) else {
            continue;
        };
        let (a, b) = (a.0.index(), b.0.index());
        if a >= arity || b >= arity {
            continue;
        }
        match (roles[a], roles[b]) {
            (Some(Role::Up), Some(Role::Kept)) => kept.push(b),
            (Some(Role::Kept), Some(Role::Up)) => kept.push(a),
            _ => {}
        }
    }
    kept
}

#[cfg(test)]
mod tests {
    use super::super::fixture::{Library, enter};
    use super::super::{Expr, FnId, Program, validate, walk};
    use super::counted;

    /// `w(i, n, total)`, taking `n` down while it counts `i` up, adding
    /// `i * 7919` each step; and three callers handing it a count from
    /// outside, a small known one and one past the bound.
    fn program(most: u64) -> (Program, FnId, [FnId; 3]) {
        let mut lib = Library::new();
        let (one, scale) = (lib.number(1), lib.number(7919));
        let (nought, small, large) = (lib.number(0), lib.number(5), lib.number(most + 1));
        let nat = lib.nat;
        let p = &mut lib.program;
        let w = p.declare("w", &[nat, nat, nat], nat);
        p.define(w, |b, args| {
            let [i, n, total] = [args[0], args[1], args[2]];
            b.match_(n, nat, |b, ctor, fields| {
                if ctor == lib.zero {
                    return total;
                }
                let one = b.known(one);
                let next = b.call(lib.add, &[i, one]);
                let scale = b.known(scale);
                let step = b.call(lib.mul, &[i, scale]);
                let total = b.call(lib.add, &[total, step]);
                b.call(w, &[next, fields[0], total])
            })
        });
        let mut callers = [w; 3];
        for (at, count) in [None, Some(small), Some(large)].into_iter().enumerate() {
            let caller = p.declare(&format!("caller{at}"), &[nat], nat);
            p.define(caller, |b, args| {
                let start = b.known(nought);
                let n = count.map_or(args[0], |count| b.known(count));
                b.call(w, &[start, n, start])
            });
            callers[at] = caller;
        }
        let entry = enter(p, &callers);
        p.set_entry(entry);
        validate(p).expect("a valid program");
        (lib.program, w, callers)
    }

    /// The names of what `from` calls.
    fn called(program: &Program, from: FnId) -> Vec<String> {
        let body = program.function(from).body().expect("a body");
        walk::within(program, body)
            .filter_map(|expr| match program.expr(expr) {
                Expr::Call(callee, _) => {
                    Some(program.name(program.function(callee).name).to_owned())
                }
                _ => None,
            })
            .collect()
    }

    #[test]
    fn a_counted_walk_is_asked_for_and_its_copy_counts_narrowly() {
        let most = 1000;
        let (program, w, [outside, small, large]) = program(most);
        let split = counted(&program, most, true).expect("a counted walk to split");
        validate(&split).expect("a valid split program");
        assert_eq!(called(&split, outside), ["w.counted.asked"]);
        assert_eq!(called(&split, small), ["w.counted"]);
        assert_eq!(called(&split, large), ["w"]);
        let copy = (0..split.functions().len())
            .map(FnId::at)
            .find(|&id| split.name(split.function(id).name) == "w.counted")
            .expect("the copy");
        // The copy is handed counts and starts at most `most`, so what it
        // counts up is bounded; the walk is still handed any.
        let facts = split.analyze();
        let counted_up = facts.takes(copy)[0]
            .high
            .expect("a bound on the copy's count up");
        assert!(counted_up <= 2 * most, "{counted_up}");
        assert_eq!(facts.takes(w)[0].high, None);
        // A walk of numbers alone is split where a walk holding a list is
        // not.
        assert!(counted(&program, most, false).is_some());
    }

    #[test]
    fn nothing_but_a_walk_counting_is_split() {
        let mut lib = Library::new();
        let nat = lib.nat;
        let p = &mut lib.program;
        // Taking a count down with nothing counted up gains nothing.
        let down = p.declare("down", &[nat, nat], nat);
        p.define(down, |b, args| {
            b.match_(args[0], nat, |b, ctor, fields| {
                if ctor == lib.zero {
                    return args[1];
                }
                let total = b.call(lib.add, &[args[1], args[1]]);
                b.call(down, &[fields[0], total])
            })
        });
        let entry = enter(p, &[down]);
        p.set_entry(entry);
        validate(p).expect("a valid program");
        assert!(counted(&lib.program, 1000, true).is_none());
    }
}
