use std::collections::HashMap;

use super::{
    Body, Definition, Expr, ExprId, FnId, Program, arithmetic, cleanup::cleanup, structural,
    validate,
};

fn library() -> Program {
    crate::surface::parse(
        &format!(
            "{}\nmain!(h) -> exit!(h Zero)",
            include_str!("../../../../standard/nat.fn")
        ),
        &crate::platform::Routines::builtin(),
    )
    .unwrap()
}

fn counts(p: &Program) -> [usize; 4] {
    [p.exprs.len(), p.atoms.len(), p.bindings.len(), p.arms.len()]
}

fn allocation<T>(values: &[T]) -> *const () {
    values.as_ptr().cast()
}

// These allocations are not term pools and must not be replaced by either pass.
fn storage(p: &Program) -> [*const (); 8] {
    let [constants, bytes] = p.constants.allocations();
    [
        allocation(p.types.as_slice()),
        allocation(p.ctors.as_slice()),
        allocation(p.functions.as_slice()),
        allocation(&p.types_pool),
        constants,
        bytes,
        allocation(&p.names),
        allocation(p.symbols.as_slice()),
    ]
}

fn assert_declarations(before: &Program, after: &Program) {
    assert_eq!(before.types, after.types);
    assert_eq!(before.ctors, after.ctors);
    assert_eq!(before.types_pool, after.types_pool);
    assert_eq!(before.constants, after.constants);
    assert_eq!(before.names, after.names);
    assert_eq!(before.symbols, after.symbols);
    assert_eq!(before.entry, after.entry);
    assert_eq!(before.functions.len(), after.functions.len());
    for (a, b) in before.functions.iter().zip(&after.functions) {
        assert_eq!((a.name, a.params, a.result), (b.name, b.params, b.result));
        if matches!(a.definition, Definition::External { .. }) {
            assert_eq!(a.definition, b.definition);
        }
    }
}

fn assert_packed(p: &Program) {
    let [mut exprs, mut atoms, mut bindings, mut arms] = counts(p).map(|n| vec![false; n]);
    let mut pending: Vec<_> = p
        .functions()
        .iter()
        .filter_map(super::Function::body)
        .collect();
    while let Some(body) = pending.pop() {
        bindings[body.bindings.range()].fill(true);
        for &id in p
            .bindings(body.bindings)
            .iter()
            .chain(std::iter::once(&body.tail))
        {
            if std::mem::replace(&mut exprs[id.index()], true) {
                continue;
            }
            match p.expr(id) {
                Expr::Con(_, args) | Expr::Call(_, args) => atoms[args.range()].fill(true),
                Expr::Match(_, range) => {
                    arms[range.range()].fill(true);
                    pending.extend(p.arms(range).iter().map(|arm| arm.body));
                }
                Expr::Atom(_) | Expr::Static(..) => {}
            }
        }
    }
    for (name, reached) in [
        ("expressions", exprs),
        ("arguments", atoms),
        ("bindings", bindings),
        ("arms", arms),
    ] {
        assert!(
            reached.iter().all(|&live| live),
            "unreachable {name} remain"
        );
    }
}

// Compare equations, including binding order and sharing-independent structure,
// without comparing the physical IDs/ranges which compaction must change.
fn assert_same_body(
    a: &Program,
    b: &Program,
    before: Body,
    after: Body,
    copied: &mut HashMap<ExprId, ExprId>,
) {
    let mut pending = vec![(before, after)];
    while let Some((before, after)) = pending.pop() {
        assert_eq!(before.bindings.len(), after.bindings.len());
        let left = a
            .bindings(before.bindings)
            .iter()
            .chain(std::iter::once(&before.tail));
        let right = b
            .bindings(after.bindings)
            .iter()
            .chain(std::iter::once(&after.tail));
        for (&left, &right) in left.zip(right) {
            if let Some(previous) = copied.insert(left, right) {
                assert_eq!(previous, right, "protected expression sharing was lost");
            }
            match (a.expr(left), b.expr(right)) {
                (Expr::Con(x, xs), Expr::Con(y, ys)) => {
                    assert_eq!(x, y);
                    assert_eq!(a.atoms(xs), b.atoms(ys));
                }
                (Expr::Call(x, xs), Expr::Call(y, ys)) => {
                    assert_eq!(x, y);
                    assert_eq!(a.atoms(xs), b.atoms(ys));
                }
                (Expr::Match(x, xs), Expr::Match(y, ys)) => {
                    assert_eq!(x, y);
                    assert_eq!(xs.len(), ys.len());
                    for (x, y) in a.arms(xs).iter().zip(b.arms(ys)) {
                        assert_eq!(x.ctor, y.ctor);
                        pending.push((x.body, y.body));
                    }
                }
                (x, y) => assert_eq!(x, y),
            }
        }
    }
}

// Share identical atoms across scopes, including protected arithmetic bodies.
fn share_atoms(p: &mut Program) {
    let mut first = HashMap::new();
    let redirects: Vec<_> = p
        .exprs
        .iter()
        .enumerate()
        .map(|(at, expr)| {
            let id = ExprId::at(at);
            if let Expr::Atom(a) = expr {
                *first.entry(a.0).or_insert(id)
            } else {
                id
            }
        })
        .collect();
    for id in &mut p.bindings {
        *id = redirects[id.index()];
    }
    for arm in &mut p.arms {
        arm.body.tail = redirects[arm.body.tail.index()];
    }
    for function in &mut p.functions {
        if let Definition::Body(body) = &mut function.definition {
            body.tail = redirects[body.tail.index()];
        }
    }
}

#[test]
fn normalization_only_appends_terms_and_keeps_declaration_storage() {
    let mut p = library();
    let before = p.clone();
    let allocations = storage(&p);
    super::normalize_with_limits(&mut p, super::InlineLimits::default());
    validate(&p).unwrap();
    assert_eq!(
        &p.exprs.as_slice()[..before.exprs.len()],
        before.exprs.as_slice()
    );
    assert_eq!(p.atoms[..before.atoms.len()], before.atoms);
    assert_eq!(p.bindings[..before.bindings.len()], before.bindings);
    assert_eq!(p.arms[..before.arms.len()], before.arms);
    assert_eq!(storage(&p), allocations);
    assert_declarations(&before, &p);
}

fn fragmented() -> (Program, FnId, super::ConstId) {
    let mut p = library();
    let nat = p.params(FnId::at(
        p.functions()
            .iter()
            .position(|f| p.name(f.name) == "add")
            .unwrap(),
    ))[0];
    let unused = p.declare("not_called_from_entry", &[nat], nat);
    let huge = p
        .intern_natural(nat, &(num_bigint::BigUint::from(1u8) << 4096usize))
        .unwrap();
    p.define(unused, |b, args| {
        b.match_(args[0], nat, |b, _, _| b.known(huge))
    });
    // Redefinition leaves obsolete match/argument/binding entries in the pools.
    p.define(unused, |b, _| b.known(huge));
    for _ in 0..4 {
        structural(&mut p);
    }
    share_atoms(&mut p);
    validate(&p).unwrap();
    (p, unused, huge)
}

#[test]
fn cleanup_reclaims_superseded_terms_but_preserves_every_definition_and_equation() {
    let (mut p, unused, huge) = fragmented();
    let before = p.clone();
    let allocations = storage(&p);
    let operations = arithmetic::recognise(&p);
    cleanup(&mut p);
    validate(&p).unwrap();
    assert_packed(&p);
    assert!(
        counts(&p)
            .iter()
            .zip(counts(&before))
            .all(|(&now, old)| now < old),
        "all four term pools should shed obsolete entries: {:?} -> {:?}",
        counts(&before),
        counts(&p)
    );
    assert_eq!(storage(&p), allocations);
    assert_declarations(&before, &p);
    assert_eq!(arithmetic::recognise(&p), operations);
    assert!(
        matches!(p.expr(p.function(unused).body().unwrap().tail), Expr::Static(id) if id == huge)
    );
    let mut copied = HashMap::new();
    for (at, operation) in operations.iter().enumerate() {
        if operation.is_some() {
            let id = FnId::at(at);
            assert_same_body(
                &before,
                &p,
                before.function(id).body().unwrap(),
                p.function(id).body().unwrap(),
                &mut copied,
            );
        }
    }
}

#[test]
fn repeated_cleanup_and_normalization_do_not_accumulate_dead_terms() {
    let (mut p, _, _) = fragmented();
    let before = p.clone();
    let allocations = storage(&p);
    cleanup(&mut p);
    let compact = p.clone();
    cleanup(&mut p);
    assert_eq!(p, compact, "cleanup is storage-idempotent");
    for _ in 0..8 {
        structural(&mut p);
        cleanup(&mut p);
        validate(&p).unwrap();
        assert_packed(&p);
        assert!(
            counts(&p)
                .iter()
                .zip(counts(&compact))
                .all(|(&now, limit)| now <= limit)
        );
        assert_eq!(storage(&p), allocations);
        assert_declarations(&before, &p);
    }
}

#[test]
fn cleanup_remaps_shared_expressions_per_lexical_occurrence() {
    let (mut p, nat, _, _) = super::tests::types();
    let one = p.intern_number(nat, 1).unwrap();
    let first = p.declare("parameter", &[nat, nat], nat);
    p.define(first, |_, args| args[1]);
    let shared = p.function(first).body().unwrap().tail;
    let second = p.declare("local", &[], nat);
    p.define(second, |b, _| {
        b.known(one);
        let live = b.known(one);
        b.known(one);
        live
    });
    let body = p.function(second).body().unwrap();
    p.functions[second].define(Body {
        tail: shared,
        ..body
    });
    p.set_entry(second);
    validate(&p).unwrap();
    cleanup(&mut p);
    validate(&p).unwrap();
    assert_packed(&p);
    let first = p.function(first).body().unwrap();
    let second = p.function(second).body().unwrap();
    assert_eq!(
        p.expr(first.tail),
        Expr::Atom(super::Atom(super::Local::at(1)))
    );
    assert_eq!(
        p.expr(second.tail),
        Expr::Atom(super::Atom(super::Local::at(0)))
    );
    assert_eq!(second.bindings.len(), 1);
}
