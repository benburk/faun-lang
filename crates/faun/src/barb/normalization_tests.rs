use super::inline::Inlining;
use super::{
    Atom, Expr, FnId, InlineLimits, Local, Program, normalize_with_limits, structural, validate,
};

fn fixture() -> (Program, FnId, FnId) {
    let (mut program, nat, _, _) = super::tests::types();
    let effect = program.declare("effect", &[], nat);
    let helper = program.declare("helper", &[], nat);
    let zero = program.intern_number(nat, 0).unwrap();
    program.define(helper, |b, _| {
        b.call(effect, &[]);
        b.known(zero)
    });
    let main = program.declare("main", &[], nat);
    program.define(main, |b, _| {
        b.call(helper, &[]);
        let alias = b.known(zero);
        b.known(zero); // An unused eager binding must survive normalization.
        alias
    });
    let body = program.function(main).body().unwrap();
    let alias = program.bindings(body.bindings)[1];
    program.write(alias, Expr::Atom(Atom(Local::at(0))));
    program.set_entry(main);
    validate(&program).unwrap();
    (program, helper, effect)
}

#[test]
fn structural_normalization_removes_aliases_without_expanding_or_discarding_calls() {
    let (mut program, helper, effect) = fixture();
    structural(&mut program);
    validate(&program).unwrap();
    let body = program.function(program.entry().unwrap()).body().unwrap();
    let bindings = program.bindings(body.bindings);
    assert_eq!(bindings.len(), 2);
    assert!(matches!(program.expr(bindings[0]), Expr::Call(id, _) if id == helper));
    assert!(matches!(program.expr(bindings[1]), Expr::Static(..)));
    assert_eq!(program.expr(body.tail), Expr::Atom(Atom(Local::at(0))));
    let body = program.function(helper).body().unwrap();
    let bindings = program.bindings(body.bindings);
    assert_eq!(bindings.len(), 1);
    assert!(matches!(program.expr(bindings[0]), Expr::Call(id, _) if id == effect));
}

#[test]
fn callers_expand_original_bodies_not_already_expanded_callees() {
    let (mut program, nat, _, _) = super::tests::types();
    let effect = program.declare("effect", &[], nat);
    let mut chain = vec![];
    for at in 0..8 {
        let called = chain.last().copied().unwrap_or(effect);
        let id = program.declare(&format!("helper_{at}"), &[], nat);
        program.define(id, |b, _| b.call(called, &[]));
        chain.push(id);
    }
    program.set_entry(*chain.last().unwrap());
    normalize_with_limits(
        &mut program,
        InlineLimits {
            max_depth: 1,
            ..Default::default()
        },
    );
    validate(&program).unwrap();
    for (at, &id) in chain.iter().enumerate() {
        let expected = at.checked_sub(2).map_or(effect, |at| chain[at]);
        let tail = program.function(id).body().unwrap().tail;
        assert!(
            matches!(program.expr(tail), Expr::Call(called, _) if called == expected),
            "helper_{at} expanded beyond the original-body depth limit"
        );
    }
}

#[test]
fn each_zero_inline_limit_uses_structural_rebuilding_without_an_inlining_plan() {
    let (original, _, _) = fixture();
    let mut expected = original.clone();
    structural(&mut expected);
    assert!(Inlining::new(&original, InlineLimits::default()).is_some());
    for limits in [
        InlineLimits {
            max_callee: 0,
            ..Default::default()
        },
        InlineLimits {
            per_function: 0,
            ..Default::default()
        },
        InlineLimits {
            total: 0,
            ..Default::default()
        },
        InlineLimits {
            max_depth: 0,
            ..Default::default()
        },
    ] {
        assert!(Inlining::new(&original, limits).is_none());
        let mut actual = original.clone();
        normalize_with_limits(&mut actual, limits);
        validate(&actual).unwrap();
        assert_eq!(actual, expected, "{limits:?}");
    }
}

/// A match that asks which constructor it has and answers with the one it
/// has is the value it asked about.
#[test]
fn a_match_that_puts_back_what_it_took_apart_is_what_it_took_apart() {
    let (mut program, nat, _, _) = super::tests::types();
    let id = program.declare("id", &[nat], nat);
    program.define(id, |b, args| {
        b.match_(args[0], nat, super::builder::Builder::con)
    });
    program.set_entry(id);
    validate(&program).unwrap();

    structural(&mut program);
    validate(&program).unwrap();
    let body = program.function(id).body().unwrap();
    assert!(
        program.bindings(body.bindings).is_empty(),
        "nothing is left"
    );
    assert_eq!(program.expr(body.tail), Expr::Atom(Atom(Local::at(0))));
}

/// One that puts back a different constructor, or the right one out of
/// other fields, is not. Both are what the rule would get wrong if it read
/// only the shape and not the fields.
#[test]
fn a_match_that_puts_back_something_else_stays() {
    let mut program = Program::default();
    let bool_ = program.declare_type("Bool");
    program.define_type(bool_, &[("False", &[]), ("True", &[])]);
    let pair = program.declare_type("Pair");
    program.define_type(pair, &[("Both", &[bool_, bool_])]);

    // `not`: each arm answers the other constructor.
    let (no, yes) = (program.ctor_at(bool_, 0), program.ctor_at(bool_, 1));
    let not = program.declare("not", &[bool_], bool_);
    program.define(not, |b, args| {
        b.match_(args[0], bool_, |b, ctor, _| {
            b.con(if ctor == no { yes } else { no }, &[])
        })
    });
    // `swap`: the right constructor, out of its fields the other way round.
    let swap = program.declare("swap", &[pair], pair);
    program.define(swap, |b, args| {
        b.match_(args[0], pair, |b, ctor, fields| {
            b.con(ctor, &[fields[1], fields[0]])
        })
    });
    program.set_entry(not);
    validate(&program).unwrap();

    structural(&mut program);
    validate(&program).unwrap();
    for held in [not, swap] {
        let body = program.function(held).body().unwrap();
        assert!(
            matches!(program.expr(body.tail), Expr::Match(..)),
            "the match stays"
        );
    }
}

/// And one whose arms work before answering stays, since the work is what
/// the match is for.
#[test]
fn a_match_whose_arms_do_something_stays() {
    let (mut program, nat, _, _) = super::tests::types();
    let effect = program.declare("effect", &[], nat);
    let held = program.declare("held", &[nat], nat);
    program.define(held, |b, args| {
        b.match_(args[0], nat, |b, ctor, fields| {
            b.call(effect, &[]);
            b.con(ctor, fields)
        })
    });
    program.set_entry(held);
    validate(&program).unwrap();

    structural(&mut program);
    validate(&program).unwrap();
    let body = program.function(held).body().unwrap();
    assert!(matches!(program.expr(body.tail), Expr::Match(..)));
}

/// A match with no arms never answers, and the value it took apart does, so
/// reading one as the other would be wrong. It is also not something a
/// program may say: this is why the rule asks, and why nothing it runs on
/// can answer yes.
#[test]
fn a_match_on_a_type_with_no_constructors_is_not_a_program() {
    let mut program = Program::default();
    let never = program.declare_type("Never");
    program.define_type(never, &[]);
    let held = program.declare("held", &[never], never);
    program.define(held, |b, args| {
        b.match_(args[0], never, |_, _, _| unreachable!("no arm to build"))
    });
    program.set_entry(held);
    let refused = validate(&program).unwrap_err();
    assert!(refused.contains("matches on nothing at all"), "{refused}");
}
