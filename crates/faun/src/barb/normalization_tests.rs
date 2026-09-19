use super::inline::Inlining;
use super::{
    Atom, Expr, FnId, InlineLimits, Local, Program, normalize_with_limits, structural, validate,
};

fn fixture() -> (Program, FnId, FnId) {
    let (mut program, nat, _, _) = super::tests::types();
    let effect = program.declare("effect", &[], nat);
    let helper = program.declare("helper", &[], nat);
    let zero = program.intern_number(nat, 0);
    program.define(helper, |b, _| {
        b.call(effect, &[]);
        b.known(nat, zero)
    });
    let main = program.declare("main", &[], nat);
    program.define(main, |b, _| {
        b.call(helper, &[]);
        let alias = b.known(nat, zero);
        b.known(nat, zero); // An unused eager binding must survive normalization.
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
