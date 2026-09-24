use super::budget::{Budget, LimitExceeded};
use super::constant::Held;
use super::evaluate::{CannotFold, Evaluator};
use super::fold::fold_with_limits;
use super::{
    Body, ConstantView, Expr, ExprId, FnId, FoldLimits, InlineLimits, Program, Value, arithmetic,
    decode, fold, normalize_with_limits, optimize, validate,
};

/// `Nat`, `Bool` and their arithmetic, as a source library writes them,
/// with an entry that answers nought and calls none of it.
fn library() -> Program {
    let library = super::fixture::Library::new();
    let (nat, zero) = (library.nat, library.zero);
    let mut program = library.program;
    let main = program.declare("main", &[], nat);
    program.define(main, |b, _| b.con(zero, &[]));
    program.set_entry(main);
    program
}

fn named(program: &Program, name: &str) -> FnId {
    FnId::at(
        program
            .functions()
            .iter()
            .position(|f| program.name(f.name) == name)
            .unwrap(),
    )
}

/// How a program may be optimized: not at all, by each stage of the
/// schedule alone, and by the whole schedule. Each stage must keep what a
/// program means on its own, not only after the stages before it.
fn schedules() -> Vec<(&'static str, Stages)> {
    vec![
        ("nothing", |_| {}),
        ("structural", super::structural),
        ("inlining", |p| {
            normalize_with_limits(p, InlineLimits::default());
        }),
        ("laws", super::laws::laws),
        ("folding", fold),
        ("algebra", |p| {
            super::normalize::algebra(p, FoldLimits::default());
        }),
        ("cleanup", super::cleanup::cleanup),
        ("everything", optimize),
    ]
}

/// Some stages of the schedule, run in order on a program.
type Stages = fn(&mut Program);

// Independent, deliberately small structural oracle. It executes every eager
// binding, records opaque calls, and does not use recognition or the folder.
fn run(program: &Program, id: FnId, args: Vec<Value>, trace: &mut Vec<FnId>) -> Value {
    fn body(program: &Program, b: Body, mut env: Vec<Value>, trace: &mut Vec<FnId>) -> Value {
        for &id in program.bindings(b.bindings) {
            let value = expr(program, id, &env, trace);
            env.push(value);
        }
        expr(program, b.tail, &env, trace)
    }
    fn expr(program: &Program, id: ExprId, env: &[Value], trace: &mut Vec<FnId>) -> Value {
        let args = |range| {
            program
                .atoms(range)
                .iter()
                .map(|a| env[a.0.index()].clone())
                .collect()
        };
        match program.expr(id) {
            Expr::Atom(a) => env[a.0.index()].clone(),
            Expr::Static(value) => {
                let value = program.constant(value);
                decode(program, value.owner(), value.encoded()).0
            }
            Expr::Con(ctor, fields) => Value(ctor, args(fields)),
            Expr::Call(called, fields) => run(program, called, args(fields), trace),
            Expr::Match(a, arms) => {
                let Value(ctor, fields) = &env[a.0.index()];
                let arm = program.arms(arms).iter().find(|a| a.ctor == *ctor).unwrap();
                let mut inner = env.to_vec();
                inner.extend(fields.iter().cloned());
                body(program, arm.body, inner, trace)
            }
        }
    }
    if let Some(b) = program.function(id).body() {
        body(program, b, args, trace)
    } else {
        trace.push(id);
        let result = program.function(id).result;
        Value(program.ctor_at(result, 0), vec![])
    }
}

fn arithmetic_probes() -> (Program, Vec<FnId>) {
    let mut original = library();
    let ty = original.params(named(&original, "add"))[0];
    let mut probes = vec![];
    for name in ["add", "sub", "mul", "div", "mod", "equals", "less_than"] {
        let called = named(&original, name);
        for left in 0..3 {
            for right in 0..3 {
                let id = original.declare(
                    &format!("probe_{name}_{left}_{right}"),
                    &[ty],
                    original.function(called).result,
                );
                let zero = original.intern_number(ty, 0).unwrap();
                let one = original.intern_number(ty, 1).unwrap();
                original.define(id, |b, args| {
                    let values = [b.known(zero), b.known(one), args[0]];
                    b.call(called, &[values[left], values[right]])
                });
                probes.push(id);
            }
        }
    }
    validate(&original).unwrap();
    (original, probes)
}

#[test]
fn schedule_ablations_preserve_small_arithmetic_and_recognition() {
    let (original, probes) = arithmetic_probes();
    let ty = original.params(named(&original, "add"))[0];
    let recognized = arithmetic::recognise(&original);
    for (schedule, stages) in schedules() {
        let mut optimized = original.clone();
        stages(&mut optimized);
        validate(&optimized).unwrap();
        assert_eq!(arithmetic::recognise(&optimized), recognized);
        for &id in &probes {
            for n in 0..6 {
                let args = vec![super::tests::nat(&original, ty, n)];
                let expected = run(&original, id, args.clone(), &mut vec![]);
                assert_eq!(
                    run(&optimized, id, args, &mut vec![]),
                    expected,
                    "{}({n}), {schedule}",
                    original.name(original.function(id).name)
                );
            }
        }
    }
}

#[test]
fn algebraic_arithmetic_collects_constants_in_safe_directions() {
    let mut original = library();
    let add = named(&original, "add");
    let mul = named(&original, "mul");
    let monus = named(&original, "sub");
    let div = named(&original, "div");
    let ty = original.params(add)[0];
    let three = original.intern_number(ty, 3).unwrap();
    let five = original.intern_number(ty, 5).unwrap();
    let mut probes = vec![];
    for (name, called, expected) in [
        ("sum", add, 8),
        ("product", mul, 15),
        ("monus", monus, 8),
        ("quotient", div, 15),
    ] {
        let id = algebra_probe(&mut original, name, called, ty, three, five);
        probes.push((name, id, called, expected));
    }
    validate(&original).unwrap();

    let mut optimized = original.clone();
    optimize(&mut optimized);
    validate(&optimized).unwrap();

    for probe in probes {
        assert_normalized_arithmetic(&original, &optimized, ty, probe);
    }
}

#[test]
fn affine_facts_collect_shared_linear_terms_without_synthesizing_calls() {
    let mut program = library();
    let add = named(&program, "add");
    let ty = program.params(add)[0];
    let three = program.intern_number(ty, 3).unwrap();
    let test = program.declare("shared_affine", &[ty], ty);
    program.define(test, |b, args| {
        let three = b.known(three);
        let a = b.call(add, &[args[0], three]);
        let sum = b.call(add, &[a, args[0]]);
        b.call(add, &[a, sum])
    });
    validate(&program).unwrap();

    let facts = crate::barb::analyzed(&program);
    let tail = program.function(test).body().unwrap().tail;
    let affine = facts.affine(tail).expect("a bounded affine summary");
    assert_eq!(affine.constant, 6);
    assert_eq!(affine.terms, vec![(super::Atom(super::Local::at(0)), 3)]);
}

#[test]
fn affine_facts_stop_at_nonlinear_products_and_the_term_limit() {
    let mut program = library();
    let add = named(&program, "add");
    let mul = named(&program, "mul");
    let ty = program.params(add)[0];

    let nonlinear = program.declare("nonlinear", &[ty, ty], ty);
    program.define(nonlinear, |b, args| b.call(mul, args));

    let params = vec![ty; 9];
    let crowded = program.declare("crowded", &params, ty);
    program.define(crowded, |b, args| {
        args[1..]
            .iter()
            .fold(args[0], |sum, &term| b.call(add, &[sum, term]))
    });
    validate(&program).unwrap();

    let facts = crate::barb::analyzed(&program);
    for id in [nonlinear, crowded] {
        let tail = program.function(id).body().unwrap().tail;
        assert!(facts.affine(tail).is_none(), "{}", program.render());
    }
}

fn algebra_probe(
    program: &mut Program,
    name: &str,
    called: FnId,
    ty: super::TypeId,
    three: super::ConstId,
    five: super::ConstId,
) -> FnId {
    let id = program.declare(name, &[ty], ty);
    program.define(id, |b, args| {
        let three = b.known(three);
        let five = b.known(five);
        match name {
            "sum" => {
                let inner = b.call(called, &[args[0], five]);
                b.call(called, &[three, inner])
            }
            "product" => {
                let inner = b.call(called, &[five, args[0]]);
                b.call(called, &[inner, three])
            }
            "monus" | "quotient" => {
                let inner = b.call(called, &[args[0], three]);
                b.call(called, &[inner, five])
            }
            _ => unreachable!("an arithmetic probe"),
        }
    });
    id
}

fn assert_normalized_arithmetic(
    original: &Program,
    optimized: &Program,
    ty: super::TypeId,
    (name, id, called, expected): (&str, FnId, FnId, u64),
) {
    assert_eq!(calls_to(optimized, id, called), 1, "{}", optimized.render());
    let body = optimized.function(id).body().unwrap();
    let Expr::Call(actual, args) = optimized.expr(body.tail) else {
        panic!("normalized arithmetic is one call\n{}", optimized.render());
    };
    assert_eq!(actual, called);
    let [dynamic, constant] = optimized.atoms(args) else {
        panic!("binary arithmetic");
    };
    assert_eq!(dynamic.0.index(), 0, "constant belongs on the right");
    let binding = optimized.bindings(body.bindings)[constant.0.index() - 1];
    let Expr::Static(value) = optimized.expr(binding) else {
        panic!("combined constant\n{}", optimized.render());
    };
    let ConstantView::Natural(value) = optimized.constant(value).view() else {
        panic!("a natural constant");
    };
    assert_eq!(value.try_u64(), Ok(expected));

    for n in [0, 1, 5, 8, 14, 15, 16, 31] {
        let args = vec![super::tests::nat(original, ty, n)];
        assert_eq!(
            run(optimized, id, args.clone(), &mut vec![]),
            run(original, id, args, &mut vec![]),
            "{name}({n})"
        );
    }
}

#[test]
fn self_division_is_not_one_and_misleading_names_do_not_earn_laws() {
    let mut program = library();
    let div = named(&program, "div");
    let ty = program.params(div)[0];
    let test = program.declare("self_div", &[ty], ty);
    program.define(test, |b, args| b.call(div, &[args[0], args[0]]));
    let fake = program.declare("add_lookalike", &[ty, ty], ty);
    program.define(fake, |_, args| args[0]);
    let use_fake = program.declare("use_fake", &[ty], ty);
    let zero = program.intern_number(ty, 0).unwrap();
    program.define(use_fake, |b, args| {
        let zero = b.known(zero);
        b.call(fake, &[zero, args[0]])
    });
    super::laws::laws(&mut program);
    assert!(
        matches!(program.expr(program.function(test).body().unwrap().tail), Expr::Call(called, _) if called == div)
    );
    assert!(
        matches!(program.expr(program.function(use_fake).body().unwrap().tail), Expr::Call(called, _) if called == fake)
    );
}

fn effect_program() -> Program {
    let mut original = library();
    let mul = named(&original, "mul");
    let ty = original.params(mul)[0];
    let first = original.declare("first_effect", &[], ty);
    let second = original.declare("second_effect", &[], ty);
    let zero = original.intern_number(ty, 0).unwrap();
    let helper = original.declare("effect_then_zero", &[], ty);
    original.define(helper, |b, _| {
        b.call(first, &[]);
        b.known(zero)
    });
    let test = original.declare("eager_test", &[], ty);
    original.define(test, |b, _| {
        let value = b.call(helper, &[]);
        b.match_(value, ty, |b, _, _| {
            let effect = b.call(second, &[]);
            let zero = b.known(zero);
            b.call(mul, &[zero, effect])
        })
    });
    original
}

#[test]
fn eager_effects_survive_folding_inlining_laws_and_cleanup() {
    let original = effect_program();
    let first = named(&original, "first_effect");
    let second = named(&original, "second_effect");
    let test = named(&original, "eager_test");
    let helper = named(&original, "effect_then_zero");
    let ty = original.function(helper).result;
    for (schedule, stages) in schedules() {
        let mut optimized = original.clone();
        stages(&mut optimized);
        let mut trace = vec![];
        assert_eq!(
            run(&optimized, test, vec![], &mut trace),
            super::tests::nat(&original, ty, 0)
        );
        assert_eq!(trace, [first, second], "{schedule}");
    }
    // The evaluator must decline the whole helper, even though its answer is
    // known: a refusal is not permission to skip an eager binding.
    let ops = arithmetic::recognise(&original);
    assert_eq!(
        Evaluator {
            program: &original,
            operations: &ops
        }
        .body(
            original.function(helper).body().unwrap(),
            vec![],
            &mut Budget::new(FoldLimits::default())
        )
        .unwrap_err(),
        CannotFold::ExternalCall
    );
}

#[test]
fn normalization_and_cleanup_keep_effects_on_their_original_paths() {
    let (mut program, ty, _, _) = super::tests::types();
    let first = program.declare("zero_effect", &[], ty);
    let second = program.declare("successor_effect", &[], ty);
    let helper = program.declare("helper", &[ty], ty);
    program.define(helper, |b, args| {
        b.match_(args[0], ty, |b, _, fields| {
            b.call(if fields.is_empty() { first } else { second }, &[])
        })
    });
    let test = program.declare("test", &[ty], ty);
    program.define(test, |b, args| b.call(helper, args));
    optimize(&mut program);
    for (n, effect) in [(0, first), (1, second)] {
        let mut trace = vec![];
        run(
            &program,
            test,
            vec![super::tests::nat(&program, ty, n)],
            &mut trace,
        );
        assert_eq!(trace, [effect]);
    }
}

#[test]
fn folding_a_known_match_does_not_erase_effects_in_its_selected_arm() {
    let (mut program, ty, _, _) = super::tests::types();
    let effect = program.declare("effect", &[], ty);
    let zero = program.intern_number(ty, 0).unwrap();
    let test = program.declare("test", &[], ty);
    program.define(test, |b, _| {
        let zero = b.known(zero);
        b.match_(zero, ty, |b, _, _| {
            b.call(effect, &[]);
            zero
        })
    });
    fold(&mut program);
    let mut trace = vec![];
    run(&program, test, vec![], &mut trace);
    assert_eq!(trace, [effect]);
    assert!(matches!(
        program.expr(program.function(test).body().unwrap().tail),
        Expr::Match(..)
    ));
}

#[test]
fn unknown_nonreturning_bindings_are_not_folded_away() {
    let (mut program, ty, _, _) = super::tests::types();
    let looping = program.declare("looping", &[], ty);
    program.define(looping, |b, _| b.call(looping, &[]));
    let zero = program.intern_number(ty, 0).unwrap();
    let helper = program.declare("helper", &[], ty);
    program.define(helper, |b, _| {
        b.call(looping, &[]);
        b.known(zero)
    });
    let test = program.declare("test", &[], ty);
    program.define(test, |b, _| b.call(helper, &[]));
    program.set_entry(test);
    assert!(validate(&program).unwrap_err().contains("stops"));
    fold(&mut program);
    assert!(matches!(
        program.expr(program.function(test).body().unwrap().tail),
        Expr::Call(..)
    ));
}

#[test]
fn fold_fuel_is_shared_across_the_whole_program() {
    let mut program = library();
    let mul = named(&program, "mul");
    let ty = program.params(mul)[0];
    let mut tests = vec![];
    let n = program.intern_number(ty, 3).unwrap();
    for at in 0..200 {
        let id = program.declare(&format!("wide_{at}"), &[], ty);
        program.define(id, |b, _| {
            let n = b.known(n);
            b.call(mul, &[n, n])
        });
        tests.push(id);
    }
    fold_with_limits(
        &mut program,
        FoldLimits {
            work: 500,
            ..FoldLimits::default()
        },
    );
    let folded = tests
        .iter()
        .filter(|&&id| {
            matches!(
                program.expr(program.function(id).body().unwrap().tail),
                Expr::Static(..)
            )
        })
        .count();
    assert!(folded > 0 && folded < tests.len(), "folded {folded}");
    let last = *tests.last().unwrap();
    assert_eq!(
        run(&program, last, vec![], &mut vec![]),
        super::tests::nat(&program, ty, 9)
    );
}

#[test]
#[expect(
    clippy::too_many_lines,
    reason = "size refusal, work refusal, and success for the same arithmetic expression"
)]
fn bigint_size_and_work_are_guarded_before_native_operations() {
    let mut program = library();
    let mul = named(&program, "mul");
    let ty = program.params(mul)[0];
    let n = num_bigint::BigUint::from(1u8) << 4000usize;
    let value = program.intern_natural(ty, &n).unwrap();
    let test = program.declare("expensive", &[], ty);
    program.define(test, |b, _| {
        let n = b.known(value);
        b.call(mul, &[n, n])
    });
    let ops = arithmetic::recognise(&program);
    let evaluator = Evaluator {
        program: &program,
        operations: &ops,
    };
    let body = program.function(test).body().unwrap();
    let mut size = Budget::new(FoldLimits {
        max_bytes: 600,
        ..FoldLimits::default()
    });
    assert_eq!(
        evaluator.body(body, vec![], &mut size).unwrap_err(),
        CannotFold::Limit(LimitExceeded::ValueSize)
    );
    assert!(size.remaining > 0, "size, not fuel, declined");
    let mut work = Budget::new(FoldLimits {
        work: 4000,
        ..FoldLimits::default()
    });
    assert_eq!(
        evaluator.body(body, vec![], &mut work).unwrap_err(),
        CannotFold::Limit(LimitExceeded::Work)
    );
    assert_eq!(
        work.remaining, 0,
        "bigint work is charged, not just one expression"
    );
    let value = evaluator
        .body(body, vec![], &mut Budget::new(FoldLimits::default()))
        .unwrap();
    let ConstantView::Natural(number) = value.as_constant(program.type_info()).view() else {
        panic!("a natural");
    };
    assert_eq!(number.to_biguint(), &n * &n);
}

fn calls_to(program: &Program, id: FnId, called: FnId) -> usize {
    let mut bodies = vec![program.function(id).body().unwrap()];
    let mut count = 0;
    while let Some(body) = bodies.pop() {
        for &expr in program
            .bindings(body.bindings)
            .iter()
            .chain(std::iter::once(&body.tail))
        {
            match program.expr(expr) {
                Expr::Call(target, _) if target == called => count += 1,
                Expr::Match(_, arms) => bodies.extend(program.arms(arms).iter().map(|a| a.body)),
                _ => {}
            }
        }
    }
    count
}

fn inline_program() -> Program {
    let (mut original, ty, _, _) = super::tests::types();
    let effect = original.declare("effect", &[], ty);
    let zero = original.intern_number(ty, 0).unwrap();
    let helper = original.declare("helper", &[], ty);
    original.define(helper, |b, _| {
        b.call(effect, &[]);
        b.known(zero)
    });
    for at in 0..2 {
        let id = original.declare(&format!("caller_{at}"), &[], ty);
        original.define(id, |b, _| {
            let mut answer = b.known(zero);
            for _ in 0..20 {
                answer = b.call(helper, &[]);
            }
            answer
        });
    }
    original
}

#[test]
fn inline_budgets_charge_copied_nodes_per_callee_caller_and_program() {
    let original = inline_program();
    let helper = named(&original, "helper");
    let effect = named(&original, "effect");
    let ty = original.function(helper).result;
    let callers = [named(&original, "caller_0"), named(&original, "caller_1")];
    // The helper costs four entries: two expressions, a binding, and a
    // possible manufactured alias tail. No allocation is made on refusal.
    for (max_callee, per_function, total, expected) in [
        (3, 100, 100, [20, 20]),
        (4, 4, 100, [19, 19]),
        (4, 100, 8, [18, 20]),
        (4, 100, 0, [20, 20]),
    ] {
        let mut program = original.clone();
        normalize_with_limits(
            &mut program,
            InlineLimits {
                max_callee,
                per_function,
                total,
                max_depth: 8,
            },
        );
        for (&id, expected) in callers.iter().zip(expected) {
            assert_eq!(calls_to(&program, id, helper), expected);
            let mut trace = vec![];
            assert_eq!(
                run(&program, id, vec![], &mut trace),
                super::tests::nat(&program, ty, 0)
            );
            assert_eq!(trace, vec![effect; 20]);
        }
    }
}

#[test]
fn large_helpers_and_deep_helper_chains_are_not_blindly_copied() {
    let (mut program, ty, _, _) = super::tests::types();
    let zero = program.intern_number(ty, 0).unwrap();
    let wide = program.declare("wide", &[], ty);
    program.define(wide, |b, _| {
        for _ in 0..1000 {
            b.known(zero);
        }
        b.known(zero)
    });
    let mut last = wide;
    for at in 0..100 {
        let id = program.declare(&format!("deep_{at}"), &[], ty);
        let called = last;
        program.define(id, |b, _| b.call(called, &[]));
        last = id;
    }
    normalize_with_limits(
        &mut program,
        InlineLimits {
            max_depth: 4,
            ..InlineLimits::default()
        },
    );
    let first = named(&program, "deep_0");
    assert_eq!(calls_to(&program, first, wide), 1);
    let Expr::Call(called, _) = program.expr(program.function(last).body().unwrap().tail) else {
        panic!("depth cap must retain a call")
    };
    assert_eq!(called, named(&program, "deep_94"));
    assert_eq!(
        run(&program, last, vec![], &mut vec![]),
        super::tests::nat(&program, ty, 0)
    );
}

#[test]
fn constructor_size_is_checked_before_concatenating_fields() {
    let (mut program, ty, _, _) = super::tests::types();
    let record = program.declare_type("Pair");
    program.define_type(record, &[("Pair", &[ty, ty])]);
    let ctor = program.ctor_at(record, 0);
    let value = program
        .intern_natural(ty, &(num_bigint::BigUint::from(1u8) << 200usize))
        .unwrap();
    let test = program.declare("pair", &[], record);
    program.define(test, |b, _| {
        let n = b.known(value);
        b.con(ctor, &[n, n])
    });
    fold_with_limits(
        &mut program,
        FoldLimits {
            max_bytes: 32,
            ..FoldLimits::default()
        },
    );
    assert!(matches!(
        program.expr(program.function(test).body().unwrap().tail),
        Expr::Con(..)
    ));
}

fn nested_capture_program() -> Program {
    let (mut program, ty, _, _) = super::tests::types();
    let pair = program.declare_type("Pair");
    program.define_type(pair, &[("Pair", &[ty, ty])]);
    let pair = program.ctor_at(pair, 0);
    let succ = program.ctor_at(ty, 1);
    let first = program.declare("first", &[], ty);
    let second = program.declare("second", &[ty], ty);
    let zero = program.intern_number(ty, 0).unwrap();
    let test = program.declare("nested", &[ty, ty], ty);
    program.define(test, |b, args| {
        b.known(zero);
        let effect = b.call(first, &[]);
        b.con(pair, &[effect, args[1]]);
        b.match_(args[0], ty, |b, _, fields| {
            let capture = fields.first().copied().unwrap_or(args[1]);
            b.known(zero);
            b.con(pair, &[capture, args[1]]);
            b.match_(args[1], ty, |b, _, fields| {
                let inner = fields.first().copied().unwrap_or(capture);
                b.con(pair, &[inner, capture]);
                b.call(second, &[effect]);
                b.con(succ, &[inner])
            })
        })
    });
    program.set_entry(test);
    program
}

fn expressions(program: &Program, id: FnId) -> Vec<Expr> {
    let mut pending = vec![program.function(id).body().unwrap()];
    let mut found = vec![];
    while let Some(body) = pending.pop() {
        for &id in program
            .bindings(body.bindings)
            .iter()
            .chain(std::iter::once(&body.tail))
        {
            let expr = program.expr(id);
            if let Expr::Match(_, arms) = expr {
                pending.extend(program.arms(arms).iter().map(|a| a.body));
            }
            found.push(expr);
        }
    }
    found
}

#[test]
fn cleanup_preserves_nested_captures_and_eager_constructor_arguments() {
    let original = nested_capture_program();
    let test = original.entry().unwrap();
    let ty = original.function(test).result;
    let mut cleaned = original.clone();
    super::cleanup::cleanup(&mut cleaned);
    validate(&cleaned).unwrap();
    assert!(
        expressions(&cleaned, test).iter().all(|expr| match expr {
            Expr::Static(..) => false,
            Expr::Con(ctor, _) => cleaned.ctor(*ctor).owner == ty,
            _ => true,
        }),
        "dead constants and Pair constructors were removed inside every arm"
    );
    for a in 0..4 {
        for b in 0..4 {
            let args = vec![
                super::tests::nat(&original, ty, a),
                super::tests::nat(&original, ty, b),
            ];
            let expected = run(&original, test, args.clone(), &mut vec![]);
            let mut trace = vec![];
            assert_eq!(run(&cleaned, test, args, &mut trace), expected);
            assert_eq!(
                trace,
                [named(&original, "first"), named(&original, "second")]
            );
        }
    }
}

#[test]
fn cleanup_substitutes_aliases_captured_across_removed_bindings() {
    let (mut program, ty, _, _) = super::tests::types();
    let one = program.intern_number(ty, 1).unwrap();
    let succ = program.ctor_at(ty, 1);
    let test = program.declare("alias", &[ty], ty);
    program.define(test, |b, args| {
        b.known(one);
        let alias = b.known(one);
        b.match_(args[0], ty, |b, _, _| {
            b.known(one);
            b.con(succ, &[alias])
        })
    });
    let body = program.function(test).body().unwrap();
    let alias = program.bindings(body.bindings)[1];
    program.write(alias, Expr::Atom(super::Atom(super::Local::at(0))));
    program.set_entry(test);
    super::cleanup::cleanup(&mut program);
    validate(&program).unwrap();
    assert!(
        program
            .bindings(program.function(test).body().unwrap().bindings)
            .is_empty()
    );
    for n in 0..4 {
        assert_eq!(
            run(
                &program,
                test,
                vec![super::tests::nat(&program, ty, n)],
                &mut vec![]
            ),
            super::tests::nat(&program, ty, n + 1)
        );
    }
}

#[test]
fn cleanup_retains_unused_calls_and_matches_in_order() {
    let (mut program, ty, _, _) = super::tests::types();
    let first = program.declare("first", &[], ty);
    let second = program.declare("second", &[], ty);
    let zero = program.intern_number(ty, 0).unwrap();
    let pure = program.declare("pure", &[], ty);
    program.define(pure, |b, _| b.known(zero));
    let test = program.declare("unused", &[ty], ty);
    program.define(test, |b, args| {
        b.call(first, &[]);
        b.call(pure, &[]);
        b.match_(args[0], ty, |b, _, _| b.call(second, &[]));
        b.known(zero)
    });
    super::cleanup::cleanup(&mut program);
    // Even a pure call is retained when no analysis classifies it as inert.
    assert_eq!(calls_to(&program, test, pure), 1);
    assert_eq!(
        expressions(&program, test)
            .iter()
            .filter(|expr| matches!(expr, Expr::Match(..)))
            .count(),
        1
    );
    for n in 0..2 {
        let mut trace = vec![];
        run(
            &program,
            test,
            vec![super::tests::nat(&program, ty, n)],
            &mut trace,
        );
        assert_eq!(trace, [first, second]);
    }
}

#[test]
fn cleanup_removes_a_wide_dead_constructor_chain_in_one_pass() {
    let (mut program, ty, _, _) = super::tests::types();
    let zero = program.intern_number(ty, 0).unwrap();
    let succ = program.ctor_at(ty, 1);
    let test = program.declare("wide", &[], ty);
    program.define(test, |b, _| {
        let zero = b.known(zero);
        let mut dead = zero;
        for _ in 0..10_000 {
            dead = b.con(succ, &[dead]);
        }
        zero
    });
    super::cleanup::cleanup(&mut program);
    assert!(
        program
            .bindings(program.function(test).body().unwrap().bindings)
            .len()
            <= 1
    );
    assert!(
        !expressions(&program, test)
            .iter()
            .any(|expr| matches!(expr, Expr::Con(..)))
    );
}

/// A definition that does not stop is refused where a program is checked,
/// and lowering checks before it reads anything, so no optimization or
/// analysis is trusted with one.
#[test]
fn optimizing_never_bypasses_totality_checking() {
    let mut library = super::fixture::Library::new();
    let (nat, zero, succ) = (library.nat, library.zero, library.succ);
    let program = &mut library.program;
    let forever = program.declare("forever", &[nat], nat);
    // forever(Zero) -> Succ(forever(Zero))
    // forever(Succ(n)) -> Succ(forever(Succ(n)))
    program.define(forever, |b, args| {
        b.match_(args[0], nat, |b, ctor, fields| {
            let again = if ctor == zero {
                b.con(zero, &[])
            } else {
                b.con(succ, &[fields[0]])
            };
            let rest = b.call(forever, &[again]);
            b.con(succ, &[rest])
        })
    });
    let main = program.declare("main", &[], nat);
    program.define(main, |b, _| {
        let zero = b.con(zero, &[]);
        b.call(forever, &[zero])
    });
    program.set_entry(main);
    for error in [
        validate(program).unwrap_err(),
        crate::machine(program, &crate::platform::Routines::builtin()).unwrap_err(),
    ] {
        assert!(
            error.contains("forever") && error.contains("stops"),
            "{error}"
        );
    }
}

#[test]
fn zero_fold_budget_is_an_exact_noop() {
    let mut program = library();
    let original = program.clone();
    fold_with_limits(
        &mut program,
        FoldLimits {
            work: 0,
            ..FoldLimits::default()
        },
    );
    assert_eq!(program, original);
}

#[test]
fn deep_evaluation_declines_without_exhausting_aggregate_fuel() {
    let (mut program, ty, _, _) = super::tests::types();
    let count = program.declare("count", &[ty], ty);
    program.define(count, |b, args| {
        b.match_(args[0], ty, |b, _, fields| {
            if let [rest] = fields {
                b.call(count, &[*rest])
            } else {
                args[0]
            }
        })
    });
    let value = Held::number(
        program.type_info(),
        ty,
        &num_bigint::BigUint::from(1_000_000u32),
    );
    let ops = arithmetic::recognise(&program);
    let mut budget = Budget::new(FoldLimits {
        max_depth: 16,
        ..FoldLimits::default()
    });
    assert_eq!(
        Evaluator {
            program: &program,
            operations: &ops
        }
        .body(
            program.function(count).body().unwrap(),
            vec![Ok(value)],
            &mut budget
        )
        .unwrap_err(),
        CannotFold::Limit(LimitExceeded::Depth)
    );
    assert!(budget.remaining > 0);
}
