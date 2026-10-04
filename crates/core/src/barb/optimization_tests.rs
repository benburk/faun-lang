use super::budget::{Budget, LimitExceeded};
use super::constant::Held;
use super::evaluate::{CannotFold, Evaluator};
use super::normalize::fold_with_limits;
use super::{
    Body, ConstantView, Expr, ExprId, FnId, FoldLimits, InlineLimits, Program, TypeId, Value,
    arithmetic, decode, fold, normalize_with_limits, optimize, validate,
};

/// `Nat`, `Bool` and their arithmetic, as a source library writes them,
/// with no entry: every definition is one a test reads, so every one is
/// kept, and each keeps its ID through optimization.
fn library() -> Program {
    super::fixture::Library::new().program
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
        ("descent", super::descent::descend),
        ("inlining", |p| {
            normalize_with_limits(p, InlineLimits::default());
        }),
        ("fusion", super::fuse::fuse),
        ("identities", super::normalize::identities),
        ("folding", fold),
        ("simplifying each definition", |p| {
            for id in super::calls::callees_first(p) {
                super::normalize::resimplify(p, &[id]);
            }
        }),
        ("simplifying", super::normalize::simplify),
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
    ty: TypeId,
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
    ty: TypeId,
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
    super::normalize::identities(&mut program);
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
    // The arm is taken where the match stood, and its call stays in it.
    assert!(
        expressions(&program, test)
            .iter()
            .any(|expr| matches!(expr, Expr::Call(called, _) if *called == effect))
    );
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
    validate(&program).expect("stopping is not asked");
    fold(&mut program);
    assert!(matches!(
        program.expr(program.function(test).body().unwrap().tail),
        Expr::Call(..)
    ));
}

#[test]
fn refolding_only_rewrites_selected_functions() {
    let mut program = library();
    let mul = named(&program, "mul");
    let ty = program.params(mul)[0];
    let effect = program.declare("effect", &[], ty);
    let first = program.declare("first", &[], ty);
    let second = program.declare("second", &[], ty);
    let three = program.intern_number(ty, 3).unwrap();
    for id in [first, second] {
        program.define(id, |b, _| {
            b.call(effect, &[]);
            let three = b.known(three);
            b.call(mul, &[three, three])
        });
    }
    validate(&program).unwrap();
    let original = program.clone();
    super::normalize::resimplify(&mut program, &[]);
    assert_eq!(program, original);
    super::normalize::resimplify(&mut program, &[first]);
    assert!(matches!(
        program.expr(program.function(first).body().unwrap().tail),
        Expr::Static(..)
    ));
    assert_eq!(
        expressions(&program, second),
        expressions(&original, second)
    );
    let mut trace = vec![];
    assert_eq!(
        run(&program, first, vec![], &mut trace),
        super::tests::nat(&program, ty, 9)
    );
    assert_eq!(trace, [effect]);

    // Recognition and external declarations remain untouched on the local path.
    let folded = program.clone();
    super::normalize::resimplify(&mut program, &[mul]);
    super::normalize::resimplify(&mut program, &[effect]);
    assert_eq!(program, folded);
}

#[test]
fn refolding_several_definitions_still_orders_callees_first() {
    let (mut program, ty, _, _) = super::tests::types();
    let zero = program.intern_number(ty, 0).unwrap();
    // Evaluating this chain at once exceeds the depth limit. Folding its
    // callees first makes every call just one step, even in caller-first input.
    let ids: Vec<_> = (0..=FoldLimits::default().max_depth)
        .map(|at| program.declare(&format!("step_{at}"), &[], ty))
        .collect();
    for (at, &id) in ids.iter().enumerate() {
        program.define(id, |b, _| {
            if let Some(&next) = ids.get(at + 1) {
                b.call(next, &[])
            } else {
                b.known(zero)
            }
        });
    }
    super::normalize::resimplify(&mut program, &ids);
    for id in ids {
        assert!(matches!(
            program.expr(program.function(id).body().unwrap().tail),
            Expr::Static(..)
        ));
    }
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
    // A call reaching no external routine is pure: unread, it goes.
    assert_eq!(calls_to(&program, test, pure), 0);
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

/// The bindings of `test`'s own body, not those of its arms.
fn top_level(program: &Program, test: FnId) -> Vec<Expr> {
    let body = program.function(test).body().unwrap();
    program
        .bindings(body.bindings)
        .iter()
        .map(|&id| program.expr(id))
        .collect()
}

/// `sunk(a, b)` builds `b + 2` ahead of a match on `a` and reads it only
/// where `a` is nought; with `both`, the other arm reads it as well.
fn built_ahead(both: bool) -> (Program, FnId, TypeId) {
    let (mut program, ty, _, _) = super::tests::types();
    let nought = program.ctor_at(ty, 0);
    let succ = program.ctor_at(ty, 1);
    let zero = program.intern_number(ty, 0).unwrap();
    let test = program.declare("sunk", &[ty, ty], ty);
    program.define(test, |b, args| {
        let once = b.con(succ, &[args[1]]);
        let twice = b.con(succ, &[once]);
        b.match_(args[0], ty, |b, built, _| {
            if built == nought {
                twice
            } else if both {
                b.con(succ, &[twice])
            } else {
                b.known(zero)
            }
        })
    });
    program.set_entry(test);
    (program, test, ty)
}

/// Inert work read in one arm of a match is worked out only there, the
/// work it depends on with it, so the other arm works out none of it.
#[test]
fn cleanup_sinks_inert_work_into_the_one_arm_that_reads_it() {
    let (original, test, ty) = built_ahead(false);
    let mut program = original.clone();
    super::cleanup::cleanup(&mut program);
    validate(&program).unwrap();
    assert!(top_level(&program, test).is_empty());
    assert_eq!(
        expressions(&program, test)
            .iter()
            .filter(|expr| matches!(expr, Expr::Con(..)))
            .count(),
        2
    );
    for a in 0..3 {
        for b in 0..3 {
            let args = vec![
                super::tests::nat(&original, ty, a),
                super::tests::nat(&original, ty, b),
            ];
            assert_eq!(
                run(&program, test, args.clone(), &mut vec![]),
                run(&original, test, args, &mut vec![])
            );
        }
    }
}

/// A match moved into an arm still reads its own fields where it binds
/// them, beneath the arm's.
#[test]
fn cleanup_sinks_a_match_with_its_fields() {
    let (mut original, ty, _, _) = super::tests::types();
    let nought = original.ctor_at(ty, 0);
    let succ = original.ctor_at(ty, 1);
    let zero = original.intern_number(ty, 0).unwrap();
    let test = original.declare("before", &[ty, ty], ty);
    original.define(test, |b, args| {
        let before = b.match_(args[1], ty, |b, built, fields| {
            if built == nought {
                b.known(zero)
            } else {
                fields[0]
            }
        });
        b.match_(args[0], ty, |b, built, _| {
            if built == nought {
                b.known(zero)
            } else {
                b.con(succ, &[before])
            }
        })
    });
    original.set_entry(test);
    let mut program = original.clone();
    super::cleanup::cleanup(&mut program);
    validate(&program).unwrap();
    assert!(top_level(&program, test).is_empty());
    for a in 0..3 {
        for b in 0..3 {
            let args = vec![
                super::tests::nat(&original, ty, a),
                super::tests::nat(&original, ty, b),
            ];
            assert_eq!(
                run(&program, test, args.clone(), &mut vec![]),
                run(&original, test, args, &mut vec![])
            );
        }
    }
}

/// A call of a definition reaching no external routine is pure, so it
/// moves into the one arm reading it; one reaching an external routine,
/// however far down, stays and happens on every path.
#[test]
fn cleanup_sinks_a_pure_call_and_keeps_one_reaching_an_effect() {
    let (mut original, ty, _, _) = super::tests::types();
    let nought = original.ctor_at(ty, 0);
    let succ = original.ctor_at(ty, 1);
    let effect = original.declare("effect", &[], ty);
    let pure = original.declare("pure", &[ty], ty);
    original.define(pure, |b, args| b.con(succ, &[args[0]]));
    let wrapped = original.declare("wrapped", &[], ty);
    original.define(wrapped, |b, _| b.call(effect, &[]));
    let test = original.declare("calls", &[ty], ty);
    original.define(test, |b, args| {
        let pured = b.call(pure, &[args[0]]);
        let effected = b.call(wrapped, &[]);
        b.match_(args[0], ty, |b, built, _| {
            if built == nought {
                b.con(succ, &[pured])
            } else {
                b.con(succ, &[effected])
            }
        })
    });
    original.set_entry(test);
    let mut program = original.clone();
    super::cleanup::cleanup(&mut program);
    validate(&program).unwrap();
    let top = top_level(&program, test);
    let ahead = |called| matches!(top[..], [Expr::Call(first, _)] if first == called);
    assert!(ahead(wrapped) && !ahead(pure));
    assert_eq!(calls_to(&program, test, pure), 1);
    for n in 0..3 {
        let args = vec![super::tests::nat(&original, ty, n)];
        let mut trace = vec![];
        assert_eq!(
            run(&program, test, args.clone(), &mut trace),
            run(&original, test, args, &mut vec![])
        );
        assert_eq!(trace, [effect]);
    }
}

/// Work two arms read stays where it was built, worked out once.
#[test]
fn cleanup_keeps_work_two_arms_read_ahead_of_them() {
    let (mut program, test, _) = built_ahead(true);
    super::cleanup::cleanup(&mut program);
    validate(&program).unwrap();
    assert_eq!(
        top_level(&program, test)
            .iter()
            .filter(|expr| matches!(expr, Expr::Con(..)))
            .count(),
        2
    );
}

/// A call of unknown meaning read in one arm may have effects, so it stays
/// where it was, and happens on every path.
#[test]
fn cleanup_keeps_a_call_one_arm_reads_where_it_was() {
    let (mut program, ty, _, _) = super::tests::types();
    let nought = program.ctor_at(ty, 0);
    let first = program.declare("first", &[], ty);
    let zero = program.intern_number(ty, 0).unwrap();
    let test = program.declare("called", &[ty], ty);
    program.define(test, |b, args| {
        let called = b.call(first, &[]);
        b.match_(args[0], ty, |b, built, _| {
            if built == nought {
                called
            } else {
                b.known(zero)
            }
        })
    });
    program.set_entry(test);
    super::cleanup::cleanup(&mut program);
    validate(&program).unwrap();
    for n in 0..2 {
        let mut trace = vec![];
        run(
            &program,
            test,
            vec![super::tests::nat(&program, ty, n)],
            &mut trace,
        );
        assert_eq!(trace, [first]);
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

/// `count(n)` builds `n` again a step at a time, its call of itself
/// nested inside the step it builds, where `tail` is false; where it is
/// true, it calls itself last and answers nought.
fn counting(tail: bool) -> (Program, FnId, TypeId) {
    let (mut program, ty, _, _) = super::tests::types();
    let succ = program.ctor_at(ty, 1);
    let count = program.declare("count", &[ty], ty);
    program.define(count, |b, args| {
        b.match_(args[0], ty, |b, _, fields| {
            if let [rest] = fields {
                let counted = b.call(count, &[*rest]);
                if tail {
                    counted
                } else {
                    b.con(succ, &[counted])
                }
            } else {
                args[0]
            }
        })
    });
    (program, count, ty)
}

#[test]
fn a_loop_longer_than_the_depth_limit_still_evaluates() {
    let (program, count, ty) = counting(true);
    let value = Held::number(program.type_info(), ty, &num_bigint::BigUint::from(1000u32));
    let ops = arithmetic::recognise(&program);
    let mut budget = Budget::new(FoldLimits {
        max_depth: 16,
        ..FoldLimits::default()
    });
    let answer = Evaluator {
        program: &program,
        operations: &ops,
    }
    .body(
        program.function(count).body().unwrap(),
        vec![Ok(value)],
        &mut budget,
    )
    .unwrap();
    let nought = Held::number(program.type_info(), ty, &num_bigint::BigUint::default());
    assert_eq!(answer.encoded(), nought.encoded());
}

#[test]
fn deep_evaluation_declines_without_exhausting_aggregate_fuel() {
    let (program, count, ty) = counting(false);
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

/// A list of numbers, its reversal, and walks over it written the way a
/// standard library writes them: `bump` builds `x + 1` for each `x` onto an
/// accumulator and answers it reversed, `running` builds each sum so far
/// the same way, `total` folds a list into a sum, and `index_over(xs limit
/// at)` counts from `at` to the first element past `limit`.
struct Walks {
    reverse: FnId,
    nat: TypeId,
    list: TypeId,
    zero: super::CtorId,
    succ: super::CtorId,
    nil: super::CtorId,
    cons: super::CtorId,
    add: FnId,
    bump: FnId,
    running: FnId,
    total: FnId,
    index_over: FnId,
}

#[expect(
    clippy::too_many_lines,
    reason = "one definition per walk, each as a library writes it"
)]
fn walks() -> (Program, Walks) {
    let library = super::fixture::Library::new();
    let (nat, zero, succ, add) = (library.nat, library.zero, library.succ, library.add);
    let (less_than, true_, bool_) = (library.less_than, library.true_, library.bool_);
    let mut p = library.program;
    let list = p.declare_type("List");
    p.define_type(list, &[("Nil", &[]), ("Cons", &[nat, list])]);
    let (nil, cons) = (p.ctor_at(list, 0), p.ctor_at(list, 1));
    let reverse = p.declare("reverse", &[list, list], list);
    p.define(reverse, |b, args| {
        b.match_(args[0], list, |b, ctor, fields| {
            if ctor == nil {
                args[1]
            } else {
                let onto = b.con(cons, &[fields[0], args[1]]);
                b.call(reverse, &[fields[1], onto])
            }
        })
    });
    let bump = p.declare("bump", &[list, list], list);
    p.define(bump, |b, args| {
        b.match_(args[0], list, |b, ctor, fields| {
            if ctor == nil {
                let empty = b.con(nil, &[]);
                b.call(reverse, &[args[1], empty])
            } else {
                let next = b.con(succ, &[fields[0]]);
                let built = b.con(cons, &[next, args[1]]);
                b.call(bump, &[fields[1], built])
            }
        })
    });
    let running = p.declare("running", &[list, nat, list], list);
    p.define(running, |b, args| {
        b.match_(args[0], list, |b, ctor, fields| {
            if ctor == nil {
                let empty = b.con(nil, &[]);
                b.call(reverse, &[args[2], empty])
            } else {
                let sum = b.call(add, &[args[1], fields[0]]);
                let built = b.con(cons, &[sum, args[2]]);
                b.call(running, &[fields[1], sum, built])
            }
        })
    });
    let total = p.declare("total", &[list, nat], nat);
    p.define(total, |b, args| {
        b.match_(args[0], list, |b, ctor, fields| {
            if ctor == nil {
                args[1]
            } else {
                let sum = b.call(add, &[args[1], fields[0]]);
                b.call(total, &[fields[1], sum])
            }
        })
    });
    let index_over = p.declare("index_over", &[list, nat, nat], nat);
    p.define(index_over, |b, args| {
        b.match_(args[0], list, |b, ctor, fields| {
            if ctor == nil {
                args[2]
            } else {
                let over = b.call(less_than, &[args[1], fields[0]]);
                b.match_(over, bool_, |b, ctor, _| {
                    if ctor == true_ {
                        args[2]
                    } else {
                        let next = b.con(succ, &[args[2]]);
                        b.call(index_over, &[fields[1], args[1], next])
                    }
                })
            }
        })
    });
    let walks = Walks {
        reverse,
        nat,
        list,
        zero,
        succ,
        nil,
        cons,
        add,
        bump,
        running,
        total,
        index_over,
    };
    (p, walks)
}

impl Walks {
    fn list_of(&self, program: &Program, values: &[u64]) -> Value {
        values
            .iter()
            .rev()
            .fold(Value(self.nil, vec![]), |rest, &n| {
                Value(
                    self.cons,
                    vec![super::tests::nat(program, self.nat, n), rest],
                )
            })
    }
}

/// Every function a body calls, anywhere in it.
fn callees(program: &Program, id: FnId) -> Vec<FnId> {
    let mut found = vec![];
    let body = program.function(id).body().unwrap();
    let mut exprs: Vec<_> = program.bindings(body.bindings).to_vec();
    exprs.push(body.tail);
    while let Some(expr) = exprs.pop() {
        match program.expr(expr) {
            Expr::Call(called, _) => found.push(called),
            Expr::Match(_, arms) => {
                for arm in program.arms(arms) {
                    exprs.extend_from_slice(program.bindings(arm.body.bindings));
                    exprs.push(arm.body.tail);
                }
            }
            _ => {}
        }
    }
    found
}

/// A list built by one walk and read once by another is never built: the
/// two become one walk over what the first walks, and a chain of them
/// fuses a link at a time.
#[test]
fn a_list_built_and_walked_once_is_never_built() {
    let (mut p, w) = walks();
    // total(bump(xs [])) and index_over(running(bump(xs []) 0 []) 5 0).
    let summed = p.declare("summed", &[w.list], w.nat);
    p.define(summed, |b, args| {
        let empty = b.con(w.nil, &[]);
        let bumped = b.call(w.bump, &[args[0], empty]);
        let zero = b.con(w.zero, &[]);
        b.call(w.total, &[bumped, zero])
    });
    let five = p.intern_number(w.nat, 5).unwrap();
    let found = p.declare("found", &[w.list], w.nat);
    p.define(found, |b, args| {
        let empty = b.con(w.nil, &[]);
        let bumped = b.call(w.bump, &[args[0], empty]);
        let zero = b.con(w.zero, &[]);
        let more = b.con(w.nil, &[]);
        let sums = b.call(w.running, &[bumped, zero, more]);
        let five = b.known(five);
        b.call(w.index_over, &[sums, five, zero])
    });
    validate(&p).unwrap();
    let original = p.clone();
    super::fuse::fuse(&mut p);
    validate(&p).unwrap();
    for id in [summed, found] {
        let called = callees(&p, id);
        assert_eq!(called.len(), 1, "one walk, not {called:?}");
        let name = p.name(p.function(called[0]).name);
        assert!(name.starts_with("bump+"), "{name}");
        for values in [&[][..], &[0], &[1, 2, 3], &[4, 0, 9, 1]] {
            let args = vec![w.list_of(&original, values)];
            let expected = run(&original, id, args.clone(), &mut vec![]);
            assert_eq!(run(&p, id, args, &mut vec![]), expected, "{values:?}");
        }
    }
    // The chain became one walk doing all three steps.
    let chained = callees(&p, found)[0];
    assert_eq!(p.name(p.function(chained).name), "bump+running+index_over");
}

/// A list read twice is built once and read twice: fusing it into one
/// reader would leave the other nothing to read.
#[test]
fn a_list_read_twice_is_built() {
    let (mut p, w) = walks();
    let twice = p.declare("twice", &[w.list], w.nat);
    p.define(twice, |b, args| {
        let empty = b.con(w.nil, &[]);
        let bumped = b.call(w.bump, &[args[0], empty]);
        let zero = b.con(w.zero, &[]);
        let first = b.call(w.total, &[bumped, zero]);
        let second = b.call(w.total, &[bumped, zero]);
        b.call(w.add, &[first, second])
    });
    super::fuse::fuse(&mut p);
    validate(&p).unwrap();
    assert!(callees(&p, twice).contains(&w.bump));
}

/// A walk reaching something outside may do something while it walks, so
/// what it does is neither interleaved with another walk nor cut short.
#[test]
fn a_walk_reaching_a_bodyless_call_is_not_fused() {
    let (mut p, w) = walks();
    let effect = p.declare("effect!", &[w.nat], w.nat);
    let noisy = p.declare("noisy", &[w.list, w.nat], w.nat);
    p.define(noisy, |b, args| {
        b.match_(args[0], w.list, |b, ctor, fields| {
            if ctor == w.nil {
                args[1]
            } else {
                let said = b.call(effect, &[fields[0]]);
                let sum = b.call(w.add, &[args[1], said]);
                b.call(noisy, &[fields[1], sum])
            }
        })
    });
    let main = p.declare("main", &[w.list], w.nat);
    p.define(main, |b, args| {
        let empty = b.con(w.nil, &[]);
        let bumped = b.call(w.bump, &[args[0], empty]);
        let zero = b.con(w.zero, &[]);
        b.call(noisy, &[bumped, zero])
    });
    super::fuse::fuse(&mut p);
    validate(&p).unwrap();
    assert!(callees(&p, main).contains(&w.bump));
}

/// A definition taking two numbers down together until one is nought is
/// what its base cases answer for the two differences, and calls itself no
/// more; a caller may then take it in whole.
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "two definitions of the shape, rewritten and compared on every small pair"
)]
fn a_descent_of_two_numbers_is_their_differences() {
    let library = super::fixture::Library::new();
    let (nat, zero, succ, bool_) = (library.nat, library.zero, library.succ, library.bool_);
    let (false_, true_) = (library.false_, library.true_);
    let mut p = library.program;
    // at_most(a, b): whether a <= b, by taking both down.
    let at_most = p.declare("at_most", &[nat, nat], bool_);
    p.define(at_most, |b, args| {
        b.match_(args[0], nat, |b, ctor, fields| {
            if ctor == zero {
                b.con(true_, &[])
            } else {
                let x = fields[0];
                b.match_(args[1], nat, |b, ctor, fields| {
                    if ctor == zero {
                        b.con(false_, &[])
                    } else {
                        b.call(at_most, &[x, fields[0]])
                    }
                })
            }
        })
    });
    // gap(a, b): b - a where a <= b, and a - b past it, plus one.
    let gap = p.declare("gap", &[nat, nat], nat);
    p.define(gap, |b, args| {
        b.match_(args[0], nat, |b, ctor, fields| {
            if ctor == zero {
                args[1]
            } else {
                let x = fields[0];
                b.match_(args[1], nat, |b, ctor, fields| {
                    if ctor == zero {
                        b.con(succ, &[x])
                    } else {
                        b.call(gap, &[x, fields[0]])
                    }
                })
            }
        })
    });
    validate(&p).unwrap();
    let original = p.clone();
    super::descent::descend(&mut p);
    validate(&p).unwrap();
    for id in [at_most, gap] {
        assert!(!callees(&p, id).contains(&id), "no longer calls itself");
        for a in 0..5 {
            for c in 0..5 {
                let args = vec![super::tests::nat(&p, nat, a), super::tests::nat(&p, nat, c)];
                let expected = run(&original, id, args.clone(), &mut vec![]);
                assert_eq!(run(&p, id, args, &mut vec![]), expected, "({a} {c})");
            }
        }
    }
}

/// A match on a value written as a constructor takes that constructor's
/// arm, and one whose arms bind nothing and say the same is that arm.
#[test]
fn a_decided_match_is_its_arm() {
    let library = super::fixture::Library::new();
    let (nat, zero, succ) = (library.nat, library.zero, library.succ);
    let (bool_, add) = (library.bool_, library.add);
    let mut p = library.program;
    let decided = p.declare("decided", &[nat, bool_], nat);
    p.define(decided, |b, args| {
        let one = b.con(zero, &[]);
        let one = b.con(succ, &[one]);
        // Known to be a step: its arm, with the field that built it.
        let known = b.match_(one, nat, |b, ctor, fields| {
            if ctor == zero {
                b.con(zero, &[])
            } else {
                b.call(add, &[fields[0], args[0]])
            }
        });
        // Either way the same.
        b.match_(args[1], bool_, |b, _, _| b.call(add, &[known, known]))
    });
    validate(&p).unwrap();
    let original = p.clone();
    super::structural(&mut p);
    validate(&p).unwrap();
    let body = p.function(decided).body().unwrap();
    let mut exprs: Vec<_> = p.bindings(body.bindings).to_vec();
    exprs.push(body.tail);
    assert!(
        exprs
            .iter()
            .all(|&expr| !matches!(p.expr(expr), Expr::Match(..))),
        "{}",
        p.render()
    );
    for n in 0..3 {
        for flag in [0, 1] {
            let flag = Value(p.ctor_at(bool_, flag), vec![]);
            let args = vec![super::tests::nat(&p, nat, n), flag];
            let expected = run(&original, decided, args.clone(), &mut vec![]);
            assert_eq!(run(&p, decided, args, &mut vec![]), expected);
        }
    }
}

/// A reversal onto another list, and a reversal of one onto nothing
/// reversed again, are recognized by their equations: what a buffer does
/// in one step. A walk doing anything else to what it moves is neither.
#[test]
fn reversals_and_prepends_are_recognized() {
    let (mut p, w) = walks();
    let extend = p.declare("extend", &[w.list, w.list], w.list);
    p.define(extend, |b, args| {
        let empty = b.con(w.nil, &[]);
        let reversed = b.call(w.reverse, &[args[0], empty]);
        b.call(w.reverse, &[reversed, args[1]])
    });
    let recognised = p.recognised().clone();
    let of = |id: FnId| recognised.sequences[id.index()];
    assert_eq!(of(w.reverse), Some(super::SequenceOperation::ReverseOnto));
    assert_eq!(of(extend), Some(super::SequenceOperation::Prepend));
    assert_eq!(of(w.bump), None);
    assert_eq!(of(w.total), None);
}

/// A walk rebuilding a list's front with the element a count reaches
/// replaced is recognized as one element written over. One that writes
/// anything but the value it was handed is not.
#[test]
fn replacements_are_recognized() {
    let (mut p, w) = walks();
    let replace = |p: &mut Program, name: &str, bumped: bool| {
        let id = p.declare(name, &[w.list, w.nat, w.nat], w.list);
        p.define(id, |b, args| {
            b.match_(args[0], w.list, |b, ctor, fields| {
                if ctor == w.nil {
                    return b.con(w.nil, &[]);
                }
                let (head, rest) = (fields[0], fields[1]);
                b.match_(args[1], w.nat, |b, ctor, fewer| {
                    if ctor == w.zero {
                        let value = if bumped {
                            b.con(w.succ, &[args[2]])
                        } else {
                            args[2]
                        };
                        b.con(w.cons, &[value, rest])
                    } else {
                        let later = b.call(id, &[rest, fewer[0], args[2]]);
                        b.con(w.cons, &[head, later])
                    }
                })
            })
        });
        id
    };
    let put = replace(&mut p, "put", false);
    let bumped = replace(&mut p, "bumped", true);
    validate(&p).unwrap();
    let recognised = p.recognised().clone();
    let of = |id: FnId| recognised.sequences[id.index()];
    assert_eq!(of(put), Some(super::SequenceOperation::Replace));
    assert_eq!(of(bumped), None);
}

/// A list reversed onto nothing and read once, by a reversal onto another,
/// is never built: the two are one prepend in order.
#[test]
fn a_list_reversed_twice_is_prepended() {
    let (mut p, w) = walks();
    let joined = p.declare("joined", &[w.list, w.list], w.nat);
    p.define(joined, |b, args| {
        let empty = b.con(w.nil, &[]);
        let reversed = b.call(w.reverse, &[args[0], empty]);
        let both = b.call(w.reverse, &[reversed, args[1]]);
        let zero = b.con(w.zero, &[]);
        b.call(w.index_over, &[both, zero, zero])
    });
    validate(&p).unwrap();
    let original = p.clone();
    super::fuse::fuse(&mut p);
    validate(&p).unwrap();
    let called = callees(&p, joined);
    assert!(!called.contains(&w.reverse), "{}", p.render());
    let recognised = p.recognised().clone();
    assert!(called.iter().any(|&id| {
        recognised.sequences[id.index()] == Some(super::SequenceOperation::Prepend)
    }));
    for (left, right) in [(&[][..], &[][..]), (&[0, 0, 3], &[5]), (&[0], &[0, 0, 2])] {
        let args = vec![w.list_of(&original, left), w.list_of(&original, right)];
        let expected = run(&original, joined, args.clone(), &mut vec![]);
        assert_eq!(
            run(&p, joined, args, &mut vec![]),
            expected,
            "{left:?} {right:?}"
        );
    }
}
