use super::*;
use crate::ir::{Op, evaluate};
use num_bigint::BigUint;

#[test]
#[expect(
    clippy::too_many_lines,
    reason = "one case table comparing suffix joins against the old fold and counting body visits"
)]
fn tag_planning_visits_each_body_once_and_preserves_every_suffix_join() {
    use Answer::{Never, Nothing, Value};
    for answers in [
        vec![],
        vec![Never],
        vec![Never, Never, Never],
        vec![Nothing, Never, Nothing],
        vec![
            Value(Class::fixed(17)),
            Never,
            Value(Class::fixed(9)),
            Value(Class::fixed(1)),
            Value(Class::fixed(0)),
        ],
        (0..128)
            .map(|at| match at % 3 {
                0 => Never,
                1 => Value(Class::Natural),
                _ => Value(Class::fixed(8)),
            })
            .collect(),
    ] {
        let arms = (0..answers.len()).map(|at| barb::Arm {
            ctor: barb::CtorId::at(at),
            body: barb::Body {
                bindings: barb::Range::EMPTY,
                tail: barb::ExprId::at(at),
            },
        });
        let mut visits = 0;
        let plan = tag_plan(arms, |body| {
            visits += 1;
            answers[body.tail.index()]
        });
        assert_eq!(visits, answers.len());
        assert_eq!(plan.len(), answers.len());
        for (at, planned) in plan.iter().enumerate() {
            assert_eq!(planned.arm.ctor, barb::CtorId::at(at));
            // The old emission recomputed this left fold at every suffix.
            assert_eq!(
                planned.suffix,
                answers[at..].iter().copied().fold(Never, widest)
            );
        }
    }
}

#[test]
#[expect(
    clippy::too_many_lines,
    reason = "one fixture covers product construction, sum tags, projection, calls, and evaluation"
)]
fn products_and_payload_sums_cross_calls_and_matches_as_cells() {
    let mut source = barb::Program::default();
    let nat = source.declare_type("Nat");
    source.define_type(nat, &[("Zero", &[]), ("Succ", &[nat])]);
    let pair = source.declare_type("Pair");
    source.define_type(pair, &[("Pair", &[nat, nat])]);
    let pair_ctor = source.ctor_at(pair, 0);
    let maybe = source.declare_type("MaybePair");
    source.define_type(maybe, &[("None", &[]), ("Some", &[pair])]);
    let some = source.ctor_at(maybe, 1);
    let zero = source.intern_number(nat, 0).unwrap();
    let forty = source.intern_number(nat, 40).unwrap();
    let two = source.intern_number(nat, 2).unwrap();

    let second = source.declare("second", &[pair], nat);
    source.define(second, |b, args| {
        b.match_(args[0], pair, |_, _, fields| fields[1])
    });
    let value = source.declare("value", &[maybe], nat);
    source.define(value, |b, args| {
        b.match_(args[0], maybe, |b, ctor, fields| {
            if ctor == some {
                b.call(second, &[fields[0]])
            } else {
                b.known(zero)
            }
        })
    });
    let run = source.declare("run", &[], nat);
    source.define(run, |b, _| {
        let first = b.known(forty);
        let second = b.known(two);
        let pair = b.con(pair_ctor, &[first, second]);
        let some = b.con(some, &[pair]);
        b.call(value, &[some])
    });
    let main = source.declare("main", &[], nat);
    source.define(main, |b, _| {
        b.call(run, &[]);
        b.known(zero)
    });
    source.set_entry(main);

    let machine = lower(
        &source,
        &barb::analyze(&source),
        &Routines::builtin().with_word(64),
    )
    .unwrap();
    assert!(machine.ops.iter().any(|op| matches!(op, Op::Cell { .. })));
    assert!(
        machine
            .ops
            .iter()
            .any(|op| matches!(op, Op::CellTag { .. }))
    );
    assert!(
        machine
            .ops
            .iter()
            .any(|op| matches!(op, Op::CellField { .. }))
    );
    let run = FunctionId::at(
        machine
            .functions()
            .iter()
            .position(|function| machine.name(function.name) == "run")
            .unwrap(),
    );
    let result = evaluate::evaluate(
        &machine,
        run,
        &[],
        evaluate::Config::default(),
        &mut evaluate::RejectHost,
    )
    .unwrap();
    assert_eq!(result.returned().unwrap(), &[BigUint::from(2u8)]);
}

#[expect(
    clippy::too_many_lines,
    reason = "one nested-match fixture with erased locals and descending result widths"
)]
fn selection() -> Program {
    let mut source = barb::Program::default();
    let nat = source.declare_type("Nat");
    source.define_type(nat, &[("Zero", &[]), ("Succ", &[nat])]);
    let unit = source.declare_type("Unit");
    source.define_type(unit, &[("Unit", &[])]);
    let unit_ctor = source.ctor_at(unit, 0);
    let choice = source.declare_type("Choice");
    source.define_type(choice, &[("A", &[]), ("B", &[]), ("C", &[]), ("D", &[])]);
    let first = source.ctor_at(choice, 0).index();
    let values = [65536, 256, 1, 0].map(|n| source.intern_number(nat, n).unwrap());
    let read = source.declare("argc!", &[], choice);
    source.bound(
        read,
        barb::Bounds {
            low: 0,
            high: Some(3),
        },
    );
    let select = source.declare("select", &[choice, choice, unit], nat);
    source.define(select, |b, args| {
        b.match_(args[0], choice, |b, ctor, _| {
            let value = values[ctor.index() - first];
            let result = b.match_(args[1], choice, |b, ctor, _| {
                // Different sibling scopes leave different scratch-stack lengths.
                for _ in 0..=ctor.index() - first {
                    b.con(unit_ctor, &[]);
                }
                b.known(value)
            });
            b.con(unit_ctor, &[]);
            result // Read a local after the nested match, not merely its tail.
        })
    });
    let main = source.declare("main", &[], nat);
    source.define(main, |b, _| {
        let outer = b.call(read, &[]);
        let inner = b.call(read, &[]);
        let unit = b.con(unit_ctor, &[]);
        b.call(select, &[outer, inner, unit])
    });
    source.set_entry(main);
    lower(
        &source,
        &barb::analyze(&source),
        &Routines::builtin().with_word(64),
    )
    .unwrap()
}

#[test]
fn nested_tagged_matches_keep_narrow_suffixes_and_local_scopes() {
    let machine = selection();
    let select = FunctionId::at(
        machine
            .functions()
            .iter()
            .position(|f| machine.name(f.name) == "select")
            .unwrap(),
    );
    assert_eq!(
        machine.signature(machine.function(select).params).len(),
        2,
        "the unit parameter is erased"
    );
    let mut region = machine.function(select).body().unwrap();
    for bits in [17, 9, 1] {
        let (otherwise, result) = machine
            .walk(region)
            .find_map(|(op, results)| match op {
                Op::If { else_region, .. } => Some((*else_region, results[0])),
                _ => None,
            })
            .unwrap();
        assert_eq!(machine.class(result).width(), Some(bits));
        region = otherwise;
    }
    for (outer, expected) in [65536u32, 256, 1, 0].into_iter().enumerate() {
        for inner in 0u8..4 {
            let result = evaluate::evaluate(
                &machine,
                select,
                &[BigUint::from(outer), BigUint::from(inner)],
                evaluate::Config::default(),
                &mut evaluate::RejectHost,
            )
            .unwrap();
            assert_eq!(result.returned().unwrap(), &[BigUint::from(expected)]);
        }
    }
}

#[expect(
    clippy::too_many_lines,
    reason = "exercise scratch restoration after both a returning and a nonreturning arm"
)]
#[test]
fn answer_analysis_restores_locals_after_nonreturning_bindings() {
    let mut source = barb::Program::default();
    let unit = source.declare_type("Unit");
    source.define_type(unit, &[("Unit", &[])]);
    let ctor = source.ctor_at(unit, 0);
    let choice = source.declare_type("Choice");
    source.define_type(choice, &[("Stop", &[]), ("Return", &[])]);
    let never = source.declare_type("Never");
    source.define_type(never, &[]);
    let stop = source.declare("stop", &[], never);
    let first = source.ctor_at(choice, 0);
    let entry = source.declare("entry", &[choice, unit], unit);
    source.define(entry, |b, args| {
        b.match_(args[0], choice, |b, arm, _| {
            b.con(ctor, &[]);
            b.con(ctor, &[]);
            if arm == first {
                b.call(stop, &[]);
            }
            args[1]
        })
    });
    source.set_entry(entry);
    barb::validate(&source).unwrap();
    let facts = barb::analyze(&source);
    let demand = Demand::discover(&source, &facts, entry).unwrap();
    let lowering = Lowering {
        barb: &source,
        facts: &facts,
        carries: demand.carries,
        takes: demand.takes,
        callees: vec![],
        refused: std::cell::RefCell::default(),
    };
    let body = source.function(entry).body().unwrap();
    let mut carried = vec![Some(Class::Word), None];
    assert_eq!(lowering.body_answer(body, &mut carried), Answer::Nothing);
    assert_eq!(carried, [Some(Class::Word), None]);
    let barb::Expr::Match(_, arms) = source.expr(body.tail) else {
        panic!("a match");
    };
    for (arm, expected) in source
        .arms(arms)
        .iter()
        .zip([Answer::Never, Answer::Nothing])
    {
        assert_eq!(lowering.body_answer(arm.body, &mut carried), expected);
        assert_eq!(carried, [Some(Class::Word), None]);
    }
}

#[test]
#[expect(
    clippy::too_many_lines,
    reason = "the fixture covers nested construction, projection, bounds, and evaluation"
)]
fn one_field_products_are_transparent_through_machine_lowering() {
    let mut source = barb::Program::default();
    let nat = source.declare_type("Nat");
    source.define_type(nat, &[("Zero", &[]), ("Succ", &[nat])]);
    let record = source.declare_inline_type("{argc: Nat}");
    source.define_type(record, &[("Record", &[nat])]);
    let record_ctor = source.ctor_at(record, 0);
    let host = source.declare_type("Host");
    source.define_type(host, &[("Host", &[record])]);
    let host_ctor = source.ctor_at(host, 0);
    let main = source.declare_named("main", &[("host", host)], nat);
    source.bound_parameter(
        main,
        0,
        barb::Bounds {
            low: 0,
            high: Some(255),
        },
    );
    source.define(main, |b, args| {
        let argc = b.match_(args[0], host, |b, _, fields| {
            b.match_(fields[0], record, |_, _, fields| fields[0])
        });
        let startup = b.con(record_ctor, &[argc]);
        let rebuilt = b.con(host_ctor, &[startup]);
        b.match_(rebuilt, host, |b, _, fields| {
            b.match_(fields[0], record, |_, _, fields| fields[0])
        })
    });
    source.set_entry(main);
    barb::validate(&source).unwrap();

    let machine = lower(&source, &barb::analyze(&source), &Routines::default()).unwrap();
    let entry = machine.entry();
    assert_eq!(machine.parameter_name(entry, 0), "host");
    assert_eq!(
        machine.signature(machine.function(entry).params),
        [Class::fixed(8)]
    );
    assert_eq!(
        evaluate::evaluate(
            &machine,
            entry,
            &[BigUint::from(42u8)],
            evaluate::Config::default(),
            &mut evaluate::RejectHost,
        )
        .unwrap()
        .returned()
        .unwrap(),
        &[BigUint::from(42u8)]
    );
}

#[test]
fn known_one_field_products_lower_as_their_field() {
    let mut source = barb::Program::default();
    let nat = source.declare_type("Nat");
    source.define_type(nat, &[("Zero", &[]), ("Succ", &[nat])]);
    let record = source.declare_type("Record");
    source.define_type(record, &[("Record", &[nat])]);
    let host = source.declare_type("Host");
    source.define_type(host, &[("Host", &[record])]);
    let mut budget = barb::Budget::new(barb::FoldLimits::default());
    let argc = source.intern_number(nat, 42).unwrap();
    let startup = source
        .construct(source.ctor_at(record, 0), &[argc], &mut budget)
        .unwrap();
    let known = source
        .construct(source.ctor_at(host, 0), &[startup], &mut budget)
        .unwrap();
    let main = source.declare("main", &[], host);
    source.define(main, |b, _| b.known(known));
    source.set_entry(main);
    barb::validate(&source).unwrap();

    let machine = lower(&source, &barb::analyze(&source), &Routines::default()).unwrap();
    let result = evaluate::evaluate(
        &machine,
        machine.entry(),
        &[],
        evaluate::Config::default(),
        &mut evaluate::RejectHost,
    )
    .unwrap();
    assert_eq!(result.returned().unwrap(), &[BigUint::from(42u8)]);
}

#[test]
fn unused_parameters_do_not_demand_unsupported_representations() {
    let mut source = barb::Program::default();
    let nat = source.declare_type("Nat");
    source.define_type(nat, &[("Zero", &[]), ("Succ", &[nat])]);
    let pair = source.declare_type("Pair");
    source.define_type(pair, &[("Pair", &[nat, nat])]);
    let zero = source.ctor_at(nat, 0);
    let main = source.declare_named("main", &[("unused", pair)], nat);
    source.define(main, |b, _| b.con(zero, &[]));
    source.set_entry(main);
    barb::validate(&source).unwrap();

    let machine = lower(&source, &barb::analyze(&source), &Routines::default()).unwrap();
    assert!(
        machine
            .signature(machine.function(machine.entry()).params)
            .is_empty()
    );
}

#[test]
fn parameters_read_only_in_impossible_arms_are_unused() {
    let mut source = barb::Program::default();
    let nat = source.declare_type("Nat");
    source.define_type(nat, &[("Zero", &[]), ("Succ", &[nat])]);
    let zero = source.ctor_at(nat, 0);
    let choice = source.declare_type("Choice");
    source.define_type(choice, &[("Chosen", &[]), ("Impossible", &[])]);
    let chosen = source.ctor_at(choice, 0);
    let main = source.declare_named("main", &[("impossible", nat)], nat);
    source.define(main, |b, args| {
        let scrutinee = b.con(chosen, &[]);
        b.match_(scrutinee, choice, |b, ctor, _| {
            if ctor == chosen {
                b.con(zero, &[])
            } else {
                args[0]
            }
        })
    });
    source.set_entry(main);
    barb::validate(&source).unwrap();

    let machine = lower(&source, &barb::analyze(&source), &Routines::default()).unwrap();
    assert!(
        machine
            .signature(machine.function(machine.entry()).params)
            .is_empty()
    );
}

#[test]
fn parameters_read_only_after_a_nonreturning_call_are_unused() {
    let mut source = barb::Program::default();
    let nat = source.declare_type("Nat");
    source.define_type(nat, &[("Zero", &[]), ("Succ", &[nat])]);
    let never = source.declare_type("Never");
    source.define_type(never, &[]);
    let stop = source.declare("stop", &[], never);
    let main = source.declare_named("main", &[("after", nat)], nat);
    source.define(main, |b, args| {
        b.call(stop, &[]);
        args[0]
    });
    source.set_entry(main);
    barb::validate(&source).unwrap();
    let mut routines = Routines::default();
    routines.push(Routine {
        name: "stop".to_owned(),
        offered: true,
        takes: vec![],
        returns: crate::platform::Returns::Never,
    });

    let machine = lower(&source, &barb::analyze(&source), &routines).unwrap();
    assert!(
        machine
            .signature(machine.function(machine.entry()).params)
            .is_empty()
    );
}

#[test]
fn external_parameter_names_survive_machine_lowering() {
    let mut source = barb::Program::default();
    let nat = source.declare_type("Nat");
    source.define_type(nat, &[("Zero", &[]), ("Succ", &[nat])]);
    let zero = source.ctor_at(nat, 0);
    let never = source.declare_type("Never");
    source.define_type(never, &[]);
    let stop = source.declare_named("stop", &[("status", nat)], never);
    let main = source.declare("main", &[], never);
    source.define(main, |b, _| {
        let status = b.con(zero, &[]);
        b.call(stop, &[status])
    });
    source.set_entry(main);
    barb::validate(&source).unwrap();
    let mut routines = Routines::default();
    routines.push(Routine {
        name: "stop".to_owned(),
        offered: true,
        takes: vec![Takes::Scalar(Class::fixed(0))],
        returns: crate::platform::Returns::Never,
    });

    let machine = lower(&source, &barb::analyze(&source), &routines).unwrap();
    let stop = machine
        .functions()
        .iter()
        .position(|function| machine.name(function.name) == "stop")
        .map(FunctionId::at)
        .unwrap();
    assert_eq!(
        machine.parameter_names(stop).collect::<Vec<_>>(),
        ["status"]
    );
}

#[test]
fn unused_parameters_leave_machine_signatures_and_calls_together() {
    let mut source = barb::Program::default();
    let nat = source.declare_type("Nat");
    source.define_type(nat, &[("Zero", &[]), ("Succ", &[nat])]);
    let zero = source.ctor_at(nat, 0);
    let keep = source.declare_named("keep", &[("kept", nat), ("ignored", nat)], nat);
    source.define(keep, |_, args| args[0]);
    let main = source.declare("main", &[], nat);
    source.define(main, |b, _| {
        let a = b.con(zero, &[]);
        let ignored = b.con(zero, &[]);
        b.call(keep, &[a, ignored])
    });
    source.set_entry(main);
    barb::validate(&source).unwrap();

    let facts = barb::analyze(&source);
    let machine = lower(&source, &facts, &Routines::default()).unwrap();
    let keep = machine
        .functions()
        .iter()
        .find(|function| machine.name(function.name) == "keep")
        .unwrap();
    assert_eq!(machine.signature(keep.params), [Class::fixed(0)]);
    assert_eq!(
        machine
            .parameter_names(FunctionId::at(1))
            .collect::<Vec<_>>(),
        ["kept"]
    );
}
