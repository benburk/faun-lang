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
            Value(Carried::One(Class::fixed(17))),
            Never,
            Value(Carried::One(Class::fixed(9))),
            Value(Carried::One(Class::fixed(1))),
            Value(Carried::One(Class::fixed(0))),
        ],
        (0..128)
            .map(|at| match at % 3 {
                0 => Never,
                1 => Value(Carried::One(Class::Natural)),
                _ => Value(Carried::One(Class::fixed(8))),
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
fn payload_sums_hold_their_products_flat() {
    for reaching in [false, true] {
        let mut source = barb::Program::default();
        let nat = source.declare_type("Nat");
        source.define_type(nat, &[("Zero", &[]), ("Succ", &[nat])]);
        let pair = source.declare_type("Pair");
        source.define_type(pair, &[("Pair", &[nat, nat])]);
        let pair_ctor = source.ctor_at(pair, 0);
        // One reaching itself through its fields has no bound on its size,
        // so it is a cell; one that does not is a tagged union. Reaching
        // itself twice keeps it from being a sequence.
        let maybe = source.declare_type("MaybePair");
        if reaching {
            source.define_type(maybe, &[("None", &[]), ("Some", &[pair, maybe, maybe])]);
        } else {
            source.define_type(maybe, &[("None", &[]), ("Some", &[pair])]);
        }
        let (none, some) = (source.ctor_at(maybe, 0), source.ctor_at(maybe, 1));
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
            let some = if reaching {
                let rest = b.con(none, &[]);
                b.con(some, &[pair, rest, rest])
            } else {
                b.con(some, &[pair])
            };
            b.call(value, &[some])
        });
        let main = source.declare("main", &[], nat);
        source.define(main, |b, _| {
            b.call(run, &[]);
            // `value` is handed both, so which one it is is asked.
            let none = b.con(none, &[]);
            b.call(value, &[none]);
            b.known(zero)
        });
        source.set_entry(main);

        let machine = lower(&source, &Routines::builtin().with_word(64)).unwrap();
        // `Some`'s pair is laid inline as two leaves, and nothing projects a
        // pair back out as a cell of its own.
        let built: Vec<_> = machine
            .ops
            .iter()
            .filter_map(|op| match *op {
                Op::Cell { fields, .. } => Some(fields.len()),
                _ => None,
            })
            .collect();
        let (tag, field) = (
            machine
                .ops
                .iter()
                .any(|op| matches!(op, Op::CellTag { .. })),
            machine
                .ops
                .iter()
                .any(|op| matches!(op, Op::CellField { .. })),
        );
        if reaching {
            // The rest and `main`'s `None` are built too, holding nothing.
            assert_eq!(built, [0, 4, 0], "{}", machine.render());
            assert!(tag && field, "{}", machine.render());
        } else {
            // The tag and the pair's two leaves, and no object at all.
            assert!(built.is_empty(), "{}", machine.render());
            assert!(!tag && !field, "{}", machine.render());
            let value = machine
                .functions()
                .iter()
                .find(|function| machine.name(function.name) == "value")
                .unwrap();
            assert_eq!(machine.signature(value.params).len(), 3);
        }
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
}

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
    // Asked with authority, which carries nothing here.
    let read = source.declare("read_byte!", &[unit], choice);
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
        let authority = b.con(unit_ctor, &[]);
        let outer = b.call(read, &[authority]);
        let inner = b.call(read, &[authority]);
        let unit = b.con(unit_ctor, &[]);
        b.call(select, &[outer, inner, unit])
    });
    source.set_entry(main);
    lower(&source, &Routines::builtin().with_word(64)).unwrap()
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
    let facts = source.analyze();
    let demand = Demand::discover(&source, &facts, &Routines::default(), entry).unwrap();
    let lowering = Lowering {
        native_inline_bytes: false,
        barb: &source,
        facts: &facts,
        carries: demand.carries,
        leaves: demand.leaves,
        takes: demand.takes,
        callees: vec![],
        refused: std::cell::RefCell::default(),
        looping: std::cell::RefCell::default(),
        round: std::cell::RefCell::default(),
        onward: std::cell::RefCell::default(),
        arguments: None,
    };
    let body = source.function(entry).body().unwrap();
    let word = Some(Carried::One(Class::Word));
    let mut carried = vec![word, None];
    assert_eq!(lowering.body_answer(body, &mut carried), Answer::Nothing);
    assert_eq!(carried, [word, None]);
    let barb::Expr::Match(_, arms) = source.expr(body.tail) else {
        panic!("a match");
    };
    for (arm, expected) in source
        .arms(arms)
        .iter()
        .zip([Answer::Never, Answer::Nothing])
    {
        assert_eq!(lowering.body_answer(arm.body, &mut carried), expected);
        assert_eq!(carried, [word, None]);
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
    source.define_fields(record, &[("Record", &[barb::Field::of(nat).named("argc")])]);
    let record_ctor = source.ctor_at(record, 0);
    let host = source.declare_type("Host");
    source.define_type(host, &[("Host", &[record])]);
    let host_ctor = source.ctor_at(host, 0);
    let main = source.declare_named("main", &[("host", host)], nat);
    source.define(main, |b, args| {
        let input = b.match_(args[0], host, |b, _, fields| {
            b.match_(fields[0], record, |_, _, fields| fields[0])
        });
        let startup = b.con(record_ctor, &[input]);
        let rebuilt = b.con(host_ctor, &[startup]);
        b.match_(rebuilt, host, |b, _, fields| {
            b.match_(fields[0], record, |_, _, fields| fields[0])
        })
    });
    source.set_entry(main);
    barb::validate(&source).unwrap();

    // A target whose word is a byte hands the entry a byte-wide count.
    let machine = lower(&source, &Routines::builtin().with_word(8)).unwrap();
    let entry = machine.entry();
    assert_eq!(machine.parameter_name(entry, 0), "argc");
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
    let input = (0..42).fold(barb::Value(source.ctor_at(nat, 0), vec![]), |held, _| {
        barb::Value(source.ctor_at(nat, 1), vec![held])
    });
    let startup = barb::Value(source.ctor_at(record, 0), vec![input]);
    let known = source
        .intern(host, &barb::Value(source.ctor_at(host, 0), vec![startup]))
        .unwrap();
    let main = source.declare("main", &[], host);
    source.define(main, |b, _| b.known(known));
    source.set_entry(main);
    barb::validate(&source).unwrap();

    let machine = lower(&source, &Routines::default()).unwrap();
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

    let machine = lower(&source, &Routines::default()).unwrap();
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

    let machine = lower(&source, &Routines::default()).unwrap();
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
        authority: false,
        takes: vec![],
        returns: Returns::Never,
        built: None,
        consumes: false,
    });

    let machine = lower(&source, &routines).unwrap();
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
        authority: false,
        takes: vec![Takes::Scalar(Class::fixed(0))],
        returns: Returns::Never,
        built: None,
        consumes: false,
    });

    let machine = lower(&source, &routines).unwrap();
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

    let machine = lower(&source, &Routines::default()).unwrap();
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

/// The functions in a lowered program named `name`.
fn named(machine: &Program, name: &str) -> FunctionId {
    FunctionId::at(
        machine
            .functions()
            .iter()
            .position(|function| machine.name(function.name) == name)
            .unwrap_or_else(|| panic!("`{name}` is lowered")),
    )
}

fn run(machine: &Program, function: FunctionId) -> Vec<BigUint> {
    evaluate::evaluate(
        machine,
        function,
        &[],
        evaluate::Config::default(),
        &mut evaluate::RejectHost,
    )
    .unwrap()
    .returned()
    .unwrap()
    .to_vec()
}

/// A product is its fields' values: a call takes and answers one machine
/// value per leaf, nested products included, and nothing is built.
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "one fixture covers nested construction, matching, calls, and evaluation"
)]
fn products_are_held_flat_across_calls_and_nesting() {
    let mut source = barb::Program::default();
    let nat = source.declare_type("Nat");
    source.define_type(nat, &[("Zero", &[]), ("Succ", &[nat])]);
    let flag = source.declare_type("Flag");
    source.define_type(flag, &[("Off", &[]), ("On", &[])]);
    let pair = source.declare_type("Pair");
    source.define_type(pair, &[("Pair", &[nat, flag])]);
    let pair_ctor = source.ctor_at(pair, 0);
    let triple = source.declare_type("Triple");
    source.define_type(triple, &[("Triple", &[pair, nat])]);
    let triple_ctor = source.ctor_at(triple, 0);
    let on = source.ctor_at(flag, 1);
    let seven = source.intern_number(nat, 7).unwrap();
    let five = source.intern_number(nat, 5).unwrap();

    // rotate(Triple(Pair(a, f), b)) -> Triple(Pair(b, f), a)
    let rotate = source.declare("rotate", &[triple], triple);
    source.define(rotate, |b, args| {
        b.match_(args[0], triple, |b, _, fields| {
            let (inner, last) = (fields[0], fields[1]);
            b.match_(inner, pair, |b, _, fields| {
                let pair = b.con(pair_ctor, &[last, fields[1]]);
                b.con(triple_ctor, &[pair, fields[0]])
            })
        })
    });
    let first = source.declare("first", &[triple], nat);
    source.define(first, |b, args| {
        b.match_(args[0], triple, |b, _, fields| {
            b.match_(fields[0], pair, |_, _, fields| fields[0])
        })
    });
    let run_it = source.declare("run", &[], nat);
    source.define(run_it, |b, _| {
        let (seven, five) = (b.known(seven), b.known(five));
        let on = b.con(on, &[]);
        let pair = b.con(pair_ctor, &[seven, on]);
        let held = b.con(triple_ctor, &[pair, five]);
        let turned = b.call(rotate, &[held]);
        b.call(first, &[turned])
    });
    let nought = source.intern_number(nat, 0).unwrap();
    let main = source.declare("main", &[], nat);
    source.define(main, |b, _| {
        b.call(run_it, &[]);
        b.known(nought)
    });
    source.set_entry(main);

    let machine = lower(&source, &Routines::builtin().with_word(64)).unwrap();
    assert!(
        !machine
            .ops
            .iter()
            .any(|op| matches!(op, Op::Cell { .. } | Op::CellField { .. })),
        "{}",
        machine.render()
    );
    let rotate = named(&machine, "rotate");
    // Both counts are only ever five or seven, and the flag is only `On`.
    let count = Class::Held(barb::Bounds {
        low: 5,
        high: Some(7),
    });
    let leaves = [count, Class::Held(barb::Bounds::at(1)), count];
    assert_eq!(machine.signature(machine.function(rotate).params), leaves);
    assert_eq!(
        machine.signature(machine.function(rotate).returns.classes()),
        leaves
    );
    assert_eq!(run(&machine, named(&machine, "run")), [BigUint::from(5u8)]);
}

/// A product with more leaves than a flat one may have is a cell, and so is
/// one that holds itself through products alone.
#[test]
fn wide_and_self_holding_products_are_cells() {
    let mut source = barb::Program::default();
    let nat = source.declare_type("Nat");
    source.define_type(nat, &[("Zero", &[]), ("Succ", &[nat])]);
    let wide = source.declare_type("Wide");
    let fields = vec![nat; FLAT_LEAVES + 1];
    source.define_type(wide, &[("Wide", &fields)]);
    let fits = source.declare_type("Fits");
    source.define_type(fits, &[("Fits", &fields[1..])]);
    let knot = source.declare_type("Knot");
    source.define_type(knot, &[("Knot", &[knot, nat])]);
    let zero = source.ctor_at(nat, 0);
    let nought = source.intern_number(nat, 0).unwrap();
    let main = source.declare_named(
        "main",
        &[("wide", wide), ("fits", fits), ("knot", knot)],
        nat,
    );
    source.define(main, |b, args| {
        let a = b.match_(args[0], wide, |_, _, fields| fields[0]);
        let c = b.match_(args[1], fits, |_, _, fields| fields[0]);
        let d = b.match_(args[2], knot, |_, _, fields| fields[1]);
        b.match_(a, nat, |_, ctor, _| if ctor == zero { c } else { d });
        b.known(nought)
    });
    source.set_entry(main);
    barb::validate(&source).unwrap();

    let machine = lower(&source, &Routines::default()).unwrap();
    let mut expected = vec![Class::Cell];
    expected.extend(vec![Class::Natural; FLAT_LEAVES]);
    expected.push(Class::Cell);
    assert_eq!(
        machine.signature(machine.function(machine.entry()).params),
        expected
    );
    assert_eq!(
        machine.parameter_names(machine.entry()).nth(1),
        Some("fits.0")
    );
}

/// A product built into a known value counts as built: its fields are as
/// wide as the constant's, not only as the ones the program works out.
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "one fixture declares its types, builds its values, and checks facts and evaluation"
)]
fn a_constant_holding_a_product_widens_its_fields() {
    let mut source = barb::Program::default();
    let nat = source.declare_type("Nat");
    source.define_type(nat, &[("Zero", &[]), ("Succ", &[nat])]);
    let (zero, succ) = (source.ctor_at(nat, 0), source.ctor_at(nat, 1));
    let pair = source.declare_type("Pair");
    source.define_type(pair, &[("Pair", &[nat, nat])]);
    let pair_ctor = source.ctor_at(pair, 0);
    let maybe = source.declare_type("Maybe");
    source.define_type(maybe, &[("None", &[]), ("Some", &[pair])]);
    let some = source.ctor_at(maybe, 1);
    let number = |n: u64| {
        (0..n).fold(barb::Value(zero, vec![]), |held, _| {
            barb::Value(succ, vec![held])
        })
    };
    let known = source
        .intern(
            maybe,
            &barb::Value(
                some,
                vec![barb::Value(pair_ctor, vec![number(200), number(1)])],
            ),
        )
        .unwrap();
    let nought = source.intern_number(nat, 0).unwrap();

    let first = source.declare("first", &[maybe], nat);
    source.define(first, |b, args| {
        b.match_(args[0], maybe, |b, ctor, fields| {
            if ctor == some {
                b.match_(fields[0], pair, |_, _, fields| fields[0])
            } else {
                b.known(nought)
            }
        })
    });
    let run_it = source.declare("run", &[], nat);
    source.define(run_it, |b, _| {
        let zero = b.known(nought);
        let made = b.con(pair_ctor, &[zero, zero]);
        let made = b.con(some, &[made]);
        b.call(first, &[made]);
        let known = b.known(known);
        b.call(first, &[known])
    });
    let main = source.declare("main", &[], nat);
    source.define(main, |b, _| {
        b.call(run_it, &[]);
        b.known(nought)
    });
    source.set_entry(main);

    let facts = source.analyze();
    assert_eq!(
        facts.field(&source, pair_ctor, 0),
        barb::Bounds {
            low: 0,
            high: Some(200)
        }
    );
    let machine = lower(&source, &Routines::builtin().with_word(64)).unwrap();
    assert_eq!(
        run(&machine, named(&machine, "run")),
        [BigUint::from(200u8)]
    );
}

/// A field carried round a recursion grows each time round, so what it can
/// hold is only known once the walk stops going round: reading it back is
/// never narrower than the last value put there.
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "one fixture declares its types, builds its values, and checks facts and evaluation"
)]
fn a_product_field_grown_by_recursion_is_held_whole() {
    let mut source = barb::Program::default();
    let nat = source.declare_type("Nat");
    source.define_type(nat, &[("Zero", &[]), ("Succ", &[nat])]);
    let (zero, succ) = (source.ctor_at(nat, 0), source.ctor_at(nat, 1));
    let state = source.declare_type("State");
    source.define_type(state, &[("S", &[nat, nat])]);
    let s = source.ctor_at(state, 0);
    let steps = source.intern_number(nat, 20).unwrap();
    let nought = source.intern_number(nat, 0).unwrap();

    let bump = source.declare("bump", &[state], state);
    source.define(bump, |b, args| {
        b.match_(args[0], state, |b, _, fields| {
            let once = b.con(succ, &[fields[1]]);
            let twice = b.con(succ, &[once]);
            b.con(s, &[fields[0], twice])
        })
    });
    let go = source.declare("go", &[nat, state], nat);
    source.define(go, |b, args| {
        b.match_(args[0], nat, |b, ctor, fields| {
            if ctor == zero {
                b.match_(args[1], state, |_, _, fields| fields[1])
            } else {
                let bumped = b.call(bump, &[args[1]]);
                b.call(go, &[fields[0], bumped])
            }
        })
    });
    let run_it = source.declare("run", &[], nat);
    source.define(run_it, |b, _| {
        let (steps, zero) = (b.known(steps), b.known(nought));
        let start = b.con(s, &[zero, zero]);
        b.call(go, &[steps, start])
    });
    let main = source.declare("main", &[], nat);
    source.define(main, |b, _| {
        b.call(run_it, &[]);
        b.known(nought)
    });
    source.set_entry(main);
    barb::validate(&source).unwrap();

    let facts = source.analyze();
    // The walk settles, and the total's field widened to anything on the
    // way; the count beside it stays nought.
    assert_eq!(facts.answers(main), barb::Bounds::at(0));
    assert_eq!(facts.field(&source, s, 1).width(), None);
    assert_eq!(facts.field(&source, s, 0), barb::Bounds::at(0));
    let machine = lower(&source, &Routines::builtin().with_word(64)).unwrap();
    assert_eq!(run(&machine, named(&machine, "run")), [BigUint::from(40u8)]);
}

/// A nominal string wraps its bytes, as Faun's `Str` wraps `List(U8)`, and
/// `write!` is handed the bytes inside: the wrapper is read through.
#[test]
fn a_wrapped_byte_string_is_handed_over_as_its_bytes() {
    let mut source = barb::Program::default();
    let host = source.declare_type("Host");
    source.define_type(host, &[("Host", &[])]);
    let unit = source.declare_type("Unit");
    source.define_type(unit, &[("Unit", &[])]);
    let nat = source.declare_type("Nat");
    source.define_type(nat, &[("Zero", &[]), ("Succ", &[nat])]);
    let list = source.declare_type("List");
    source.define_type(list, &[("Nil", &[]), ("Cons", &[nat, list])]);
    let text = source.declare_type("Str");
    source.define_type(text, &[("Str", &[list])]);
    let bytes = source.intern_byte_spine(list, b"hi\n").unwrap();
    let barb::ConstantView::Spine(spine) = source.constant(bytes).view() else {
        panic!("a spine");
    };
    let elements: Vec<_> = spine.to_bytes().unwrap();
    let number = |n: u8| {
        (0..n).fold(barb::Value(source.ctor_at(nat, 0), vec![]), |held, _| {
            barb::Value(source.ctor_at(nat, 1), vec![held])
        })
    };
    let listed = elements.iter().rev().fold(
        barb::Value(source.ctor_at(list, 0), vec![]),
        |rest, &byte| barb::Value(source.ctor_at(list, 1), vec![number(byte), rest]),
    );
    let greeting = source
        .intern(text, &barb::Value(source.ctor_at(text, 0), vec![listed]))
        .unwrap();
    let write = source.declare("write!", &[host, text], unit);
    let nought = source.intern_number(nat, 0).unwrap();
    let main = source.declare_named("main!", &[("host", host)], nat);
    source.define(main, |b, args| {
        let greeting = b.known(greeting);
        b.call(write, &[args[0], greeting]);
        b.known(nought)
    });
    source.set_entry(main);
    barb::validate(&source).unwrap();

    // The string is lowered as a value too, which nothing reads once the
    // call is handed its bytes, so only those are left.
    let machine = crate::ir::optimize(&lower(&source, &Routines::builtin()).unwrap());
    assert_eq!(machine.data(), b"hi\n");
}

/// An entry parameter held through a field named for a startup value is
/// named for that field, and is as wide as the target's startup table says,
/// though nothing in the program bounds it: the target supplies it by name.
#[test]
fn a_startup_field_names_and_bounds_what_the_entry_is_handed() {
    let mut library = barb::fixture::Library::new();
    let nat = library.nat;
    let p = &mut library.program;
    let host = p.declare_type("Host");
    let word = barb::Bounds {
        low: 0,
        high: Some(u64::from(u16::MAX)),
    };
    p.define_fields(host, &[("Host", &[barb::Field::of(nat).named("argc")])]);
    let never = p.declare_type("Never");
    p.define_type(never, &[]);
    let exit = p.declare("exit!", &[host, nat], never);
    let main = p.declare_named("main!", &[("host", host)], never);
    p.define(main, |b, args| {
        b.match_(args[0], host, |b, _, fields| {
            b.call(exit, &[args[0], fields[0]])
        })
    });
    p.set_entry(main);
    assert!(
        p.render().contains("Host = Host(argc: Nat)"),
        "{}",
        p.render()
    );

    let routines = Routines::builtin().with_word(16);
    let machine = crate::lower_to_machine_ir(&library.program, &routines).unwrap();
    let entry = machine.entry();
    assert_eq!(machine.parameter_names(entry).collect::<Vec<_>>(), ["argc"]);
    let body = machine.function(entry).body().unwrap();
    let argc = machine.values(machine.region(body).params)[0];
    assert_eq!(machine.class(argc), Class::Held(word));
}
