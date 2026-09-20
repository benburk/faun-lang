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
            Value(Class::Fixed { bits: 17 }),
            Never,
            Value(Class::Fixed { bits: 9 }),
            Value(Class::Fixed { bits: 1 }),
        ],
        (0..128)
            .map(|at| match at % 3 {
                0 => Never,
                1 => Value(Class::Natural),
                _ => Value(Class::Fixed { bits: 8 }),
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
    let read = source.declare("argc", &[], choice);
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
        assert_eq!(machine.class(result), Class::Fixed { bits });
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
        callees: vec![],
    };
    let body = source.function(entry).body().unwrap();
    let mut carried = vec![true, false];
    assert_eq!(lowering.body_answer(body, &mut carried), Answer::Nothing);
    assert_eq!(carried, [true, false]);
    let barb::Expr::Match(_, arms) = source.expr(body.tail) else {
        panic!("a match");
    };
    for (arm, expected) in source
        .arms(arms)
        .iter()
        .zip([Answer::Never, Answer::Nothing])
    {
        assert_eq!(lowering.body_answer(arm.body, &mut carried), expected);
        assert_eq!(carried, [true, false]);
    }
}
