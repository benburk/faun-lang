use super::budget::Budget;
use super::constant::Held;
use super::evaluate::{CannotFold, Evaluator};

fn budget(work: u64) -> Budget {
    Budget::new(FoldLimits {
        work,
        max_depth: 512,
        ..FoldLimits::default()
    })
}
use super::*;
use num_bigint::BigUint;

/// The fixture's arithmetic, with an entry answering nought so the
/// program validates.
fn library() -> Program {
    let mut library = fixture::Library::new();
    let nought = library.number(0);
    let main = library.program.declare("main", &[], library.nat);
    library.program.define(main, |b, _| b.known(nought));
    library.program.set_entry(main);
    library.program
}

/// Which clause of the arithmetic [`variant`] writes wrongly.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Miss {
    Nothing,
    Div,
    Mod,
    Sub,
    Mul,
    Equals,
}

/// The fixture's arithmetic written again: renamed, with the number type
/// called `Count`, its successor and `Bool`'s `True` declared first and
/// addition called `plus`, and with the clause `miss` names written wrongly.
#[expect(
    clippy::too_many_lines,
    reason = "one definition per operation, as the fixture writes them"
)]
fn variant(renamed: bool, miss: Miss) -> Program {
    let mut p = Program::default();
    let nat = p.declare_type(if renamed { "Count" } else { "Nat" });
    let bool_ = p.declare_type("Bool");
    if renamed {
        p.define_type(nat, &[("Succ", &[nat]), ("Zero", &[])]);
        p.define_type(bool_, &[("True", &[]), ("False", &[])]);
    } else {
        p.define_type(nat, &[("Zero", &[]), ("Succ", &[nat])]);
        p.define_type(bool_, &[("False", &[]), ("True", &[])]);
    }
    let (zero, succ) = (named_ctor(&p, nat, "Zero"), named_ctor(&p, nat, "Succ"));
    let (false_, true_) = (
        named_ctor(&p, bool_, "False"),
        named_ctor(&p, bool_, "True"),
    );
    let two = [nat, nat];

    let add = p.declare(if renamed { "plus" } else { "add" }, &two, nat);
    p.define(add, |b, args| {
        b.match_(args[1], nat, |b, ctor, fields| {
            if ctor == zero {
                args[0]
            } else {
                let rest = b.call(add, &[args[0], fields[0]]);
                b.con(succ, &[rest])
            }
        })
    });
    let sub = p.declare("sub", &two, nat);
    p.define(sub, |b, args| {
        b.match_(args[0], nat, |b, ctor, left| {
            if ctor == zero {
                return if miss == Miss::Sub {
                    args[1]
                } else {
                    b.con(zero, &[])
                };
            }
            b.match_(args[1], nat, |b, ctor, right| {
                if ctor == zero {
                    b.con(succ, &[left[0]])
                } else {
                    b.call(sub, &[left[0], right[0]])
                }
            })
        })
    });
    let mul = p.declare("mul", &two, nat);
    p.define(mul, |b, args| {
        b.match_(args[1], nat, |b, ctor, fields| {
            if ctor != zero {
                let rest = b.call(mul, &[args[0], fields[0]]);
                b.call(add, &[args[0], rest])
            } else if miss == Miss::Mul {
                args[0]
            } else {
                b.con(zero, &[])
            }
        })
    });
    let equals = p.declare("equals", &two, bool_);
    p.define(equals, |b, args| {
        b.match_(args[0], nat, |b, ctor, left| {
            let left_zero = ctor == zero;
            b.match_(args[1], nat, |b, ctor, right| {
                match (left_zero, ctor == zero) {
                    (true, true) => b.con(true_, &[]),
                    (true, false) if miss == Miss::Equals => b.con(true_, &[]),
                    (true, false) | (false, true) => b.con(false_, &[]),
                    (false, false) => b.call(equals, &[left[0], right[0]]),
                }
            })
        })
    });
    let mod_step = p.declare("mod_step", &[bool_, nat], nat);
    p.define(mod_step, |b, args| {
        b.match_(args[0], bool_, |b, ctor, _| {
            if ctor == true_ {
                b.con(zero, &[])
            } else {
                b.con(succ, &[args[1]])
            }
        })
    });
    let modulo = p.declare("mod", &two, nat);
    p.define(modulo, |b, args| {
        b.match_(args[1], nat, |b, ctor, divisor| {
            if ctor == zero {
                return if miss == Miss::Mod {
                    b.con(zero, &[])
                } else {
                    args[0]
                };
            }
            b.match_(args[0], nat, |b, ctor, dividend| {
                if ctor == zero {
                    return b.con(zero, &[]);
                }
                let whole = b.con(succ, &[divisor[0]]);
                let r = b.call(modulo, &[dividend[0], whole]);
                let last = b.call(equals, &[r, divisor[0]]);
                b.call(mod_step, &[last, r])
            })
        })
    });
    let div_step = p.declare("div_step", &[bool_, nat], nat);
    p.define(div_step, |b, args| {
        b.match_(args[0], bool_, |b, ctor, _| {
            if ctor == true_ {
                b.con(succ, &[args[1]])
            } else {
                args[1]
            }
        })
    });
    let div = p.declare("div", &two, nat);
    p.define(div, |b, args| {
        b.match_(args[1], nat, |b, ctor, divisor| {
            if ctor == zero {
                return if miss == Miss::Div {
                    args[0]
                } else {
                    b.con(zero, &[])
                };
            }
            b.match_(args[0], nat, |b, ctor, dividend| {
                if ctor == zero {
                    return b.con(zero, &[]);
                }
                let whole = b.con(succ, &[divisor[0]]);
                let q = b.call(div, &[dividend[0], whole]);
                let whole = b.con(succ, &[divisor[0]]);
                let r = b.call(modulo, &[dividend[0], whole]);
                let last = b.call(equals, &[r, divisor[0]]);
                b.call(div_step, &[last, q])
            })
        })
    });
    let main = p.declare("main", &[], nat);
    p.define(main, |b, _| b.con(zero, &[]));
    p.set_entry(main);
    p
}

/// The constructor of `owner` called `name`, wherever it was declared.
fn named_ctor(program: &Program, owner: TypeId, name: &str) -> CtorId {
    let tag = program
        .ctors(owner)
        .iter()
        .position(|ctor| program.name(ctor.name) == name)
        .unwrap();
    program.ctor_at(owner, u32::try_from(tag).unwrap())
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
fn number(program: &Program, owner: TypeId, n: u64) -> Held {
    Held::number(program.type_info(), owner, &BigUint::from(n))
}

#[test]
fn library_equations_are_recognized_before_and_after_folding() {
    let mut program = library();
    validate(&program).unwrap();
    for _ in 0..2 {
        let facts = program.analyze();
        for (name, op) in [
            ("add", Operation::Add),
            ("sub", Operation::Monus),
            ("mul", Operation::Mul),
            ("div", Operation::Div),
            ("mod", Operation::Mod),
        ] {
            assert_eq!(
                facts.operation(named(&program, name)),
                Some(op),
                "{name}\n{}",
                program.render()
            );
        }
        assert!(matches!(
            facts.operation(named(&program, "equals")),
            Some(Operation::Equals { .. })
        ));
        assert!(matches!(
            facts.operation(named(&program, "less_than")),
            Some(Operation::LessThan { .. })
        ));
        fold(&mut program);
    }
}

#[test]
fn recognition_is_structural_and_zero_divisor_near_misses_are_not_operations() {
    let program = variant(true, Miss::Nothing);
    assert_eq!(
        program.analyze().operation(named(&program, "plus")),
        Some(Operation::Add)
    );
    assert_eq!(
        program.analyze().operation(named(&program, "mod")),
        Some(Operation::Mod)
    );
    let program = variant(false, Miss::Nothing);
    assert_eq!(
        program.analyze().operation(named(&program, "div")),
        Some(Operation::Div)
    );
    for (miss, name) in [
        (Miss::Div, "div"),
        (Miss::Mod, "mod"),
        (Miss::Sub, "sub"),
        (Miss::Mul, "mul"),
        (Miss::Equals, "equals"),
    ] {
        let program = variant(false, miss);
        validate(&program).unwrap();
        assert_eq!(
            program.analyze().operation(named(&program, name)),
            None,
            "{name}"
        );
    }
}

#[test]
fn structural_evaluation_matches_arithmetic_for_small_inputs() {
    let program = library();
    let operations = arithmetic::recognise(&program);
    let unknown = vec![None; program.functions().len()];
    for name in ["add", "sub", "mul", "div", "mod", "equals", "less_than"] {
        let id = named(&program, name);
        let ty = program.params(id)[0];
        for a in 0..12 {
            for b in 0..8 {
                let args = vec![Ok(number(&program, ty, a)), Ok(number(&program, ty, b))];
                let body = program.function(id).body().unwrap();
                let baseline = Evaluator {
                    program: &program,
                    operations: &unknown,
                }
                .body(body, args.clone(), &mut budget(1_000_000))
                .unwrap_or_else(|reason| panic!("baseline {name}({a}, {b}): {reason:?}"));
                // Evaluate a call so the recognized fast path is exercised at
                // the root too, including zero-divisor and comparison cases.
                let mut caller = program.clone();
                let test = caller.declare("test", &[ty, ty], caller.function(id).result);
                caller.define(test, |builder, args| builder.call(id, args));
                let mut ops = operations.clone();
                ops.push(None);
                let fast = Evaluator {
                    program: &caller,
                    operations: &ops,
                }
                .body(
                    caller.function(test).body().unwrap(),
                    args,
                    &mut budget(1000),
                )
                .unwrap();
                assert_eq!(baseline.owner(), fast.owner());
                assert_eq!(baseline.encoded(), fast.encoded(), "{name}({a}, {b})");
            }
        }
    }
}

#[test]
fn folded_values_are_not_limited_to_u64() {
    let mut program = library();
    let mul = named(&program, "mul");
    let ty = program.params(mul)[0];
    let n = BigUint::from(1u8) << 100usize;
    let value = program.intern_natural(ty, &n).unwrap();
    let test = program.declare("huge", &[], ty);
    program.define(test, |b, _| {
        let n = b.known(value);
        b.call(mul, &[n, n])
    });
    fold(&mut program);
    let Expr::Static(value) = program.expr(program.function(test).body().unwrap().tail) else {
        panic!("not folded")
    };
    let ConstantView::Natural(number) = program.constant(value).view() else {
        panic!("a natural");
    };
    assert_eq!(number.to_biguint(), &n * &n);
    assert_eq!(number.try_u64(), Err(TooWide));
    assert!(program.render().contains(&(&n * &n).to_string()));
}

#[test]
#[expect(
    clippy::too_many_lines,
    reason = "the guard, its entry and the lowering check are one program"
)]
fn an_early_exit_refines_the_continuation() {
    let routines = crate::platform::Routines::builtin();
    let mut library = fixture::Library::new();
    let two = library.number(2);
    let nought = library.number(0);
    let (nat, bool_, true_) = (library.nat, library.bool_, library.true_);
    let (add, less_than) = (library.add, library.less_than);
    let p = &mut library.program;
    let host = p.declare_type("Host");
    p.define_type(host, &[("Host", &[])]);
    let never = p.declare_type("Never");
    p.define_type(never, &[]);
    let exit = p.declare("exit!", &[host, nat], never);
    let input = p.declare("read_byte!", &[host], nat);
    // bounded!(h, True, n) -> n
    // bounded!(h, False, n) -> exit!(h, Zero)
    let bounded = p.declare("bounded!", &[host, bool_, nat], nat);
    p.define(bounded, |b, args| {
        b.match_(args[1], bool_, |b, ctor, _| {
            if ctor == true_ {
                args[2]
            } else {
                let nought = b.known(nought);
                b.call(exit, &[args[0], nought])
            }
        })
    });
    let main = p.declare_named("main!", &[("host", host)], never);
    p.define(main, |b, args| {
        let count = b.call(input, &[args[0]]);
        let two = b.known(two);
        let below = b.call(less_than, &[count, two]);
        let n = b.call(bounded, &[args[0], below, count]);
        let sum = b.call(add, &[n, n]);
        b.call(exit, &[args[0], sum])
    });
    p.set_entry(main);
    let mut program = library.program;
    validate(&program).unwrap();
    normalize_with_limits(&mut program, InlineLimits::default());
    fold(&mut program);
    let facts = program.analyze();
    let body = program.function(program.entry().unwrap()).body().unwrap();
    let sum = program.bindings(body.bindings).iter().copied().find(|expr| {
        matches!(program.expr(*expr), Expr::Call(called, _) if facts.operation(called) == Some(Operation::Add))
    }).expect("runtime addition");
    assert_eq!(
        facts.held(sum),
        Bounds {
            low: 0,
            high: Some(2)
        }
    );
    let machine = crate::ir::lower(&program, &routines).unwrap();
    assert!(
        (0..machine.values_count())
            .all(|at| machine.class(crate::ir::ValueId::at(at)) != crate::ir::Class::Natural)
    );
}

#[test]
fn unrecognized_recursion_still_has_an_evaluation_budget() {
    let mut program = library();
    let nat = program.params(named(&program, "add"))[0];
    let zero = program.ctor_at(nat, 0);
    // count(Zero) -> Zero
    // count(Succ(n)) -> count(n)
    let id = program.declare("count", &[nat], nat);
    program.define(id, |b, args| {
        b.match_(args[0], nat, |b, ctor, fields| {
            if ctor == zero {
                b.con(zero, &[])
            } else {
                b.call(id, &[fields[0]])
            }
        })
    });
    let ty = program.params(id)[0];
    let operations = arithmetic::recognise(&program);
    assert_eq!(operations[id.index()], None);
    let result = Evaluator {
        program: &program,
        operations: &operations,
    }
    .body(
        program.function(id).body().unwrap(),
        vec![Ok(number(&program, ty, 1_000_000))],
        &mut budget(32),
    );
    assert_eq!(result.unwrap_err(), CannotFold::Limit(LimitExceeded::Work));
}

#[test]
fn range_propagation_observes_earlier_answers_in_the_same_round() {
    let (mut program, nat, _, _) = tests::types();
    let seven = program.intern_number(nat, 7).unwrap();
    let first = program.declare("first", &[], nat);
    program.define(first, |b, _| b.known(seven));
    let mut previous = first;
    // Longer than the round limit: moving the snapshot to a whole round
    // would lose precision here. Each walk reads the current result table.
    let mut chain = vec![first];
    for at in 0..64 {
        let id = program.declare(&format!("forward_{at}"), &[], nat);
        program.define(id, |b, _| b.call(previous, &[]));
        chain.push(id);
        previous = id;
    }
    program.set_entry(previous);
    validate(&program).unwrap();
    let facts = program.analyze();
    for id in chain {
        assert_eq!(facts.answers(id), Bounds::at(7));
    }
}

#[test]
#[expect(
    clippy::too_many_lines,
    reason = "every operation's bounds against every small answer, in one table"
)]
fn arithmetic_interval_bounds_contain_every_small_answer() {
    for a0 in 0..5 {
        for a1 in a0..6 {
            for b0 in 0..5 {
                for b1 in b0..6 {
                    let a = Bounds {
                        low: a0,
                        high: Some(a1),
                    };
                    let b = Bounds {
                        low: b0,
                        high: Some(b1),
                    };
                    for (op, bounds) in [
                        (Operation::Add, a.plus(b)),
                        (Operation::Monus, a.monus(b)),
                        (Operation::Mul, a.times(b)),
                        (Operation::Div, a.quotient(b)),
                        (Operation::Mod, a.remainder(b)),
                        (Operation::And, a.masked(b)),
                        (Operation::Or, a.merged(b, true)),
                        (Operation::Xor, a.merged(b, false)),
                        (Operation::Pow, a.power(b)),
                    ] {
                        for x in a0..=a1 {
                            for y in b0..=b1 {
                                let n = op.calculate(&BigUint::from(x), &BigUint::from(y)).unwrap();
                                assert!(n >= BigUint::from(bounds.low), "{op:?}: {a:?}, {b:?}");
                                assert!(
                                    bounds.high.is_none_or(|high| n <= BigUint::from(high)),
                                    "{op:?}: {a:?}, {b:?}"
                                );
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(Bounds::at(u64::MAX).plus(Bounds::at(1)).high, None);
    assert_eq!(Bounds::ANY.times(Bounds::at(0)), Bounds::at(0));
    assert_eq!(Bounds::ANY.remainder(Bounds::at(0)), Bounds::ANY);
    assert_eq!(Bounds::ANY.quotient(Bounds::at(0)), Bounds::at(0));
    assert_eq!(Bounds::at(0).merged(Bounds::at(0), true), Bounds::at(0));
    assert_eq!(
        Bounds::at(u64::MAX).merged(Bounds::at(1), true).high,
        Some(u64::MAX)
    );
    assert_eq!(Bounds::at(2).power(Bounds::at(64)).high, None);
    assert_eq!(Bounds::ANY.power(Bounds::at(0)).high, None);
    assert_eq!(Bounds::at(1).power(Bounds::ANY), Bounds::at(1));
}

/// A sum taken modulo a power of two is worked out modulo that power of two
/// throughout, which is how a number counting without a last step says a
/// machine word.
#[test]
fn a_sum_modulo_a_power_of_two_is_a_sum_of_remainders() {
    // One side reduced, added to itself, and that reduced: both sides being
    // the same side, one remainder of it does for both.
    let held = reduced(|b, t| {
        let sum = b.call(t.add, &[t.n, t.n]);
        b.call(t.modulo, &[sum, t.two_fifty_six])
    });
    assert_eq!(held.matches("mod(").count(), 2, "{held}");
    assert!(held.contains("add(v"), "{held}");

    // A side known before the program runs, and under the modulus, is
    // already every bit of itself the modulus keeps. Only the count takes a
    // remainder of its own; the constant is added as it stands, and wrapping
    // it in one would have the tier below reading a number widened to the
    // modulus and narrowed straight back.
    let held = reduced(|b, t| {
        let sum = b.call(t.add, &[t.n, t.four]);
        b.call(t.modulo, &[sum, t.two_fifty_six])
    });
    assert_eq!(held.matches("mod(").count(), 2, "{held}");
    assert!(held.contains("add(v"), "{held}");

    // Under it is what buys that, not being known: one as big as the modulus
    // loses something to it, so it takes a remainder like anything else.
    let held = reduced(|b, t| {
        let sum = b.call(t.add, &[t.n, t.sixteen]);
        b.call(t.modulo, &[sum, t.sixteen])
    });
    assert_eq!(held.matches("mod(").count(), 3, "{held}");
}

/// A product too, for the same reason.
#[test]
fn a_product_modulo_a_power_of_two_is_a_product_of_remainders() {
    let held = reduced(|b, t| {
        let product = b.call(t.mul, &[t.n, t.n]);
        b.call(t.modulo, &[product, t.two_fifty_six])
    });
    assert_eq!(held.matches("mod(").count(), 2, "{held}");
}

/// Not by anything else. Reducing each side first leaves three divisions
/// where there was one, and divides nothing away.
#[test]
fn a_sum_modulo_anything_else_is_left_as_it_stands() {
    let held = reduced(|b, t| {
        let sum = b.call(t.add, &[t.n, t.n]);
        b.call(t.modulo, &[sum, t.ten])
    });
    assert_eq!(held.matches("mod(").count(), 1, "{held}");
}

/// And not truncated subtraction, which stops at nought rather than
/// carrying through a remainder, nor the division or remainder themselves.
#[test]
fn only_what_carries_through_a_remainder_is_pushed_inside_one() {
    // Two different values, so that nothing collapses for being the same.
    let inner: [(&str, Pick); 3] = [
        ("sub", |t| t.sub),
        ("div", |t| t.div),
        ("mod", |t| t.modulo),
    ];
    for (held, operation) in inner {
        let rendered = reduced(|b, t| {
            let inside = b.call(operation(t), &[t.n, t.four]);
            b.call(t.modulo, &[inside, t.two_fifty_six])
        });
        let wanted = usize::from(held == "mod") + 1;
        assert_eq!(
            rendered.matches("mod(").count(),
            wanted,
            "{held}: {rendered}"
        );
    }
}

/// What `main!` works out of the count it was handed, and the arithmetic
/// it may use: the count `n`, the constants it names, and the operations.
struct Terms {
    n: Atom,
    four: Atom,
    sixteen: Atom,
    two_fifty_six: Atom,
    ten: Atom,
    add: FnId,
    sub: FnId,
    mul: FnId,
    div: FnId,
    modulo: FnId,
}

/// Which of the operations in [`Terms`] to use.
type Pick = fn(&Terms) -> FnId;

/// `main!` as the optimizer leaves it, for a program exiting with what
/// `held` works out of the count it was handed.
#[expect(
    clippy::too_many_lines,
    reason = "the host, the constants and the operations `held` may use"
)]
fn reduced(held: impl FnOnce(&mut Builder<'_>, &Terms) -> Atom) -> String {
    let mut library = fixture::Library::new();
    let two = library.number(2);
    let nat = library.nat;
    let (add, sub, mul) = (library.add, library.sub, library.mul);
    let (div, modulo) = (library.div, library.modulo);
    let p = &mut library.program;
    let host = p.declare_type("Host");
    p.define_type(host, &[("Host", &[])]);
    let never = p.declare_type("Never");
    p.define_type(never, &[]);
    let exit = p.declare("exit!", &[host, nat], never);
    let input = p.declare("read_byte!", &[host], nat);
    let main = p.declare("main!", &[host], never);
    p.define(main, |b, args| {
        let n = b.call(input, &[args[0]]);
        let two = b.known(two);
        let four = b.call(mul, &[two, two]);
        let sixteen = b.call(mul, &[four, four]);
        let two_fifty_six = b.call(mul, &[sixteen, sixteen]);
        let six = b.call(add, &[four, two]);
        let ten = b.call(add, &[four, six]);
        let terms = Terms {
            n,
            four,
            sixteen,
            two_fifty_six,
            ten,
            add,
            sub,
            mul,
            div,
            modulo,
        };
        let status = held(b, &terms);
        b.call(exit, &[args[0], status])
    });
    p.set_entry(main);
    let mut program = library.program;
    validate(&program).unwrap();
    optimize(&mut program);
    let rendered = program.render();
    let (_, main) = rendered.split_once("main!(v0: Host)").expect("an entry");
    main.to_owned()
}

/// A field holds what was built into it: reading one back answers no more
/// than the values some construction put there.
#[test]
fn a_field_holds_what_was_built_into_it() {
    let mut program = Program::default();
    let order = program.declare_type("Order");
    program.define_type(order, &[("Lt", &[]), ("Eq", &[]), ("Gt", &[])]);
    let nat = program.declare_type("Nat");
    program.define_type(nat, &[("Zero", &[]), ("Succ", &[nat])]);
    let pair = program.declare_type("Pair");
    program.define_type(pair, &[("Pair", &[order, nat])]);
    let outcome = program.declare("outcome", &[pair], order);
    program.define(outcome, |b, args| {
        b.match_(args[0], pair, |_, _, fields| fields[0])
    });
    let count = program.declare("count", &[pair], nat);
    program.define(count, |b, args| {
        b.match_(args[0], pair, |_, _, fields| fields[1])
    });
    let (gt, zero) = (program.ctor_at(order, 2), program.ctor_at(nat, 0));
    let pair_ctor = program.ctor_at(pair, 0);
    let main = program.declare("main", &[], order);
    program.define(main, |b, _| {
        let fields = [b.con(gt, &[]), b.con(zero, &[])];
        let held = b.con(pair_ctor, &fields);
        b.call(count, &[held]);
        b.call(outcome, &[held])
    });
    program.set_entry(main);
    let facts = program.analyze();
    assert_eq!(facts.answers(outcome), Bounds::at(2));
    assert_eq!(facts.answers(count), Bounds::at(0));
    assert_eq!(facts.field(&program, pair_ctor, 0), Bounds::at(2));
}

/// A value handed in at the entry was built out of sight, so its fields
/// could hold anything -- except that a field whose type is a run of bare
/// tags is still one of them: the type says that much alone.
#[test]
fn a_field_built_out_of_sight_is_known_only_by_its_type() {
    let mut program = Program::default();
    let order = program.declare_type("Order");
    program.define_type(order, &[("Lt", &[]), ("Eq", &[]), ("Gt", &[])]);
    let nat = program.declare_type("Nat");
    program.define_type(nat, &[("Zero", &[]), ("Succ", &[nat])]);
    let pair = program.declare_type("Pair");
    program.define_type(pair, &[("Pair", &[order, nat])]);
    let pair_ctor = program.ctor_at(pair, 0);
    let main = program.declare_named("main", &[("handed", pair)], order);
    program.define(main, |b, args| {
        b.match_(args[0], pair, |_, _, fields| fields[0])
    });
    program.set_entry(main);
    let facts = program.analyze();
    assert_eq!(
        facts.answers(main),
        Bounds {
            low: 0,
            high: Some(2)
        }
    );
    assert_eq!(facts.field(&program, pair_ctor, 1), Bounds::ANY);
}

/// A recursion counting down from a large constant lowers what its argument
/// can be by one each time round. Past widening that is given up as nought,
/// so the walk settles instead of forgetting everything it knew.
#[test]
fn a_long_countdown_settles_with_nought_as_its_least() {
    let mut program = Program::default();
    let nat = program.declare_type("Nat");
    program.define_type(nat, &[("Zero", &[]), ("Succ", &[nat])]);
    let zero = program.ctor_at(nat, 0);
    let start = program.intern_number(nat, 300).unwrap();
    let down = program.declare("down", &[nat], nat);
    program.define(down, |b, args| {
        b.match_(args[0], nat, |b, ctor, fields| {
            if ctor == zero {
                b.con(zero, &[])
            } else {
                b.call(down, &[fields[0]])
            }
        })
    });
    let main = program.declare("main", &[], nat);
    program.define(main, |b, _| {
        let start = b.known(start);
        b.call(down, &[start])
    });
    program.set_entry(main);
    let facts = program.analyze();
    assert_eq!(
        facts.takes(down),
        [Bounds {
            low: 0,
            high: Some(300)
        }]
    );
    assert_eq!(facts.answers(main), Bounds::at(0));
}

/// A call chain walked against the order its definitions are declared in
/// carries what the deepest answers up one call each time round, so a chain
/// longer than any fixed number of rounds still settles, rather than
/// forgetting everything the walk knew.
#[test]
fn a_call_chain_longer_than_the_rounds_still_settles() {
    let mut program = Program::default();
    let nat = program.declare_type("Nat");
    program.define_type(nat, &[("Zero", &[]), ("Succ", &[nat])]);
    let (zero, succ) = (program.ctor_at(nat, 0), program.ctor_at(nat, 1));
    let main = program.declare("main", &[], nat);
    let chain: Vec<FnId> = (0..48)
        .map(|at| program.declare(&format!("link{at}"), &[], nat))
        .collect();
    program.define(main, |b, _| b.call(chain[0], &[]));
    for pair in chain.windows(2) {
        program.define(pair[0], |b, _| b.call(pair[1], &[]));
    }
    program.define(chain[chain.len() - 1], |b, _| {
        let nought = b.con(zero, &[]);
        b.con(succ, &[nought])
    });
    program.set_entry(main);
    let facts = program.analyze();
    assert_eq!(facts.unsettled(), None);
    assert_eq!(facts.answers(main), Bounds::at(1));
}

/// A count with no last step is given no greatest bound, but its remainder
/// by 256 is still below 256, and so is what that remainder is handed to:
/// widening the count must not widen them with it.
#[test]
fn a_remainder_of_a_widened_count_stays_below_its_divisor() {
    let mut library = fixture::Library::new();
    let (nat, zero, succ) = (library.nat, library.zero, library.succ);
    let divisor = library.number(256);
    let program = &mut library.program;
    let count = program.declare("count", &[nat], nat);
    program.define(count, |b, args| {
        b.match_(args[0], nat, |b, ctor, fields| {
            if ctor == zero {
                b.con(zero, &[])
            } else {
                let rest = b.call(count, &[fields[0]]);
                b.con(succ, &[rest])
            }
        })
    });
    let sink = program.declare("sink", &[nat], nat);
    let main = program.declare("main", &[nat], nat);
    program.define(main, |b, args| {
        let counted = b.call(count, &[args[0]]);
        let divisor = b.known(divisor);
        let low = b.call(library.modulo, &[counted, divisor]);
        b.call(sink, &[low])
    });
    program.set_entry(main);
    let facts = program.analyze();
    let below = Bounds {
        low: 0,
        high: Some(255),
    };
    assert_eq!(facts.answers(count), Bounds::ANY);
    assert_eq!(facts.answers(library.modulo), below);
    assert_eq!(facts.takes(sink), [below]);
}

/// A field that grows round a loop, kept below a width by a remainder, and
/// copied into itself round another loop. Widening it to no bound would be
/// for good: narrowing cannot take back what a field copied into itself
/// holds. Widened to the next machine width instead, it stays bounded.
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "two loops over one field, written as their equations"
)]
fn a_field_kept_below_a_width_is_widened_to_that_width() {
    let mut library = fixture::Library::new();
    let (nat, zero) = (library.nat, library.zero);
    let (nought, one, modulus) = (library.number(0), library.number(1), library.number(4096));
    let program = &mut library.program;
    let boxed = program.declare_type("Box");
    program.define_type(boxed, &[("Box", &[nat, nat])]);
    let make = program.ctor_at(boxed, 0);
    // spin(n, Box(v, w)) steps v modulo 4096, n times.
    let spin = program.declare("spin", &[nat, boxed], boxed);
    program.define(spin, |b, args| {
        b.match_(args[0], nat, |b, ctor, fields| {
            if ctor == zero {
                return args[1];
            }
            b.match_(args[1], boxed, |b, _, held| {
                let one = b.known(one);
                let modulus = b.known(modulus);
                let next = b.call(library.add, &[held[0], one]);
                let next = b.call(library.modulo, &[next, modulus]);
                let stepped = b.con(make, &[next, held[1]]);
                b.call(spin, &[fields[0], stepped])
            })
        })
    });
    // copy(n, Box(v, w)) builds the same box again, n times.
    let copy = program.declare("copy", &[nat, boxed], boxed);
    program.define(copy, |b, args| {
        b.match_(args[0], nat, |b, ctor, fields| {
            if ctor == zero {
                return args[1];
            }
            b.match_(args[1], boxed, |b, _, held| {
                let again = b.con(make, &[held[0], held[1]]);
                b.call(copy, &[fields[0], again])
            })
        })
    });
    let main = program.declare("main", &[nat], boxed);
    program.define(main, |b, args| {
        let nought = b.known(nought);
        let start = b.con(make, &[nought, nought]);
        let stepped = b.call(spin, &[args[0], start]);
        b.call(copy, &[args[0], stepped])
    });
    program.set_entry(main);
    let facts = program.analyze();
    let held = facts.field(program, make, 0);
    assert!(
        held.high
            .is_some_and(|high| (4095..=u64::from(u16::MAX)).contains(&high)),
        "{held:?}"
    );
}

/// How a step of a list is counted, for [`counted`].
#[derive(Clone, Copy, Debug)]
enum Step {
    /// `Succ(count(rest))`.
    Succ,
    /// `1 + count(rest)`.
    OnePlus,
    /// `count(rest) + 1`.
    PlusOne,
    /// `element + count(rest)`: a sum, not a count.
    PlusElement,
    /// `Succ(Succ(count(rest)))`: twice the length.
    Twice,
    /// `Succ(count(rest))`, but from one: the length and one more.
    FromOne,
}

/// A list declared step first, its rest before its element when
/// `rest_first`, and a count of it stepping as `step` says.
fn counted(step: Step, rest_first: bool) -> (Program, FnId) {
    let mut library = fixture::Library::new();
    let one = library.number(1);
    let (nat, zero, succ, add) = (library.nat, library.zero, library.succ, library.add);
    let p = &mut library.program;
    let list = p.declare_type("List");
    let fields = if rest_first { [list, nat] } else { [nat, list] };
    p.define_type(list, &[("Cons", &fields), ("Nil", &[])]);
    let nil = p.ctor_at(list, 1);
    let (element, rest) = if rest_first { (1, 0) } else { (0, 1) };
    let count = p.declare("count", &[list], nat);
    p.define(count, |b, args| {
        b.match_(args[0], list, |b, ctor, fields| {
            if ctor == nil {
                let nought = b.con(zero, &[]);
                return match step {
                    Step::FromOne => b.con(succ, &[nought]),
                    _ => nought,
                };
            }
            let counted = b.call(count, &[fields[rest]]);
            match step {
                Step::Succ | Step::FromOne => b.con(succ, &[counted]),
                Step::OnePlus => {
                    let one = b.known(one);
                    b.call(add, &[one, counted])
                }
                Step::PlusOne => {
                    let one = b.known(one);
                    b.call(add, &[counted, one])
                }
                Step::PlusElement => b.call(add, &[fields[element], counted]),
                Step::Twice => {
                    let stepped = b.con(succ, &[counted]);
                    b.con(succ, &[stepped])
                }
            }
        })
    });
    (library.program, count)
}

/// A count of a list is its length however the step adds its one, whichever
/// constructor comes first and wherever the rest is; nothing reads a name.
#[test]
fn a_count_of_a_list_is_its_length() {
    for step in [Step::Succ, Step::OnePlus, Step::PlusOne] {
        for rest_first in [false, true] {
            let (program, count) = counted(step, rest_first);
            assert_eq!(
                program.analyze().sequence_operation(count),
                Some(SequenceOperation::Length),
                "{step:?}, rest first: {rest_first}"
            );
        }
    }
}

/// A walk that adds its elements, counts two per step or starts from one
/// is not a length, however close it comes.
#[test]
fn a_near_miss_of_a_count_is_not_a_length() {
    for step in [Step::PlusElement, Step::Twice, Step::FromOne] {
        let (program, count) = counted(step, false);
        assert_eq!(
            program.analyze().sequence_operation(count),
            None,
            "{step:?}"
        );
    }
}

/// `walk(list, total, index)` over a known list: the total plus each
/// element times where it is, stepping the index by `step` each time round.
fn counted_walk(step: u64) -> (Program, FnId) {
    let mut library = fixture::Library::new();
    let (nat, add, mul) = (library.nat, library.add, library.mul);
    let (nought, stepped) = (library.number(0), library.number(step));
    let program = &mut library.program;
    let list = program.declare_type("List");
    program.define_type(list, &[("Nil", &[]), ("Cons", &[nat, list])]);
    let nil = program.ctor_at(list, 0);
    let walk = program.declare("walk", &[list, nat, nat], nat);
    program.define(walk, |b, args| {
        b.match_(args[0], list, |b, ctor, fields| {
            if ctor == nil {
                return args[1];
            }
            let scaled = b.call(mul, &[fields[0], args[2]]);
            let total = b.call(add, &[args[1], scaled]);
            let by = b.known(stepped);
            let next = b.call(add, &[args[2], by]);
            b.call(walk, &[fields[1], total, next])
        })
    });
    let known = program.intern_byte_spine(list, &[3, 1, 4, 1, 5]).unwrap();
    let main = program.declare("main", &[nat], nat);
    program.define(main, |b, args| {
        let known = b.known(known);
        let nought = b.known(nought);
        b.call(walk, &[known, args[0], nought])
    });
    program.set_entry(main);
    validate(program).unwrap();
    (library.program, walk)
}

/// An index stepped by one beside a walk down a known list of five is
/// never more than five, whatever widening makes of a count going round.
#[test]
fn a_count_beside_a_walk_is_bounded_by_what_it_walks() {
    let (program, walk) = counted_walk(1);
    let facts = program.analyze();
    assert_eq!(facts.takes(walk)[2].high, Some(5));
    // Stepped by two, the sum is not kept, and nothing bounds it.
    let (program, walk) = counted_walk(2);
    let facts = program.analyze();
    assert_ne!(facts.takes(walk)[2].high, Some(5));
}
