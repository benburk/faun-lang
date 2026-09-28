//! Bitwise walks and powers by squaring, written as the standard library
//! writes them, are recognized as operations only through a call starting
//! them from their identity, and a near miss of any equation is not.

#![expect(
    clippy::many_single_char_names,
    reason = "the walks' own equations name their numbers a, b and so on"
)]

use super::*;
use num_bigint::BigUint;

/// Which walk a definition takes, and which of its equations, if any, it
/// writes wrongly.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Walk {
    And,
    Or,
    Xor,
    /// An or whose zero cases answer only what was built, as an and's do.
    OrForgettingTheRest,
    /// An exclusive or halving one side by three.
    XorByThree,
    /// An and whose bit is an or's.
    AndOfEither,
    Pow,
    /// A power keeping the product where the exponent is even.
    PowOnEven,
}

/// The fixture's arithmetic, a walk, and `start(a, b)`, a call of the walk
/// from its identity: a place of one and nothing built, or one built.
#[expect(
    clippy::too_many_lines,
    reason = "each walk written as its equations, in one fixture"
)]
fn walk(kind: Walk) -> (Program, FnId, FnId) {
    let library = fixture::Library::new();
    let (nat, zero, true_) = (library.nat, library.zero, library.true_);
    let fixture::Library {
        add,
        mul,
        div,
        modulo,
        equals,
        ..
    } = library;
    let mut p = library.program;
    let pow = matches!(kind, Walk::Pow | Walk::PowOnEven);
    let params: &[TypeId] = if pow { &[nat; 3] } else { &[nat; 4] };
    let walk = p.declare("walk", params, nat);
    p.define(walk, |b, args| {
        let one = b.number(nat, 1).unwrap();
        let one = b.known(one);
        let two = b.number(nat, 2).unwrap();
        let two = b.known(two);
        if pow {
            // walk(_, 0, built) -> built
            // walk(base, 1, built) -> built * base
            // walk(base, e, built) ->
            //   walk(base * base, e / 2, e % 2 == 1 ? built * base : built)
            let [base, exponent, built] = [args[0], args[1], args[2]];
            return b.match_(exponent, nat, |b, ctor, _| {
                if ctor == zero {
                    return built;
                }
                let low = b.call(modulo, &[exponent, two]);
                let odd = b.call(equals, &[low, one]);
                let times = b.call(mul, &[built, base]);
                let kept = b.match_(odd, library.bool_, |_, ctor, _| {
                    if (ctor == true_) == (kind == Walk::Pow) {
                        times
                    } else {
                        built
                    }
                });
                let squared = b.call(mul, &[base, base]);
                let half = b.call(div, &[exponent, two]);
                b.call(walk, &[squared, half, kept])
            });
        }
        // walk(0, b, place, built) -> built + b * place (or built)
        // walk(a, 0, place, built) -> built + a * place (or built)
        // walk(a, b, place, built) ->
        //   walk(a / 2, b / 2, place * 2, built + bit * place)
        let [a, c, place, built] = [args[0], args[1], args[2], args[3]];
        let keeps = matches!(kind, Walk::Or | Walk::Xor | Walk::XorByThree);
        let rest = |b: &mut Builder<'_>, rest: Atom| {
            if keeps {
                let scaled = b.call(mul, &[rest, place]);
                b.call(add, &[built, scaled])
            } else {
                built
            }
        };
        b.match_(a, nat, |b, ctor, _| {
            if ctor == zero {
                return rest(b, c);
            }
            b.match_(c, nat, |b, ctor, _| {
                if ctor == zero {
                    return rest(b, a);
                }
                let x = b.call(modulo, &[a, two]);
                let y = b.call(modulo, &[c, two]);
                let bit = match kind {
                    Walk::And => b.call(mul, &[x, y]),
                    Walk::Xor | Walk::XorByThree => {
                        let sum = b.call(add, &[a, c]);
                        b.call(modulo, &[sum, two])
                    }
                    _ => {
                        let either = b.call(add, &[x, y]);
                        let both = b.call(mul, &[x, y]);
                        b.call(library.sub, &[either, both])
                    }
                };
                let three = b.number(nat, 3).unwrap();
                let three = b.known(three);
                let halves = [a, c].map(|n| b.call(div, &[n, two]));
                let halves = if kind == Walk::XorByThree {
                    [halves[0], b.call(div, &[c, three])]
                } else {
                    halves
                };
                let doubled = b.call(mul, &[place, two]);
                let scaled = b.call(mul, &[bit, place]);
                let sum = b.call(add, &[built, scaled]);
                b.call(walk, &[halves[0], halves[1], doubled, sum])
            })
        })
    });
    let start = p.declare("start", &[nat, nat], nat);
    p.define(start, |b, args| {
        let one = b.number(nat, 1).unwrap();
        let one = b.known(one);
        if pow {
            return b.call(walk, &[args[0], args[1], one]);
        }
        let nought = b.number(nat, 0).unwrap();
        let nought = b.known(nought);
        b.call(walk, &[args[0], args[1], one, nought])
    });
    let main = p.declare("main", &[], nat);
    p.define(main, |b, _| b.con(zero, &[]));
    p.set_entry(main);
    validate(&p).unwrap();
    (p, walk, start)
}

#[test]
fn a_walk_started_from_its_identity_is_its_operation() {
    for (kind, op) in [
        (Walk::And, Operation::And),
        (Walk::Or, Operation::Or),
        (Walk::Xor, Operation::Xor),
        (Walk::Pow, Operation::Pow),
    ] {
        let (program, walk, start) = walk(kind);
        let operations = arithmetic::recognise(&program);
        assert_eq!(operations[start.index()], Some(op), "{kind:?}");
        // The walk itself takes more than two numbers, and is no operation.
        assert_eq!(operations[walk.index()], None, "{kind:?}");
    }
}

#[test]
fn a_near_miss_of_a_walk_is_no_operation() {
    for kind in [
        Walk::OrForgettingTheRest,
        Walk::XorByThree,
        Walk::AndOfEither,
        Walk::PowOnEven,
    ] {
        let (program, _, start) = walk(kind);
        let operations = arithmetic::recognise(&program);
        assert_eq!(operations[start.index()], None, "{kind:?}");
    }
}

#[test]
fn a_recognized_walk_folds_to_its_operation() {
    for (kind, op) in [
        (Walk::And, Operation::And),
        (Walk::Or, Operation::Or),
        (Walk::Xor, Operation::Xor),
        (Walk::Pow, Operation::Pow),
    ] {
        for (a, b) in [(0u64, 0u64), (12, 10), (255, 3), (7, 0), (0, 9)] {
            let expected = op.calculate(&BigUint::from(a), &BigUint::from(b)).unwrap();
            let (mut program, _, start) = walk(kind);
            let main = program.entry().unwrap();
            let nat = program.function(start).result;
            program.define(main, |builder, _| {
                let [x, y] = [a, b].map(|n| {
                    let n = builder.number(nat, n).unwrap();
                    builder.known(n)
                });
                builder.call(start, &[x, y])
            });
            optimize(&mut program);
            let main = program.entry().unwrap();
            let body = program.function(main).body().unwrap();
            let Expr::Static(answer) = program.expr(body.tail) else {
                panic!("{kind:?} {a} {b} folds:\n{}", program.render());
            };
            let ConstantView::Natural(n) = program.constant(answer).view() else {
                panic!("a number");
            };
            assert_eq!(n.to_biguint(), expected, "{kind:?} {a} {b}");
        }
    }
}
