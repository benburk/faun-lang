//! Splitting keeps what a program answers: each instruction on numbers wider
//! than the word answers the same run a word at a time as it does whole.

use num_bigint::BigUint;

use super::evaluate::{self, RejectHost};
use super::{Binary, Builder, Class, Direction, FunctionId, Program, Relation, ValueId, split};

/// A program whose entry answers nought, and a function `test` taking and
/// answering `params` and `results`, whose body `body` writes.
fn program(
    params: &[Class],
    results: &[Class],
    body: impl FnOnce(&mut Builder, &[ValueId]) -> Vec<ValueId>,
) -> (Program, FunctionId) {
    let (mut p, main) = Program::new("main");
    p.define(main, |b, _| {
        let zero = b.constant(Class::Word, 0);
        b.ret(&[zero]);
    });
    let test = p.declare("test", params, results);
    p.define(test, |b, args| {
        let answer = body(b, args);
        b.ret(&answer);
    });
    super::validate(&p).unwrap();
    (p, test)
}

fn run(p: &Program, test: FunctionId, args: &[BigUint], word_bits: u16) -> Vec<BigUint> {
    let evaluation = evaluate::evaluate(
        p,
        test,
        args,
        evaluate::Config {
            word_bits,
            fuel: 10_000_000,
            ..evaluate::Config::default()
        },
        &mut RejectHost,
    )
    .expect("an evaluation");
    evaluation.returned().expect("an answer").to_vec()
}

/// How many words a target of `word_bits` holds `class` in.
fn words_of(class: Class, word_bits: u16) -> usize {
    class
        .width()
        .filter(|&bits| bits > word_bits)
        .map_or(1, |bits| usize::from(bits.div_ceil(word_bits)))
}

/// Each of `values`, at `classes`, as the words a split program takes it in.
fn split_args(values: &[BigUint], classes: &[Class], word_bits: u16) -> Vec<BigUint> {
    let mask = (BigUint::from(1u8) << usize::from(word_bits)) - 1u8;
    values
        .iter()
        .zip(classes)
        .flat_map(|(value, &class)| {
            (0..words_of(class, word_bits))
                .map(|at| (value >> (at * usize::from(word_bits))) & &mask)
                .collect::<Vec<_>>()
        })
        .collect()
}

/// A split program's answers, each wide one put back together.
fn joined(words: &[BigUint], classes: &[Class], word_bits: u16) -> Vec<BigUint> {
    let mut at = 0;
    classes
        .iter()
        .map(|&class| {
            let n = words_of(class, word_bits);
            let whole = words[at..at + n]
                .iter()
                .rev()
                .fold(BigUint::default(), |held, word| {
                    (held << usize::from(word_bits)) + word
                });
            at += n;
            whole
        })
        .collect()
}

/// That `test` answers the same for every one of `cases`, whole and split,
/// at every narrow word.
fn same(
    p: &Program,
    test: FunctionId,
    (params, results): (&[Class], &[Class]),
    cases: &[Vec<BigUint>],
) {
    for word_bits in [16, 32] {
        let split = split(p, word_bits);
        super::validate(&split).unwrap_or_else(|error| panic!("{word_bits}: {error}"));
        let word = BigUint::from(1u8) << usize::from(word_bits);
        for case in cases {
            // Whole, where every fixed width is one number; a word it
            // answers is then what a narrower word holds of it.
            let whole: Vec<_> = run(p, test, case, 64)
                .into_iter()
                .zip(results)
                .map(|(value, &class)| {
                    if class == Class::Word {
                        value % &word
                    } else {
                        value
                    }
                })
                .collect();
            let args = split_args(case, params, word_bits);
            let words = run(&split, test, &args, word_bits);
            assert_eq!(
                joined(&words, results, word_bits),
                whole,
                "{word_bits} bits, {case:?}"
            );
        }
    }
}

/// Numbers to try, below `2^bits`: the edges and some that are not.
fn numbers(bits: u16, seed: u64) -> Vec<BigUint> {
    let top = (BigUint::from(1u8) << usize::from(bits)) - 1u8;
    let mut state = seed;
    let mut picked = vec![
        BigUint::default(),
        BigUint::from(1u8),
        BigUint::from(0xffffu32),
        BigUint::from(0x1_0000u32),
        top.clone(),
    ];
    for _ in 0..6 {
        state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1);
        picked.push(BigUint::from(state) % (&top + 1u8));
    }
    picked.retain(|n| n <= &top);
    picked
}

fn pairs(left: u16, right: u16) -> Vec<(BigUint, BigUint)> {
    let xs = numbers(left, 7);
    let ys = numbers(right, 11);
    xs.iter()
        .flat_map(|x| ys.iter().map(move |y| (x.clone(), y.clone())))
        .collect()
}

/// A sum, a difference, a monus and a product: each wide, each answering
/// what it does whole, where it fits.
#[test]
fn arithmetic_on_words_answers_what_it_does_whole() {
    let (a, c) = (Class::fixed(40), Class::fixed(24));
    for (op, answer) in [
        (Binary::Add, Class::fixed(41)),
        (Binary::Sub, Class::fixed(40)),
        (Binary::Monus, Class::fixed(40)),
        (Binary::Mul, Class::fixed(64)),
    ] {
        let (p, test) = program(&[a, c], &[answer], |b, args| {
            vec![b.binary_at(answer, op, args[0], args[1])]
        });
        let cases: Vec<_> = pairs(40, 24)
            .into_iter()
            // A difference is asked only of what is at least as large.
            .filter(|(x, y)| op != Binary::Sub || x >= y)
            .map(|(x, y)| vec![x, y])
            .collect();
        same(&p, test, (&[a, c], &[answer]), &cases);
    }
}

/// A quotient and a remainder, by divisors fitting half a word, which is
/// short division, and by wider ones, which go through a natural; by nought
/// as a word's quotient is.
#[test]
fn division_on_words_answers_what_it_does_whole() {
    let a = Class::fixed(48);
    for divisor in [Class::fixed(7), Class::fixed(8), Class::fixed(40)] {
        for op in [Binary::Div, Binary::Mod] {
            let (p, test) = program(&[a, divisor], &[a], |b, args| {
                vec![b.binary_at(a, op, args[0], args[1])]
            });
            let bits = divisor.width().unwrap();
            let cases: Vec<_> = pairs(48, bits)
                .into_iter()
                .map(|(x, y)| vec![x, y])
                .collect();
            same(&p, test, (&[a, divisor], &[a]), &cases);
        }
    }
}

#[test]
fn orders_on_words_answer_what_they_do_whole() {
    let (a, c) = (Class::fixed(40), Class::fixed(36));
    for relation in [Relation::Equal, Relation::Less] {
        let (p, test) = program(&[a, c], &[Class::Word], |b, args| {
            vec![b.compare(relation, args[0], args[1])]
        });
        let mut cases: Vec<_> = pairs(40, 36).into_iter().map(|(x, y)| vec![x, y]).collect();
        cases.extend(numbers(36, 3).into_iter().map(|x| vec![x.clone(), x]));
        same(&p, test, (&[a, c], &[Class::Word]), &cases);
    }
}

#[test]
fn shifts_on_words_answer_what_they_do_whole() {
    let a = Class::fixed(40);
    for (direction, by, answer) in [
        (Direction::Up, 3, Class::fixed(43)),
        (Direction::Up, 16, Class::fixed(56)),
        (Direction::Up, 21, Class::fixed(61)),
        // What a shift answers holds what it shifts.
        (Direction::Down, 5, a),
        (Direction::Down, 32, a),
        (Direction::Down, 17, a),
    ] {
        let (p, test) = program(&[a], &[answer], |b, args| {
            vec![b.shift(answer, direction, args[0], by)]
        });
        let cases: Vec<_> = numbers(40, 5).into_iter().map(|x| vec![x]).collect();
        same(&p, test, (&[a], &[answer]), &cases);
    }
}

/// Read at a wider class, a number is itself; at a narrower one, what that
/// class holds of it; as a word, its lowest word's worth.
#[test]
fn conversions_on_words_answer_what_they_do_whole() {
    let a = Class::fixed(40);
    for answer in [
        Class::fixed(60),
        Class::fixed(20),
        Class::fixed(36),
        Class::Word,
        Class::fixed(8),
    ] {
        let (p, test) = program(&[a], &[answer], |b, args| vec![b.convert(answer, args[0])]);
        let cases: Vec<_> = numbers(40, 13).into_iter().map(|x| vec![x]).collect();
        same(&p, test, (&[a], &[answer]), &cases);
    }
}

/// Wide state goes round a loop, through an `if` and a call, and into a
/// cell and a buffer and back out, as it does whole.
#[test]
fn wide_values_cross_regions_calls_and_fields() {
    let wide = Class::fixed(48);
    let (p, test) = crossing(wide);
    let cases: Vec<_> = numbers(48, 17)
        .into_iter()
        .flat_map(|x| [0u8, 1, 5, 8].map(|n| vec![x.clone(), BigUint::from(n)]))
        .collect();
    same(&p, test, (&[wide, Class::Word], &[wide, wide]), &cases);
}

/// A function taking a `wide` number and a count, going round a loop with
/// it, through an `if` and a call, into a cell and a buffer and out.
fn crossing(wide: Class) -> (Program, FunctionId) {
    let (mut p, main) = Program::new("main");
    p.define(main, |b, _| {
        let zero = b.constant(Class::Word, 0);
        b.ret(&[zero]);
    });
    let twice = p.declare("twice", &[wide], &[wide]);
    p.define(twice, |b, args| {
        let doubled = b.binary_at(wide, Binary::Add, args[0], args[0]);
        b.ret(&[doubled]);
    });
    let test = p.declare("test", &[wide, Class::Word], &[wide, wide]);
    p.define(test, |b, args| {
        let looped = halving(b, [args[0], args[1]], (wide, twice));
        // Into a cell beside a word, and a buffer, and back.
        let shape = b.shape(&[Class::Word, wide]);
        let seven = b.constant(Class::Word, 7);
        let cell = b.cell(1, shape, &[seven, looped]);
        let held = b.cell_field((wide, shape), cell, 1);
        let elements = b.shape(&[wide]);
        let empty = b.buffer_empty(elements);
        let none = b.constant(Class::Word, 0);
        let pushed = b.buffer_push((empty, none, none), elements, &[held]);
        let read = b.buffer_field((wide, elements), pushed.into(), 0);
        let constant = b.constant(wide, 0x1234_5678_9abc);
        b.ret(&[read, constant]);
    });
    super::validate(&p).unwrap();
    (p, test)
}

/// Down from `count`, halving `x` where the count is odd and doubling a
/// quarter of it by a call to `twice` where not, all at `wide`.
fn halving(b: &mut Builder, start: [ValueId; 2], (wide, twice): (Class, FunctionId)) -> ValueId {
    let zero = b.constant(Class::Word, 0);
    b.loop_(&start, &[wide], |b, state| {
        let [x, n] = [state[0], state[1]];
        let done = b.compare(Relation::Equal, n, zero);
        b.if_(done, &[], |b| b.break_(&[x]), |b| b.yield_(&[]));
        let two = b.constant(Class::Word, 2);
        let odd = b.binary(Binary::Mod, n, two);
        let next = b.if_(
            odd,
            &[wide],
            |b| {
                let half = b.shift(wide, Direction::Down, x, 1);
                b.yield_(&[half]);
            },
            |b| {
                let small = b.shift(wide, Direction::Down, x, 2);
                let doubled = b.call_one(twice, &[small]);
                b.yield_(&[doubled]);
            },
        )[0];
        let one = b.constant(Class::Word, 1);
        let n = b.binary(Binary::Sub, n, one);
        b.continue_(&[next, n]);
    })[0]
}
