//! Valid multivalue IR fixtures: target ABI limits are not language limits.

use crate::ir::{Binary, Class, Program, Relation};

/// A runtime call which checks every argument and result, returning zero.
///
/// # Panics
/// If the requested test signature is too large to count in a u64.
#[must_use]
#[expect(
    clippy::too_many_lines,
    reason = "the fixture builds both sides of a runtime ABI call"
)]
pub fn function(params: usize, returns: usize) -> Program {
    let (mut program, main) = Program::new("main");
    let function = program.declare(
        "wide",
        &vec![Class::Word; params],
        &vec![Class::Word; returns],
    );
    program.define(function, |b, args| {
        let mut sum = b.constant(Class::Word, 0);
        for &arg in args {
            sum = b.binary(Binary::Add, sum, arg);
        }
        let results: Vec<_> = (0..returns)
            .map(|index| {
                let index = b.constant(
                    Class::Word,
                    u64::try_from(index).expect("a small signature"),
                );
                b.binary(Binary::Add, sum, index)
            })
            .collect();
        b.ret(&results);
    });
    program.define(main, |b, _| {
        let args: Vec<_> = (1..=params)
            .map(|index| {
                b.constant(
                    Class::Word,
                    u64::try_from(index).expect("a small signature"),
                )
            })
            .collect();
        let results = b.call(function, &args);
        let mut passed = b.constant(Class::Word, 0);
        for (index, result) in results.into_iter().enumerate() {
            let expected = params * (params + 1) / 2 + index;
            let expected = b.constant(
                Class::Word,
                u64::try_from(expected).expect("a small signature"),
            );
            let equal = b.compare(Relation::Equal, result, expected);
            passed = b.binary(Binary::Add, passed, equal);
        }
        let count = b.constant(
            Class::Word,
            u64::try_from(returns).expect("a small signature"),
        );
        let difference = b.binary(Binary::Sub, count, passed);
        b.ret(&[difference]);
    });
    program
}

/// Two pointer results, as an owned-natural return looks after legalization.
#[must_use]
pub fn pointer_pair() -> Program {
    let (mut program, main) = Program::new("main");
    let data = program.intern(&[0]);
    let pair = program.declare("pair", &[], &[Class::Address; 2]);
    program.define(pair, |b, _| {
        let pointer = b.address_of(data);
        b.ret(&[pointer, pointer]);
    });
    program.define(main, |b, _| {
        b.call(pair, &[]);
        let zero = b.constant(Class::Word, 0);
        b.ret(&[zero]);
    });
    program
}

/// A construct with `count` incoming state or outgoing results.
#[derive(Clone, Copy, Debug)]
pub enum Transfer {
    If,
    LoopState,
    LoopResults,
}

/// Region edges carry multiple values even on targets with one function result.
#[must_use]
pub fn region(kind: Transfer, count: usize) -> Program {
    let (mut program, main) = Program::new("main");
    program.define(main, |b, _| {
        let one = b.constant(Class::Word, 1);
        let values = vec![one; count];
        match kind {
            Transfer::If => {
                b.if_(
                    one,
                    &vec![Class::Word; count],
                    |b| b.yield_(&values),
                    |b| b.yield_(&values),
                );
            }
            Transfer::LoopState => {
                b.loop_(&values, &[], |b, _| b.break_(&[]));
            }
            Transfer::LoopResults => {
                b.loop_(&[], &vec![Class::Word; count], |b, _| b.break_(&values));
            }
        }
        let zero = b.constant(Class::Word, 0);
        b.ret(&[zero]);
    });
    program
}
