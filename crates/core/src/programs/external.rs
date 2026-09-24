//! External symbols and internal bodies share IDs but not code-generation roles.

use crate::ir::{Binary, Class, Program, Returns};

/// Interleave external declarations and bodies whose names resemble host functions.
///
/// Writes `externals\n`, then exits 42 if two declarations of `read_byte!`
/// agree, which they do with nothing on standard input: both read the end.
#[must_use]
pub fn interleaved() -> Program {
    let (mut p, main) = Program::new("main");
    let byte = Class::fixed(9);
    let read = p.external("read_byte!", &[], Returns::Values(&[byte]));
    let increment = p.declare("read_byte!", &[Class::Word], &[Class::Word]);
    let write = p.external(
        "write!",
        &[Class::Address, Class::Word],
        Returns::Values(&[]),
    );
    let wrapper = p.declare("exit!", &[Class::Word], &[Class::Word]);
    let again = p.external("read_byte!", &[], Returns::Values(&[byte]));
    let exit = p.external("exit!", &[Class::Word], Returns::Never);
    let data = p.intern(b"externals\n");
    p.define(increment, |b, args| {
        let one = b.constant(Class::Word, 1);
        let next = b.binary(Binary::Add, args[0], one);
        b.ret(&[next]);
    });
    p.define(wrapper, |b, args| {
        let address = b.address_of(data);
        let length = b.data_len(data);
        b.call(write, &[address, length]);
        let value = b.call(increment, args);
        b.ret(&value);
    });
    p.define(main, |b, _| {
        let before = b.call_one(read, &[]);
        let before = b.convert(Class::Word, before);
        let held = b.call_one(wrapper, &[before]);
        let after = b.call_one(again, &[]);
        let after = b.convert(Class::Word, after);
        let difference = b.binary(Binary::Sub, held, after);
        let expected = b.constant(Class::Word, 41);
        let status = b.binary(Binary::Add, expected, difference);
        b.call(exit, &[status]);
    });
    p
}

/// Read three arbitrary bytes, then observe EOF twice. Answers zero only when
/// the host preserves every byte and keeps EOF stable across repeated reads.
#[must_use]
pub fn reads_bytes() -> Program {
    let (mut program, main) = Program::new("main");
    let read = crate::platform::Routines::builtin().declare(&mut program, "read_byte!");
    let byte = Class::fixed(9);

    program.define(main, |b, _| {
        let expected = [1, 128, 256, 0, 0];
        let mut correct = b.constant(Class::fixed(1), 1);
        for wanted in expected {
            let got = b.call_one(read, &[]);
            let wanted = b.constant(byte, wanted);
            let same = b.compare(crate::ir::Relation::Equal, got, wanted);
            let same = b.convert(Class::fixed(1), same);
            correct = b.binary(Binary::Mul, correct, same);
        }
        let one = b.constant(Class::fixed(1), 1);
        let status = b.binary(Binary::Sub, one, correct);
        let status = b.convert(Class::Word, status);
        b.ret(&[status]);
    });
    program
}
