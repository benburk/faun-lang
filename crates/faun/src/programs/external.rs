//! External symbols and internal bodies share IDs but not code-generation roles.

use crate::ir::{Binary, Class, Program, Returns, Terminator};

/// Interleave external declarations and bodies whose names resemble host functions.
/// Writes `externals\n`, then exits 42 if two argc declarations agree.
#[must_use]
pub fn interleaved() -> Program {
    let (mut p, main) = Program::new("main");
    let count = p.external("argc", &[], Returns::Values(&[Class::Word]));
    let increment = p.declare("argc", &[Class::Word], &[Class::Word]);
    let write = p.external(
        "write",
        &[Class::Address, Class::Word],
        Returns::Values(&[]),
    );
    let wrapper = p.declare("exit", &[Class::Word], &[Class::Word]);
    let again = p.external("argc", &[], Returns::Values(&[Class::Word]));
    let exit = p.external("exit", &[Class::Word], Returns::Never);
    let data = p.intern(b"externals\n");
    p.define(increment, |b, args| {
        let one = b.constant(Class::Word, 1);
        let next = b.binary(Binary::Add, args[0], one);
        b.ret(&[next])
    });
    p.define(wrapper, |b, args| {
        let address = b.address_of(data);
        let length = b.data_len(data);
        b.call(write, &[address, length]);
        let value = b.call(increment, args);
        b.ret(&value)
    });
    p.define(main, |b, _| {
        let before = b.call(count, &[])[0];
        let held = b.call(wrapper, &[before])[0];
        let after = b.call(again, &[])[0];
        let difference = b.binary(Binary::Sub, held, after);
        let expected = b.constant(Class::Word, 41);
        let status = b.binary(Binary::Add, expected, difference);
        b.call(exit, &[status]);
        Terminator::UNREACHABLE
    });
    p
}
