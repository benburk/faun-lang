//! External symbols and internal bodies share IDs but not code-generation roles.

use crate::ir::{Binary, Class, Program, Returns, Terminator};

/// Interleave bodies and declarations, with deliberately misleading local names.
/// Writes `aliases\n`, then exits 42 if two argc aliases report the same value.
#[must_use]
pub fn aliases() -> Program {
    let (mut p, main) = Program::new("main");
    let count = p.external("write", "argc", &[], Returns::Values(&[Class::Word]));
    let identity = p.declare("identity", &[Class::Word], &[Class::Word]);
    let write = p.external(
        "argc",
        "write",
        &[Class::Address, Class::Word],
        Returns::Values(&[]),
    );
    let wrapper = p.declare("wrapper", &[Class::Word], &[Class::Word]);
    let again = p.external("exit", "argc", &[], Returns::Values(&[Class::Word]));
    let exit = p.external("done", "exit", &[Class::Word], Returns::Never);
    let data = p.intern(b"aliases\n");
    p.define(identity, |b, args| b.ret(&[args[0]]));
    p.define(wrapper, |b, args| {
        let address = b.address_of(data);
        let length = b.data_len(data);
        b.call(write, &[address, length]);
        let value = b.call(identity, args);
        b.ret(&value)
    });
    p.define(main, |b, _| {
        let before = b.call(count, &[])[0];
        let held = b.call(wrapper, &[before])[0];
        let after = b.call(again, &[])[0];
        let difference = b.binary(Binary::Sub, held, after);
        let expected = b.constant(Class::Word, 42);
        let status = b.binary(Binary::Add, expected, difference);
        b.call(exit, &[status]);
        Terminator::UNREACHABLE
    });
    p
}
