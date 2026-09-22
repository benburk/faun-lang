//! Completion without a redundant marker, including returns across regions.

use crate::ir::{Class, Program};
use crate::platform::Routines;

/// Both entry branches return, without a trailing transfer at their join.
#[must_use]
pub fn entry_returns(condition: u64) -> Program {
    let (mut p, main) = Program::new("main");
    p.define(main, |b, _| {
        let condition = b.constant(Class::Word, condition);
        let yes = b.constant(Class::Word, 42);
        let no = b.constant(Class::Word, 17);
        b.if_(condition, &[], |b| b.ret(&[yes]), |b| b.ret(&[no]));
    });
    p
}

/// The same completion in a result-bearing internal function.
#[must_use]
pub fn function_returns(condition: u64) -> Program {
    let (mut p, main) = Program::new("main");
    let helper = p.declare("choose", &[Class::Word], &[Class::Word]);
    p.define(helper, |b, params| {
        let yes = b.constant(Class::Word, 42);
        let no = b.constant(Class::Word, 17);
        b.if_(params[0], &[], |b| b.ret(&[yes]), |b| b.ret(&[no]));
    });
    p.define(main, |b, _| {
        let condition = b.constant(Class::Word, condition);
        let result = b.call(helper, &[condition]);
        b.ret(&result);
    });
    p
}

/// Returning zero from a nested branch must skip the later write, even when
/// the target needs no process-exit import anywhere in the program.
#[must_use]
pub fn early_success(condition: u64) -> Program {
    let (mut p, main) = Program::new("main");
    let write = Routines::builtin().declare(&mut p, "write");
    let text = p.intern(b"continued\n");
    p.define(main, |b, _| {
        let condition = b.constant(Class::Word, condition);
        let zero = b.constant(Class::Word, 0);
        b.loop_(&[], &[], |b, _| {
            b.if_(condition, &[], |b| b.ret(&[zero]), |b| b.break_(&[]));
        });
        let address = b.address_of(text);
        let len = b.data_len(text);
        b.call(write, &[address, len]);
        b.ret(&[zero]);
    });
    p
}
