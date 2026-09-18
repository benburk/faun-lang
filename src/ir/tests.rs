use super::*;

/// The mistake `Convert` exists to make visible: an entry that says it
/// leaves with a word, leaving with eight bits instead.
#[test]
fn a_width_that_changes_without_saying_so_is_rejected() {
    let (mut program, main) = Program::new("main");
    program.define(main, |b, _| {
        let byte = b.constant(Class::Fixed { bits: 8 }, 250);
        b.ret(&[byte])
    });

    let error = validate(&program).unwrap_err();
    assert!(error.contains("main returns"), "{error}");

    let (mut program, main) = Program::new("main");
    program.define(main, |b, _| {
        let byte = b.constant(Class::Fixed { bits: 8 }, 250);
        let word = b.convert(Class::Word, byte);
        b.ret(&[word])
    });
    assert!(validate(&program).is_ok());
}

#[test]
fn operands_of_one_operation_must_agree() {
    let (mut program, main) = Program::new("main");
    program.define(main, |b, _| {
        let byte = b.constant(Class::Fixed { bits: 8 }, 1);
        let word = b.constant(Class::Word, 1);
        let sum = b.binary(Binary::Add, byte, word);
        let sum = b.convert(Class::Word, sum);
        b.ret(&[sum])
    });

    let error = validate(&program).unwrap_err();
    assert!(error.contains("in one operation"), "{error}");
}

#[test]
fn an_instruction_stays_small() {
    assert!(size_of::<Op>() <= 24, "{} bytes", size_of::<Op>());
}

/// A call reads its arguments by position, so one too many or one of the
/// wrong class is read as something it is not. Nothing below this tier
/// checks, and a target would compile it in silence.
#[test]
fn a_call_gives_a_name_what_it_takes() {
    let bad = |args: usize, class: Class| {
        let (mut program, main) = Program::new("main");
        let takes_one = program.declare("takes_one", &[Class::Word], &[Class::Word]);
        program.define(takes_one, |b, params| b.ret(&[params[0]]));
        program.define(main, |b, _| {
            let held: Vec<_> = (0..args).map(|_| b.constant(class, 1)).collect();
            let answer = b.call(takes_one, &held);
            b.ret(&answer)
        });
        validate(&program)
    };

    assert!(bad(1, Class::Word).is_ok());
    let error = bad(2, Class::Word).unwrap_err();
    assert!(error.contains("main calls `takes_one`"), "{error}");
    let error = bad(1, Class::Fixed { bits: 8 }).unwrap_err();
    assert!(error.contains("main calls `takes_one`"), "{error}");
}

/// The same of a routine a target answers for, whose signature is the only
/// thing saying what it reads.
#[test]
fn a_platform_call_gives_a_routine_what_it_takes() {
    let (mut program, main) = Program::new("main");
    let exit = program.platform("exit");
    program.define(main, |b, _| {
        b.platform_call(exit, &[]);
        let status = b.constant(Class::Word, 0);
        b.ret(&[status])
    });

    let error = validate(&program).unwrap_err();
    assert!(error.contains("main calls `exit`"), "{error}");
}

/// A routine that does not come back is the end of its region. A program
/// that carries on after one is saying something no target can lay out,
/// and the mistake is in the saying rather than in any of the three.
#[test]
fn nothing_is_written_after_a_routine_that_does_not_come_back() {
    let (mut program, main) = Program::new("main");
    let exit = program.platform("exit");
    program.define(main, |b, _| {
        let status = b.constant(Class::Word, 0);
        b.platform_call(exit, &[status]);
        let held = b.constant(Class::Word, 1);
        b.ret(&[held])
    });

    let error = validate(&program).unwrap_err();
    assert!(error.contains("does not come back"), "{error}");

    let (mut program, main) = Program::new("main");
    let exit = program.platform("exit");
    program.define(main, |b, _| {
        let status = b.constant(Class::Word, 0);
        b.platform_call(exit, &[status]);
        Terminator::UNREACHABLE
    });
    assert!(validate(&program).is_ok());
}
