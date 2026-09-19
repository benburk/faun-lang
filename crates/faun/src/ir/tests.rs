use super::*;
use crate::barb::Bounds;

/// A program read from text, against what a compiler knows. These are
/// about what this tier makes of one, so which target would take it is not
/// a question any of them asks.
fn read(text: &str) -> Result<Program, String> {
    crate::read(text, &crate::platform::Routines::builtin())
}

/// A width is what a value needs, so a value needing fewer bits than what
/// reads it is already what reads it: what it holds above those bits is
/// nought. Needing more is the mistake, and `Convert` is what says where a
/// value is taken modulo a width rather than assumed to fit one.
#[test]
fn a_value_wider_than_what_reads_it_is_rejected() {
    let narrow = |bits| {
        let (mut program, main) = Program::new("main");
        let takes = program.declare("takes", &[Class::Fixed { bits: 8 }], &[]);
        program.define(takes, |b, _| b.ret(&[]));
        program.define(main, |b, _| {
            let held = b.constant(Class::Fixed { bits }, 1);
            b.call(takes, &[held]);
            let status = b.constant(Class::Word, 0);
            b.ret(&[status])
        });
        program
    };

    assert!(validate(&narrow(8)).is_ok(), "the width it reads");
    assert!(validate(&narrow(3)).is_ok(), "narrower, which already fits");
    let error = validate(&narrow(16)).unwrap_err();
    assert!(error.contains("main calls `takes`"), "{error}");

    // The entry leaves with a word, and a byte is a word with nothing above
    // its eight bits.
    let (mut program, main) = Program::new("main");
    program.define(main, |b, _| {
        let byte = b.constant(Class::Fixed { bits: 8 }, 250);
        b.ret(&[byte])
    });
    assert!(validate(&program).is_ok());
}

/// Operands are read at the width of what they answer, and a value needing
/// fewer bits already reads as one needing more. Wider than what reads it is
/// the mistake: the bits above would be dropped without anything saying so.
#[test]
fn an_operand_wider_than_what_reads_it_is_rejected() {
    let held = |left: Class, right: Class| {
        let (mut program, main) = Program::new("main");
        program.define(main, |b, _| {
            let left = b.constant(left, 1);
            let right = b.constant(right, 1);
            // The result is as wide as the left operand, which is what a
            // program building its own IR means by adding them.
            let sum = b.binary(Binary::Add, left, right);
            let sum = b.convert(Class::Word, sum);
            b.ret(&[sum])
        });
        validate(&program)
    };

    let byte = Class::Fixed { bits: 8 };
    assert!(held(Class::Word, byte).is_ok(), "a byte read as a word");
    assert!(held(byte, byte).is_ok());
    let error = held(byte, Class::Word).unwrap_err();
    assert!(error.contains("read as"), "{error}");
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
    // A byte is read as a word without anything in between; an address is
    // not a number, whatever it is as wide as.
    assert!(bad(1, Class::Fixed { bits: 8 }).is_ok());
    let error = bad(1, Class::Address).unwrap_err();
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

/// One routine, reached by two names. What a program calls a thing and what
/// answers for it are different names, so a program may declare the same
/// routine at as many types as it uses it at -- there is no body to copy, so
/// nothing is duplicated by saying it twice.
#[test]
fn two_names_may_give_the_same_routine() {
    let mut program = crate::barb::Program::default();
    let nat = program.declare_type("Nat");
    program.define_type(nat, &[("Zero", &[]), ("Succ", &[nat])]);
    let bool_ = program.declare_type("Bool");
    program.define_type(bool_, &[("False", &[]), ("True", &[])]);

    let holds = |program: &mut crate::barb::Program, name, type_| {
        let id = program.declare(name, &[type_], type_);
        program.answered_by(id, "hold");
        // Builder clients supply finite host contracts, like the frontend.
        program.bound(id, Bounds::at(0).or(Bounds::at(u64::MAX)));
        id
    };
    let held_nat = holds(&mut program, "held_nat", nat);
    let held_bool = holds(&mut program, "held_bool", bool_);

    let (yes, zero) = (program.ctor_at(bool_, 1), program.ctor_at(nat, 0));
    let main = program.declare("main", &[], nat);
    program.define(main, |b, _| {
        let true_ = b.con(yes, &[]);
        let asked = b.call(held_bool, &[true_]);
        let nought = b.con(zero, &[]);
        let kept = b.call(held_nat, &[nought]);
        b.match_(asked, bool_, |_, _, _| kept)
    });
    program.set_entry(main);

    let mut routines = crate::platform::Routines::builtin();
    routines.push(crate::platform::Routine {
        name: "hold".to_owned(),
        called: None,
        takes: vec![Class::Word],
        returns: crate::platform::Returns::Value(Class::Word),
    });

    let facts = crate::barb::analyze(&program);
    let machine = lower(&program, &facts, &routines).expect("a representable program");
    let held: Vec<&str> = machine
        .platforms()
        .iter()
        .map(|held| machine.name(held.name))
        .collect();
    // One per declaration, since each is handed a value of its own type and
    // what a target reads is stated per call. Both say the same routine,
    // which is the whole of what the name was doing before.
    assert_eq!(held, ["hold", "hold"], "both answered elsewhere");
}

/// A value too wide for what a routine reads is refused, not narrowed.
///
/// Where a width was worked out from the same bounds the value was, holding
/// a value in fewer bits takes nothing off it. A routine's width came from
/// outside and says nothing about what a program worked out, so a value not
/// fitting one is a program this tier cannot lower rather than a value to
/// quietly make fit.
#[test]
fn a_value_too_wide_for_a_routine_is_refused() {
    let mut routines = crate::platform::Routines::builtin();
    routines.push(crate::platform::Routine {
        name: "narrow".to_owned(),
        called: None,
        takes: vec![Class::Fixed { bits: 4 }],
        returns: crate::platform::Returns::Unit,
    });

    let held = |value: u64| {
        let mut program = crate::barb::Program::default();
        let nat = program.declare_type("Nat");
        program.define_type(nat, &[("Zero", &[]), ("Succ", &[nat])]);
        let unit = program.declare_type("Unit");
        program.define_type(unit, &[("Only", &[])]);

        let narrow = program.declare("narrow", &[nat], unit);
        program.answered_by(narrow, "narrow");

        let number = program.intern_number(nat, value);
        let main = program.declare("main", &[], nat);
        program.define(main, |b, _| {
            let held = b.known(nat, number);
            b.call(narrow, &[held]);
            held
        });
        program.set_entry(main);

        let facts = crate::barb::analyze(&program);
        lower(&program, &facts, &routines)
    };

    held(9).expect("a value inside four bits");

    let refused = held(100).unwrap_err();
    assert!(refused.contains("`narrow`"), "{refused}");
}

/// What a tag is not: a constructor carrying something has no
/// representation here yet, however many of them there are.
#[test]
fn a_constructor_that_carries_something_is_not_a_tag() {
    let refused = read(
        "type Nat Zero Succ(Nat)
         type Maybe None Some(Nat)
         unwrap(None) -> Zero
         unwrap(Some(n)) -> n

         main!(h) -> n = argc!(h) exit!(h unwrap(Some(n)))",
    )
    .unwrap_err();
    assert!(
        refused.contains("`Maybe` has no representation"),
        "{refused}"
    );
}

/// What a routine reads is what the name means, not what a program hands
/// it. A type with one constructor says nothing by being one value rather
/// than another, so it carries no bits and is not passed at all -- which
/// leaves `exit!` with no status to leave with.
#[test]
fn an_effect_hands_over_what_the_routine_reads() {
    let refused = read(
        "type Nat Zero

         main!(h) -> exit!(h Zero)",
    )
    .unwrap_err();
    assert!(
        refused.contains("`exit` reads a word, and is handed nothing"),
        "{refused}"
    );
}

/// How wide a number is held is what its values can be, worked out by the
/// tier above from what the program does with them. Nothing says it and
/// nothing wraps: a value needing three bits is held in three bits, and a
/// value nothing bounds is held in a machine word.
#[test]
fn how_wide_a_number_is_held_is_what_it_can_be() {
    let widths = |text: &str| {
        let program = read(text).expect("a program");
        (0..program.values_count())
            .map(|at| program.class(ValueId::at(at)))
            .collect::<Vec<_>>()
    };

    // Two and two is four, which three bits hold.
    let held = widths(
        "type Nat Zero Succ(Nat)

         add(a Zero) -> a
         add(a Succ(k)) -> Succ(add(a k))

         main!(h) ->
           two = Succ(Succ(Zero))
           exit!(h add(two two))",
    );
    assert!(held.contains(&Class::Fixed { bits: 3 }), "{held:?}");
    assert!(
        held.iter()
            .all(|held| held.fits(Class::Fixed { bits: 3 }) || *held == Class::Word),
        "{held:?}"
    );
}
