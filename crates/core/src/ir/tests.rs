use super::*;
use crate::barb;

/// What a frontend declares for its host: the authority a program is
/// handed, a type with no values for what never comes back, and the
/// routines, each bodyless and named for what answers it.
pub(super) struct World {
    pub host: barb::TypeId,
    pub never: barb::TypeId,
    pub exit: barb::FnId,
    pub input: barb::FnId,
}

/// Declare `exit!` and `read_byte!` over `nat`. The byte read is the
/// program's input from outside; how wide it is, lowering assumes from the
/// routine it names.
pub(super) fn host(program: &mut barb::Program, nat: barb::TypeId) -> World {
    let host = program.declare_type("Host");
    program.define_type(host, &[("Host", &[])]);
    let never = program.declare_type("Never");
    program.define_type(never, &[]);
    let exit = program.declare("exit!", &[host, nat], never);
    let input = program.declare("read_byte!", &[host], nat);
    World {
        host,
        never,
        exit,
        input,
    }
}

/// `bounded!(host test n)`: `n` where `test` is true, and leaving with
/// nought where it is false. A program writes this to prove a count small
/// before it does arithmetic on it.
pub(super) fn bounded(library: &mut barb::fixture::Library, world: &World) -> barb::FnId {
    let (nat, bool_, zero, yes) = (library.nat, library.bool_, library.zero, library.true_);
    let exit = world.exit;
    let program = &mut library.program;
    let bounded = program.declare_named(
        "bounded!",
        &[("host", world.host), ("test", bool_), ("n", nat)],
        nat,
    );
    program.define(bounded, |b, args| {
        b.match_(args[1], bool_, |b, ctor, _| {
            if ctor == yes {
                args[2]
            } else {
                let nought = b.con(zero, &[]);
                b.call(exit, &[args[0], nought])
            }
        })
    });
    bounded
}

/// Validate and optimize a Barb program as the default pipeline does, then
/// lower it.
pub(super) fn machine(
    mut program: barb::Program,
    routines: &crate::platform::Routines,
) -> Result<Program, String> {
    barb::validate(&program)?;
    barb::optimize(&mut program);
    crate::lower_to_machine_ir(&mut program, routines)
}

/// A width is what a value needs, so a value needing fewer bits than what
/// reads it is already what reads it: what it holds above those bits is
/// nought. Needing more is the mistake, and `Convert` is what says where a
/// value is taken modulo a width rather than assumed to fit one.
#[test]
fn a_value_wider_than_what_reads_it_is_rejected() {
    let narrow = |bits| {
        let (mut program, main) = Program::new("main");
        let takes = program.declare("takes", &[Class::fixed(8)], &[]);
        program.define(takes, |b, _| b.ret(&[]));
        program.define(main, |b, _| {
            let held = b.constant(Class::fixed(bits), 1);
            b.call(takes, &[held]);
            let status = b.constant(Class::Word, 0);
            b.ret(&[status]);
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
        let byte = b.constant(Class::fixed(8), 250);
        b.ret(&[byte]);
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
            b.ret(&[sum]);
        });
        validate(&program)
    };

    let byte = Class::fixed(8);
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
            b.ret(&answer);
        });
        validate(&program)
    };

    assert!(bad(1, Class::Word).is_ok());
    let error = bad(2, Class::Word).unwrap_err();
    assert!(error.contains("main calls `takes_one`"), "{error}");
    // A byte is read as a word without anything in between; an address is
    // not a number, whatever it is as wide as.
    assert!(bad(1, Class::fixed(8)).is_ok());
    let error = bad(1, Class::Address).unwrap_err();
    assert!(error.contains("main calls `takes_one`"), "{error}");
}

/// The same of a routine a target answers for, whose signature is the only
/// thing saying what it reads.
#[test]
fn a_platform_call_gives_a_routine_what_it_takes() {
    let (mut program, main) = Program::new("main");
    let exit = crate::platform::Routines::builtin().declare(&mut program, "exit!");
    program.define(main, |b, _| {
        b.call(exit, &[]);
        let status = b.constant(Class::Word, 0);
        b.ret(&[status]);
    });

    let error = validate(&program).unwrap_err();
    assert!(error.contains("main calls `exit!`"), "{error}");
}

/// A routine that does not come back is the end of its region. A program
/// that carries on after one is saying something no target can lay out,
/// and the mistake is in the saying rather than in any of the three.
#[test]
fn nothing_is_written_after_a_routine_that_does_not_come_back() {
    let (mut program, main) = Program::new("main");
    let exit = crate::platform::Routines::builtin().declare(&mut program, "exit!");
    program.define(main, |b, _| {
        let status = b.constant(Class::Word, 0);
        b.call(exit, &[status]);
        let held = b.constant(Class::Word, 1);
        b.ret(&[held]);
    });

    let error = validate(&program).unwrap_err();
    assert!(error.contains("does not come back"), "{error}");

    let (mut program, main) = Program::new("main");
    let exit = crate::platform::Routines::builtin().declare(&mut program, "exit!");
    program.define(main, |b, _| {
        let status = b.constant(Class::Word, 0);
        b.call(exit, &[status]);
    });
    assert!(validate(&program).is_ok());
}

/// One routine, reached by two names. What a program calls a thing and what
/// answers for it are different names, so a program may declare the same
/// routine at as many types as it uses it at -- there is no body to copy, so
/// nothing is duplicated by saying it twice.
#[test]
fn two_names_may_give_the_same_routine() {
    let mut program = barb::Program::default();
    let nat = program.declare_type("Nat");
    program.define_type(nat, &[("Zero", &[]), ("Succ", &[nat])]);
    let bool_ = program.declare_type("Bool");
    program.define_type(bool_, &[("False", &[]), ("True", &[])]);

    let holds = |program: &mut barb::Program, name, type_| {
        let id = program.declare(name, &[type_], type_);
        program.answered_by(id, "hold");
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
        offered: false,
        authority: false,
        takes: vec![crate::platform::Takes::Scalar(Class::Word)],
        returns: crate::platform::Returns::Value(Class::Word),
        through: None,
    });

    let machine = lower(&mut program, &routines).expect("a representable program");
    let held: Vec<&str> = machine
        .functions()
        .iter()
        .filter(|f| f.definition == Definition::External)
        .map(|f| machine.name(f.name))
        .collect();
    // Lowering resolves source aliases; machine declarations retain only the
    // provider name. Parameter names are shared diagnostic symbols.
    assert_eq!(held, ["hold", "hold"], "both answered elsewhere");
    assert_eq!(machine.symbols.len(), 3, "main, hold, and v0 only");
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
        offered: false,
        authority: false,
        takes: vec![crate::platform::Takes::Scalar(Class::fixed(4))],
        returns: crate::platform::Returns::Unit,
        through: None,
    });

    let held = |value: u64| {
        let mut program = barb::Program::default();
        let nat = program.declare_type("Nat");
        program.define_type(nat, &[("Zero", &[]), ("Succ", &[nat])]);
        let unit = program.declare_type("Unit");
        program.define_type(unit, &[("Only", &[])]);

        let narrow = program.declare("narrow", &[nat], unit);
        program.answered_by(narrow, "narrow");

        let number = program.intern_number(nat, value).unwrap();
        let main = program.declare("main", &[], nat);
        program.define(main, |b, _| {
            let held = b.known(number);
            b.call(narrow, &[held]);
            held
        });
        program.set_entry(main);

        lower(&mut program, &routines)
    };

    held(9).expect("a value inside four bits");

    let refused = held(100).unwrap_err();
    assert!(refused.contains("`narrow`"), "{refused}");
}

/// A payload-carrying constructor is a cell, not merely its tag.
#[test]
fn a_constructor_that_carries_something_is_not_a_tag() {
    let routines = crate::platform::Routines::builtin();
    let mut source = barb::Program::default();
    let nat = source.declare_type("Nat");
    source.define_type(nat, &[("Zero", &[]), ("Succ", &[nat])]);
    let maybe = source.declare_type("Maybe");
    source.define_type(maybe, &[("None", &[]), ("Some", &[nat])]);
    let (zero, some) = (source.ctor_at(nat, 0), source.ctor_at(maybe, 1));
    let world = host(&mut source, nat);
    let unwrap = source.declare("unwrap", &[maybe], nat);
    source.define(unwrap, |b, args| {
        b.match_(args[0], maybe, |b, ctor, fields| {
            if ctor == some {
                fields[0]
            } else {
                b.con(zero, &[])
            }
        })
    });
    let main = source.declare_named("main!", &[("host", world.host)], world.never);
    source.define(main, |b, args| {
        let n = b.call(world.input, &[args[0]]);
        let held = b.con(some, &[n]);
        b.call(unwrap, &[held]);
        let status = b.con(zero, &[]);
        b.call(world.exit, &[args[0], status])
    });
    source.set_entry(main);
    let program = lower(&mut source, &routines).unwrap();
    assert!(program.ops.iter().any(|op| matches!(op, Op::Cell { .. })));
    assert!(program.classes.as_slice().contains(&Class::Cell));
}

/// What a routine reads is what the name means, not what a program hands
/// it. A type with one constructor says nothing by being one value rather
/// than another, so it carries no bits and is not passed at all -- which
/// leaves `exit!` with no status to leave with.
#[test]
fn an_effect_hands_over_what_the_routine_reads() {
    let routines = crate::platform::Routines::builtin();
    let mut source = barb::Program::default();
    let nat = source.declare_type("Nat");
    source.define_type(nat, &[("Zero", &[])]);
    let zero = source.ctor_at(nat, 0);
    let world = host(&mut source, nat);
    let main = source.declare_named("main!", &[("host", world.host)], world.never);
    source.define(main, |b, args| {
        let status = b.con(zero, &[]);
        b.call(world.exit, &[args[0], status])
    });
    source.set_entry(main);
    let refused = machine(source, &routines).unwrap_err();
    assert!(
        refused.contains("`exit!` reads a word, and is handed nothing"),
        "{refused}"
    );
}

/// How wide a number is held is what its values can be, worked out by the
/// tier above from what the program does with them. Nothing says it and
/// nothing wraps: a value needing three bits is held in three bits, and a
/// value nothing bounds is held in a machine word.
#[test]
fn how_wide_a_number_is_held_is_what_it_can_be() {
    let routines = crate::platform::Routines::builtin();
    let mut library = barb::fixture::Library::new();
    let two = library.number(2);
    let (nat, add) = (library.nat, library.add);
    let world = host(&mut library.program, nat);
    let main = library
        .program
        .declare_named("main!", &[("host", world.host)], world.never);
    library.program.define(main, |b, args| {
        let two = b.known(two);
        let four = b.call(add, &[two, two]);
        b.call(world.exit, &[args[0], four])
    });
    library.program.set_entry(main);
    let program = machine(library.program, &routines).expect("a program");
    let held: Vec<_> = (0..program.values_count())
        .map(|at| program.class(ValueId::at(at)))
        .collect();

    // Two and two is four, which three bits hold.
    assert!(held.iter().any(|held| held.width() == Some(3)), "{held:?}");
    assert!(
        held.iter()
            .all(|held| held.width().is_some_and(|bits| bits <= 3) || *held == Class::Word),
        "{held:?}"
    );
}
