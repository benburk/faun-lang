use faun_core::barb::*;

/// Every test here reads against what a compiler knows, since none of them
/// is about a routine somebody wrote down.
fn parse(text: &str) -> Result<Program, String> {
    super::parse(text, &faun_core::platform::Routines::builtin())
}

#[test]
fn a_program_reads_from_text() {
    let program = parse(
        "type Nat Zero Succ(Nat)

         add(a Zero) -> a
         add(a Succ(k)) -> Succ(add(a k))

         main!(h) -> exit!(h add(Succ(Succ(Zero)) Succ(Succ(Zero))))",
    )
    .expect("a program");
    assert_eq!(
        program.render(),
        "Host = Host
Unit = Unit
Never
Nat = Zero | Succ(Nat)

exit!(v0: Host, v1: Nat) -> Never = <elsewhere>

add(v0: Nat, v1: Nat) -> Nat =
  match v1
    Zero =>
      v0
    Succ(v2) =>
      v3 = add(v0, v2)
      Succ(v3)

main!(v0: Host) -> Never =
  v1 = Zero
  v2 = Succ(v1)
  v3 = Succ(v2)
  v4 = Zero
  v5 = Succ(v4)
  v6 = Succ(v5)
  v7 = add(v3, v6)
  exit!(v0, v7)
"
    );
}

#[test]
fn what_the_surface_will_not_read_it_names() {
    // A pattern is one constructor deep: anything further is a name, and
    // a name is a word rather than something applied.
    let deep = "type Nat Zero Succ(Nat)
                f(Succ(Succ(k))) -> k
                f(a) -> a
                main!(h) -> exit!(h f(Zero))";
    assert!(parse(deep).unwrap_err().contains("expected a name"));

    let comma = "type Nat Zero Succ(Nat)
                 f(a, b) -> a
                 main!(h) -> exit!(h Zero)";
    assert!(parse(comma).unwrap_err().contains("found `,`"));

    let missing = "type Nat Zero Succ(Nat)
                   f(Zero) -> g(Zero)
                   main!(h) -> exit!(h f(Zero))";
    assert!(parse(missing).unwrap_err().contains("nothing named `g`"));
}

/// Steps, which is what a body needs once anything answers something worth
/// keeping: each is bound where it was named, in the order written.
#[test]
fn a_body_works_things_out_on_the_way() {
    let program = parse(
        "type Nat Zero Succ(Nat)

         double(n) ->
           m = add(n n)
           m

         add(a Zero) -> a
         add(a Succ(k)) -> Succ(add(a k))

         main!(h) ->
           two = Succ(Succ(Zero))
           four = double(two)
           exit!(h four)",
    )
    .expect("a program");
    assert_eq!(
        program.render(),
        "Host = Host
Unit = Unit
Never
Nat = Zero | Succ(Nat)

exit!(v0: Host, v1: Nat) -> Never = <elsewhere>

double(v0: Nat) -> Nat =
  add(v0, v0)

add(v0: Nat, v1: Nat) -> Nat =
  match v1
    Zero =>
      v0
    Succ(v2) =>
      v3 = add(v0, v2)
      Succ(v3)

main!(v0: Host) -> Never =
  v1 = Zero
  v2 = Succ(v1)
  v3 = Succ(v2)
  v4 = double(v3)
  exit!(v0, v4)
"
    );
}

/// The authority cannot be made, and what an effect answers can: a branch
/// that does nothing has to answer something, and that is what it answers.
/// Constructors run until the next declaration, so what ends them is the
/// lookahead: a name, a parenthesised run, and an arrow is a clause, and
/// anything else is another constructor. The hard case is a constructor
/// taking nothing, written last.
#[test]
fn constructors_need_nothing_between_them() {
    let program = parse(
        "type Nat Succ(Nat) Zero
         type Pair Both(Nat Nat)

         first(Both(a b)) -> a

         main!(h) -> exit!(h first(Both(Succ(Zero) Zero)))",
    )
    .expect("a program");
    assert!(
        program.render().starts_with(
            "Host = Host\nUnit = Unit\nNever\nNat = Succ(Nat) | Zero\nPair = Both(Nat, Nat)\n"
        ),
        "{}",
        program.render()
    );
}

#[test]
fn a_program_may_write_unit_and_may_not_write_host() {
    let refused = parse(
        "type Nat Zero Succ(Nat)
         sneak() -> Host
         main!(h) -> exit!(h Zero)",
    )
    .unwrap_err();
    assert!(refused.contains("`Host` cannot be built"), "{refused}");

    let program = parse(
        "type Nat Zero Succ(Nat)
         maybe!(h Zero) -> Unit
         maybe!(h Succ(k)) -> exit!(h Succ(k))
         main!(h) ->
           held = maybe!(h Succ(Zero))
           exit!(h Zero)",
    )
    .expect("a program");
    assert!(
        program
            .render()
            .contains("maybe!(v0: Host, v1: Nat) -> Unit"),
        "{}",
        program.render()
    );
}

/// What a name answers when it does not answer. `exit!` leaves, so nothing
/// comes back from it and nothing comes back from a name that ends in it:
/// the type says so, and says it about a wrapper nobody declared.
#[test]
fn a_name_that_leaves_answers_never() {
    let program = parse(
        "type Nat Zero Succ(Nat)
         die!(h) -> exit!(h Zero)
         quit!(h n) -> die!(h)
         main!(h) -> quit!(h Zero)",
    )
    .expect("a program");
    let render = program.render();
    for held in [
        "exit!(v0: Host, v1: Nat) -> Never",
        "die!(v0: Host) -> Never",
        "quit!(v0: Host, v1: Nat) -> Never",
        "main!(v0: Host) -> Never",
    ] {
        assert!(render.contains(held), "{render}");
    }
}

/// A clause that leaves says nothing about what the others answer, which is
/// the whole of what `Never` buys: it stands at whatever type it is used at,
/// and the use beside it is what settles the name.
#[test]
fn a_clause_that_leaves_does_not_decide_what_the_rest_answer() {
    let program = parse(
        "type Nat Zero Succ(Nat)
         pick!(h Zero) -> exit!(h Zero)
         pick!(h Succ(k)) -> k
         main!(h) ->
           held = pick!(h Succ(Succ(Zero)))
           exit!(h held)",
    )
    .expect("a program");
    assert!(
        program.render().contains("pick!(v0: Host, v1: Nat) -> Nat"),
        "{}",
        program.render()
    );
}

/// Two uses of `exit!` at different types is not two types for `exit!`.
#[test]
fn leaving_twice_does_not_tie_the_two_together() {
    let program = parse(
        "type Nat Zero Succ(Nat)
         type Flag Off On

         status!(h Off) -> exit!(h Zero)
         status!(h On) -> Zero

         flag!(h Zero) -> exit!(h Zero)
         flag!(h Succ(k)) -> On

         main!(h) ->
           held = flag!(h Succ(Zero))
           kept = status!(h held)
           exit!(h kept)",
    )
    .expect("a program");
    let render = program.render();
    assert!(
        render.contains("status!(v0: Host, v1: Flag) -> Nat"),
        "{render}"
    );
    assert!(
        render.contains("flag!(v0: Host, v1: Nat) -> Flag"),
        "{render}"
    );
}

/// `Never` is the compiler's, like the authority is, and for the same
/// reason: a program that could declare it could disagree about it.
#[test]
fn a_program_may_not_declare_never() {
    let refused = parse(
        "type Never Nope
         main!(h) -> exit!(h Nope)",
    )
    .unwrap_err();
    assert!(refused.contains("`Never` is the compiler's"), "{refused}");

    let refused = parse(
        "type Nat Zero Succ(Nat)
         sneak() -> Never
         main!(h) -> exit!(h Zero)",
    )
    .unwrap_err();
    assert!(refused.contains("`Never` cannot be built"), "{refused}");
}

/// An argument too many lands on the name's own result, and the call
/// answers whatever was allocated after it. Nothing else says so.
#[test]
fn a_call_gives_a_name_what_it_takes() {
    let refused = |text: &str| parse(text).unwrap_err();

    let held = refused(
        "type Nat Zero Succ(Nat)
         f(a) -> a
         main!(h) -> exit!(h f(Zero Zero))",
    );
    assert!(held.contains("`f` takes 1 argument, not 2"), "{held}");

    let held = refused(
        "type Nat Zero Succ(Nat)
         f(a b) -> b
         main!(h) -> exit!(h f(Zero))",
    );
    assert!(held.contains("`f` takes 2 arguments, not 1"), "{held}");

    let held = refused(
        "type Nat Zero Succ(Nat)
         main!(h) -> exit!(h)",
    );
    assert!(held.contains("`exit!` takes 2 arguments"), "{held}");
}

/// A term reads a name as a constructor before it reads it as anything, so
/// a second one is not a second meaning but the loss of the first.
#[test]
fn a_name_stands_for_one_thing() {
    let refused = |text: &str| parse(text).unwrap_err();

    let held = refused(
        "type Nat Zero Succ(Nat)
         type Other Zero
         main!(h) -> exit!(h Succ(Zero))",
    );
    assert!(held.contains("`Zero` is declared twice"), "{held}");

    let held = refused(
        "type Nat Zero Succ(Nat)
         Zero(a) -> a
         main!(h) -> exit!(h Zero)",
    );
    assert!(held.contains("a constructor and a name"), "{held}");
}

/// Clauses are tried in the order they are written, so one that nothing
/// reaches is a mistake rather than a spare. Which rows reach a leaf is
/// what compiling the match works out, so this is one answer to what were
/// three different-looking mistakes.
#[test]
fn every_clause_is_reached_by_something() {
    let refused = |text: &str| parse(text).unwrap_err();

    // The same constructor twice.
    let held = refused(
        "type Nat Zero Succ(Nat)
         f(Zero) -> Zero
         f(Zero) -> Succ(Zero)
         f(Succ(k)) -> k
         main!(h) -> exit!(h f(Zero))",
    );
    assert!(held.contains("a clause nothing reaches"), "{held}");

    // Anything after a clause that takes the argument as a name.
    let held = refused(
        "type Nat Zero Succ(Nat)
         f(n) -> n
         f(Succ(k)) -> k
         main!(h) -> exit!(h f(Zero))",
    );
    assert!(held.contains("a clause nothing reaches"), "{held}");

    // Two clauses with nothing to tell them apart.
    let held = refused(
        "type Nat Zero Succ(Nat)
         f(a) -> a
         f(a) -> Zero
         main!(h) -> exit!(h f(Zero))",
    );
    assert!(held.contains("a clause nothing reaches"), "{held}");

    // And a column covered everywhere but one pairing.
    let held = refused(
        "type Nat Zero Succ(Nat)
         f(Zero Zero) -> Zero
         f(Succ(m) Zero) -> m
         main!(h) -> exit!(h f(Zero Zero))",
    );
    assert!(
        held.contains("no clause covers `Zero` and `Succ`"),
        "{held}"
    );
}

/// A clause matches as many arguments as it likes. `sub` and `cmp` are the
/// definitions that want it: both take two numbers apart at once, and both
/// are written here the way they are written anywhere.
#[test]
fn a_clause_matches_as_many_arguments_as_it_likes() {
    let program = parse(
        "type Nat Zero Succ(Nat)
         type Order Lt Eq Gt

         sub(Zero b) -> Zero
         sub(Succ(m) Zero) -> Succ(m)
         sub(Succ(m) Succ(n)) -> sub(m n)

         cmp(Zero Zero) -> Eq
         cmp(Zero Succ(n)) -> Lt
         cmp(Succ(m) Zero) -> Gt
         cmp(Succ(m) Succ(n)) -> cmp(m n)

         main!(h) -> exit!(h sub(Succ(Zero) Zero))",
    )
    .expect("a program");
    let render = program.render();
    assert!(render.contains("sub(v0: Nat, v1: Nat) -> Nat"), "{render}");
    assert!(
        render.contains("cmp(v0: Nat, v1: Nat) -> Order"),
        "{render}"
    );
}

/// There is nobody to hand the entry anything more than the authority.
#[test]
fn the_entry_is_handed_the_authority_and_nothing_else() {
    let held = parse(
        "type Nat Zero Succ(Nat)
         main!(h n) -> exit!(h n)",
    )
    .unwrap_err();
    assert!(held.contains("the authority and nothing else"), "{held}");
}

/// A clause binds its own names, and a name it binds is a value however it
/// is declared elsewhere.
#[test]
fn a_name_a_clause_binds_is_not_the_name_it_shadows() {
    parse(
        "type Nat Zero Succ(Nat)

         add(a Zero) -> a
         add(a Succ(k)) -> Succ(add(a k))

         f(add) -> add

         main!(h) -> exit!(h f(Succ(Zero)))",
    )
    .expect("a program");
}

/// What a number can be, worked out from what a program does with it.
#[test]
fn what_a_number_can_be_is_read_off_what_is_done_with_it() {
    // What a definition answers, which is what its callers hold.
    let held = |text: &str, name: &str| {
        let program = parse(text).expect("a program");
        let facts = analyze(&program);
        let at = program
            .functions()
            .iter()
            .position(|held| program.name(held.name) == name)
            .expect("the definition");
        (facts.answers(FnId::at(at)), program, facts)
    };

    // Two and two is four, whether or not the four is worked out here.
    let (bounds, ..) = held(
        "type Nat Zero Succ(Nat)
         add(a Zero) -> a
         add(a Succ(k)) -> Succ(add(a k))
         double(n) -> add(n n)
         main!(h) ->
           two = Succ(Succ(Zero))
           exit!(h double(two))",
        "double",
    );
    assert_eq!(
        bounds,
        Bounds {
            low: 4,
            high: Some(4)
        }
    );
    assert_eq!(bounds.width(), Some(3));

    // A definition counting up without a last step has no last value, and
    // saying so is what keeps the walk from going round after it.
    let (bounds, ..) = held(
        "type Nat Zero Succ(Nat)
         up(Zero) -> Succ(Zero)
         up(Succ(k)) -> Succ(Succ(up(k)))
         main!(h) ->
           n = Succ(Zero)
           exit!(h up(n))",
        "up",
    );
    assert_eq!(bounds.high, None);
    assert_eq!(bounds.width(), None);
}

/// What a match says of what it took apart: an arm for `Succ` binds one
/// less than what it matched, and what it matched is whatever the only name
/// calling it hands over.
#[test]
fn a_match_says_what_it_took_apart_could_be() {
    let held = |text: &str| {
        let program = parse(text).expect("a program");
        let facts = analyze(&program);
        (program, facts)
    };

    let (program, facts) = held(
        "type Nat Zero Succ(Nat)
         which(Zero) -> Zero
         which(Succ(k)) -> k
         main!(h) ->
           n = Succ(Succ(Zero))
           exit!(h which(n))",
    );
    let which = program
        .functions()
        .iter()
        .position(|held| program.name(held.name) == "which")
        .expect("the definition");
    assert_eq!(
        facts.takes(FnId::at(which))[0],
        Bounds {
            low: 2,
            high: Some(2)
        },
        "what it is handed"
    );
    assert_eq!(
        facts.answers(FnId::at(which)),
        Bounds {
            low: 1,
            high: Some(1)
        },
        "what `Succ` wraps, which is what it answers"
    );
}

/// Mutual recursion goes round the longer way, and the same argument has to
/// be what gets smaller all the way round: one definition taking its first
/// apart and the next taking its second is two things getting smaller by
/// turns, and reading the calls one at a time cannot tell that from neither
/// of them running out.
#[test]
fn what_goes_round_the_long_way_is_read_the_same() {
    let held = |text: &str| parse(text).and_then(|program| validate(&program));

    // Even and odd, each taking its argument apart before handing it on.
    assert!(
        held(
            "type Nat Zero Succ(Nat)
             type Bool False True

             even(Zero) -> True
             even(Succ(k)) -> odd(k)

             odd(Zero) -> False
             odd(Succ(k)) -> even(k)

             count(False) -> Zero
             count(True) -> Succ(Zero)

             main!(h) -> exit!(h count(even(Succ(Succ(Zero)))))",
        )
        .is_ok()
    );

    // And the same pair handing on what they were handed.
    let refused = held(
        "type Nat Zero Succ(Nat)
         type Bool False True

         even(n) -> odd(n)
         odd(n) -> even(n)

         count(False) -> Zero
         count(True) -> Succ(Zero)

         main!(h) -> exit!(h count(even(Zero)))",
    )
    .unwrap_err();
    assert!(refused.contains("nothing here shows"), "{refused}");
}

/// A program leaves through an effect. What it did is what it is, so the
/// last thing it does is the last thing there is -- nothing after it could
/// be told to run, and nothing before it can be dropped for want of a
/// reader, which is what holds a run of effects together once there is more
/// than one.
#[test]
fn a_program_leaves_through_an_effect() {
    // `maybe!` leaves on one arm and answers on the other, so a program
    // ending in it is one that might come back.
    let refused = parse(
        "type Nat Zero Succ(Nat)

         maybe!(h Zero) -> Unit
         maybe!(h Succ(k)) -> exit!(h Succ(k))

         main!(h) -> maybe!(h Zero)",
    )
    .unwrap_err();
    assert!(
        refused.contains("a program leaves through an effect"),
        "{refused}"
    );

    // Through a name that leaves counts: what matters is that nothing comes
    // back, not which name it was.
    parse(
        "type Nat Zero Succ(Nat)

         leave!(h n) -> exit!(h n)

         main!(h) -> leave!(h Zero)",
    )
    .expect("a program");
}

/// A term nested past what this reads is refused rather than read.
///
/// Everything that reads a term walks it the way it was written, so a term
/// deeper than the machine has stack for would take the compiler down with
/// it -- and refusing one after it is built is too late, since letting go of
/// a tree that deep is itself a walk.
#[test]
fn a_term_nested_too_deep_is_refused() {
    let held = |deep: usize| {
        format!(
            "type Nat Zero Succ(Nat)\n\nmain!(h) -> exit!(h {}Zero{})",
            "Succ(".repeat(deep),
            ")".repeat(deep)
        )
    };
    parse(&held(64)).expect("a program nested as deep as anyone writes");

    let refused = parse(&held(4096)).unwrap_err();
    assert!(refused.contains("nested more than"), "{refused}");
}

/// A routine somebody wrote down is one a program may name.
///
/// What a compiler knows is a set rather than a list it is built from, so a
/// name it has never heard of is reachable by handing it one more -- which
/// is what a file saying where to find something outside amounts to.
#[test]
fn a_routine_written_down_is_one_a_program_may_name() {
    let held = "type Nat Zero Succ(Nat)

                main!(h) ->
                  ticked = tick!(h)
                  exit!(h Zero)";

    let refused = parse(held).unwrap_err();
    assert!(refused.contains("nothing named `tick!`"), "{refused}");

    let mut routines = faun_core::platform::Routines::builtin();
    routines.push(faun_core::platform::Routine {
        name: "tick!".to_owned(),
        offered: true,
        takes: Vec::new(),
        returns: faun_core::platform::Returns::Unit,
    });

    let program = super::parse(held, &routines).expect("a program naming it");
    let tick = program
        .functions()
        .iter()
        .find(|f| program.name(f.name) == "tick!")
        .unwrap();
    let Definition::External { symbol, .. } = tick.definition else {
        panic!("an external declaration");
    };
    // The name written down is the name every tier below reads.
    assert_eq!(program.name(symbol), "tick!");
    assert!(
        program
            .render()
            .contains("tick!(v0: Host) -> Unit = <elsewhere>")
    );
    assert!(program.render().contains("tick!(v0)"));

    let facts = analyze(&program);
    let machine = faun_core::ir::lower(&program, &facts, &routines).unwrap();
    faun_core::ir::validate(&machine).unwrap();
    let providers: Vec<_> = machine
        .functions()
        .iter()
        .filter_map(faun_core::ir::Function::external)
        .map(|symbol| machine.name(symbol))
        .collect();
    assert_eq!(providers, ["exit!", "tick!"]);
}

/// An effect stands on its own: as the whole of a step, or as what a clause
/// answers. Which of two goes first is then answered by where their names
/// are written, rather than by how one term nests inside another.
#[test]
fn an_effect_may_not_stand_in_an_argument() {
    let refused = parse(
        "type Nat Zero Succ(Nat)

         main!(h) -> exit!(h argc!(h))",
    )
    .unwrap_err();
    assert!(refused.contains("stands on its own"), "{refused}");

    // The same program with the effect bound to a name, which says what
    // runs first by saying it first.
    parse(
        "type Nat Zero Succ(Nat)

         add(a Zero) -> a
         add(a Succ(k)) -> Succ(add(a k))

         main!(h) ->
           n = argc!(h)
           exit!(h add(n n))",
    )
    .expect("a program");
}

/// A routine nothing calls settles nothing, and needs to. One something
/// calls that still settles nothing is a program that never said which type
/// it was working over, and saying so beats saying the name does not exist.
#[test]
fn a_routine_nothing_settles_is_named_as_one() {
    let refused = parse(
        "type Nat Zero Succ(Nat)

         main!(h) ->
           n = argc!(h)
           exit!(h n)",
    )
    .unwrap_err();
    assert!(refused.contains("nothing says what type"), "{refused}");
}

/// A pure name may not do observable work.
#[test]
fn a_pure_name_cannot_call_an_effect() {
    let refused = parse(
        "type Nat Zero Succ(Nat)

         quietly(h) -> exit!(h Zero)

         main!(h) -> quietly(h)",
    )
    .unwrap_err();
    assert!(
        refused.contains("`quietly` is pure and calls `exit!`"),
        "{refused}"
    );
}
