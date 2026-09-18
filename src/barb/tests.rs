use super::*;

/// `Nat`, `U8`, and `List_U8`, which between them reach every case the
/// encoding has.
pub(super) fn types() -> (Program, TypeId, TypeId, TypeId) {
    let mut program = Program::default();
    let nat = program.declare_type("Nat");
    program.define_type(nat, &[("Zero", &[]), ("Succ", &[nat])]);
    let byte = program.declare_type("U8");
    program.define_type(byte, &[("Zero", &[]), ("Succ", &[byte])]);
    let list = program.declare_type("List_U8");
    program.define_type(list, &[("Nil", &[]), ("Cons", &[byte, list])]);
    (program, nat, byte, list)
}

pub(super) fn nat(program: &Program, id: TypeId, value: u64) -> Value {
    let mut term = Value(program.ctor_at(id, 0), Vec::new());
    for _ in 0..value {
        term = Value(program.ctor_at(id, 1), vec![term]);
    }
    term
}

fn list(program: &Program, list: TypeId, byte: TypeId, bytes: &[u8]) -> Value {
    let mut term = Value(program.ctor_at(list, 0), Vec::new());
    for value in bytes.iter().rev() {
        term = Value(
            program.ctor_at(list, 1),
            vec![nat(program, byte, u64::from(*value)), term],
        );
    }
    term
}

#[test]
fn a_name_is_interned_once_and_reads_back() {
    let (mut program, nat, byte, list) = types();
    // `Zero` names a constructor of both `Nat` and `U8`; it is one symbol.
    let on_nat = program.ctor(program.ctor_at(nat, 0)).name;
    let on_byte = program.ctor(program.ctor_at(byte, 0)).name;
    assert_eq!(on_nat, on_byte, "one name, one symbol");
    assert_eq!(program.name(on_nat), "Zero");
    assert_eq!(program.name(program.type_(list).name), "List_U8");

    // Interning is idempotent, so a name costs one entry however often it is
    // written, and asking for one already held answers what is already there.
    assert_eq!(program.symbol("Zero"), on_nat);

    // Every name the program uses, once each and end to end: naming things
    // costs no allocation beyond the pool growing.
    let names = "NatZeroSuccU8List_U8NilCons";
    assert_eq!(
        program.names_text(),
        names,
        "each name once, in declaration order"
    );
}

#[test]
fn a_term_stays_small() {
    assert_eq!(size_of::<Expr>(), 16);
    assert_eq!(size_of::<Arm>(), 16);
    assert_eq!(size_of::<Body>(), 12);
    assert_eq!(size_of::<Atom>(), 4);
}

#[test]
fn a_spine_is_recognised_and_a_branching_type_is_not() {
    let (mut program, nat, _, list) = types();
    assert!(matches!(shape(&program, nat), Shape::Spine { .. }));
    assert!(matches!(shape(&program, list), Shape::Spine { .. }));

    let tree = program.declare_type("Tree");
    program.define_type(tree, &[("Leaf", &[]), ("Node", &[tree, tree])]);
    assert_eq!(shape(&program, tree), Shape::Tagged, "two recursive fields");

    let extra = program.declare_type("Three");
    program.define_type(extra, &[("A", &[]), ("B", &[extra]), ("C", &[])]);
    assert_eq!(shape(&program, extra), Shape::Tagged, "a third constructor");
}

#[test]
fn a_natural_costs_the_logarithm_of_its_value() {
    let (mut program, nat_id, _, _) = types();
    let thousand = nat(&program, nat_id, 1000);
    let id = program.intern(nat_id, &thousand);
    assert_eq!(
        program.known_bytes(id),
        [0xE8, 0x07],
        "1000, seven bits a byte"
    );
    assert_eq!(
        decode(&program, nat_id, program.known_bytes(id)).0,
        thousand
    );
    assert_eq!(
        as_number(&program, nat_id, program.known_bytes(id)),
        Some(1000)
    );
}

/// The same bytes, without ever building the chain they stand for. `decode`
/// and the tree a caller hands `intern` both cost the magnitude; these do not.
#[test]
fn a_number_and_a_run_of_bytes_can_be_written_outright() {
    let (mut program, nat_id, byte, list_id) = types();
    let chain = program.intern(nat_id, &nat(&program, nat_id, 1000));
    let direct = program.intern_number(nat_id, 1000);
    assert_eq!(program.known_bytes(chain), program.known_bytes(direct));

    let built = list(&program, list_id, byte, b"Hello");
    let chain = program.intern(list_id, &built);
    let direct = program.intern_bytes(list_id, b"Hello");
    assert_eq!(program.known_bytes(chain), program.known_bytes(direct));
}

#[test]
fn an_ascii_string_is_its_own_bytes_after_the_count() {
    let (mut program, _, byte, list_id) = types();
    let hello = list(&program, list_id, byte, b"Hello");
    let id = program.intern(list_id, &hello);
    assert_eq!(program.known_bytes(id), b"\x05Hello");

    let lifted = as_bytes(&program, list_id, program.known_bytes(id));
    assert_eq!(lifted, Some(&b"Hello"[..]), "liftable as it stands");
    assert_eq!(decode(&program, list_id, program.known_bytes(id)).0, hello);
}

/// A byte past 127 takes two bytes to encode, so the run is no longer the
/// value and a target has to decode it.
#[test]
fn a_string_past_ascii_is_not_liftable() {
    let (mut program, _, byte, list_id) = types();
    let cafe = list(&program, list_id, byte, "café".as_bytes());
    let id = program.intern(list_id, &cafe);
    assert!(as_bytes(&program, list_id, program.known_bytes(id)).is_none());
    assert_eq!(decode(&program, list_id, program.known_bytes(id)).0, cafe);
}

#[test]
fn a_record_costs_no_tag_and_packs_into_a_list() {
    let (mut program, nat_id, _, _) = types();
    let point = program.declare_type("Point");
    program.define_type(point, &[("MkPoint", &[nat_id, nat_id])]);
    let points = program.declare_type("List_Point");
    program.define_type(points, &[("Nil", &[]), ("Cons", &[point, points])]);

    let at = |program: &Program, x, y| {
        Value(
            program.ctor_at(point, 0),
            vec![nat(program, nat_id, x), nat(program, nat_id, y)],
        )
    };
    let mut value = Value(program.ctor_at(points, 0), Vec::new());
    for (x, y) in [(3u64, 4u64), (1, 2)] {
        value = Value(program.ctor_at(points, 1), vec![at(&program, x, y), value]);
    }
    let id = program.intern(points, &value);
    assert_eq!(
        program.known_bytes(id),
        [2, 1, 2, 3, 4],
        "count, then packed pairs"
    );
    assert_eq!(decode(&program, points, program.known_bytes(id)).0, value);
}

/// `add(a, b)` by recursion on the second argument, which is the shape every
/// numeric operation has before the machine tier recognises it.
#[test]
fn the_builder_writes_the_lets_itself() {
    let (mut program, nat, _, _) = types();
    let add = program.declare("add", &[nat, nat], nat);
    program.define(add, |b, args| {
        let (left, right) = (args[0], args[1]);
        b.match_(right, nat, |b, ctor, fields| match fields {
            // Zero: the left operand, untouched.
            [] => left,
            // Succ(k): Succ(add(left, k)).
            [k] => {
                let rest = b.call(add, &[left, *k]);
                b.con(ctor, &[rest])
            }
            _ => unreachable!("Nat takes at most one field"),
        })
    });

    // Two parameters, `k` in the recursive arm, and the call bound inside it.
    // Neither the constructor nor the match binds anything: each is the tail
    // of its body.
    assert_eq!(program.locals(add), 4);

    let body = program.function(add).body.expect("a defined function");
    assert!(
        program.bindings(body.bindings).is_empty(),
        "the match is the tail, with nothing bound before it"
    );
    let Expr::Match(scrutinee, arms) = program.expr(body.tail) else {
        panic!("the body answers with the match itself");
    };
    assert_eq!(scrutinee, Atom(Local(1)), "the second parameter");
    let arms = program.arms(arms).to_vec();
    assert_eq!(arms.len(), 2, "one arm per constructor, by construction");
    assert_eq!(
        program.expr(arms[0].body.tail),
        Expr::Atom(Atom(Local(0))),
        "Zero answers the left operand"
    );

    // The recursive arm binds its call and answers the constructor.
    let recursive = arms[1].body;
    let [call] = program.bindings(recursive.bindings) else {
        panic!("one binding, for the call");
    };
    assert!(matches!(program.expr(*call), Expr::Call(..)));
    assert!(matches!(program.expr(recursive.tail), Expr::Con(..)));
}

#[test]
fn two_and_two_reads_back_as_what_was_written() {
    let program = crate::two_and_two();
    assert_eq!(
        program.render(),
        "Nat = Zero | Succ(Nat)

add(v0: Nat, v1: Nat) -> Nat =
  match v1 {
    Zero =>
      v0
    Succ(v2) =>
      v3 = add(v0, v2)
      Succ(v3)
  }

main() -> Nat =
  v0 = 2
  add(v0, v0)
"
    );
}

#[test]
fn addition_is_recognised_and_its_near_miss_is_not() {
    let program = crate::two_and_two();
    let facts = recognise(&program);
    let add = FnId::at(0);
    assert_eq!(program.name(program.function(add).name), "add");
    assert_eq!(facts.operation(add), Some(Operation::Add));
    assert_eq!(
        facts.operation(FnId::at(1)),
        None,
        "main takes no arguments"
    );

    // The same shape, answering the argument it counted down rather than the
    // one it kept. That is the identity on its second argument, not addition.
    let mut program = Program::default();
    let nat = program.declare_type("Nat");
    program.define_type(nat, &[("Zero", &[]), ("Succ", &[nat])]);
    let wrong = program.declare("wrong", &[nat, nat], nat);
    program.define(wrong, |b, args| {
        let right = args[1];
        b.match_(right, nat, |b, ctor, fields| match fields {
            [] => right,
            [k] => {
                let rest = b.call(wrong, &[args[0], *k]);
                b.con(ctor, &[rest])
            }
            _ => unreachable!("Nat takes at most one field"),
        })
    });
    assert_eq!(recognise(&program).operation(wrong), None);
}

/// The surface: the same program as [`crate::two_and_two`], written out.
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

exit!(v0: Host, v1: Nat) -> Never =
  <elsewhere>

add(v0: Nat, v1: Nat) -> Nat =
  match v1 {
    Zero =>
      v0
    Succ(v2) =>
      v3 = add(v0, v2)
      Succ(v3)
  }

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

exit!(v0: Host, v1: Nat) -> Never =
  <elsewhere>

double(v0: Nat) -> Nat =
  add(v0, v0)

add(v0: Nat, v1: Nat) -> Nat =
  match v1 {
    Zero =>
      v0
    Succ(v2) =>
      v3 = add(v0, v2)
      Succ(v3)
  }

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
         main!(h) -> maybe!(h Succ(Zero))",
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
         main!(h) -> exit!(h pick!(h Succ(Succ(Zero))))",
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

         main!(h) -> exit!(h status!(h flag!(h Succ(Zero))))",
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

/// What the compiler may not see through. `opaque!` answers what it was
/// given, so its type is the type it was given -- and it is an effect,
/// which is what makes it the one thing the tier above stops at.
#[test]
fn a_value_handed_over_is_one_nothing_worked_out() {
    let program = parse(
        "type Nat Zero Succ(Nat)

         add(a Zero) -> a
         add(a Succ(k)) -> Succ(add(a k))

         main!(h) ->
           two = opaque!(h Succ(Succ(Zero)))
           exit!(h add(two two))",
    )
    .expect("a program");
    assert!(
        program
            .render()
            .contains("opaque!(v0: Host, v1: Nat) -> Nat"),
        "{}",
        program.render()
    );

    // A pure name may not call one, like any other effect.
    let refused = parse(
        "type Nat Zero Succ(Nat)
         quietly(h n) -> opaque!(h n)
         main!(h) -> exit!(h quietly(h Zero))",
    )
    .unwrap_err();
    assert!(
        refused.contains("`quietly` is pure and calls `opaque!`"),
        "{refused}"
    );
}

/// What a number can be, worked out from what a program does with it. A
/// value handed over is unknown and its bounds are not: `opaque!` answers
/// what it was given, so what it answers is between what that was.
#[test]
fn what_a_number_can_be_is_read_off_what_is_done_with_it() {
    // What a definition answers, which is what its callers hold.
    let held = |text: &str, name: &str| {
        let program = parse(text).expect("a program");
        let facts = recognise(&program);
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
           two = opaque!(h Succ(Succ(Zero)))
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
           n = opaque!(h Succ(Zero))
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
        let facts = recognise(&program);
        (program, facts)
    };

    let (program, facts) = held(
        "type Nat Zero Succ(Nat)
         which(Zero) -> Zero
         which(Succ(k)) -> k
         main!(h) ->
           n = opaque!(h Succ(Succ(Zero)))
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

/// What the tiers below are entitled to assume. A program built rather than
/// written reaches them too, and nothing about a builder makes a call give
/// a name what it takes.
#[test]
fn a_program_built_wrongly_is_refused() {
    let mut program = Program::default();
    let nat = program.declare_type("Nat");
    program.define_type(nat, &[("Zero", &[]), ("Succ", &[nat])]);
    let takes_two = program.declare("takes_two", &[nat, nat], nat);
    program.define(takes_two, |_, args| args[0]);
    let zero = program.ctor_at(nat, 0);
    let main = program.declare("main", &[], nat);
    program.define(main, |b, _| {
        let held = b.con(zero, &[]);
        b.call(takes_two, &[held])
    });
    program.set_entry(main);

    let refused = validate(&program).unwrap_err();
    assert!(
        refused.contains("gives `takes_two` 1 where it takes 2"),
        "{refused}"
    );
}

/// A program with nowhere to start is not a program.
#[test]
fn a_program_says_where_it_starts() {
    let mut program = Program::default();
    let nat = program.declare_type("Nat");
    program.define_type(nat, &[("Zero", &[]), ("Succ", &[nat])]);
    let refused = validate(&program).unwrap_err();
    assert!(refused.contains("where the program starts"), "{refused}");
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
