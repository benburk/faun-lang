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

    assert_eq!(program.name(program.type_(nat).name), "Nat");
    assert_eq!(program.name(program.type_(byte).name), "U8");
}

#[test]
fn a_definition_replaces_external_metadata_instead_of_retaining_it() {
    let (mut program, nat, _, _) = types();
    let function = program.declare("external", &[], nat);
    assert_eq!(
        program.function(function).definition,
        Definition::External {
            symbol: program.function(function).name,
        }
    );
    program.answered_by(function, "provider");
    let Definition::External { symbol } = program.function(function).definition else {
        panic!("a declaration has no body");
    };
    assert_eq!(program.name(symbol), "provider");
    program.define(function, |b, _| {
        let value = b.number(nat, 3).unwrap();
        b.known(value)
    });
    assert!(matches!(
        program.function(function).definition,
        Definition::Body(_)
    ));
    assert_eq!(program.function(function).provider(), None);
    program.set_entry(function);
    validate(&program).unwrap();
}

#[test]
#[should_panic(expected = "only an external declaration can name a provider")]
fn a_defined_function_cannot_acquire_a_host_provider() {
    let (mut program, nat, _, _) = types();
    let function = program.declare("defined", &[], nat);
    program.define(function, |b, _| {
        let value = b.number(nat, 3).unwrap();
        b.known(value)
    });
    program.answered_by(function, "provider");
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
fn runtime_shapes_distinguish_sequences_from_other_spines_and_aggregates() {
    let (mut program, nat, byte, list) = types();
    assert!(matches!(
        type_shape(&program, nat),
        TypeShape::Natural { .. }
    ));
    assert!(matches!(
        type_shape(&program, list),
        TypeShape::Sequence { element, .. } if element == byte
    ));

    let empty = program.declare_type("Empty");
    program.define_type(empty, &[]);
    let unit = program.declare_type("Unitish");
    program.define_type(unit, &[("Only", &[])]);
    let wrapper = program.declare_type("Wrapped");
    program.define_type(wrapper, &[("Wrap", &[nat])]);
    let product = program.declare_type("Pair");
    program.define_type(product, &[("Pair", &[nat, nat])]);
    let enumeration = program.declare_type("Choice");
    program.define_type(enumeration, &[("Left", &[]), ("Right", &[])]);
    let sum = program.declare_type("Maybe");
    program.define_type(sum, &[("None", &[]), ("Some", &[nat])]);
    let wide = program.declare_type("WideSpine");
    program.define_type(wide, &[("Push", &[wide, nat, nat]), ("Empty", &[])]);

    assert_eq!(type_shape(&program, empty), TypeShape::Uninhabited);
    assert!(matches!(type_shape(&program, unit), TypeShape::Unit { .. }));
    assert!(matches!(
        type_shape(&program, wrapper),
        TypeShape::Wrapper { field, .. } if field == nat
    ));
    assert!(matches!(
        type_shape(&program, product),
        TypeShape::Product { .. }
    ));
    assert_eq!(type_shape(&program, enumeration), TypeShape::Enumeration);
    assert_eq!(type_shape(&program, sum), TypeShape::Sum);
    assert!(matches!(
        type_shape(&program, wide),
        TypeShape::Spine { .. }
    ));
}

#[test]
fn a_natural_costs_the_logarithm_of_its_value() {
    let (mut program, nat_id, _, _) = types();
    let thousand = nat(&program, nat_id, 1000);
    let id = program.intern(nat_id, &thousand).unwrap();
    assert_eq!(
        program.known_bytes(id),
        [0xE8, 0x07],
        "1000, seven bits a byte"
    );
    assert_eq!(
        decode(&program, nat_id, program.known_bytes(id)).0,
        thousand
    );
    let ConstantView::Natural(number) = program.constant(id).view() else {
        panic!("a natural");
    };
    assert_eq!(number.try_u64(), Ok(1000));
    let direct = program.intern_number(nat_id, 1000).unwrap();
    assert_eq!(program.known_bytes(id), program.known_bytes(direct));
}

#[test]
fn an_ascii_string_is_its_own_bytes_after_the_count() {
    let (mut program, _, byte, list_id) = types();
    let hello = list(&program, list_id, byte, b"Hello");
    let id = program.intern(list_id, &hello).unwrap();
    assert_eq!(program.known_bytes(id), b"\x05Hello");

    let ConstantView::Spine(spine) = program.constant(id).view() else {
        panic!("a spine");
    };
    assert_eq!(
        spine.byte_slice(),
        ByteView::Borrowed(b"Hello"),
        "liftable as it stands"
    );
    assert_eq!(decode(&program, list_id, program.known_bytes(id)).0, hello);
}

/// A byte past 127 takes two bytes to encode, so the run is no longer the
/// value and a target has to decode it.
#[test]
fn a_string_past_ascii_is_not_liftable() {
    let (mut program, _, byte, list_id) = types();
    let cafe = list(&program, list_id, byte, "café".as_bytes());
    let id = program.intern(list_id, &cafe).unwrap();
    let ConstantView::Spine(spine) = program.constant(id).view() else {
        panic!("a spine");
    };
    assert_eq!(spine.byte_slice(), ByteView::NeedsDecoding);
    assert_eq!(spine.to_bytes().as_deref(), Some("café".as_bytes()));
    let direct = program
        .intern_byte_spine(list_id, "café".as_bytes())
        .expect("a spine of natural bytes");
    assert_eq!(program.known_bytes(direct), program.known_bytes(id));
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
    let id = program.intern(points, &value).unwrap();
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

    let body = program.function(add).body().expect("a defined function");
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
    let program = crate::programs::two_and_two_in_barb();
    assert_eq!(
        program.render(),
        "Nat = Zero | Succ(Nat)

add(v0: Nat, v1: Nat) -> Nat =
  match v1
    Zero =>
      v0
    Succ(v2) =>
      v3 = add(v0, v2)
      Succ(v3)

main() -> Nat =
  v0 = 2
  add(v0, v0)
"
    );
}

#[test]
fn inline_types_are_written_at_their_uses_not_as_declarations() {
    let mut program = Program::default();
    let empty = program.declare_inline_type("[]");
    program.define_type(empty, &[]);
    program.declare("stop", &[], empty);
    assert_eq!(program.render(), "\nstop() -> [] = <elsewhere>\n");
}

#[test]
fn addition_is_recognised_and_its_near_miss_is_not() {
    let program = crate::programs::two_and_two_in_barb();
    let facts = analyzed(&program);
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
    assert_eq!(analyzed(&program).operation(wrong), None);
}

/// The surface: the same program as [`crate::two_and_two`], written out.
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

/// Recognized arithmetic works on the compact magnitude, not the unary tree.
#[test]
fn large_arithmetic_does_not_expand_constructor_spines() {
    let mut program = Program::default();
    let nat = program.declare_type("Nat");
    program.define_type(nat, &[("Zero", &[]), ("Succ", &[nat])]);

    let add = program.declare("add", &[nat, nat], nat);
    program.define(add, |b, args| {
        let (left, right) = (args[0], args[1]);
        b.match_(right, nat, |b, ctor, fields| match fields {
            [] => left,
            [k] => {
                let rest = b.call(add, &[left, *k]);
                b.con(ctor, &[rest])
            }
            _ => unreachable!("Nat takes at most one field"),
        })
    });

    let held = |magnitude| {
        let mut program = program.clone();
        let number = program.intern_number(nat, magnitude).unwrap();
        let main = program.declare("main", &[], nat);
        program.define(main, |b, _| {
            let value = b.known(number);
            b.call(add, &[value, value])
        });
        program.set_entry(main);
        fold(&mut program);
        program.render()
    };

    // Small enough to work out: what is left is the answer, and nothing to
    // work it out with.
    let small = held(3);
    assert!(small.contains("\n  6\n"), "{small}");
    assert!(!small.contains("add(v0, v0)"), "{small}");

    let large = held(4_000_000);
    assert!(large.contains("\n  8000000\n"), "{large}");
    assert!(!large.contains("add(v0, v0)"), "{large}");
}

/// A definition may go round only on something it took apart, so each time
/// round is over something smaller and the taking apart has an end.
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "a refused definition, the same shape taking its argument apart, and an alias"
)]
fn a_definition_that_does_not_stop_is_refused() {
    // spin(n) -> add(Zero spin(n))
    let mut lib = fixture::Library::new();
    let (nat, zero, add) = (lib.nat, lib.zero, lib.add);
    let p = &mut lib.program;
    let spin = p.declare("spin", &[nat], nat);
    p.define(spin, |b, args| {
        let nought = b.con(zero, &[]);
        let again = b.call(spin, &[args[0]]);
        b.call(add, &[nought, again])
    });
    enter(p, nat, spin, 0);
    let refused = validate(p).unwrap_err();
    assert!(
        refused.contains("nothing here shows `spin` stops"),
        "{refused}"
    );

    // The same shape, taking its argument apart: this one has an end.
    // twice(Zero) -> Zero
    // twice(Succ(k)) -> Succ(Succ(twice(k)))
    let mut lib = fixture::Library::new();
    let (nat, zero, succ) = (lib.nat, lib.zero, lib.succ);
    let p = &mut lib.program;
    let twice = p.declare("twice", &[nat], nat);
    p.define(twice, |b, args| {
        b.match_(args[0], nat, |b, ctor, fields| {
            if ctor == zero {
                return b.con(zero, &[]);
            }
            let rest = b.call(twice, &[fields[0]]);
            let once = b.con(succ, &[rest]);
            b.con(succ, &[once])
        })
    });
    enter(p, nat, twice, 2);
    validate(p).expect("a program that stops");

    // A local alias does not hide that the recursive argument was a field.
    // down(Zero) -> Zero
    // down(Succ(k)) -> alias = k down(alias)
    let mut lib = fixture::Library::new();
    let (nat, zero, succ) = (lib.nat, lib.zero, lib.succ);
    let p = &mut lib.program;
    let down = p.declare("down", &[nat], nat);
    // The builder never writes an alias, so the body is laid out directly:
    // the parameter is local 0, the field local 1 and the alias local 2.
    let at = |level| Atom(Local::at(level));
    let empty = p.terms.hold_atoms(std::iter::empty());
    let nought = p.terms.push(Expr::Con(zero, empty));
    let stopped = p.terms.hold_body(&[], nought);
    let alias = p.terms.push(Expr::Atom(at(1)));
    let args = p.terms.hold_atoms(std::iter::once(at(2)));
    let again = p.terms.push(Expr::Call(down, args));
    let descended = p.terms.hold_body(&[alias], again);
    let arms = p.terms.hold_arms(&[
        Arm {
            ctor: zero,
            body: stopped,
        },
        Arm {
            ctor: succ,
            body: descended,
        },
    ]);
    let tail = p.terms.push(Expr::Match(at(0), arms));
    let body = p.terms.hold_body(&[], tail);
    p.replace_bodies(vec![(down, body)]);
    enter(p, nat, down, 0);
    validate(p).expect("an alias retains the field's descent");
}

/// Constructor distances survive partial reconstruction: the recursive value
/// below removes two constructors and puts one back.
#[test]
fn size_change_accepts_reconstructed_subterms() {
    let (mut program, nat, _, _) = types();
    let zero = program.ctor_at(nat, 0);
    let successor = program.ctor_at(nat, 1);
    let descend = program.declare("descend", &[nat], nat);
    program.define(descend, |b, args| {
        b.match_(args[0], nat, |b, ctor, fields| {
            if ctor == zero {
                return b.con(zero, &[]);
            }
            b.match_(fields[0], nat, |b, ctor, fields| {
                if ctor == zero {
                    b.con(zero, &[])
                } else {
                    let predecessor = b.con(successor, &[fields[0]]);
                    b.call(descend, &[predecessor])
                }
            })
        })
    });
    program.set_entry(descend);

    validate(&program).expect("two constructors taken and one rebuilt is a decrease");
}

/// Recognized arithmetic bounds preserve decreases that are not visible as a
/// bare pattern field at the recursive call.
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "Fibonacci, factorial, GCD and popcount, each written as its equations"
)]
fn size_change_accepts_arithmetic_recursion() {
    let mut lib = fixture::Library::new();
    let (nat, zero, succ) = (lib.nat, lib.zero, lib.succ);
    let (add, mul, div, modulo) = (lib.add, lib.mul, lib.div, lib.modulo);
    let p = &mut lib.program;

    // fibonacci(Zero) -> Zero
    // fibonacci(Succ(n)) -> fibonacci_step(n)
    // fibonacci_step(Zero) -> Succ(Zero)
    // fibonacci_step(Succ(n)) ->
    //   previous = Succ(n)
    //   add(fibonacci(previous) fibonacci(n))
    let fibonacci = p.declare("fibonacci", &[nat], nat);
    let step = p.declare("fibonacci_step", &[nat], nat);
    p.define(fibonacci, |b, args| {
        b.match_(args[0], nat, |b, ctor, fields| {
            if ctor == zero {
                b.con(zero, &[])
            } else {
                b.call(step, &[fields[0]])
            }
        })
    });
    p.define(step, |b, args| {
        b.match_(args[0], nat, |b, ctor, fields| {
            if ctor == zero {
                let nought = b.con(zero, &[]);
                return b.con(succ, &[nought]);
            }
            let previous = b.con(succ, &[fields[0]]);
            let one = b.call(fibonacci, &[previous]);
            let two = b.call(fibonacci, &[fields[0]]);
            b.call(add, &[one, two])
        })
    });

    // factorial(Zero) -> Succ(Zero)
    // factorial(Succ(n)) -> mul(Succ(n) factorial(n))
    let factorial = p.declare("factorial", &[nat], nat);
    p.define(factorial, |b, args| {
        b.match_(args[0], nat, |b, ctor, fields| {
            if ctor == zero {
                let nought = b.con(zero, &[]);
                return b.con(succ, &[nought]);
            }
            let whole = b.con(succ, &[fields[0]]);
            let rest = b.call(factorial, &[fields[0]]);
            b.call(mul, &[whole, rest])
        })
    });

    // gcd(a Zero) -> a
    // gcd(a Succ(b)) -> divisor = Succ(b) gcd(divisor mod(a divisor))
    let gcd = p.declare("gcd", &[nat, nat], nat);
    p.define(gcd, |b, args| {
        b.match_(args[1], nat, |b, ctor, fields| {
            if ctor == zero {
                return args[0];
            }
            let divisor = b.con(succ, &[fields[0]]);
            let remainder = b.call(modulo, &[args[0], divisor]);
            b.call(gcd, &[divisor, remainder])
        })
    });

    // popcount(Zero) -> Zero
    // popcount(Succ(n)) ->
    //   value = Succ(n)
    //   two = Succ(Succ(Zero))
    //   half = div(value two)
    //   add(mod(value two) popcount(half))
    let popcount = p.declare("popcount", &[nat], nat);
    p.define(popcount, |b, args| {
        b.match_(args[0], nat, |b, ctor, fields| {
            if ctor == zero {
                return b.con(zero, &[]);
            }
            let value = b.con(succ, &[fields[0]]);
            let nought = b.con(zero, &[]);
            let one = b.con(succ, &[nought]);
            let two = b.con(succ, &[one]);
            let half = b.call(div, &[value, two]);
            let low = b.call(modulo, &[value, two]);
            let rest = b.call(popcount, &[half]);
            b.call(add, &[low, rest])
        })
    });

    let main = p.declare("main", &[], nat);
    p.define(main, |b, _| {
        let nought = b.con(zero, &[]);
        let counts = [fibonacci, factorial, popcount].map(|id| b.call(id, &[nought]));
        let divided = b.call(gcd, &[counts[0], counts[1]]);
        b.call(add, &[divided, counts[2]])
    });
    p.set_entry(main);
    validate(p).expect("modulo, Fibonacci, factorial, GCD, and popcount all stop");
}

/// Weak arithmetic bounds are not strict decreases. Dividing by one and
/// taking a remainder with zero therefore cannot disguise an unchanged
/// recursive argument.
#[test]
fn size_change_rejects_non_decreasing_arithmetic() {
    let mut lib = fixture::Library::new();
    let (nat, zero, succ) = (lib.nat, lib.zero, lib.succ);
    let (div, modulo) = (lib.div, lib.modulo);
    let p = &mut lib.program;
    // stall(Zero) -> Zero
    // stall(Succ(n)) -> value = Succ(n) one = Succ(Zero) stall_mod(div(value one))
    // stall_mod(n) -> zero = Zero stall(mod(n zero))
    let stall = p.declare("stall", &[nat], nat);
    let stall_mod = p.declare("stall_mod", &[nat], nat);
    p.define(stall, |b, args| {
        b.match_(args[0], nat, |b, ctor, fields| {
            if ctor == zero {
                return b.con(zero, &[]);
            }
            let value = b.con(succ, &[fields[0]]);
            let nought = b.con(zero, &[]);
            let one = b.con(succ, &[nought]);
            let divided = b.call(div, &[value, one]);
            b.call(stall_mod, &[divided])
        })
    });
    p.define(stall_mod, |b, args| {
        let nought = b.con(zero, &[]);
        let remainder = b.call(modulo, &[args[0], nought]);
        b.call(stall, &[remainder])
    });
    enter(p, nat, stall, 0);
    let refused = validate(p).unwrap_err();
    assert!(
        refused.contains("nothing here shows `stall`, `stall_mod` stops"),
        "{refused}"
    );
}

/// Names that go round together are one round, however many of them there
/// are and whichever of them is reached first. What every definition in one
/// reaches is every other, so a round is found the way a program's calls
/// make it rather than by asking each pair in turn.
#[test]
fn a_round_is_every_name_that_goes_round_together() {
    // Three deep, taking a part each time round, which stops.
    // one(Zero) -> Zero    one(Succ(k)) -> two(k)
    // two(Zero) -> Zero    two(Succ(k)) -> three(k)
    // three(Zero) -> Zero  three(Succ(k)) -> one(k)
    let mut lib = fixture::Library::new();
    let (nat, zero) = (lib.nat, lib.zero);
    let p = &mut lib.program;
    let round = ["one", "two", "three"].map(|name| p.declare(name, &[nat], nat));
    for (at, &id) in round.iter().enumerate() {
        let next = round[(at + 1) % round.len()];
        p.define(id, |b, args| {
            b.match_(args[0], nat, |b, ctor, fields| {
                if ctor == zero {
                    b.con(zero, &[])
                } else {
                    b.call(next, &[fields[0]])
                }
            })
        });
    }
    enter(p, nat, round[0], 3);
    validate(p).expect("a round that takes something apart");

    // The same three, going round on what they were handed.
    // one(n) -> add(Zero two(n)), and so on round.
    let mut lib = fixture::Library::new();
    let (nat, zero, add) = (lib.nat, lib.zero, lib.add);
    let p = &mut lib.program;
    let round = ["one", "two", "three"].map(|name| p.declare(name, &[nat], nat));
    for (at, &id) in round.iter().enumerate() {
        let next = round[(at + 1) % round.len()];
        p.define(id, |b, args| {
            let nought = b.con(zero, &[]);
            let again = b.call(next, &[args[0]]);
            b.call(add, &[nought, again])
        });
    }
    enter(p, nat, round[0], 0);
    let refused = validate(p).unwrap_err();
    assert!(refused.contains("`one`, `two`, `three` stops"), "{refused}");
}

/// Give `program` an entry answering `called(n)`.
fn enter(program: &mut Program, nat: TypeId, called: FnId, n: u64) {
    let n = program.intern_number(nat, n).unwrap();
    let main = program.declare("main", &[], nat);
    program.define(main, |b, _| {
        let n = b.known(n);
        b.call(called, &[n])
    });
    program.set_entry(main);
}

/// Size-change termination follows each repeatable path rather than demanding
/// that one argument decrease at every recursive call site.
#[test]
fn size_change_accepts_descent_on_alternative_arguments() {
    let (mut program, _, _, list) = types();
    let choice = program.declare_type("Choice");
    program.define_type(choice, &[("Left", &[]), ("Right", &[])]);

    let merge = program.declare("merge", &[list, list, choice], list);
    let left_choice = program.ctor_at(choice, 0);
    program.define(merge, |b, args| {
        let (left, right, choose) = (args[0], args[1], args[2]);
        b.match_(choose, choice, |b, ctor, _| {
            if ctor == left_choice {
                b.match_(left, list, |b, _, fields| match fields {
                    [] => right,
                    [_, tail] => b.call(merge, &[*tail, right, choose]),
                    _ => unreachable!("a list has zero or two fields"),
                })
            } else {
                b.match_(right, list, |b, _, fields| match fields {
                    [] => left,
                    [_, tail] => b.call(merge, &[left, *tail, choose]),
                    _ => unreachable!("a list has zero or two fields"),
                })
            }
        })
    });
    program.set_entry(merge);

    validate(&program).expect("each path through merge descends on one list");
}

/// A decrease somewhere in a matrix is not enough: only a strict diagonal in
/// every idempotent composition proves that repeated calls run out.
#[test]
fn size_change_rejects_an_unchanged_permutation() {
    let (mut program, nat, _, _) = types();
    let swap = program.declare("swap", &[nat, nat], nat);
    program.define(swap, |b, args| b.call(swap, &[args[1], args[0]]));
    program.set_entry(swap);

    let refused = validate(&program).unwrap_err();
    assert!(
        refused.contains("nothing here shows `swap` stops"),
        "{refused}"
    );
}
