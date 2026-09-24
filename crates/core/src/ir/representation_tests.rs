use super::tests::{World, host};
use super::*;
use crate::barb::fixture::Library;
use crate::{barb, platform::Routines};

fn bodies(program: &Program) -> usize {
    program
        .functions()
        .iter()
        .filter_map(Function::body)
        .count()
}

fn externals(program: &Program) -> usize {
    program
        .functions()
        .iter()
        .filter_map(Function::external)
        .count()
}

fn routines() -> Routines {
    Routines::builtin().with_word(64)
}

fn lower_program(source: &barb::Program) -> Result<Program, String> {
    lower(&mut source.clone(), &routines())
}

/// Natural arithmetic, the host, a byte held as eight flags and a signed
/// number held as a sum, with the few conversions these tests call. A test
/// adds its own entry.
struct Standard {
    library: Library,
    world: World,
    pos: barb::CtorId,
    u8_zero: barb::FnId,
    u8_ones: barb::FnId,
    u8_to_nat: barb::FnId,
    u8_from_nat: barb::FnId,
    int_from_nat: barb::FnId,
    int_abs: barb::FnId,
    int_negate: barb::FnId,
}

impl Standard {
    #[expect(
        clippy::too_many_lines,
        reason = "one definition per conversion, in the order a library declares them"
    )]
    fn new() -> Self {
        let mut library = Library::new();
        let world = host(&mut library.program, library.nat);
        let (nat, bool_) = (library.nat, library.bool_);
        let (zero, succ, yes, no) = (library.zero, library.succ, library.true_, library.false_);
        let (add, div, modulo, equals) = (library.add, library.div, library.modulo, library.equals);
        let (one, two) = (library.number(1), library.number(2));
        let p = &mut library.program;
        let u8_type = p.declare_type("U8");
        p.define_type(u8_type, &[("U8", &[bool_; 8])]);
        let byte = p.ctor_at(u8_type, 0);
        let int = p.declare_type("Int");
        p.define_type(int, &[("Pos", &[nat]), ("NegSucc", &[nat])]);
        let (pos, neg) = (p.ctor_at(int, 0), p.ctor_at(int, 1));

        let flags = |p: &mut barb::Program, name: &str, flag: barb::CtorId| {
            let id = p.declare(name, &[], u8_type);
            p.define(id, |b, _| {
                let flags: Vec<_> = (0..8).map(|_| b.con(flag, &[])).collect();
                b.con(byte, &flags)
            });
            id
        };
        let u8_zero = flags(p, "u8_zero", no);
        let u8_ones = flags(p, "u8_ones", yes);

        // digit(False n) -> add(n n); digit(True n) -> Succ(add(n n))
        let digit = p.declare("u8_digit", &[bool_, nat], nat);
        p.define(digit, |b, args| {
            let doubled = b.call(add, &[args[1], args[1]]);
            b.match_(args[0], bool_, |b, ctor, _| {
                if ctor == yes {
                    b.con(succ, &[doubled])
                } else {
                    doubled
                }
            })
        });
        let u8_to_nat = p.declare("u8_to_nat", &[u8_type], nat);
        p.define(u8_to_nat, |b, args| {
            b.match_(args[0], u8_type, |b, _, flags| {
                let mut value = b.con(zero, &[]);
                for &flag in flags.iter().rev() {
                    value = b.call(digit, &[flag, value]);
                }
                value
            })
        });

        // The low bit of each of eight halvings, lowest first.
        let low_bit = p.declare("u8_low_bit", &[nat], bool_);
        p.define(low_bit, |b, args| {
            let two = b.known(two);
            let rest = b.call(modulo, &[args[0], two]);
            let one = b.known(one);
            b.call(equals, &[rest, one])
        });
        let u8_from_nat = p.declare("u8_from_nat_wrapping", &[nat], u8_type);
        p.define(u8_from_nat, |b, args| {
            let two = b.known(two);
            let mut held = args[0];
            let mut flags = Vec::with_capacity(8);
            for _ in 0..8 {
                flags.push(b.call(low_bit, &[held]));
                held = b.call(div, &[held, two]);
            }
            b.con(byte, &flags)
        });

        let int_from_nat = p.declare("int_from_nat", &[nat], int);
        p.define(int_from_nat, |b, args| b.con(pos, &[args[0]]));
        let int_abs = p.declare("int_abs", &[int], nat);
        p.define(int_abs, |b, args| {
            b.match_(args[0], int, |b, ctor, fields| {
                if ctor == pos {
                    fields[0]
                } else {
                    b.con(succ, &[fields[0]])
                }
            })
        });
        // int_negate(Pos(Zero)) -> Pos(Zero); int_negate(Pos(Succ(n))) ->
        // NegSucc(n); int_negate(NegSucc(n)) -> Pos(Succ(n))
        let int_negate = p.declare("int_negate", &[int], int);
        p.define(int_negate, |b, args| {
            b.match_(args[0], int, |b, ctor, fields| {
                if ctor == neg {
                    let magnitude = b.con(succ, &[fields[0]]);
                    return b.con(pos, &[magnitude]);
                }
                b.match_(fields[0], nat, |b, ctor, below| {
                    if ctor == zero {
                        b.con(pos, &[fields[0]])
                    } else {
                        b.con(neg, &[below[0]])
                    }
                })
            })
        });
        Self {
            library,
            world,
            pos,
            u8_zero,
            u8_ones,
            u8_to_nat,
            u8_from_nat,
            int_from_nat,
            int_abs,
            int_negate,
        }
    }

    /// Give the program its entry, `main!(host)`, built by `body`.
    fn main(
        mut self,
        body: impl FnOnce(&mut barb::Builder<'_>, barb::Atom, &Self) -> barb::Atom,
    ) -> barb::Program {
        let world = &self.world;
        let main =
            self.library
                .program
                .declare_named("main!", &[("host", world.host)], world.never);
        let mut program = std::mem::take(&mut self.library.program);
        program.define(main, |b, args| body(b, args[0], &self));
        program.set_entry(main);
        barb::validate(&program).unwrap();
        program
    }

    /// `exit!(host status)`.
    fn exit(&self, b: &mut barb::Builder<'_>, host: barb::Atom, status: barb::Atom) -> barb::Atom {
        b.call(self.world.exit, &[host, status])
    }

    /// `exit!(host Zero)`.
    fn exit_zero(&self, b: &mut barb::Builder<'_>, host: barb::Atom) -> barb::Atom {
        let zero = b.con(self.library.zero, &[]);
        self.exit(b, host, zero)
    }

    /// A number known outright, built as the constructors that spell it.
    fn nat(&self, b: &mut barb::Builder<'_>, n: u64) -> barb::Atom {
        let mut held = b.con(self.library.zero, &[]);
        for _ in 0..n {
            held = b.con(self.library.succ, &[held]);
        }
        held
    }
}

#[test]
fn unused_library_types_and_functions_do_not_need_runtime_representations() {
    let source = Standard::new().main(|b, host, s| {
        let n = b.call(s.world.input, &[host]);
        let two = s.nat(b, 2);
        let rest = b.call(s.library.modulo, &[n, two]);
        s.exit(b, host, rest)
    });
    let mut optimized = source.clone();
    barb::optimize(&mut optimized);
    for machine in [
        lower_program(&source).unwrap(),
        crate::to_machine(&mut optimized, &routines()).unwrap(),
    ] {
        validate(&machine).unwrap();
        assert_eq!(bodies(&machine), 1, "only main is emitted");
        assert_eq!(externals(&machine), 2, "input and exit are retained");
    }
}

/// A byte's value and a signed magnitude, each worked out through the
/// library: all eight flags set is 255, and the magnitude of minus one is 1.
fn statuses(b: &mut barb::Builder<'_>, s: &Standard) -> [barb::Atom; 2] {
    let ones = b.call(s.u8_ones, &[]);
    let byte = b.call(s.u8_to_nat, &[ones]);
    let one = s.nat(b, 1);
    let positive = b.con(s.pos, &[one]);
    let negative = b.call(s.int_negate, &[positive]);
    let magnitude = b.call(s.int_abs, &[negative]);
    [byte, magnitude]
}

#[test]
fn folded_library_calls_leave_no_runtime_representation_demand() {
    let mut source = Standard::new().main(|b, host, s| {
        let [byte, magnitude] = statuses(b, s);
        let sum = b.call(s.library.add, &[byte, magnitude]);
        s.exit(b, host, sum)
    });
    barb::fold(&mut source);
    // The old function bodies and library types remain in the arenas, but
    // their callers now hold naturals, not products or signed sums.
    let machine = lower_program(&source).unwrap();
    assert_eq!(bodies(&machine), 1);
    assert_eq!(externals(&machine), 1);
}

#[test]
fn default_pipeline_removes_folded_library_temporaries() {
    for (which, expected) in [(0, 255), (1, 1), (2, 256)] {
        let source = Standard::new().main(|b, host, s| {
            let [byte, magnitude] = statuses(b, s);
            let status = match which {
                0 => byte,
                1 => magnitude,
                _ => b.call(s.library.add, &[byte, magnitude]),
            };
            s.exit(b, host, status)
        });
        let mut optimized = source.clone();
        barb::optimize(&mut optimized);
        let machine = crate::to_machine(&mut optimized, &routines()).unwrap();
        validate(&machine).unwrap();
        assert_eq!(bodies(&machine), 1);
        assert_eq!(externals(&machine), 1, "only exit remains");
        assert!(
            machine
                .every(machine.function(machine.entry()).body().unwrap())
                .any(|op| matches!(op, Op::Constant { value, .. } if *value == expected))
        );
        // Without cleanup, which would remove what folding left behind.
        let mut uncleaned = source;
        barb::structural(&mut uncleaned);
        barb::normalize_with_limits(&mut uncleaned, barb::InlineLimits::default());
        barb::fold(&mut uncleaned);
        let uncleaned = crate::to_machine(&mut uncleaned, &routines()).unwrap();
        validate(&uncleaned).unwrap();
    }
}

/// A byte converted from a count and back, or a count made signed and its
/// magnitude taken; each answers nought.
fn runtime_product(byte: bool) -> barb::Program {
    Standard::new().main(|b, host, s| {
        let n = b.call(s.world.input, &[host]);
        if byte {
            let held = b.call(s.u8_from_nat, &[n]);
            b.call(s.u8_to_nat, &[held]);
        } else {
            let signed = b.call(s.int_from_nat, &[n]);
            b.call(s.int_abs, &[signed]);
        }
        s.exit_zero(b, host)
    })
}

#[test]
fn default_pipeline_accepts_runtime_product_programs() {
    for byte in [true, false] {
        let mut source = runtime_product(byte);
        barb::optimize(&mut source);
        let machine = crate::to_machine(&mut source, &routines()).unwrap();
        validate(&machine).unwrap();
    }
}

/// A byte is a product of eight flags, held flat as eight words; a signed
/// number is a sum carrying a payload, held as a cell. Neither unused
/// binding is erased by lowering.
#[test]
fn runtime_products_and_signed_sums_lower_without_erasing_unused_bindings() {
    let zero_byte = Standard::new().main(|b, host, s| {
        b.call(s.u8_zero, &[]);
        s.exit_zero(b, host)
    });
    for (source, cells) in [
        (runtime_product(true), false),
        (runtime_product(false), true),
        (zero_byte, false),
    ] {
        let machine = lower_program(&source).unwrap();
        validate(&machine).unwrap();
        assert_eq!(
            machine.ops.iter().any(|op| matches!(op, Op::Cell { .. })),
            cells,
            "{}",
            machine.render()
        );
        assert!(
            bodies(&machine) > 1,
            "the library calls are lowered, not erased"
        );
    }
}

/// `select!(host x)` leaves with nought where `x` is built by `good` and
/// works out a byte's value where it is anything else, and `main!` calls it
/// with a value built by `argument`.
fn selected(owner_is_nat: bool, good: usize, argument: usize) -> barb::Program {
    let mut standard = Standard::new();
    let lib = &standard.library;
    let (owner, tags) = if owner_is_nat {
        (lib.nat, [lib.zero, lib.succ])
    } else {
        (lib.bool_, [lib.false_, lib.true_])
    };
    let (exit, zero) = (standard.world.exit, lib.zero);
    let (u8_zero, u8_to_nat) = (standard.u8_zero, standard.u8_to_nat);
    let host_type = standard.world.host;
    let p = &mut standard.library.program;
    let select = p.declare_named(
        "select!",
        &[("host", host_type), ("x", owner)],
        standard.world.never,
    );
    p.define(select, |b, args| {
        b.match_(args[1], owner, |b, ctor, _| {
            if ctor == tags[good] {
                let nought = b.con(zero, &[]);
                b.call(exit, &[args[0], nought])
            } else {
                let byte = b.call(u8_zero, &[]);
                let value = b.call(u8_to_nat, &[byte]);
                b.call(exit, &[args[0], value])
            }
        })
    });
    standard.main(|b, host, s| {
        let value = if owner_is_nat {
            s.nat(b, u64::try_from(argument).unwrap())
        } else {
            b.con(tags[argument], &[])
        };
        b.call(select, &[host, value])
    })
}

#[test]
fn unsupported_types_in_impossible_arms_do_not_demand_storage_or_functions() {
    // Nought is `Zero`, one is `Succ(Zero)`, and the Bool case takes `True`.
    for (owner_is_nat, good, argument) in [(true, 0, 0), (true, 1, 1), (false, 1, 1)] {
        let source = selected(owner_is_nat, good, argument);
        // No folding or inlining: the lowering's own reachability must agree
        // between function discovery, type demand, and branch emission.
        let machine = lower_program(&source).unwrap();
        assert_eq!(bodies(&machine), 2, "main and select only");
        assert_eq!(externals(&machine), 1);
    }
}

#[test]
fn recognized_definition_bodies_do_not_demand_runtime_representations() {
    let routines = routines();
    let mut source = barb::Program::default();
    let nat = source.declare_type("Nat");
    source.define_type(nat, &[("Zero", &[]), ("Succ", &[nat])]);
    let int = source.declare_type("Int");
    source.define_type(int, &[("Pos", &[nat]), ("NegSucc", &[nat])]);
    let (zero, succ, pos) = (
        source.ctor_at(nat, 0),
        source.ctor_at(nat, 1),
        source.ctor_at(int, 0),
    );
    let world = host(&mut source, nat);
    // add(a Zero) -> ignored = Pos(a) a
    // add(a Succ(b)) -> Succ(add(a b))
    let add = source.declare("add", &[nat, nat], nat);
    source.define(add, |b, args| {
        b.match_(args[1], nat, |b, ctor, fields| {
            if ctor == zero {
                b.con(pos, &[args[0]]);
                args[0]
            } else {
                let rest = b.call(add, &[args[0], fields[0]]);
                b.con(succ, &[rest])
            }
        })
    });
    let main = source.declare_named("main!", &[("host", world.host)], world.never);
    source.define(main, |b, args| {
        let n = b.call(world.input, &[args[0]]);
        let nought = b.con(zero, &[]);
        let sum = b.call(add, &[n, nought]);
        b.call(world.exit, &[args[0], sum])
    });
    source.set_entry(main);
    let facts = barb::analyzed(&source);
    assert_eq!(facts.operation(add), Some(barb::Operation::Add));
    let machine = lower(&mut source, &routines).unwrap();
    assert_eq!(bodies(&machine), 1, "add becomes an instruction");
}

#[test]
#[expect(
    clippy::too_many_lines,
    reason = "declare the leaving routine, then lower both ways of leaving"
)]
fn unsupported_values_after_nonreturning_bindings_are_not_lowered() {
    for leaves_through_stop in [false, true] {
        let mut standard = Standard::new();
        let (nat, zero, exit, host_type) = (
            standard.library.nat,
            standard.library.zero,
            standard.world.exit,
            standard.world.host,
        );
        let p = &mut standard.library.program;
        // stop!(h Zero) -> exit!(h Zero); stop!(h Succ(n)) -> exit!(h Zero)
        let stop = p.declare_named(
            "stop!",
            &[("host", host_type), ("n", nat)],
            standard.world.never,
        );
        p.define(stop, |b, args| {
            b.match_(args[1], nat, |b, _, _| {
                let nought = b.con(zero, &[]);
                b.call(exit, &[args[0], nought])
            })
        });
        let source = standard.main(|b, host, s| {
            let count = b.call(s.world.input, &[host]);
            let nought = b.con(s.library.zero, &[]);
            let n = b.call(s.library.add, &[count, nought]);
            if leaves_through_stop {
                b.call(stop, &[host, n]);
            } else {
                s.exit_zero(b, host);
            }
            let byte = b.call(s.u8_zero, &[]);
            let value = b.call(s.u8_to_nat, &[byte]);
            s.exit(b, host, value)
        });
        for normalized in [false, true] {
            let mut source = source.clone();
            if normalized {
                // The second case becomes a match whose every arm leaves.
                barb::normalize_with_limits(&mut source, barb::InlineLimits::default());
            }
            lower_program(&source).unwrap();
        }
    }
}

#[test]
fn detached_arena_expressions_do_not_demand_a_representation() {
    let standard = Standard::new();
    let (exit, zero) = (standard.world.exit, standard.library.zero);
    let mut source = standard.main(|b, host, s| {
        let byte = b.call(s.u8_zero, &[]);
        let value = b.call(s.u8_to_nat, &[byte]);
        s.exit(b, host, value)
    });
    let nat = source.params(exit)[1];
    assert_eq!(source.ctor(zero).owner, nat);
    let zero = source.intern_number(nat, 0).unwrap();
    source.define(source.entry().unwrap(), |b, args| {
        let zero = b.known(zero);
        b.call(exit, &[args[0], zero])
    });
    let machine = lower_program(&source).unwrap();
    assert_eq!(bodies(&machine), 1);
    assert_eq!(externals(&machine), 1);
}

/// A wrapper around a product is held as that product, so matching one binds
/// the product itself rather than taking a step into it. Both are held flat,
/// so nothing is built and nothing is read back.
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "one fixture declares its types and functions and checks the lowering"
)]
fn a_wrapper_around_a_product_stays_transparent_when_matched() {
    let mut standard = Standard::new();
    let nat = standard.library.nat;
    let p = &mut standard.library.program;
    let pair = p.declare_type("Pair");
    p.define_type(pair, &[("MkPair", &[nat, nat])]);
    let boxed = p.declare_type("Boxed");
    p.define_type(boxed, &[("MkBoxed", &[pair])]);
    let (mk_pair, mk_boxed) = (p.ctor_at(pair, 0), p.ctor_at(boxed, 0));
    let unbox = p.declare("unbox", &[boxed], pair);
    p.define(unbox, |b, args| {
        b.match_(args[0], boxed, |_, _, fields| fields[0])
    });
    let first = p.declare("first", &[pair], nat);
    p.define(first, |b, args| {
        b.match_(args[0], pair, |_, _, fields| fields[0])
    });
    let source = standard.main(|b, host, s| {
        let n = b.call(s.world.input, &[host]);
        let nought = b.con(s.library.zero, &[]);
        let inner = b.con(mk_pair, &[n, nought]);
        let held = b.con(mk_boxed, &[inner]);
        let inner = b.call(unbox, &[held]);
        let n = b.call(first, &[inner]);
        let two = s.nat(b, 2);
        let rest = b.call(s.library.modulo, &[n, two]);
        s.exit(b, host, rest)
    });
    let machine = lower_program(&source).unwrap();
    validate(&machine).unwrap();
    let rendered = machine.render();
    assert!(
        !machine
            .ops
            .iter()
            .any(|op| matches!(op, Op::Cell { .. } | Op::CellField { .. })),
        "{rendered}"
    );
    // The wrapper and the product it holds are the same two values.
    let unbox = machine
        .functions()
        .iter()
        .find(|function| machine.name(function.name) == "unbox")
        .expect("unbox is lowered");
    assert_eq!(
        machine.signature(unbox.params),
        machine.signature(unbox.returns.classes())
    );
    assert_eq!(machine.signature(unbox.params).len(), 2, "{rendered}");
}

/// A cell's fields are held at the class the cell says, which is the class a
/// projection reads them back at. Storing a value at whatever width it was
/// worked out as would let a projection read a count as an address.
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "one fixture declares its types, builds its values, and checks facts and evaluation"
)]
fn cell_fields_are_held_at_the_class_their_projection_reads() {
    let mut standard = Standard::new();
    let (nat, zero) = (standard.library.nat, standard.library.zero);
    let p = &mut standard.library.program;
    let pair = p.declare_type("Pair");
    p.define_type(pair, &[("NoPair", &[]), ("MkPair", &[nat, nat])]);
    let mk_pair = p.ctor_at(pair, 1);
    let first = p.declare("first", &[pair], nat);
    p.define(first, |b, args| {
        b.match_(args[0], pair, |b, ctor, fields| {
            if ctor == mk_pair {
                fields[0]
            } else {
                b.con(zero, &[])
            }
        })
    });
    let source = standard.main(|b, host, s| {
        let n = b.call(s.world.input, &[host]);
        let nought = b.con(s.library.zero, &[]);
        let held = b.con(mk_pair, &[n, nought]);
        let n = b.call(first, &[held]);
        let two = s.nat(b, 2);
        let rest = b.call(s.library.modulo, &[n, two]);
        s.exit(b, host, rest)
    });
    let machine = lower_program(&source).unwrap();
    validate(&machine).unwrap();
    let rendered = machine.render();
    let mut built = Vec::new();
    let mut read = Vec::new();
    for (op, results) in machine
        .functions()
        .iter()
        .filter_map(Function::body)
        .flat_map(|body| machine.walk_within(body))
    {
        match *op {
            Op::Cell { fields, .. } => built.extend(
                machine
                    .values(fields)
                    .iter()
                    .map(|&field| machine.class(field)),
            ),
            Op::CellField { index, .. } => read.push((index, machine.class(results[0]))),
            _ => {}
        }
    }
    // The byte read is held as wide as a read can answer, and the second
    // field only ever holds nought: each field is as wide as what is built
    // there.
    assert_eq!(
        built,
        [
            Class::Held(barb::Bounds {
                low: 0,
                high: Some(511)
            }),
            Class::fixed(0)
        ],
        "{rendered}"
    );
    assert!(!read.is_empty(), "{rendered}");
    for (index, class) in read {
        assert_eq!(class, built[usize::try_from(index).unwrap()], "{rendered}");
    }
}
