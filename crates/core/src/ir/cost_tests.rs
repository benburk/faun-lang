//! What programs cost at run time, counted by the reference interpreter.
//!
//! An allocation count alone reads a loop that recopies its result every
//! step as linear. So each fixture is measured at two sizes and every count
//! must grow no faster than the work does, and the counts at one size are
//! recorded exactly: lower them when ownership or representation improves,
//! and explain any rise.
use num_bigint::BigUint;

use super::evaluate::{self, Counts, RejectHost};
use super::test_support::no_live_objects;
use super::*;
use crate::barb;
use crate::platform::Routines;

const HEAP_BYTES: usize = 1 << 20;

/// What one run cost, as the runtime helpers and stores count it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Cost {
    allocations: u64,
    retains: u64,
    releases: u64,
    stored_bytes: u64,
}

impl Cost {
    fn of(program: &Program, counts: &Counts) -> Self {
        Self {
            allocations: counts.calls_to(program, "nat.allocate"),
            retains: counts.calls_to(program, "nat.retain"),
            releases: counts.calls_to(program, "cell.release")
                + counts.calls_to(program, "nat.release"),
            stored_bytes: counts.stored_bytes,
        }
    }

    fn each(self) -> [(&'static str, u64); 4] {
        [
            ("allocations", self.allocations),
            ("retains", self.retains),
            ("releases", self.releases),
            ("stored bytes", self.stored_bytes),
        ]
    }
}

/// Lower, legalize and run a Barb program's entry, checking that it frees
/// everything it built.
fn cost(source: &barb::Program) -> Cost {
    let machine = lower(&mut source.clone(), &Routines::builtin().with_word(64)).unwrap();
    let config = natural::Config {
        word_bits: 64,
        heap_bytes: HEAP_BYTES,
        grows: false,
        inline_small: true,
    };
    let scalar = legalize(&machine, config).unwrap();
    let result = evaluate::evaluate(
        &scalar,
        scalar.entry(),
        &[],
        evaluate::Config {
            fuel: 100_000_000,
            ..evaluate::Config::default()
        },
        &mut RejectHost,
    )
    .unwrap();
    assert_eq!(result.returned().unwrap(), [BigUint::from(0u8)]);
    no_live_objects(&scalar, &result, config);
    Cost::of(&scalar, &result.counts)
}

/// Build a list of `n` counts, reverse it, and take its length.
#[expect(
    clippy::too_many_lines,
    reason = "the fixture declares its list and each of the three walks over it"
)]
fn round_trip(n: u64) -> barb::Program {
    let mut source = barb::Program::default();
    let nat = source.declare_type("Nat");
    source.define_type(nat, &[("Zero", &[]), ("Succ", &[nat])]);
    let (zero, succ) = (source.ctor_at(nat, 0), source.ctor_at(nat, 1));
    let list = source.declare_type("List");
    source.define_type(list, &[("Nil", &[]), ("Cons", &[nat, list])]);
    let (nil, cons) = (source.ctor_at(list, 0), source.ctor_at(list, 1));
    let count = source.intern_number(nat, n).unwrap();
    let nought = source.intern_number(nat, 0).unwrap();

    let build = source.declare("build", &[nat, list], list);
    source.define(build, |b, args| {
        b.match_(args[0], nat, |b, ctor, fields| {
            if ctor == zero {
                args[1]
            } else {
                let grown = b.con(cons, &[fields[0], args[1]]);
                b.call(build, &[fields[0], grown])
            }
        })
    });
    let reverse = source.declare("reverse", &[list, list], list);
    source.define(reverse, |b, args| {
        b.match_(args[0], list, |b, ctor, fields| {
            if ctor == nil {
                args[1]
            } else {
                let grown = b.con(cons, &[fields[0], args[1]]);
                b.call(reverse, &[fields[1], grown])
            }
        })
    });
    let length = source.declare("length", &[list], nat);
    source.define(length, |b, args| {
        b.match_(args[0], list, |b, ctor, fields| {
            if ctor == nil {
                b.con(zero, &[])
            } else {
                let rest = b.call(length, &[fields[1]]);
                b.con(succ, &[rest])
            }
        })
    });
    let run_it = source.declare("run", &[], nat);
    source.define(run_it, |b, _| {
        let count = b.known(count);
        let empty = b.con(nil, &[]);
        let listed = b.call(build, &[count, empty]);
        let empty = b.con(nil, &[]);
        let turned = b.call(reverse, &[listed, empty]);
        b.call(length, &[turned])
    });
    let main = source.declare("main", &[], nat);
    source.define(main, |b, _| {
        b.call(run_it, &[]);
        b.known(nought)
    });
    source.set_entry(main);
    barb::validate(&source).unwrap();
    source
}

/// Build a list of `n` counts, then copy it the way `map` does: each step
/// puts its element in front of what the rest of the walk answered.
fn copied_on_the_way_out(n: u64) -> barb::Program {
    let mut source = round_trip(n);
    let nat = barb::TypeId::at(0);
    let list = barb::TypeId::at(1);
    let (nil, cons) = (source.ctor_at(list, 0), source.ctor_at(list, 1));
    let count = source.intern_number(nat, n).unwrap();
    let nought = source.intern_number(nat, 0).unwrap();
    let build = barb::FnId::at(0);
    let length = barb::FnId::at(2);
    let copy = source.declare("copy", &[list], list);
    source.define(copy, |b, args| {
        b.match_(args[0], list, |b, ctor, fields| {
            if ctor == nil {
                b.con(nil, &[])
            } else {
                let rest = b.call(copy, &[fields[1]]);
                b.con(cons, &[fields[0], rest])
            }
        })
    });
    let run_it = source.declare("run copy", &[], nat);
    source.define(run_it, |b, _| {
        let count = b.known(count);
        let empty = b.con(nil, &[]);
        let listed = b.call(build, &[count, empty]);
        let copied = b.call(copy, &[listed]);
        b.call(length, &[copied])
    });
    let main = source.declare("main copy", &[], nat);
    source.define(main, |b, _| {
        b.call(run_it, &[]);
        b.known(nought)
    });
    source.set_entry(main);
    barb::validate(&source).unwrap();
    source
}

/// Building on the way out, as `map` does, pushes onto a buffer the walk
/// just answered and nothing else holds, so it writes in place: linear, not
/// a copy of the rest at every step.
#[test]
fn a_list_copied_on_the_way_out_costs_linear_work() {
    let small = cost(&copied_on_the_way_out(100));
    let large = cost(&copied_on_the_way_out(200));
    assert_linear("copy on the way out", small, large);
}

/// Every count at twice the size is at most a quarter more than twice as
/// much: room for buffers doubling at different points, none for anything
/// growing with the square of the work.
fn assert_linear(name: &str, small: Cost, large: Cost) {
    for ((what, small), (_, large)) in small.each().into_iter().zip(large.each()) {
        assert!(
            4 * large <= 9 * small + 64,
            "{name}: {what} grew from {small} to {large} when the work doubled"
        );
    }
}

#[test]
fn a_list_round_trip_costs_linear_work() {
    let small = cost(&round_trip(100));
    let large = cost(&round_trip(200));
    assert_linear("round trip", small, large);
}

/// The exact counts at one size. Lower these when the compiler improves.
#[test]
fn a_list_round_trip_costs_what_is_recorded() {
    assert_eq!(
        cost(&round_trip(100)),
        Cost {
            allocations: 6,
            retains: 0,
            releases: 8,
            stored_bytes: 1046,
        }
    );
}

/// A parameter is owned where its function takes a claim to it: the list
/// an accumulator grows is consumed into each new step, while the list a
/// walk only takes apart is borrowed, and so is a count.
#[test]
fn only_what_a_function_consumes_is_owned() {
    // Called from one place, `build` would be the loop that place goes
    // round; called from two, it is a function of its own.
    let mut source = round_trip(3);
    let named = |source: &barb::Program, name: &str| {
        (0..source.functions().len())
            .map(barb::FnId::at)
            .find(|&id| source.name(source.function(id).name) == name)
            .expect("a definition by that name")
    };
    let (build, main) = (named(&source, "build"), named(&source, "main"));
    let [nat, list] = source.params(build) else {
        unreachable!("build takes a count and a list");
    };
    let (nat, list) = (*nat, *list);
    let nil = source.ctor_at(list, 0);
    let nought = source.intern_number(nat, 0).unwrap();
    let twice = source.declare("twice", &[], nat);
    source.define(twice, |b, _| {
        b.call(main, &[]);
        let none = b.known(nought);
        let empty = b.con(nil, &[]);
        let listed = b.call(build, &[none, empty]);
        b.call(build, &[none, listed]);
        b.known(nought)
    });
    source.set_entry(twice);
    let machine = lower(&mut source, &Routines::builtin().with_word(64)).unwrap();
    let owned = ownership::owned_parameters(&machine);
    let lowered = |name: &str| {
        machine
            .functions
            .iter_enumerated()
            .find(|(_, function)| machine.name(function.name) == name)
            .map(|(id, _)| id)
    };
    let of = |name: &str| {
        let id = lowered(name).unwrap_or_else(|| panic!("`{name}` is lowered"));
        owned[id.index()].clone()
    };
    // A list is three parameters, its buffer, start and length; only a
    // buffer carries a claim. `build` grows the list it is handed, so it
    // owns it.
    assert_eq!(of("build"), [false, true, false, false]);
    // A reversal onto another list is answered by copying one buffer's
    // elements in front of the other's, and is not lowered.
    assert_eq!(lowered("reverse"), None);
    // A count of a list reads the length it holds, and is not lowered.
    assert_eq!(lowered("length"), None);
}

/// A value read last by an `if` is released inside each arm, where that arm
/// is done with it, rather than after the `if` has run both ways.
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "one fixture builds the branch, legalizes it, and finds each arm"
)]
fn a_claim_read_last_by_a_branch_is_released_in_each_arm() {
    let (mut p, main) = Program::new_with_params("main", &[("argc", Class::Word)]);
    p.define(main, |b, params| {
        let count = params[0];
        let held = b.convert(Class::Natural, count);
        let one = b.constant(Class::Word, 1);
        let test = b.compare(Relation::Equal, count, one);
        b.if_(
            test,
            &[Class::Word],
            |b| {
                let word = b.convert(Class::Word, held);
                b.yield_(&[word]);
            },
            |b| {
                let zero = b.constant(Class::Word, 0);
                b.yield_(&[zero]);
            },
        );
        let zero = b.constant(Class::Word, 0);
        b.ret(&[zero]);
    });
    let config = natural::Config {
        word_bits: 64,
        heap_bytes: 256,
        grows: false,
        inline_small: true,
    };
    let scalar = legalize(&p, config).unwrap();
    let release = scalar
        .functions
        .iter_enumerated()
        // A natural is given up through the routine that looks first.
        .find(|(_, function)| scalar.name(function.name) == "nat.drop")
        .map(|(id, _)| id)
        .unwrap();
    let body = scalar.function(main).body().unwrap();
    // The branch the program wrote is the one answering a word; any other
    // is legalization asking whether a natural is an immediate.
    let (then_region, else_region) = scalar
        .walk(body)
        .find_map(|(op, results)| match *op {
            Op::If {
                then_region,
                else_region,
                ..
            } if !results.is_empty() => Some((then_region, else_region)),
            _ => None,
        })
        .unwrap();
    let branch = (then_region, else_region);
    let releases = |region| releases_in(&scalar, region, release, branch);
    assert_eq!(releases(body), 0, "{}", scalar.render());
    assert_eq!(releases(then_region), 1, "{}", scalar.render());
    assert_eq!(releases(else_region), 1, "{}", scalar.render());
}

/// Calls of `release` in a region, looking into every branch and loop in it
/// but `skip`.
fn releases_in(
    scalar: &Program,
    region: RegionId,
    release: FunctionId,
    skip: (RegionId, RegionId),
) -> usize {
    scalar
        .walk(region)
        .map(|(op, _)| match *op {
            Op::Call { function, .. } if function == release => 1,
            Op::If {
                then_region,
                else_region,
                ..
            } if (then_region, else_region) != skip => {
                releases_in(scalar, then_region, release, skip)
                    + releases_in(scalar, else_region, release, skip)
            }
            Op::Loop { body, .. } => releases_in(scalar, body, release, skip),
            _ => 0,
        })
        .sum()
}

/// A machine program pushing `n` elements onto one sequence, each element a
/// count and a cell holding it, then forking the result: two sequences
/// sharing its tail, each one element longer. It answers the sum of both
/// forks' first counts (seven each), the count in the last element's cell
/// (nought) and the count first in the unforked sequence (`n - 1`): `n + 13`.
#[expect(
    clippy::too_many_lines,
    reason = "one program built, forked, and read back from each fork"
)]
fn pushes(n: u64) -> Program {
    let (mut p, main) = Program::new("main");
    p.define(main, |b, _| {
        let pairs = b.shape(&[Class::Word, Class::Cell]);
        let empty = b.buffer_empty(pairs);
        let zero = b.constant(Class::Word, 0);
        let limit = b.constant(Class::Word, n);
        let sequence = [Class::Buffer, Class::Word, Class::Word];
        let built = b.loop_(&[empty, zero, zero], &sequence, |b, state| {
            let (buffer, start, len) = (state[0], state[1], state[2]);
            let done = b.compare(Relation::Equal, len, limit);
            b.if_(
                done,
                &[],
                |b| b.break_(&[buffer, start, len]),
                |b| b.yield_(&[]),
            );
            let word = b.shape(&[Class::Word]);
            let boxed = b.cell(0, word, &[len]);
            let [grown, earlier] = b.buffer_push((buffer, start, len), pairs, &[len, boxed]);
            let one = b.constant(Class::Word, 1);
            let longer = b.binary(Binary::Add, len, one);
            b.continue_(&[grown, earlier, longer]);
        });
        let (buffer, start, len) = (built[0], built[1], built[2]);
        let seven = b.constant(Class::Word, 7);
        let (none, word) = (b.shape(&[]), b.shape(&[Class::Word]));
        let mark = b.cell(1, none, &[]);
        let [left, left_start] = b.buffer_push((buffer, start, len), pairs, &[seven, mark]);
        let mark = b.cell(1, none, &[]);
        let right = b.buffer_push((buffer, start, len), pairs, &[seven, mark]);
        let a = b.buffer_field((Class::Word, pairs), (left, left_start), 0);
        let c = b.buffer_field((Class::Word, pairs), right.into(), 0);
        let past = b.binary(Binary::Add, left_start, len);
        let last = b.buffer_field((Class::Cell, pairs), (left, past), 1);
        let last = b.cell_field((Class::Word, word), last, 0);
        let first = b.buffer_field((Class::Word, pairs), (buffer, start), 0);
        let sum = b.binary(Binary::Add, a, c);
        let sum = b.binary(Binary::Add, sum, last);
        let sum = b.binary(Binary::Add, sum, first);
        b.ret(&[sum]);
    });
    p
}

/// Legalize and run a machine program's entry at 64 bits.
fn run_machine(machine: &Program) -> (Vec<BigUint>, Cost) {
    validate(machine).unwrap();
    let expected = evaluate::evaluate(
        machine,
        machine.entry(),
        &[],
        evaluate::Config {
            fuel: 100_000_000,
            ..evaluate::Config::default()
        },
        &mut RejectHost,
    )
    .unwrap()
    .returned()
    .unwrap()
    .to_vec();
    let config = natural::Config {
        word_bits: 64,
        heap_bytes: HEAP_BYTES,
        grows: false,
        inline_small: true,
    };
    let scalar = legalize(machine, config).unwrap();
    let result = evaluate::evaluate(
        &scalar,
        scalar.entry(),
        &[],
        evaluate::Config {
            fuel: 100_000_000,
            ..evaluate::Config::default()
        },
        &mut RejectHost,
    )
    .unwrap();
    assert_eq!(result.returned().unwrap(), expected);
    no_live_objects(&scalar, &result, config);
    (expected, Cost::of(&scalar, &result.counts))
}

#[test]
fn buffers_push_in_place_and_copy_only_what_is_shared() {
    let (small, small_cost) = run_machine(&pushes(100));
    let (large, large_cost) = run_machine(&pushes(200));
    assert_eq!(small, [BigUint::from(113u8)]);
    assert_eq!(large, [BigUint::from(213u8)]);
    assert_linear("pushes", small_cost, large_cost);
    // A buffer grows by doubling, so a run of pushes allocates a buffer a
    // logarithmic number of times, beside one cell per element.
    assert!(small_cost.allocations < 100 + 2 + 20, "{small_cost:?}");
}
