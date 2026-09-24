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
    let machine = lower(
        source,
        &barb::analyze(source),
        &Routines::builtin().with_word(64),
    )
    .unwrap();
    let config = natural::Config {
        word_bits: 64,
        heap_bytes: HEAP_BYTES,
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

/// Every count at twice the size is at most twice as much, and a little.
fn assert_linear(name: &str, small: Cost, large: Cost) {
    for ((what, small), (_, large)) in small.each().into_iter().zip(large.each()) {
        assert!(
            large <= 2 * small + 16,
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
            allocations: 401,
            retains: 400,
            releases: 1305,
            stored_bytes: 51656,
        }
    );
}

/// A parameter is owned where its function takes a claim to it: the list
/// an accumulator grows is consumed into each new step, while the list a
/// walk only takes apart is borrowed, and so is a count.
#[test]
fn only_what_a_function_consumes_is_owned() {
    let machine = lower(
        &round_trip(3),
        &barb::analyze(&round_trip(3)),
        &Routines::builtin().with_word(64),
    )
    .unwrap();
    let owned = ownership::owned_parameters(&machine);
    let of = |name: &str| {
        let id = machine
            .functions
            .iter_enumerated()
            .find(|(_, function)| machine.name(function.name) == name)
            .map_or_else(|| panic!("`{name}` is lowered"), |(id, _)| id);
        owned[id.index()].clone()
    };
    assert_eq!(of("build"), [false, true]);
    assert_eq!(of("reverse"), [false, true]);
    assert_eq!(of("length"), [false]);
}

/// A value read last by an `if` is released inside each arm, where that arm
/// is done with it, rather than after the `if` has run both ways.
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "one fixture builds the branch, legalizes it, and finds each arm"
)]
fn a_claim_read_last_by_a_branch_is_released_in_each_arm() {
    let (mut p, main) = Program::new("main");
    let argc = p.external("argc!", &[], Returns::Values(&[Class::Word]));
    p.define(main, |b, _| {
        let count = b.call_one(argc, &[]);
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
    };
    let scalar = legalize(&p, config).unwrap();
    let release = scalar
        .functions
        .iter_enumerated()
        .find(|(_, function)| scalar.name(function.name) == "nat.release")
        .map(|(id, _)| id)
        .unwrap();
    let releases = |region: RegionId| {
        scalar
            .walk(region)
            .filter(|(op, _)| matches!(**op, Op::Call { function, .. } if function == release))
            .count()
    };
    let body = scalar.function(main).body().unwrap();
    let (then_region, else_region) = scalar
        .walk(body)
        .find_map(|(op, _)| match *op {
            Op::If {
                then_region,
                else_region,
                ..
            } => Some((then_region, else_region)),
            _ => None,
        })
        .unwrap();
    assert_eq!(releases(body), 0, "{}", scalar.render());
    assert_eq!(releases(then_region), 1, "{}", scalar.render());
    assert_eq!(releases(else_region), 1, "{}", scalar.render());
}
