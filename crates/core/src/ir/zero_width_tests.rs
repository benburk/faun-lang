use super::{Class, Op, Program, Returns, evaluate, validate};
use crate::barb::fixture::Library;
use crate::barb::{self, Atom, Builder, CtorId, FnId, TypeId};
use crate::platform::Routines;
use num_bigint::BigUint;

const ZERO: Class = Class::fixed(0);
const BIT: Class = Class::fixed(1);

/// The arithmetic library with the authority an entry is handed and the two
/// routines these programs call: `read_byte!`, bounded as its routine says, and
/// `exit!`, which does not come back.
struct Hosted {
    library: Library,
    host: TypeId,
    never: TypeId,
    input: FnId,
    exit: FnId,
}

impl Hosted {
    fn new(routines: &Routines) -> Self {
        let mut library = Library::new();
        let nat = library.nat;
        let p = &mut library.program;
        let (host, never, input, exit) = host_routines(p, nat, routines);
        Self {
            library,
            host,
            never,
            input,
            exit,
        }
    }

    /// Declare the entry, `main!(host)`, which leaves through `exit!`.
    fn main(&mut self, body: impl FnOnce(&mut Builder, Atom) -> Atom) {
        let p = &mut self.library.program;
        let main = p.declare_named("main!", &[("host", self.host)], self.never);
        p.define(main, |b, args| body(b, args[0]));
        p.set_entry(main);
    }

    /// Lower after running `stages`.
    fn lower(mut self, routines: &Routines, stages: impl FnOnce(&mut barb::Program)) -> Program {
        stages(&mut self.library.program);
        let program = crate::lower(&mut self.library.program, routines).unwrap();
        validate(&program).unwrap();
        program
    }
}

/// Declare `Host`, `Never`, and the routines `read_byte!` and `exit!` over `nat`,
/// answering `(host, never, input, exit)`.
fn host_routines(
    p: &mut barb::Program,
    nat: TypeId,
    routines: &Routines,
) -> (TypeId, TypeId, FnId, FnId) {
    let host = p.declare_type("Host");
    p.define_type(host, &[("Host", &[])]);
    let never = p.declare_type("Never");
    p.define_type(never, &[]);
    let input = p.declare("read_byte!", &[host], nat);
    let held = routines
        .get("read_byte!")
        .and_then(crate::platform::Routine::bounds);
    p.bound(input, held.expect("a bounded byte"));
    let exit = p.declare("exit!", &[host, nat], never);
    (host, never, input, exit)
}

/// `n` as the chain of constructors a program writes for it.
fn written(b: &mut Builder, (zero, succ): (CtorId, CtorId), n: usize) -> Atom {
    let nought = b.con(zero, &[]);
    (0..n).fold(nought, |held, _| b.con(succ, &[held]))
}

/// Every stage, or none of them.
fn stages(optimized: bool) -> fn(&mut barb::Program) {
    if optimized { barb::optimize } else { |_| {} }
}

/// Inlining and folding, without the laws that would decide a remainder
/// outright.
fn without_laws(program: &mut barb::Program) {
    barb::structural(program);
    barb::normalize_with_limits(program, barb::InlineLimits::default());
    barb::fold(program);
}

#[test]
fn zero_constants_choose_fixed0_but_the_entry_still_returns_a_word() {
    for word_bits in [16, 32, 64] {
        for (value, bits) in [(0, 0), (1, 1), (2, 2)] {
            for optimized in [true, false] {
                let routines = Routines::builtin().with_word(word_bits);
                let mut hosted = Hosted::new(&routines);
                let nat = (hosted.library.zero, hosted.library.succ);
                let exit = hosted.exit;
                hosted.main(|b, host| {
                    let status = written(b, nat, value);
                    b.call(exit, &[host, status])
                });
                let program = hosted.lower(&routines, stages(optimized));
                let entry = program.function(program.entry());
                assert_eq!(program.signature(entry.returns.classes()), [Class::Word]);
                let body = entry.body().unwrap();
                let Some(Op::Call { args, .. }) = program.ops(body).last() else {
                    panic!("the source ends with exit");
                };
                assert_eq!(program.values(*args).len(), 1);
                assert_eq!(program.class(program.values(*args)[0]).width(), Some(bits));
            }
        }
    }
}

/// A known-zero scalar is still an argument, a result and a branch result.
/// Computing it calls `read_byte!` again: knowing the result must not erase that
/// call. Optimized or not, since inlining would otherwise remove the calls
/// and joins these tests are about.
fn program(word_bits: u16, optimized: bool) -> Program {
    let routines = Routines::builtin().with_word(word_bits);
    let mut hosted = Hosted::new(&routines);
    let (host, input, exit) = (hosted.host, hosted.input, hosted.exit);
    let library = &hosted.library;
    let (nat, bool_, equals) = (library.nat, library.bool_, library.equals);
    let (zero, succ, yes) = (library.zero, library.succ, library.true_);
    let p = &mut hosted.library.program;

    // keep_zero!(h n) -> observed = read_byte!(h) n
    let keep_zero = p.declare_named("keep_zero!", &[("h", host), ("n", nat)], nat);
    p.define(keep_zero, |b, args| {
        b.call(input, &[args[0]]);
        args[1]
    });
    // select_zero!(h False) -> keep_zero!(h Zero)
    // select_zero!(h True) -> keep_zero!(h Zero)
    let select_zero = p.declare_named("select_zero!", &[("h", host), ("flag", bool_)], nat);
    p.define(select_zero, |b, args| {
        b.match_(args[1], bool_, |b, _, _| {
            let zero = b.con(zero, &[]);
            b.call(keep_zero, &[args[0], zero])
        })
    });
    // zero_or_one(False n) -> n
    // zero_or_one(True n) -> Succ(n)
    let zero_or_one = p.declare("zero_or_one", &[bool_, nat], nat);
    p.define(zero_or_one, |b, args| {
        b.match_(args[0], bool_, |b, ctor, _| {
            if ctor == yes {
                b.con(succ, &[args[1]])
            } else {
                args[1]
            }
        })
    });
    hosted.main(|b, host| {
        let count = b.call(input, &[host]);
        let one = written(b, (zero, succ), 1);
        let first = b.call(equals, &[count, one]);
        let z = b.call(select_zero, &[host, first]);
        let status = b.call(zero_or_one, &[first, z]);
        b.call(exit, &[host, status])
    });
    hosted.lower(&routines, stages(optimized))
}

#[test]
fn zero_parameters_results_and_joins_are_not_erased() {
    for word_bits in [16, 32, 64] {
        let p = program(word_bits, false);
        for (name, params, result) in [
            ("keep_zero!", vec![ZERO], ZERO),
            ("select_zero!", vec![BIT], ZERO),
            ("zero_or_one", vec![BIT, ZERO], BIT),
        ] {
            let function = p
                .functions()
                .iter()
                .find(|f| p.name(f.name) == name)
                .unwrap();
            assert_eq!(p.signature(function.params), params, "{name}");
            let Returns::Values(results) = function.returns else {
                panic!("a scalar result")
            };
            assert_eq!(p.signature(results), [result], "{name}");
        }
        let has_join = |class| {
            p.regions.ids().any(|id| {
                p.walk(id).any(|(op, results)| {
                    matches!(op, Op::If { .. })
                        && results.len() == 1
                        && p.class(results[0]) == class
                })
            })
        };
        assert!(has_join(ZERO), "two zero-valued arms join as fixed0");
        assert!(
            has_join(BIT),
            "zero and one join at a width that holds both"
        );
    }
}

#[test]
fn range_proven_zero_arithmetic_selects_fixed0() {
    for word_bits in [16, 32, 64] {
        let routines = Routines::builtin().with_word(word_bits);
        let mut hosted = Hosted::new(&routines);
        let (input, exit) = (hosted.input, hosted.exit);
        let library = &hosted.library;
        let (zero, succ, modulo) = (library.zero, library.succ, library.modulo);
        // main!(h) -> n = read_byte!(h) exit!(h mod(n Succ(Zero)))
        hosted.main(|b, host| {
            let n = b.call(input, &[host]);
            let one = written(b, (zero, succ), 1);
            let status = b.call(modulo, &[n, one]);
            b.call(exit, &[host, status])
        });
        let p = hosted.lower(&routines, without_laws);
        let body = p.function(p.entry()).body().unwrap();
        // A remainder by one is every bit below the first, which is none of
        // them: read at no width at all rather than divided by anything.
        assert!(!p.every(body).any(|op| matches!(
            op,
            Op::Binary {
                op: super::Binary::Mod,
                ..
            }
        )));
        assert!(p.walk_within(body).any(|(op, results)| {
            matches!(op, Op::Convert { .. }) && p.class(results[0]) == ZERO
        }));
        for input in [0, 1, 255, 511] {
            let mut host = Host {
                input,
                ..Host::default()
            };
            let result = evaluate_entry(&p, word_bits, &mut host);
            assert_eq!(result.halted().unwrap(), [BigUint::from(0u8)]);
            assert_eq!(host.calls, ["read_byte!", "exit!"]);
        }
    }
}

/// What a comparison probe asks of the argument count.
#[derive(Clone, Copy, Debug)]
enum Probe {
    /// `equals(n Succ(Zero))`
    IsOne,
    /// `less_than(n Succ(Zero))`
    BelowOne,
    /// `equals(mod(n Succ(Zero)) Zero)`, which always holds.
    DividesByOne,
    /// `less_than(n Zero)`, which never does.
    BelowZero,
}

/// Comparison, remainder and the `Bool` they answer with, its constructors
/// in the order given: which tag means yes is up to the program.
struct Comparisons {
    bool_: TypeId,
    no: CtorId,
    equals: FnId,
    less_than: FnId,
    modulo: FnId,
}

/// Declare `Bool` in `order` and both comparisons and the remainder over it,
/// clause by clause as the arithmetic library writes them.
#[expect(
    clippy::too_many_lines,
    reason = "the remainder and both comparisons are written clause by clause"
)]
fn comparisons(
    p: &mut barb::Program,
    (nat, zero, succ): (TypeId, CtorId, CtorId),
    order: [&str; 2],
) -> Comparisons {
    let bool_ = p.declare_type("Bool");
    p.define_type(bool_, &[(order[0], &[]), (order[1], &[])]);
    let named = |p: &barb::Program, name: &str| {
        (0..2)
            .map(|tag| p.ctor_at(bool_, tag))
            .find(|&ctor| p.name(p.ctor(ctor).name) == name)
            .expect("a Bool constructor")
    };
    let (yes, no) = (named(p, "True"), named(p, "False"));
    let compare = |p: &mut barb::Program, name: &str, [both, below, above]: [CtorId; 3]| {
        let id = p.declare(name, &[nat, nat], bool_);
        p.define(id, |b, args| {
            b.match_(args[0], nat, |b, ctor, left| {
                let left_zero = ctor == zero;
                b.match_(args[1], nat, |b, ctor, right| {
                    match (left_zero, ctor == zero) {
                        (true, true) => b.con(both, &[]),
                        (true, false) => b.con(below, &[]),
                        (false, true) => b.con(above, &[]),
                        (false, false) => b.call(id, &[left[0], right[0]]),
                    }
                })
            })
        });
        id
    };
    let equals = compare(p, "equals", [yes, no, no]);
    let less_than = compare(p, "less_than", [no, yes, no]);
    // mod_step(True r) -> Zero
    // mod_step(False r) -> Succ(r)
    let mod_step = p.declare("mod_step", &[bool_, nat], nat);
    p.define(mod_step, |b, args| {
        b.match_(args[0], bool_, |b, ctor, _| {
            if ctor == yes {
                b.con(zero, &[])
            } else {
                b.con(succ, &[args[1]])
            }
        })
    });
    // mod(a Zero) -> a
    // mod(Zero Succ(b)) -> Zero
    // mod(Succ(a) Succ(b)) -> r = mod(a Succ(b)) mod_step(equals(r b) r)
    let modulo = p.declare("mod", &[nat, nat], nat);
    p.define(modulo, |b, args| {
        b.match_(args[1], nat, |b, ctor, divisor| {
            if ctor == zero {
                return args[0];
            }
            b.match_(args[0], nat, |b, ctor, dividend| {
                if ctor == zero {
                    return b.con(zero, &[]);
                }
                let whole = b.con(succ, &[divisor[0]]);
                let r = b.call(modulo, &[dividend[0], whole]);
                let last = b.call(equals, &[r, divisor[0]]);
                b.call(mod_step, &[last, r])
            })
        })
    });
    Comparisons {
        bool_,
        no,
        equals,
        less_than,
        modulo,
    }
}

/// `probe(n)`, answering what `probe` asks of `n`.
fn declare_probe(
    p: &mut barb::Program,
    (nat, zero, succ): (TypeId, CtorId, CtorId),
    ops: &Comparisons,
    probe: Probe,
) -> FnId {
    let id = p.declare("probe", &[nat], ops.bool_);
    p.define(id, |b, args| {
        let n = args[0];
        match probe {
            Probe::IsOne => {
                let one = written(b, (zero, succ), 1);
                b.call(ops.equals, &[n, one])
            }
            Probe::BelowOne => {
                let one = written(b, (zero, succ), 1);
                b.call(ops.less_than, &[n, one])
            }
            Probe::DividesByOne => {
                let one = written(b, (zero, succ), 1);
                let r = b.call(ops.modulo, &[n, one]);
                let nought = b.con(zero, &[]);
                b.call(ops.equals, &[r, nought])
            }
            Probe::BelowZero => {
                let nought = b.con(zero, &[]);
                b.call(ops.less_than, &[n, nought])
            }
        }
    });
    id
}

/// The program as lowering leaves it, and as the machine passes leave it.
///
/// Lowering writes a comparison as the tag it answers with, whatever reads
/// it; the passes read a match on that tag together with it. Both are worth
/// holding here, since what says a pass changed the shape and not the
/// answer is running the two of them against each other.
fn comparison_programs(word_bits: u16, order: [&str; 2], probe: Probe) -> (Program, Program) {
    let routines = Routines::builtin().with_word(word_bits);
    let mut p = barb::Program::default();
    let nat = p.declare_type("Nat");
    p.define_type(nat, &[("Zero", &[]), ("Succ", &[nat])]);
    let (zero, succ) = (p.ctor_at(nat, 0), p.ctor_at(nat, 1));
    let (host, never, input, exit) = host_routines(&mut p, nat, &routines);
    let ops = comparisons(&mut p, (nat, zero, succ), order);
    let probe = declare_probe(&mut p, (nat, zero, succ), &ops, probe);
    // status!(h False) -> exit!(h Zero)
    // status!(h True) -> exit!(h Succ(Zero))
    let status = p.declare_named("status!", &[("h", host), ("flag", ops.bool_)], never);
    p.define(status, |b, args| {
        b.match_(args[1], ops.bool_, |b, ctor, _| {
            let answer = written(b, (zero, succ), usize::from(ctor != ops.no));
            b.call(exit, &[args[0], answer])
        })
    });
    let main = p.declare_named("main!", &[("h", host)], never);
    p.define(main, |b, args| {
        let n = b.call(input, &[args[0]]);
        let asked = b.call(probe, &[n]);
        b.call(status, &[args[0], asked])
    });
    p.set_entry(main);

    // Inlining, without the laws or folding that would decide the comparison.
    barb::structural(&mut p);
    barb::normalize_with_limits(&mut p, barb::InlineLimits::default());
    let lowered = crate::ir::lower(p.analyze(), &routines).unwrap();
    validate(&lowered).unwrap();
    let optimized = crate::ir::optimize(&lowered);
    validate(&optimized).unwrap();
    (lowered, optimized)
}

fn comparison_arms(p: &Program, yes_tag: u64) {
    let body = p.function(p.entry()).body().unwrap();
    let (yes, no, result) = p
        .walk(body)
        .find_map(|(op, results)| match *op {
            Op::If {
                then_region,
                else_region,
                ..
            } => Some((then_region, else_region, results[0])),
            _ => None,
        })
        .expect("a comparison materialized as a tagged result");
    assert_eq!(
        p.class(result),
        BIT,
        "the join must hold either emitted tag"
    );
    for (arm, tag) in [(yes, yes_tag), (no, 1 - yes_tag)] {
        let (op, results) = p.walk(arm).next().unwrap();
        let class = if tag == 0 { ZERO } else { BIT };
        assert_eq!(*op, Op::Constant { value: tag });
        assert_eq!(p.class(results[0]).width(), class.width());
        assert_eq!(
            p.outgoing(arm),
            results,
            "yield the narrow constant directly"
        );
    }
}

#[test]
fn comparison_arms_use_minimal_constants_and_a_wide_enough_join() {
    for word_bits in [16, 32, 64] {
        for (order, yes_tag) in [(["False", "True"], 1), (["True", "False"], 0)] {
            for (probe, answers, known) in [
                (Probe::IsOne, [0u8, 1, 0, 0], None),
                (Probe::BelowOne, [1, 0, 0, 0], None),
                (Probe::DividesByOne, [1, 1, 1, 1], Some(true)),
                (Probe::BelowZero, [0, 0, 0, 0], Some(false)),
            ] {
                let (lowered, optimized) = comparison_programs(word_bits, order, probe);
                comparison_arms(&lowered, yes_tag);
                if known.is_some_and(|yes| if yes { yes_tag == 0 } else { yes_tag == 1 }) {
                    let body = lowered.function(lowered.entry()).body().unwrap();
                    assert!(
                        lowered.walk_within(body).any(|(op, results)| {
                            matches!(op, Op::Convert { .. }) && lowered.class(results[0]) == ZERO
                        }),
                        "a proven zero is narrowed after the join"
                    );
                }
                for (input, answer) in [0, 1, 2, 33].into_iter().zip(answers) {
                    for p in [&lowered, &optimized] {
                        let mut host = Host {
                            input,
                            ..Host::default()
                        };
                        let result = evaluate_entry(p, word_bits, &mut host);
                        assert_eq!(
                            result.halted().unwrap(),
                            [BigUint::from(answer)],
                            "{order:?}: {probe:?}, input={input}"
                        );
                        assert_eq!(host.calls, ["read_byte!", "exit!"]);
                    }
                }
            }
        }
    }
}

fn evaluate_entry(p: &Program, word_bits: u16, host: &mut Host) -> evaluate::Evaluation {
    evaluate::evaluate(
        p,
        p.entry(),
        &[],
        evaluate::Config {
            word_bits,
            ..evaluate::Config::default()
        },
        host,
    )
    .unwrap()
}

#[derive(Default)]
struct Host {
    input: u16,
    calls: Vec<String>,
    halt_on_read: Option<usize>,
}

impl evaluate::Host for Host {
    fn call(
        &mut self,
        name: &str,
        args: &[BigUint],
        _: &mut evaluate::Memory<'_>,
    ) -> Result<evaluate::HostResult, evaluate::Error> {
        self.calls.push(name.to_owned());
        match name {
            "read_byte!" if self.halt_on_read == Some(self.calls.len()) => {
                Ok(evaluate::HostResult::Halt(vec![BigUint::from(7u8)]))
            }
            "read_byte!" => Ok(evaluate::HostResult::Return(vec![BigUint::from(
                self.input,
            )])),
            "exit!" => Ok(evaluate::HostResult::Halt(args.to_vec())),
            _ => Err(evaluate::Error::Host(name.to_owned())),
        }
    }
}

#[test]
fn zero_results_preserve_eager_calls_and_nonreturning_execution() {
    for word_bits in [16, 32, 64] {
        for optimized in [true, false] {
            let p = program(word_bits, optimized);
            for input in [1, 2, 33] {
                for halt_on_read in [None, Some(2)] {
                    let mut host = Host {
                        input,
                        halt_on_read,
                        ..Host::default()
                    };
                    let result = evaluate_entry(&p, word_bits, &mut host);
                    let (answer, calls): (u8, &[&str]) = if halt_on_read.is_some() {
                        (7, &["read_byte!", "read_byte!"])
                    } else {
                        (u8::from(input == 1), &["read_byte!", "read_byte!", "exit!"])
                    };
                    assert_eq!(result.halted().unwrap(), [BigUint::from(answer)]);
                    assert_eq!(host.calls, calls);
                }
            }
        }
    }
}
