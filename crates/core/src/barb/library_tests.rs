use super::budget::Budget;
use super::constant::Held;
use super::evaluate::Evaluator;
use super::*;
use num_bigint::BigUint;

/// The fixture's arithmetic, with a signed number (a sum carrying a
/// magnitude) and a pair of numbers (a product) over it.
struct Library {
    program: Program,
    operations: Vec<Option<Operation>>,
}

impl Library {
    #[expect(
        clippy::too_many_lines,
        reason = "each definition written as its equations, in one fixture"
    )]
    fn new() -> Self {
        let library = fixture::Library::new();
        let (nat, zero, succ) = (library.nat, library.zero, library.succ);
        let (add, mul) = (library.add, library.mul);
        let mut p = library.program;
        let signed = p.declare_type("Signed");
        p.define_type(signed, &[("Pos", &[nat]), ("NegSucc", &[nat])]);
        let (pos, neg) = (p.ctor_at(signed, 0), p.ctor_at(signed, 1));
        let pair = p.declare_type("Pair");
        p.define_type(pair, &[("Pair", &[nat, nat])]);
        let both = p.ctor_at(pair, 0);

        // magnitude(Pos(n)) -> n
        // magnitude(NegSucc(n)) -> Succ(n)
        let magnitude = p.declare("magnitude", &[signed], nat);
        p.define(magnitude, |b, args| {
            b.match_(args[0], signed, |b, ctor, fields| {
                if ctor == pos {
                    fields[0]
                } else {
                    b.con(succ, &[fields[0]])
                }
            })
        });
        // negative(Zero) -> Pos(Zero)
        // negative(Succ(n)) -> NegSucc(n)
        let negative = p.declare("negative", &[nat], signed);
        p.define(negative, |b, args| {
            b.match_(args[0], nat, |b, ctor, fields| {
                if ctor == zero {
                    b.con(pos, &[args[0]])
                } else {
                    b.con(neg, &[fields[0]])
                }
            })
        });
        // negate(Pos(n)) -> negative(n)
        // negate(NegSucc(n)) -> Pos(Succ(n))
        let negate = p.declare("negate", &[signed], signed);
        p.define(negate, |b, args| {
            b.match_(args[0], signed, |b, ctor, fields| {
                if ctor == pos {
                    b.call(negative, &[fields[0]])
                } else {
                    let whole = b.con(succ, &[fields[0]]);
                    b.con(pos, &[whole])
                }
            })
        });
        // signed_mul(a b): the product of the magnitudes, negative where
        // exactly one side is.
        let signed_mul = p.declare("signed_mul", &[signed, signed], signed);
        p.define(signed_mul, |b, args| {
            b.match_(args[0], signed, |b, left, a| {
                b.match_(args[1], signed, |b, right, c| {
                    let a = if left == pos {
                        a[0]
                    } else {
                        b.con(succ, &[a[0]])
                    };
                    let c = if right == pos {
                        c[0]
                    } else {
                        b.con(succ, &[c[0]])
                    };
                    let product = b.call(mul, &[a, c]);
                    if (left == pos) == (right == pos) {
                        b.con(pos, &[product])
                    } else {
                        b.call(negative, &[product])
                    }
                })
            })
        });
        // pair_swap(Pair(a b)) -> Pair(b a)
        let pair_swap = p.declare("pair_swap", &[pair], pair);
        p.define(pair_swap, |b, args| {
            b.match_(args[0], pair, |b, _, fields| {
                b.con(both, &[fields[1], fields[0]])
            })
        });
        // pair_sum(Pair(a b)) -> add(a b)
        let pair_sum = p.declare("pair_sum", &[pair], nat);
        p.define(pair_sum, |b, args| {
            b.match_(args[0], pair, |b, _, fields| {
                b.call(add, &[fields[0], fields[1]])
            })
        });
        // pair_scaled(Pair(a b) n) -> Pair(mul(a n) mul(b n))
        let pair_scaled = p.declare("pair_scaled", &[pair, nat], pair);
        p.define(pair_scaled, |b, args| {
            b.match_(args[0], pair, |b, _, fields| {
                let first = b.call(mul, &[fields[0], args[1]]);
                let second = b.call(mul, &[fields[1], args[1]]);
                b.con(both, &[first, second])
            })
        });
        let main = p.declare("main", &[], nat);
        p.define(main, |b, _| b.con(zero, &[]));
        p.set_entry(main);

        validate(&p).unwrap();
        let operations = arithmetic::recognise(&p);
        Self {
            program: p,
            operations,
        }
    }

    fn function(&self, name: &str) -> FnId {
        FnId::at(
            self.program
                .functions()
                .iter()
                .position(|f| self.program.name(f.name) == name)
                .unwrap(),
        )
    }

    fn call(&self, name: &str, args: &[Held]) -> Held {
        let id = self.function(name);
        assert_eq!(
            self.program.params(id),
            args.iter().map(Held::owner).collect::<Vec<_>>()
        );
        Evaluator {
            program: &self.program,
            operations: &self.operations,
        }
        .body(
            self.program.function(id).body().unwrap(),
            args.iter().cloned().map(Ok).collect(),
            &mut Budget::new(FoldLimits {
                max_depth: 512,
                ..FoldLimits::default()
            }),
        )
        .unwrap_or_else(|reason| panic!("cannot evaluate {name}: {reason:?}"))
    }

    fn natural(&self, n: impl Into<BigUint>) -> Held {
        let owner = self.program.params(self.function("add"))[0];
        Held::number(self.program.type_info(), owner, &n.into())
    }

    // Construct values independently of the library's own definitions.
    fn construct(&self, name: &str, fields: &[Held]) -> Held {
        let ctor = (0..self.program.types().len())
            .flat_map(|at| self.program.ctors(TypeId::at(at)))
            .find(|c| self.program.name(c.name) == name)
            .unwrap();
        let id = self
            .program
            .ctors(ctor.owner)
            .iter()
            .position(|c| c.name == ctor.name)
            .map(|tag| {
                self.program
                    .ctor_at(ctor.owner, u32::try_from(tag).unwrap())
            })
            .unwrap();
        Held::build(
            self.program.type_info(),
            id,
            fields,
            &mut Budget::new(FoldLimits::default()),
        )
        .unwrap()
    }

    fn integer(&self, n: i64) -> Held {
        if n < 0 {
            self.construct("NegSucc", &[self.natural(n.unsigned_abs() - 1)])
        } else {
            self.construct("Pos", &[self.natural(n.unsigned_abs())])
        }
    }

    fn pair(&self, a: impl Into<BigUint>, b: impl Into<BigUint>) -> Held {
        self.construct("Pair", &[self.natural(a), self.natural(b)])
    }
}

fn same(actual: &Held, expected: &Held) {
    assert_eq!(actual.owner(), expected.owner());
    assert_eq!(actual.encoded(), expected.encoded());
}

/// Evaluation reads a definition's equations when nothing about it is
/// recognised, and answers what recognised arithmetic would.
#[test]
fn small_library_calls_also_evaluate_without_arithmetic_recognition() {
    let mut lib = Library::new();
    lib.operations.fill(None);
    for a in -3i64..=3 {
        for b in -3i64..=3 {
            let args = [lib.integer(a), lib.integer(b)];
            same(&lib.call("signed_mul", &args), &lib.integer(a * b));
        }
        let n = u32::try_from(a + 3).unwrap();
        same(&lib.call("negate", &[lib.integer(a)]), &lib.integer(-a));
        same(
            &lib.call("pair_sum", &[lib.pair(n, 2u32)]),
            &lib.natural(n + 2),
        );
        same(
            &lib.call("pair_swap", &[lib.pair(n, 2u32)]),
            &lib.pair(2u32, n),
        );
    }
}

#[test]
fn library_products_sums_and_large_magnitudes_fold_as_ordinary_calls() {
    let mut lib = Library::new();
    let huge = BigUint::from(1u8) << 100usize;
    let expected = lib.construct("Pos", &[lib.natural((&huge + 1u8) * (&huge + 1u8))]);
    let squared = lib.call(
        "signed_mul",
        &[
            lib.construct("NegSucc", &[lib.natural(huge.clone())]),
            lib.construct("NegSucc", &[lib.natural(huge.clone())]),
        ],
    );
    same(&squared, &expected);
    let cases = [
        (
            "signed_mul",
            vec![
                lib.construct("NegSucc", &[lib.natural(huge.clone())]),
                lib.construct("NegSucc", &[lib.natural(huge.clone())]),
            ],
        ),
        ("signed_mul", vec![lib.integer(3), lib.integer(-4)]),
        ("negate", vec![lib.integer(0)]),
        (
            "magnitude",
            vec![lib.construct("NegSucc", &[lib.natural(huge.clone())])],
        ),
        ("pair_swap", vec![lib.pair(1u32, 2u32)]),
        ("pair_sum", vec![lib.pair(huge, 5u32)]),
        (
            "pair_scaled",
            vec![
                lib.pair(3u32, 4u32),
                lib.natural(BigUint::from(1u8) << 64usize),
            ],
        ),
    ];
    assert_calls_fold(&mut lib, &cases);
}

fn assert_calls_fold(lib: &mut Library, cases: &[(&str, Vec<Held>)]) {
    let mut probes = vec![];
    for (index, (name, args)) in cases.iter().enumerate() {
        let expected = lib.call(name, args);
        let called = lib.function(name);
        let probe = lib
            .program
            .declare(&format!("probe_{index}"), &[], expected.owner());
        let values: Vec<_> = args.iter().map(|v| lib.program.intern_held(v)).collect();
        lib.program.define(probe, |b, _| {
            let args: Vec<_> = values.iter().map(|&v| b.known(v)).collect();
            b.call(called, &args)
        });
        probes.push((probe, expected));
    }
    for normalized in [false, true] {
        let mut program = lib.program.clone();
        if normalized {
            normalize_with_limits(&mut program, InlineLimits::default());
        }
        fold(&mut program);
        validate(&program).unwrap();
        for (id, expected) in &probes {
            let Expr::Static(value) = program.expr(program.function(*id).body().unwrap().tail)
            else {
                panic!("probe did not fold (normalized={normalized})");
            };
            same(
                &program
                    .constant(value)
                    .to_owned(&mut Budget::new(FoldLimits::default()))
                    .unwrap(),
                expected,
            );
        }
    }
}

/// A probe over renamed types whose constructors are declared in another
/// order folds to what the same probe does over the usual ones.
#[test]
fn library_meaning_does_not_depend_on_names_or_constructor_order() {
    for renamed in [false, true] {
        let (mut program, probe) = naming_probe(renamed);
        normalize_with_limits(&mut program, InlineLimits::default());
        fold(&mut program);
        validate(&program).unwrap();
        let Expr::Static(value) = program.expr(program.function(probe).body().unwrap().tail) else {
            panic!("probe did not fold (renamed={renamed})");
        };
        let ConstantView::Natural(number) = program.constant(value).view() else {
            panic!("a natural");
        };
        assert_eq!(number.try_u64(), Ok(255), "renamed={renamed}");
    }
}

/// `magnitude(NegSucc(sub(add(k one) one)))` for `k = 254`, over a number
/// type and a signed type that are, where `renamed`, called otherwise, with
/// their constructors declared the other way round and the arithmetic
/// called otherwise too.
#[expect(
    clippy::too_many_lines,
    reason = "the types, the arithmetic and the probe are one fixture"
)]
fn naming_probe(renamed: bool) -> (Program, FnId) {
    let name = |plain: &'static str, other: &'static str| if renamed { other } else { plain };
    let mut p = Program::default();
    let nat = p.declare_type(name("Nat", "Count"));
    let signed = p.declare_type(name("Signed", "Integer"));
    if renamed {
        p.define_type(nat, &[("Next", &[nat]), ("Nil", &[])]);
        p.define_type(signed, &[("Below", &[nat]), ("Above", &[nat])]);
    } else {
        p.define_type(nat, &[("Zero", &[]), ("Succ", &[nat])]);
        p.define_type(signed, &[("Pos", &[nat]), ("NegSucc", &[nat])]);
    }
    let tag = u32::from(renamed);
    let (zero, succ) = (p.ctor_at(nat, tag), p.ctor_at(nat, 1 - tag));
    let (pos, neg) = (p.ctor_at(signed, tag), p.ctor_at(signed, 1 - tag));

    let add = p.declare(name("add", "plus"), &[nat, nat], nat);
    p.define(add, |b, args| {
        b.match_(args[1], nat, |b, ctor, fields| {
            if ctor == zero {
                args[0]
            } else {
                let rest = b.call(add, &[args[0], fields[0]]);
                b.con(succ, &[rest])
            }
        })
    });
    let sub = p.declare(name("sub", "minus"), &[nat, nat], nat);
    p.define(sub, |b, args| {
        b.match_(args[0], nat, |b, ctor, left| {
            if ctor == zero {
                return b.con(zero, &[]);
            }
            b.match_(args[1], nat, |b, ctor, right| {
                if ctor == zero {
                    b.con(succ, &[left[0]])
                } else {
                    b.call(sub, &[left[0], right[0]])
                }
            })
        })
    });
    let magnitude = p.declare(name("magnitude", "size"), &[signed], nat);
    p.define(magnitude, |b, args| {
        b.match_(args[0], signed, |b, ctor, fields| {
            if ctor == pos {
                fields[0]
            } else {
                b.con(succ, &[fields[0]])
            }
        })
    });
    let k = p.intern_number(nat, 254).unwrap();
    let probe = p.declare("probe", &[], nat);
    p.define(probe, |b, _| {
        let nought = b.con(zero, &[]);
        let one = b.con(succ, &[nought]);
        let k = b.known(k);
        let up = b.call(add, &[k, one]);
        let back = b.call(sub, &[up, one]);
        let negative = b.con(neg, &[back]);
        b.call(magnitude, &[negative])
    });
    p.set_entry(probe);
    (p, probe)
}
