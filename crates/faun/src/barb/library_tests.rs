use super::budget::Budget;
use super::constant::Held;
use super::evaluate::Evaluator;
use super::*;
use num_bigint::BigUint;

const NAT: &str = include_str!("../../../../standard/simple/nat.fn");
const U8: &str = include_str!("../../../../standard/simple/u8.fn");
const INT: &str = include_str!("../../../../standard/simple/int.fn");

struct Library {
    program: Program,
    operations: Vec<Option<Operation>>,
}

impl Library {
    fn new() -> Self {
        let text = format!("{NAT}\n{U8}\n{INT}\nmain!(h) -> exit!(h Zero)");
        let program = crate::simple::parse(&text, &crate::platform::Routines::builtin()).unwrap();
        validate(&program).unwrap();
        let operations = arithmetic::recognise(&program);
        Self {
            program,
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

    // Construct tagged values independently of the library's conversions.
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
        assert_eq!(
            self.program.fields(id),
            fields.iter().map(Held::owner).collect::<Vec<_>>()
        );
        let mut bytes = vec![];
        if self.program.ctors(ctor.owner).len() > 1 {
            constant::write_natural(&BigUint::from(self.program.tag(id)), &mut bytes);
        }
        for field in fields {
            bytes.extend_from_slice(field.encoded());
        }
        constant::read_checked(
            self.program.type_info(),
            ctor.owner,
            &bytes,
            &mut Budget::new(FoldLimits::default()),
        )
        .unwrap()
        .to_owned(&mut Budget::new(FoldLimits::default()))
        .unwrap()
    }

    fn boolean(&self, yes: bool) -> Held {
        self.construct(if yes { "True" } else { "False" }, &[])
    }

    fn byte(&self, n: u8) -> Held {
        self.construct(
            "U8",
            &(0..8)
                .map(|bit| self.boolean(n & (1 << bit) != 0))
                .collect::<Vec<_>>(),
        )
    }

    fn integer(&self, n: i64) -> Held {
        if n < 0 {
            self.construct("NegSucc", &[self.natural(n.unsigned_abs() - 1)])
        } else {
            self.construct("Pos", &[self.natural(n.unsigned_abs())])
        }
    }
}

fn same(actual: &Held, expected: &Held) {
    assert_eq!(actual.owner(), expected.owner());
    assert_eq!(actual.encoded(), expected.encoded());
}

#[test]
fn every_constructible_byte_roundtrips_and_narrowing_is_explicit() {
    let lib = Library::new();
    let owner = lib.byte(0).owner();
    assert_eq!(lib.program.ctors(owner).len(), 1);
    let fields = lib.program.fields(lib.program.ctor_at(owner, 0));
    assert_eq!(fields, &[lib.boolean(false).owner(); 8]);
    // Eight Bool fields: these enumerate *all* constructible U8 values.
    for n in 0..=255u8 {
        let byte = lib.byte(n);
        same(&lib.call("u8_to_nat", &[byte]), &lib.natural(n));
    }
    same(&lib.call("u8_zero", &[]), &lib.byte(0));
    for n in 0..=1024u32 {
        let byte = lib.byte(u8::try_from(n % 256).unwrap());
        same(&lib.call("u8_from_nat_wrapping", &[lib.natural(n)]), &byte);
        let checked = if n < 256 {
            lib.construct("U8Value", &[byte])
        } else {
            lib.construct("U8Overflow", &[])
        };
        same(
            &lib.call("u8_from_nat_checked", &[lib.natural(n)]),
            &checked,
        );
    }
    let huge = (BigUint::from(1u8) << 200usize) + BigUint::from(173u8);
    same(
        &lib.call("u8_from_nat_wrapping", &[lib.natural(huge.clone())]),
        &lib.byte(173),
    );
    same(
        &lib.call("u8_from_nat_checked", &[lib.natural(huge)]),
        &lib.construct("U8Overflow", &[]),
    );
}

#[test]
fn byte_arithmetic_wraps_instead_of_using_monus_or_escaping_the_type() {
    let lib = Library::new();
    for a in 0..=255u8 {
        for b in [0u8, 1, 2, 3, 127, 128, 254, 255] {
            let args = [lib.byte(a), lib.byte(b)];
            for (name, expected) in [
                ("u8_add_wrapping", a.wrapping_add(b)),
                ("u8_sub_wrapping", a.wrapping_sub(b)),
                ("u8_mul_wrapping", a.wrapping_mul(b)),
            ] {
                same(&lib.call(name, &args), &lib.byte(expected));
            }
            same(&lib.call("u8_equals", &args), &lib.boolean(a == b));
            same(&lib.call("u8_less_than", &args), &lib.boolean(a < b));
        }
    }
}

#[test]
fn signed_arithmetic_comparisons_and_conversions_have_canonical_zero() {
    let lib = Library::new();
    same(&lib.call("int_zero", &[]), &lib.integer(0));
    for a in -16i64..=16 {
        let value = lib.integer(a);
        same(
            &lib.call("int_negate", std::slice::from_ref(&value)),
            &lib.integer(-a),
        );
        same(
            &lib.call("int_abs", std::slice::from_ref(&value)),
            &lib.natural(a.unsigned_abs()),
        );
        same(
            &lib.call("int_is_negative", std::slice::from_ref(&value)),
            &lib.boolean(a < 0),
        );
        let checked = if a < 0 {
            lib.construct("IntNegative", &[])
        } else {
            lib.construct("IntNatural", &[lib.natural(a.unsigned_abs())])
        };
        same(&lib.call("int_to_nat_checked", &[value]), &checked);
        if a >= 0 {
            same(
                &lib.call("int_from_nat", &[lib.natural(a.unsigned_abs())]),
                &lib.integer(a),
            );
        }
        for b in -16i64..=16 {
            let args = [lib.integer(a), lib.integer(b)];
            for (name, expected) in [("int_add", a + b), ("int_sub", a - b), ("int_mul", a * b)] {
                same(&lib.call(name, &args), &lib.integer(expected));
            }
            same(&lib.call("int_equals", &args), &lib.boolean(a == b));
            same(&lib.call("int_less_than", &args), &lib.boolean(a < b));
        }
    }
}

#[test]
fn small_library_calls_also_evaluate_without_arithmetic_recognition() {
    let mut lib = Library::new();
    lib.operations.fill(None);
    for a in -3i64..=3 {
        for b in -3i64..=3 {
            let args = [lib.integer(a), lib.integer(b)];
            for (name, expected) in [("int_add", a + b), ("int_sub", a - b), ("int_mul", a * b)] {
                same(&lib.call(name, &args), &lib.integer(expected));
            }
        }
    }
    for n in 0..8u8 {
        same(
            &lib.call("u8_from_nat_wrapping", &[lib.natural(n)]),
            &lib.byte(n),
        );
    }
    for (name, expected) in [("u8_add_wrapping", 5), ("u8_mul_wrapping", 6)] {
        same(
            &lib.call(name, &[lib.byte(2), lib.byte(3)]),
            &lib.byte(expected),
        );
    }
}

#[test]
fn signed_magnitudes_remain_unbounded() {
    let lib = Library::new();
    let n = BigUint::from(1u8) << 200usize;
    let positive = lib.construct("Pos", &[lib.natural(n.clone())]);
    let negative = lib.construct("NegSucc", &[lib.natural(&n - BigUint::from(1u8))]);
    same(
        &lib.call("int_add", &[positive.clone(), negative.clone()]),
        &lib.integer(0),
    );
    same(
        &lib.call("int_sub", &[negative.clone(), positive]),
        &lib.construct(
            "NegSucc",
            &[lib.natural((&n << 1usize) - BigUint::from(1u8))],
        ),
    );
    same(
        &lib.call("int_mul", &[negative.clone(), negative]),
        &lib.construct("Pos", &[lib.natural(&n * &n)]),
    );
}

#[test]
fn library_products_sums_and_large_magnitudes_fold_as_ordinary_calls() {
    let mut lib = Library::new();
    let huge = BigUint::from(1u8) << 100usize;
    let cases = [
        ("u8_sub_wrapping", vec![lib.byte(0), lib.byte(1)]),
        ("u8_mul_wrapping", vec![lib.byte(255), lib.byte(255)]),
        ("u8_from_nat_checked", vec![lib.natural(255u32)]),
        ("u8_from_nat_checked", vec![lib.natural(256u32)]),
        ("int_negate", vec![lib.integer(0)]),
        ("int_sub", vec![lib.integer(-3), lib.integer(5)]),
        (
            "int_mul",
            vec![
                lib.construct("NegSucc", &[lib.natural(huge.clone())]),
                lib.construct("NegSucc", &[lib.natural(huge)]),
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

#[test]
fn library_meaning_does_not_depend_on_names_or_constructor_order() {
    let source = format!(
        "{NAT}\n{U8}\n{INT}\nprobe() ->
          one = Succ(Zero)
          byte = u8_sub_wrapping(u8_zero() u8_from_nat_wrapping(one))
          int_abs(int_add(NegSucc(u8_to_nat(byte)) Pos(one)))
        main!(h) -> exit!(h probe())"
    );
    let source = source
        .replace("Nat", "Count")
        .replace("Zero", "Nil")
        .replace("Succ", "Next")
        .replace("Bool False True", "Truth True False")
        .replace("Bool", "Truth")
        .replace("U8", "Octet")
        .replace(
            "Int Pos(Count) NegNext(Count)",
            "Signed NegNext(Count) Pos(Count)",
        )
        .replace("u8_", "byte_")
        .replace("int_", "signed_");
    let mut program = crate::simple::parse(&source, &crate::platform::Routines::builtin()).unwrap();
    normalize_with_limits(&mut program, InlineLimits::default());
    fold(&mut program);
    validate(&program).unwrap();
    let probe = program
        .functions()
        .iter()
        .find(|f| program.name(f.name) == "probe")
        .unwrap();
    let Expr::Static(value) = program.expr(probe.body().unwrap().tail) else {
        panic!("renamed probe did not fold");
    };
    let ConstantView::Natural(number) = program.constant(value).view() else {
        panic!("a natural");
    };
    assert_eq!(number.try_u64(), Ok(255));
}
