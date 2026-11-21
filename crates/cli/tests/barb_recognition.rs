//! Verify recognition through the frontend and the public Barb facts API.
mod support;

use std::collections::BTreeMap;
use std::fmt::Write as _;

use faun_core::targets::Target;
use faun_x86_64_linux::X86_64Linux;
use support::Package;

fn optimized(package: &Package) -> barb::Program {
    let mut program =
        faun_frontend::lower_to_barb(&package.entry(), &faun_driver::platform(&X86_64Linux))
            .unwrap();
    barb::optimize(&mut program);
    barb::validate(&program).unwrap();
    program
}

/// The facts a target with float instructions reads, which name the float
/// operations it answers.
fn with_floats(program: &barb::Program) -> barb::Facts {
    program.assuming(&barb::Assumed {
        floats: true,
        ..barb::Assumed::default()
    })
}

#[test]
fn rotations_are_recognized_by_equations_with_a_checked_input_range() {
    for (modulus, recognized) in [(256, true), (1024, false)] {
        let package = Package::new(
            &format!("rotation-{modulus}"),
            &format!(
                r"
            turn : (Nat, Nat) -> Nat
            turn(value, amount) -> (
              moved = value * 2.pow(amount % 8)
              moved % 256 + moved / 256
            )
            main!(host) -> host.exit!(U8.of_nat(turn(host.args.len() % {modulus}, host.args.len())))
        "
            ),
        );
        let program = optimized(&package);
        let facts = program.analyze();
        assert_eq!(
            program
                .function_ids()
                .any(|id| facts.rotation(id).is_some_and(|r| r.bits == 8)),
            recognized
        );
    }
}

#[test]
fn floating_sign_recognition_preserves_the_signed_zero_exception() {
    for (left, found) in [("4.0", true), ("-0.0", false)] {
        let package = Package::new(
            &format!("float-sign-{found}"),
            &format!(
                r"
            answer : (F64, Nat) -> Bool
            answer(value, 0) -> ({left} - value).sign_bit()
            answer(value, n) -> answer(value, n - 1)
            main!(host) -> host.exit!(answer(F64.of_nat(host.args.len()), host.args.len()).select(1, 0))
        "
            ),
        );
        let program = optimized(&package);
        let facts = program.analyze();
        let recognized = (0..program.exprs_count())
            .any(|at| facts.float_comparison(barb::ExprId::at(at)).is_some());
        assert_eq!(recognized, found);
    }
}

#[test]
fn final_tree_facts_identify_the_builder_and_reader_before_lowering() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../frontend/examples/benchmarks-game/binary-trees/main.fn");
    let mut program =
        faun_frontend::lower_to_barb(&path, &faun_driver::platform(&X86_64Linux)).unwrap();
    barb::optimize(&mut program);
    let facts = program.analyze();
    let roles: Vec<_> = program
        .function_ids()
        .map(|id| facts.tree_role(id))
        .collect();
    assert!(roles.contains(&barb::TreeRole::Builder));
    assert!(roles.contains(&barb::TreeRole::Reader));
}

#[test]
fn float_doubling_is_rewritten_before_machine_lowering() {
    let package = Package::new(
        "float-doubling",
        r"
        twice : (F64, Nat) -> F64
        twice(value, 0) -> value * 2.0 + value
        twice(value, n) -> twice(value, n - 1)
        main!(host) -> (
          host.print!(twice(F64.of_nat(host.args.len()), host.args.len()).to_str())
          host.exit!(0)
        )
    ",
    );
    let program = optimized(&package);
    let facts = with_floats(&program);
    let function = program
        .functions()
        .iter()
        .find(|f| program.name(f.name) == "twice")
        .unwrap();
    let mut adds = 0;
    for expr in expressions(&program, function.body().unwrap()) {
        if let barb::Expr::Call(id, _) = expr
            && let Some(float) = facts.float(id)
        {
            assert_ne!(float.operation, barb::float::Operation::Mul);
            adds += usize::from(float.operation == barb::float::Operation::Add);
        }
    }
    assert!(adds >= 2);
}

fn expressions(program: &barb::Program, body: barb::Body) -> Vec<barb::Expr> {
    let mut result = Vec::new();
    for id in program
        .bindings(body.bindings)
        .iter()
        .copied()
        .chain([body.tail])
    {
        let expr = program.expr(id);
        result.push(expr);
        if let barb::Expr::Match(_, arms) = expr {
            for arm in program.arms(arms) {
                result.extend(expressions(program, arm.body));
            }
        }
    }
    result
}

/// Every float operation the standard has, at both formats.
const FLOATS: [(&str, &str); 2] = [("F64", "Binary64"), ("F32", "Binary32")];
const OPERATIONS: [(&str, &str); 5] = [
    ("add", "Add"),
    ("sub", "Sub"),
    ("mul", "Mul"),
    ("div", "Div"),
    ("sqrt", "Sqrt"),
];

/// A program asking every float operation of both formats.
fn every_float_operation() -> Package {
    Package::new(
        "every-float-operation",
        r"
        main!(host) -> (
          n = host.args.len()
          wide = F64.of_nat(n)
          narrow = F32.of_nat(n)
          host.print!((wide + wide - wide * wide / wide).sqrt().to_str())
          host.print!((narrow + narrow - narrow * narrow / narrow).sqrt().to_str())
          host.exit!(0)
        )
    ",
    )
}

/// Each standard float operation's fingerprint, as its code comes to after
/// canonicalizing, on every target, with the operation and format it is.
fn reference_fingerprints() -> BTreeMap<u128, (&'static str, &'static str)> {
    let package = every_float_operation();
    let targets: [&dyn Target; 4] = [
        &X86_64Linux,
        &faun_aarch64_macos::Aarch64Macos,
        &faun_wasm32_wasi::Wasm32Wasi,
        &faun_mos6502_sim65::Mos6502Sim65,
    ];
    let mut known = BTreeMap::new();
    for target in targets {
        let mut program =
            faun_frontend::lower_to_barb(&package.entry(), &faun_driver::platform(target)).unwrap();
        barb::test_support::canonical(&mut program);
        for (float, format) in FLOATS {
            for (method, operation) in OPERATIONS {
                let name = format!("{float}.{method}");
                let id = program
                    .function_ids()
                    .find(|&id| program.name(program.function(id).name) == name)
                    .unwrap_or_else(|| panic!("the standard has no `{name}`"));
                let print = barb::test_support::fingerprint(&program, id)
                    .unwrap_or_else(|| panic!("`{name}` has no fingerprint"));
                known.insert(print, (operation, format));
            }
        }
    }
    known
}

/// The table Barb recognizes float operations by, as Rust.
fn reference_table() -> String {
    let mut table = String::from(
        "//! Written by `FAUN_BLESS=1 cargo nextest run -p faun --test barb_recognition`\n\
         //! from the standard's float operations, as the code of each comes to after\n\
         //! canonicalizing. Do not edit by hand.\n\n\
         use crate::float::{Float, Format, Operation};\n\n\
         pub(super) const KNOWN: &[(u128, Float)] = &[\n",
    );
    for (print, (operation, format)) in reference_fingerprints() {
        let digits = format!("{print:032x}");
        let print = digits
            .as_bytes()
            .chunks(4)
            .map(|chunk| std::str::from_utf8(chunk).unwrap())
            .collect::<Vec<_>>()
            .join("_");
        writeln!(
            table,
            "    (\n        0x{print},\n        Float {{\n            operation: Operation::{operation},\n            format: Format::{format},\n        }},\n    ),"
        )
        .unwrap();
    }
    table.push_str("];\n");
    table
}

#[test]
fn the_reference_float_table_is_the_standards_code() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../barb/src/floats/known.rs");
    let table = reference_table();
    if std::env::var_os("FAUN_BLESS").is_some_and(|value| value != "0") {
        std::fs::write(&path, &table).unwrap();
        return;
    }
    assert!(
        std::fs::read_to_string(&path).unwrap() == table,
        "the standard's float code changed: run `just bless` and read the diff"
    );
}

/// What a failing recognition says: the table no longer matches the
/// standard's code, and how to write it again.
const STALE: &str = "Barb's table of the standard's float code (crates/barb/src/floats/known.rs) \
     is stale, so this operation would run as the software routine on x86-64: \
     run `just bless` (FAUN_BLESS=1 cargo nextest run -p faun --test barb_recognition \
     the_reference_float_table) and read the diff";

/// A program asking `float`'s `method` and no other float operation.
fn asking(float: &str, method: &str) -> Package {
    let asked = if method == "sqrt" {
        "x.sqrt()".to_owned()
    } else {
        let symbol = match method {
            "add" => "+",
            "sub" => "-",
            "mul" => "*",
            _ => "/",
        };
        format!("x {symbol} x")
    };
    Package::new(
        &format!("float-{float}-{method}"),
        &format!(
            r"
        main!(host) -> (
          x = {float}.of_nat(host.args.len())
          host.print!(({asked}).to_str())
          host.exit!(0)
        )
    "
        ),
    )
}

/// Each operation the table covers, at each format, asked alone by a
/// program built for x86-64, whose float instructions answer it, is
/// recognized as itself: a library edit that changes a routine's code
/// without blessing the table would otherwise leave float code silently on
/// the software routines.
#[test]
fn every_float_operation_is_recognized_by_its_code() {
    for (float, format) in FLOATS {
        for (method, operation) in OPERATIONS {
            let name = format!("{float}.{method}");
            let program = optimized(&asking(float, method));
            let facts = with_floats(&program);
            // A recognized definition is never inlined, so one swept from a
            // program asking it was not recognized either.
            let recognized = program
                .function_ids()
                .find(|&id| program.name(program.function(id).name) == name)
                .and_then(|id| facts.float(id))
                .unwrap_or_else(|| panic!("`{name}` is not recognized: {STALE}"));
            assert_eq!(
                format!("{:?}", recognized.operation),
                operation,
                "{name}: {STALE}"
            );
            assert_eq!(
                format!("{:?}", recognized.format),
                format,
                "{name}: {STALE}"
            );
        }
    }
}
