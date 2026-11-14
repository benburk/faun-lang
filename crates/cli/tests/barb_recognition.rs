//! Verify recognition through the frontend and the public Barb facts API.
mod support;

use faun_core::barb::{self, FnId};
use faun_x86_64_linux::X86_64Linux;
use support::Package;

fn optimized(package: &Package) -> barb::Program {
    let mut program = faun::lower_to_barb(&package.entry(), &X86_64Linux).unwrap();
    barb::optimize(&mut program);
    barb::validate(&program).unwrap();
    program
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
                .functions()
                .iter()
                .enumerate()
                .any(|(at, _)| { facts.rotation(FnId::at(at)).is_some_and(|r| r.bits == 8) }),
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
        .join("../faun/examples/benchmarks-game/binary-trees/main.fn");
    let mut program = faun::lower_to_barb(&path, &X86_64Linux).unwrap();
    barb::optimize(&mut program);
    let facts = program.analyze();
    let roles: Vec<_> = (0..program.functions().len())
        .map(|at| facts.tree_role(FnId::at(at)))
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
    let function = program
        .functions()
        .iter()
        .find(|f| program.name(f.name) == "twice")
        .unwrap();
    let mut adds = 0;
    for expr in expressions(&program, function.body().unwrap()) {
        if let barb::Expr::Call(id, _) = expr
            && let Some(float) = program.function(id).float
        {
            assert_ne!(float.operation, faun_core::float::Operation::Mul);
            adds += usize::from(float.operation == faun_core::float::Operation::Add);
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
