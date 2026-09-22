use super::*;

const EXAMPLE: &str = include_str!("../../simple/examples/expressions.fn");

#[test]
fn inspection_parses_each_stage_and_target_before_the_source_path() {
    cli().check_invariants(false);
    for (flag, expected) in [
        ("barb", Stage::Barb),
        ("ir", Stage::Ir),
        ("prepared-ir", Stage::PreparedIr),
    ] {
        let parsed = cli()
            .run_inner(
                &[
                    "inspect",
                    "--target",
                    "mos6502-sim65",
                    "--emit",
                    flag,
                    "crates/simple/examples/expressions.fn",
                ][..],
            )
            .unwrap();
        let Command::Inspect {
            source,
            target,
            stage,
        } = parsed
        else {
            panic!("inspection command expected");
        };
        assert_eq!(
            source,
            PathBuf::from("crates/simple/examples/expressions.fn")
        );
        assert_eq!(target.name(), "mos6502-sim65");
        assert_eq!(stage, expected);
    }
    assert!(
        cli()
            .run_inner(&["inspect", "--emit", "unknown", "example.fn"][..])
            .is_err()
    );
}

#[test]
fn inspection_uses_normal_optimization_and_target_widths() {
    for target in ALL {
        let barb = inspect(EXAMPLE, target, Stage::Barb).unwrap();
        let (_, main) = barb.split_once("main!(").unwrap();
        assert!(main.contains("= 2\n"));
        assert!(main.contains("= 32\n"));
        assert!(main.contains("argc!("));
        assert!(main.contains("exit!("));
        assert!(barb.contains("exit!(v0: Host, v1: Nat) -> Never = <elsewhere>\n"));
        assert!(barb.contains("argc!(v0: Host) -> Nat = <elsewhere>\n"));
        assert!(!barb.contains(['{', '}']));
        assert_eq!(main.matches("= add(").count(), 2);

        machine_ir(target);
    }
}

/// What the machine tier is handed for the same example.
fn machine_ir(target: &'static dyn Target) {
    {
        let ir = inspect(EXAMPLE, target, Stage::Ir).unwrap();
        assert!(ir.starts_with(
            "# Classes are per-value representation requirements, not source types.\n"
        ));
        assert!(ir.contains("fn f0 main!() -> (word) = r0"));
        // Every count the machine can report, which is every number its
        // word holds.
        let count = u64::MAX >> (64 - target.word());
        assert!(ir.contains(&format!("argc!() -> (0..{count})")));
        assert!(ir.contains("call argc!()  # f2"));
        assert_eq!(ir.matches("= Up ").count(), 1);
        assert_eq!(ir.matches("= Add ").count(), 1);
        assert!(
            ir.contains("0..0 = const 0"),
            "a known zero can be nothing else"
        );
        assert!(
            ir.contains("v2: word = Less v1, v0\n  v5: 0..31 = if v2 then r1 else r2"),
            "the guard branches on its comparison, with no tag in between"
        );
        assert_eq!(ir.matches(" = if ").count(), 1, "one branch, not two");
        assert!(
            ir.contains("0..31"),
            "the guard proves the count is under thirty-two"
        );
        assert!(
            ir.contains("v0: 32..32 = const 32"),
            "a known number can be nothing but itself"
        );
        assert_eq!(
            ir.matches(" = convert ").count(),
            1,
            "only the narrowing the guard proves, never a widening"
        );
        if target.name() == "aarch64-macos" {
            let error = inspect(EXAMPLE, target, Stage::PreparedIr).unwrap_err();
            assert!(error.contains("baseline emission does not yet support"));
        } else {
            assert_eq!(ir, inspect(EXAMPLE, target, Stage::PreparedIr).unwrap());
        }
    }
}

#[test]
fn inspection_never_skips_totality_checks() {
    let source = "type Nat Zero Succ(Nat)
                  forever(Zero) -> Succ(forever(Zero))
                  forever(Succ(n)) -> Succ(forever(Succ(n)))
                  main!(h) -> exit!(h forever(Zero))";
    for stage in [Stage::Barb, Stage::Ir, Stage::PreparedIr] {
        let error = inspect(source, &Mos6502Sim65, stage).unwrap_err();
        assert!(
            error.contains("forever") && error.contains("stops"),
            "{error}"
        );
    }
}

#[test]
fn lowered_ir_can_be_inspected_before_target_acceptance() {
    let source = "type Nat Zero Succ(Nat)
                  add(a Zero) -> a
                  add(a Succ(b)) -> Succ(add(a b))
                  main!(h) ->
                    n = argc!(h)
                    too_wide = add(n n)
                    exit!(h too_wide)";
    assert!(inspect(source, &Mos6502Sim65, Stage::Barb).is_ok());
    assert!(
        inspect(source, &Mos6502Sim65, Stage::Ir)
            .unwrap()
            .contains("0..131070")
    );
    let error = inspect(source, &Mos6502Sim65, Stage::PreparedIr).unwrap_err();
    assert!(error.contains("17"), "{error}");
}
