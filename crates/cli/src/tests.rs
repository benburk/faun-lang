use super::*;

const EXAMPLE: &str = include_str!("../../../examples/expressions.fn");

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
                    "examples/expressions.fn",
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
        assert_eq!(source, PathBuf::from("examples/expressions.fn"));
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

        let ir = inspect(EXAMPLE, target, Stage::Ir).unwrap();
        assert!(ir.starts_with(
            "# Classes are per-value representation requirements, not source types.\n"
        ));
        assert!(ir.contains("fn f0 main!() -> (word) = r0"));
        assert!(ir.contains(&format!("argc!() -> (fixed{})", target.word())));
        assert!(ir.contains("call argc!()  # f2"));
        assert_eq!(ir.matches("= Add ").count(), 2);
        assert!(ir.contains("fixed0 = const 0"), "known zero selects fixed0");
        assert!(
            ir.contains("v2: word = Less v1, v0\n  v5: fixed5 = if v2 then r1 else r2"),
            "the guard branches on its comparison, with no tag in between"
        );
        assert_eq!(ir.matches(" = if ").count(), 1, "one branch, not two");
        assert!(ir.contains("fixed5"), "the guarded value is narrowed");
        assert!(
            ir.contains("v0: fixed6 = const 32"),
            "a constant is written as narrow as it is, and read as it stands"
        );
        assert_eq!(
            ir.matches(" = convert ").count(),
            1,
            "only the narrowing the guard proves, never a widening"
        );
        assert_eq!(ir, inspect(EXAMPLE, target, Stage::PreparedIr).unwrap());
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
            .contains("fixed17")
    );
    let error = inspect(source, &Mos6502Sim65, Stage::PreparedIr).unwrap_err();
    assert!(error.contains("17"), "{error}");
}
