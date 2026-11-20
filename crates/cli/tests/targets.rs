//! Exercise target selection, runtime argument forwarding and the
//! representation of a sum carrying a byte sequence through the real CLI.
mod support;

use std::process::Command;
use support::Package;

const BYTE_RESULT: &str = r"pick : (Nat, List(U8)) -> Result(List(U8), U8)
        pick(0, _) -> Err(11)
        pick(_, bytes) -> Ok(bytes)
        answer : Result(List(U8), U8) -> U8
        answer(Ok(bytes)) -> bytes.get(0).ok_or(9)
        answer(Err(code)) -> code
        expect answer(pick(0, [7])) == 11
        main!(host) -> (
          count = host.args.len()
          host.exit!(answer(pick(count - 1, [U8.of_nat(count)])))
        )";

#[test]
fn both_arms_run_on_wasm_and_6502() {
    let package = Package::new("byte-result-targets", BYTE_RESULT);
    for target in ["wasm32-wasi", "mos6502-sim65"] {
        for (args, expected) in [(vec![], 11), (vec!["a", "b"], 3)] {
            let result = Command::new(env!("CARGO_BIN_EXE_faun"))
                .args(["run", "--target", target])
                .arg(package.entry())
                .arg("--")
                .args(args)
                .output()
                .unwrap();
            assert_eq!(
                result.status.code(),
                Some(expected),
                "{target}: {}",
                String::from_utf8_lossy(&result.stderr)
            );
        }
        let result = Command::new(env!("CARGO_BIN_EXE_faun"))
            .args(["test", "--target", target])
            .arg(package.entry())
            .output()
            .unwrap();
        assert!(
            result.status.success(),
            "{target}: {}",
            String::from_utf8_lossy(&result.stderr)
        );
    }
}

#[test]
fn apple_silicon_builds_the_greeting() {
    let source = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../frontend/examples/minimal-hello.fn");
    let dir = Package::new("macho-greeting", "main!(host) -> host.exit!(0)");
    let path = dir.entry().with_file_name("greeting");
    let output = Command::new(env!("CARGO_BIN_EXE_faun"))
        .args(["build", "--target", "aarch64-macos", "-o"])
        .arg(&path)
        .arg(&source)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let image = std::fs::read(&path).unwrap();
    assert_eq!(&image[..8], &[0xcf, 0xfa, 0xed, 0xfe, 0x0c, 0, 0, 1]);
    #[cfg(all(target_arch = "aarch64", target_os = "macos"))]
    {
        let result = Command::new(&path).output().unwrap();
        assert!(result.status.success());
        assert_eq!(result.stdout, b"Hello, world!");
    }
}

/// Every target has one backend. `--backend lab` names it still, for a
/// script written when there were two, and builds the same image as
/// leaving it out; the stock backend is gone, and asking for it says so.
#[test]
fn the_backend_named_lab_is_the_only_one() {
    let source = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../frontend/examples/minimal-hello.fn");
    let dir = Package::new("one-backend", "main!(host) -> host.exit!(0)");
    for target in ["x86_64-linux", "wasm32-wasi", "mos6502-sim65"] {
        let images: Vec<Vec<u8>> = [&[][..], &["--backend", "lab"][..]]
            .into_iter()
            .enumerate()
            .map(|(at, backend)| {
                let path = dir.entry().with_file_name(format!("{target}-{at}"));
                let output = Command::new(env!("CARGO_BIN_EXE_faun"))
                    .args(["build", "--target", target])
                    .args(backend)
                    .arg("-o")
                    .arg(&path)
                    .arg(&source)
                    .output()
                    .unwrap();
                let stdout = String::from_utf8_lossy(&output.stdout);
                let written = stdout.trim().strip_prefix("wrote ").unwrap_or_else(|| {
                    panic!("{target}: {}", String::from_utf8_lossy(&output.stderr))
                });
                std::fs::read(written).unwrap()
            })
            .collect();
        assert_eq!(images[0], images[1], "{target}");
        let refused = Command::new(env!("CARGO_BIN_EXE_faun"))
            .args(["build", "--target", target, "--backend", "stock", "-o"])
            .arg(dir.entry().with_file_name("stock"))
            .arg(&source)
            .output()
            .unwrap();
        assert!(!refused.status.success(), "{target}");
        assert!(
            String::from_utf8_lossy(&refused.stderr).contains("the stock backend is gone"),
            "{target}: {}",
            String::from_utf8_lossy(&refused.stderr)
        );
    }
}

#[test]
fn shared_semantic_facts_lower_on_wasm_and_6502() {
    let package = Package::new(
        "semantic-targets",
        r"
        compare : (F32, Nat) -> Bool
        compare(value, 0) -> (4.0 - value).sign_bit()
        compare(value, n) -> compare(value, n - 1)
        main!(host) -> (
          count = host.args.len()
          value = F32.of_bits(U32.of_nat(0x40800000 + count))
          rotated = U8.of_nat(count).rotate_left(count)
          host.exit!(compare(value, count).select(rotated, 99))
        )
    ",
    );
    for target in ["wasm32-wasi", "mos6502-sim65"] {
        let result = Command::new(env!("CARGO_BIN_EXE_faun"))
            .args(["run", "--target", target])
            .arg(package.entry())
            .output()
            .unwrap();
        assert_eq!(
            result.status.code(),
            Some(2),
            "{target}: {}",
            String::from_utf8_lossy(&result.stderr)
        );
    }
}
