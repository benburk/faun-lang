//! Exercise target selection, runtime argument forwarding and the lab
//! representation of a sum carrying a byte sequence through the real CLI.
mod support;

use std::process::Command;
use support::Package;

const BYTE_RESULT: &str = r"pick : (Nat, List(U8)) -> Result(List(U8), U8)
        pick(0, _) -> Err(11)
        pick(_, bytes) -> Ok(bytes)
        answer : Result(List(U8), U8) -> U8
        answer(Ok(bytes)) -> bytes.get_or(0, 9)
        answer(Err(code)) -> code
        expect answer(pick(0, [7])) == 11
        main!(host) -> (
          count = host.args.len()
          host.exit!(answer(pick(count - 1, [U8.of_nat(count)])))
        )";

#[test]
fn lab_runs_both_arms_on_wasm_and_6502() {
    let package = Package::new("lab-targets", BYTE_RESULT);
    for target in ["wasm32-wasi", "mos6502-sim65"] {
        for (args, expected) in [(vec![], 11), (vec!["a", "b"], 3)] {
            let result = Command::new(env!("CARGO_BIN_EXE_faun"))
                .args(["run", "--backend", "lab", "--target", target])
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
            .args(["test", "--backend", "lab", "--target", target])
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
fn apple_silicon_builds_the_greeting_on_each_backend() {
    let source =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../faun/examples/minimal-hello.fn");
    let dir = Package::new("lab-macho", "main!(host) -> host.exit!(0)");
    for backend in ["stock", "lab"] {
        let path = dir.entry().with_file_name(backend);
        let output = Command::new(env!("CARGO_BIN_EXE_faun"))
            .args([
                "build",
                "--target",
                "aarch64-macos",
                "--backend",
                backend,
                "-o",
            ])
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
}
