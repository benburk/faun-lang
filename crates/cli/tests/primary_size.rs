use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

const CONSTANT: &str =
    "import std.host {Host exit!}\n\nmain! : Host -> []\nmain!(host) -> exit!(host 0)\n";
const COUNT: &str = "import std.host {Host argc! exit!}\n\nmain! : Host -> []\nmain!(host) ->\n  count = argc!(host)\n  exit!(host count)\n";
const ARITHMETIC: &str = "import std.host {Host argc! exit!}\n\nmain! : Host -> []\nmain!(host) ->\n  count = argc!(host)\n  exit!(host (count + 4) % 256)\n";

#[test]
fn primary_frontend_preserves_initial_size_ratchets() {
    let root = std::env::temp_dir().join(format!("faun-primary-size-{}", std::process::id()));
    fs::create_dir_all(&root).unwrap();

    for (target, extension, ceilings) in [
        ("x86_64-linux", "", [127, 129, 134]),
        ("mos6502-sim65", ".bin", [17, 33, 36]),
        ("wasm32-wasi", ".wasm", [36, 158, 181]),
    ] {
        for ((name, source), ceiling) in [
            ("constant", CONSTANT),
            ("count", COUNT),
            ("arithmetic", ARITHMETIC),
        ]
        .into_iter()
        .zip(ceilings)
        {
            let source_path = root.join(format!("{name}.fn"));
            let output = root.join(format!("{target}-{name}"));
            fs::write(&source_path, source).unwrap();
            build(target, &source_path, &output);
            let artifact = PathBuf::from(format!("{}{extension}", output.display()));
            let size = fs::metadata(&artifact).unwrap().len();
            assert!(
                size <= ceiling,
                "{target} {name} grew to {size} bytes (ceiling {ceiling})"
            );
        }
    }

    fs::remove_dir_all(root).unwrap();
}

fn build(target: &str, source: &Path, output: &Path) {
    let result = Command::new(env!("CARGO_BIN_EXE_faun"))
        .args(["build", "--target", target, "--output"])
        .arg(output)
        .arg(source)
        .output()
        .unwrap();
    assert!(
        result.status.success(),
        "faun build failed: {}",
        String::from_utf8_lossy(&result.stderr)
    );
}
