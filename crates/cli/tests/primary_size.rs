//! The first rungs of the ladder, written in Faun and built by the command
//! line, are exactly as small as the same rungs built with the Barb builder:
//! source adds nothing to what a target writes. Sizes are exact, so a change
//! either way is seen; lower them when codegen improves, and explain a rise.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use faun_core::programs::ladder;
use faun_core::targets::Target;
use faun_mos6502_sim65::Mos6502Sim65;
use faun_wasm32_wasi::Wasm32Wasi;
use faun_x86_64_linux::X86_64Linux;

/// Each rung: the ladder's name for it, and the same program in Faun.
const RUNGS: [(&str, &str); 5] = [
    (
        "a constant",
        "import std.host {Host}\n\nmain! : Host -> []\nmain!(host) -> host.exit!(0)\n",
    ),
    (
        "the count",
        "import std.host {Host}\n\nmain! : Host -> []\nmain!(host) ->\n  count = host.args.len()\n  host.exit!(count)\n",
    ),
    (
        "the count and a constant",
        "import std.host {Host}\n\nmain! : Host -> []\nmain!(host) ->\n  count = host.args.len()\n  host.exit!((count + 4) % 256)\n",
    ),
    (
        "the low bits of a sum",
        "import std.host {Host}\n\nmain! : Host -> []\nmain!(host) ->\n  count = host.args.len()\n  host.exit!((count + count) % 256)\n",
    ),
    (
        "a greeting",
        include_str!("../../faun/examples/minimal-hello.fn"),
    ),
];

/// Each target, what it appends to an output name, and each rung's size.
const SIZES: [(&dyn Target, &str, [u64; 5]); 3] = [
    (&X86_64Linux, "", [127, 129, 132, 131, 157]),
    (&Mos6502Sim65, ".bin", [17, 31, 34, 32, 51]),
    (&Wasm32Wasi, ".wasm", [36, 158, 181, 181, 164]),
];

#[test]
fn faun_rungs_are_as_small_as_the_ladder() {
    let root = std::env::temp_dir().join(format!("faun-primary-size-{}", std::process::id()));
    fs::create_dir_all(&root).unwrap();
    let built_ladder = ladder::every();

    for (target, extension, sizes) in SIZES {
        for ((name, source), size) in RUNGS.into_iter().zip(sizes) {
            let source_path = root.join(format!("{}.fn", name.replace(' ', "-")));
            let output = root.join(format!("{}-{}", target.name(), name.replace(' ', "-")));
            fs::write(&source_path, source).unwrap();
            build(target.name(), &source_path, &output);
            let artifact = PathBuf::from(format!("{}{extension}", output.display()));
            let written = fs::metadata(&artifact).unwrap().len();
            assert_eq!(written, size, "{} `{name}` from Faun", target.name());

            let (_, rung) = built_ladder
                .iter()
                .find(|(rung, _)| *rung == name)
                .expect("a rung of the ladder");
            let mut barb = rung.clone();
            faun_core::barb::optimize(&mut barb);
            let machine = faun_core::lower_to_machine_ir(&mut barb, &target.routines()).unwrap();
            let image = target.compile_machine_ir(&machine).unwrap();
            assert_eq!(
                u64::try_from(image.len()).unwrap(),
                written,
                "{} `{name}`: Faun and the ladder differ",
                target.name()
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
