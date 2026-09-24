//! Baselines for normally optimized source expressions with runtime inputs.
//! Sizes include the image header; cycles include startup, argc, the guard,
//! expression and exit. These are whole-program costs, not isolated ALU costs.
//! Lower the ratchets when codegen improves; explain any increase.

use std::fs;
use std::path::Path;
use std::process::Command;

use faun_core::targets::Target;
use faun_mos6502_sim65::Mos6502Sim65;

#[path = "../../core/tests/support/expressions.rs"]
mod expressions;
#[path = "../../core/tests/support/faun.rs"]
mod faun;

use expressions::{CASES, COUNTS, Case};

// Case, image bytes, maximum cycles over COUNTS (including rejected inputs).
// Carry rose from 95 bytes and 80 cycles when the corpus moved to Faun: its
// guard now branches with the count itself rather than answering a narrowed
// copy, and lowering still adds at the count's word width inside the arm
// that proves it small. Narrowing a refined local in its arm would win this
// back.
const BASELINES: &[(Case, usize, u64)] = &[
    (Case::Chain, 50, 36),
    (Case::Shared, 55, 44),
    (Case::ConstantLeft, 50, 36),
    (Case::Carry, 121, 115),
    (Case::Monus, 83, 64),
];

#[test]
fn guarded_argc_expressions_stay_within_size_and_cycle_ceilings() {
    assert_eq!(CASES.len(), BASELINES.len());
    for (case, &(expected, size, ceiling)) in CASES.into_iter().zip(BASELINES) {
        assert_eq!(case, expected, "baselines must match the corpus");
        measure(case, size, ceiling);
    }
}

fn measure(case: Case, size: usize, ceiling: u64) {
    let program =
        faun::machine(&case.source(), &Mos6502Sim65).expect("a guarded source expression");
    // Reading (above), preparation and emission happen once per case, not
    // per input. Every invocation below executes this same image.
    let image = Mos6502Sim65.compile(&program).expect("scalar compilation");
    assert!(
        image.len() <= size,
        "{case:?}: {} bytes, ceiling {size}",
        image.len()
    );
    let dir = std::env::temp_dir().join(format!(
        "faun-expression-cost-{}-{case:?}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("a clock after the epoch")
            .as_nanos()
    ));
    fs::create_dir_all(&dir).expect("a scratch directory");
    let path = dir.join("image");
    fs::write(&path, &image).expect("the image");

    for &argc in COUNTS {
        let (status, cycles) = run(&path, argc);
        assert_eq!(status, case.expected(argc), "{case:?}, argc={argc}");
        assert!(
            cycles <= ceiling,
            "{case:?}, argc={argc}: {cycles} cycles, ceiling {ceiling}"
        );
    }
    fs::remove_dir_all(&dir).expect("the scratch directory to go");
}

/// Run an existing image, returning its status and the simulator's cycle tally.
fn run(path: &Path, argc: u16) -> (i32, u64) {
    let output = Command::new("sim65")
        .arg("-c")
        .arg(path)
        .args((1..argc).map(|_| "dummy"))
        .output()
        .expect("sim65 on the path");
    let text = String::from_utf8_lossy(&output.stderr).into_owned()
        + &String::from_utf8_lossy(&output.stdout);
    let status = output
        .status
        .code()
        .unwrap_or_else(|| panic!("the simulator was signalled: {text}"));
    let cycles = text
        .lines()
        .rev()
        .find_map(|line| line.trim().strip_suffix(" cycles")?.trim().parse().ok())
        .unwrap_or_else(|| panic!("no cycle count in {text:?}"));
    (status, cycles)
}
