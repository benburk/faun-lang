//! Compiling Faun source from tests. The primary frontend reads
//! applications from files, so each program is written to a fresh scratch
//! directory, compiled for the target, and the directory removed.

use std::fs;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};

use crate::ir::Program;
use crate::targets::Target;

/// Lower a Faun application to the machine IR `target` compiles: to Barb,
/// optimized, then to machine IR.
pub(crate) fn lower(text: &str, target: &dyn Target) -> Result<Program, String> {
    let (dir, path) = source_file(text);
    let barb = ::faun::lower_to_barb(&path, &faun_x86_64_linux::X86_64Linux);
    fs::remove_dir_all(dir).expect("the scratch source to go");
    let mut barb = barb?;
    crate::barb::optimize(&mut barb);
    crate::lower_to_machine_ir(&barb, &target.routines())
}

/// Lower a Faun package's expectations as `faun test` builds them: an
/// application printing the number of each that does not hold.
#[allow(
    dead_code,
    reason = "not every test binary including this runs expectations"
)]
pub(crate) fn expectations(text: &str, target: &dyn Target) -> Result<Program, String> {
    let (dir, path) = source_file(text);
    let program = expectations_at(&path, target);
    fs::remove_dir_all(dir).expect("the scratch source to go");
    program
}

/// The same, for the package whose entry is at `path`.
#[allow(
    dead_code,
    reason = "not every test binary including this runs expectations"
)]
pub(crate) fn expectations_at(
    path: &std::path::Path,
    target: &dyn Target,
) -> Result<Program, String> {
    let mut barb = ::faun::lower_tests_to_barb(path, &faun_x86_64_linux::X86_64Linux)?.barb;
    crate::barb::optimize(&mut barb);
    crate::lower_to_machine_ir(&barb, &target.routines())
}

/// The same, without optimizing Barb, for a test of shapes the optimizer
/// would have removed.
#[allow(
    dead_code,
    reason = "not every test binary including this reads unoptimized"
)]
pub(crate) fn unoptimized(text: &str, target: &dyn Target) -> Result<Program, String> {
    let (dir, path) = source_file(text);
    let barb = ::faun::lower_to_barb(&path, &faun_x86_64_linux::X86_64Linux);
    fs::remove_dir_all(dir).expect("the scratch source to go");
    crate::lower_to_machine_ir(&barb?, &target.routines())
}

/// Write `text` as the entry module of a fresh scratch directory.
fn source_file(text: &str) -> (PathBuf, PathBuf) {
    static NEXT: AtomicU64 = AtomicU64::new(0);
    let at = NEXT.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("faun-source-{}-{at}", std::process::id()));
    fs::create_dir_all(&dir).expect("a scratch directory");
    let path = dir.join("main.fn");
    fs::write(&path, text).expect("somewhere to write the source");
    (dir, path)
}
