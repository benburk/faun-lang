//! Compiling Faun source from tests. The primary frontend reads
//! applications from files, so each program is written to a fresh scratch
//! directory, compiled for the target, and the directory removed.

use std::fs;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};

use faun_core::ir::Program;
use faun_core::targets::Target;

/// Compile a Faun application to the machine IR `target` compiles.
pub(crate) fn machine(text: &str, target: &dyn Target) -> Result<Program, String> {
    let (dir, path) = source_file(text);
    let machine = faun_driver::machine(&path, target);
    fs::remove_dir_all(dir).expect("the scratch source to go");
    machine
}

/// The same, lowered without optimizing, for a test of shapes the
/// optimizer would have removed.
#[allow(
    dead_code,
    reason = "not every test binary including this reads unoptimized"
)]
pub(crate) fn unoptimized(text: &str, target: &dyn Target) -> Result<Program, String> {
    let (dir, path) = source_file(text);
    let barb = faun_driver::barb(&path, target);
    fs::remove_dir_all(dir).expect("the scratch source to go");
    faun_core::machine(&mut barb?, &target.routines())
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
