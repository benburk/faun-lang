//! Check the built-in standard library once, as the compiler is built, and
//! write what checking it leaves to `OUT_DIR` as a snapshot, which the
//! command builds in and reads in place of checking the library in every
//! compile.

use std::path::PathBuf;
use std::{env, fs};

/// As the command's own thread: checking walks the library as written.
const STACK: usize = 512 << 20;

fn main() {
    let snapshot = std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(faun_frontend::standard_snapshot)
        .expect("the checking thread starts")
        .join()
        .expect("checking the standard library does not panic")
        .unwrap_or_else(|refused| panic!("the standard library is refused: {refused}"));
    let out = PathBuf::from(env::var_os("OUT_DIR").expect("cargo sets OUT_DIR"));
    fs::write(out.join("standard.snapshot"), snapshot).expect("OUT_DIR is writable");
}
