//! Build the standard library into the compiler: a table of every `.fn`
//! file under `standard/`, by its path there, each included as text, so
//! the compiler is one file wherever it is put.

use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::{env, fs};

fn main() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("standard");
    println!("cargo:rerun-if-changed={}", root.display());
    let mut files = Vec::new();
    sources(&root, &mut files);
    files.sort();
    let mut table = String::from("&[\n");
    for file in &files {
        let relative = file.strip_prefix(&root).expect("a file under the root");
        let relative = relative.to_str().expect("a standard path is UTF-8");
        let absolute = file.to_str().expect("a standard path is UTF-8");
        writeln!(table, "    ({relative:?}, include_str!({absolute:?})),")
            .expect("writing to a string");
    }
    table.push(']');
    let out = PathBuf::from(env::var_os("OUT_DIR").expect("cargo sets OUT_DIR"));
    fs::write(out.join("standard.rs"), table).expect("OUT_DIR is writable");
}

/// Every `.fn` file under `directory`, at any depth.
fn sources(directory: &Path, files: &mut Vec<PathBuf>) {
    for entry in fs::read_dir(directory).expect("standard/ is readable") {
        let path = entry.expect("standard/ is readable").path();
        if path.is_dir() {
            sources(&path, files);
        } else if path.extension().is_some_and(|extension| extension == "fn") {
            files.push(path);
        }
    }
}
