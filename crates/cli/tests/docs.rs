//! Every Faun example the repository's Markdown writes is a program that
//! holds.
//!
//! A ```` ```ruby ```` block in a note or a README is written to a file of
//! its own and run with `faun test`, so a definition that no longer checks,
//! or an `expect` that no longer holds, fails here rather than misleading a
//! reader. A block that is not a whole program, an excerpt, a fragment
//! leaning on names around it, refused or historical syntax shown on
//! purpose, says so in its fence, ```` ```ruby ignore ````, as Rust's
//! documentation tests do.
//!
//! Each block is its own test, named by its file and line, so one can be run
//! alone and one failing does not hide another.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use libtest_mimic::{Arguments, Failed, Trial};

fn main() {
    let arguments = Arguments::from_args();
    let root = root();
    let mut trials = Vec::new();
    for file in markdown(&root) {
        let text = fs::read_to_string(&file).expect("a Markdown file is readable");
        let shown = file
            .strip_prefix(&root)
            .unwrap_or(&file)
            .display()
            .to_string();
        for (line, code) in blocks(&text) {
            let name = format!("{shown}:{line}");
            trials.push(Trial::test(name.clone(), move || holds(&name, &code)));
        }
    }
    libtest_mimic::run(&arguments, trials).exit();
}

/// The repository's root.
fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// Every Markdown file under `directory`, but in build output, version
/// control and other hidden directories.
fn markdown(directory: &Path) -> Vec<PathBuf> {
    let mut files = Vec::new();
    let Ok(entries) = fs::read_dir(directory) else {
        return files;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        let name = entry.file_name();
        let name = name.to_string_lossy();
        if name.starts_with('.') || name == "target" || name == "node_modules" {
            continue;
        }
        if path.is_dir() {
            files.extend(markdown(&path));
        } else if path.extension().is_some_and(|extension| extension == "md") {
            files.push(path);
        }
    }
    files.sort();
    files
}

/// Each ```` ```ruby ```` block `text` holds, unmarked, and the line its
/// fence is on.
fn blocks(text: &str) -> Vec<(usize, String)> {
    let mut blocks = Vec::new();
    let mut open: Option<(usize, String)> = None;
    for (index, line) in text.lines().enumerate() {
        match &mut open {
            None if line == "```ruby" => open = Some((index + 1, String::new())),
            None => {}
            Some(_) if line == "```" => blocks.extend(open.take()),
            Some((_, code)) => {
                code.push_str(line);
                code.push('\n');
            }
        }
    }
    blocks
}

/// Run `code` with `faun test`, in a directory of its own.
fn holds(name: &str, code: &str) -> Result<(), Failed> {
    let slug: String = name
        .chars()
        .map(|c| if c.is_ascii_alphanumeric() { c } else { '-' })
        .collect();
    let directory = std::env::temp_dir().join(format!("faun-docs-{}-{slug}", std::process::id()));
    fs::create_dir_all(&directory).map_err(|error| format!("cannot write a scratch: {error}"))?;
    let entry = directory.join("main.fn");
    fs::write(&entry, code).map_err(|error| format!("cannot write the block: {error}"))?;
    let output = Command::new(env!("CARGO_BIN_EXE_faun"))
        .args(["test", "--target", "x86_64-linux"])
        .arg(&entry)
        .env("FAUN_CACHE", directory.join("cache"))
        .output()
        .map_err(|error| format!("cannot run faun: {error}"));
    let _ = fs::remove_dir_all(&directory);
    let output = output?;
    if output.status.success() {
        return Ok(());
    }
    Err(format!(
        "this example does not hold:\n\n{code}\n{}\n\
         Fix it, or, where it is not a whole program, mark its fence ```ruby ignore.",
        String::from_utf8_lossy(&output.stderr)
    )
    .into())
}
