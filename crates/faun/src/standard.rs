//! The standard library, built into the compiler so that it is one file
//! wherever it is put.
//!
//! Its modules are named under a root of their own, `<std>`, which no
//! module read from disk shares: every other path the loader holds is
//! canonical, so absolute. Setting `FAUN_STD` to a directory reads the
//! standard library from there instead, to work on it without rebuilding.

use std::path::{Path, PathBuf};
use std::sync::OnceLock;

/// Each built-in module's text, by its path under the root.
static FILES: &[(&str, &str)] = include!(concat!(env!("OUT_DIR"), "/standard.rs"));

/// The root built-in modules are named under.
const BUILT_IN: &str = "<std>";

/// The standard library's root module: built in, or `FAUN_STD`'s where set.
pub(crate) fn root_module() -> &'static Path {
    static ROOT: OnceLock<PathBuf> = OnceLock::new();
    ROOT.get_or_init(|| {
        let directory =
            std::env::var_os("FAUN_STD").map_or_else(|| PathBuf::from(BUILT_IN), PathBuf::from);
        directory.join("standard.fn")
    })
}

/// The text of the built-in module at `path`, where it names one.
pub(crate) fn built_in(path: &Path) -> Option<&'static str> {
    let relative = path.strip_prefix(BUILT_IN).ok()?;
    FILES
        .iter()
        .find(|(name, _)| Path::new(name) == relative)
        .map(|(_, text)| *text)
}

/// Whether `path` names a built-in module or a file on disk.
pub(crate) fn is_module(path: &Path) -> bool {
    built_in(path).is_some() || path.is_file()
}
