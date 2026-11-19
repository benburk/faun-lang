//! The standard library, built into the compiler so that it is one file
//! wherever it is put.
//!
//! Its modules are named under a root of their own, `<std>`, which no
//! module read from disk shares: every other path the loader holds is
//! canonical, so absolute. Setting `FAUN_STD` to a directory reads the
//! standard library from there instead, to work on it without rebuilding.
//!
//! The command builds in a snapshot of the built-in library checked, and
//! hands it here: a compile reads that in place of checking the library,
//! unless `FAUN_STD` names other text.

use std::path::{Path, PathBuf};
use std::sync::OnceLock;

/// Each built-in module's text, by its path under the root.
static FILES: &[(&str, &str)] = include!(concat!(env!("OUT_DIR"), "/standard.rs"));

/// The root built-in modules are named under.
const BUILT_IN: &str = "<std>";

/// The snapshot of the built-in library, once the command hands it over.
static SNAPSHOT: OnceLock<&'static [u8]> = OnceLock::new();

/// The standard library's root module: built in, or `FAUN_STD`'s where set.
pub(crate) fn root_module() -> &'static Path {
    static ROOT: OnceLock<PathBuf> = OnceLock::new();
    ROOT.get_or_init(|| {
        std::env::var_os("FAUN_STD")
            .map_or_else(|| PathBuf::from(BUILT_IN), PathBuf::from)
            .join("standard.fn")
    })
}

/// The built-in library's root module, whatever `FAUN_STD` says.
pub(crate) fn built_in_root() -> PathBuf {
    Path::new(BUILT_IN).join("standard.fn")
}

/// Read the built-in library from `snapshot` from now on.
pub(crate) fn set_snapshot(snapshot: &'static [u8]) {
    // A second snapshot would be the same compiler's, so the same.
    let _ = SNAPSHOT.set(snapshot);
}

/// The snapshot to read the library from: none where none was handed
/// over, or where `FAUN_STD` names the library's text.
pub(crate) fn snapshot() -> Option<&'static [u8]> {
    (root_module() == built_in_root())
        .then(|| SNAPSHOT.get().copied())
        .flatten()
}

/// The text of the built-in module at `path`, where it names one.
pub(crate) fn built_in(path: &Path) -> Option<&'static str> {
    let relative = path.strip_prefix(BUILT_IN).ok()?;
    FILES
        .iter()
        .find(|(name, _)| Path::new(name) == relative)
        .map(|(_, text)| *text)
}

/// The text of the built-in module a diagnostic shows as `name`: its path
/// under `std` rather than the root.
pub(crate) fn shown(name: &Path) -> Option<&'static str> {
    built_in(&Path::new(BUILT_IN).join(name.strip_prefix("std").ok()?))
}

/// Whether `path` names a built-in module or a file on disk.
pub(crate) fn is_module(path: &Path) -> bool {
    built_in(path).is_some() || path.is_file()
}
