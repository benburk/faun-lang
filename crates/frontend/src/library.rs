//! The standard library checked alone, and a program checked after it.
//!
//! The standard package never imports the host, so it is the same on every
//! target and for every program. [`Library::check`] takes it alone through
//! every stage [`crate::checked()`] runs. What that leaves, the [`Earlier`]
//! state, is what the host and the program are then loaded, resolved and
//! checked against: sources, modules, symbols and sites are numbered on from
//! the library's, and the typed program it checked is where the program's
//! definitions are added. Nothing a later step does to its own modules
//! reaches back into the library's.
//!
//! A [`Library`] is also what a snapshot holds: the compiler's build checks
//! the built-in library and writes it ([`Library::write`]), and a compile
//! reads it back ([`Library::read`]) in place of checking the library.

use rustc_hash::FxHashSet as HashSet;
use serde::{Deserialize, Serialize};
use std::path::Path;

use crate::blessed::PreludeIds;
use crate::check;
use crate::context::Context;
use crate::diagnostic::Diagnostic;
use crate::hir as h;
use crate::modules::{LoadedProgram, Loader};
use crate::packages::Packages;
use crate::resolve::Resolution;
use crate::typed;
use crate::{Symbol, builders};

/// What checking the modules loaded first leaves for checking those loaded
/// after them: everything the later ones may read of the earlier ones.
#[derive(Debug, Default, Serialize, Deserialize)]
pub(crate) struct Earlier {
    /// How many modules are checked.
    pub(crate) modules: usize,
    /// The next site, and which are splices' `to_str` calls.
    pub(crate) sites: h::Sites,
    /// The standard identities, once the standard package is checked.
    pub(crate) prelude: Option<PreludeIds>,
    /// Which globals are values, and every alias.
    pub(crate) resolution: Resolution,
    /// The functions that ask for record builders.
    #[serde(serialize_with = "crate::sorted::set")]
    pub(crate) pairings: HashSet<Symbol>,
    /// Each definition's scheme and bounds, each constructor's and field's,
    /// and the methods each spelling names.
    pub(crate) environment: check::Environment,
    /// Every definition checked, as typed HIR, with the types declared and
    /// the members each type has.
    pub(crate) typed: typed::Program,
}

/// The standard package, loaded and checked alone, and the loader that
/// goes on to load the host and the program after it.
#[derive(Debug, Serialize, Deserialize)]
pub(crate) struct Library {
    loader: Loader,
    earlier: Earlier,
}

impl Library {
    /// Check the standard package `loader` holds, alone.
    ///
    /// # Errors
    /// Reports what resolving or checking the standard package refuses.
    pub(crate) fn check(mut loader: Loader) -> Result<Self, Diagnostic> {
        let mut earlier = Earlier::default();
        let prelude = PreludeIds::find_among(&loader.view())?;
        let prelude_module = loader.prelude();
        let (modules, sources, symbols) = loader.parts();
        let resolved = earlier.resolution.resolve(
            (modules, 0),
            prelude_module,
            sources,
            (symbols, &mut earlier.sites),
        )?;
        earlier.modules = modules.len();
        let module_sources = modules.iter().map(|module| module.source).collect();
        let package = modules.iter().map(|module| module.id).collect();
        let mut cx = Context {
            sources: std::mem::take(&mut loader.sources),
            symbols: std::mem::take(&mut loader.symbols),
            sites: std::mem::take(&mut earlier.sites),
            module_sources,
            package,
            host_module: None,
            prelude,
            host: None,
        };
        let program = builders::desugar(
            h::Program { modules: resolved },
            &mut cx,
            &mut earlier.pairings,
        );
        crate::checked_after(program, &mut cx, &mut earlier)?;
        loader.forget_syntax();
        loader.sources = cx.sources;
        loader.symbols = cx.symbols;
        earlier.sites = cx.sites;
        earlier.prelude = Some(cx.prelude);
        Ok(Self { loader, earlier })
    }

    /// The library as a snapshot: everything it holds, each type in its
    /// environment resolved.
    ///
    /// # Panics
    /// Never: writing to memory does not fail.
    pub(crate) fn write(mut self) -> Vec<u8> {
        self.earlier.environment.close();
        postcard::to_allocvec(&self).expect("a library is written to memory")
    }

    /// The library a snapshot [`Self::write`] wrote.
    ///
    /// # Errors
    /// Reports a snapshot that is not one this compiler wrote.
    pub(crate) fn read(snapshot: &[u8]) -> Result<Self, Diagnostic> {
        postcard::from_bytes(snapshot).map_err(|error| {
            Diagnostic::new(format!(
                "the standard library's snapshot is unreadable: {error}"
            ))
        })
    }

    /// Whether the module at `path` is one of the library's.
    pub(crate) fn holds(&self, path: &Path) -> bool {
        self.loader.holds(path)
    }

    /// Load the target's `host` and the package at `entry` after the
    /// library, reading each URL dependency from where `packages` says: the
    /// whole program, and what checking the library left for the rest.
    ///
    /// # Errors
    /// Reports what loading any module does.
    pub(crate) fn rest(
        self,
        entry: &Path,
        host: &Path,
        packages: &Packages,
    ) -> Result<(LoadedProgram, Earlier), Diagnostic> {
        Ok((self.loader.rest(entry, host, packages)?, self.earlier))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A snapshot holds what the library's check leaves, so checking a
    /// program after it must leave that as it was.
    #[test]
    fn checking_a_program_after_the_library_leaves_the_library_as_it_was() {
        let library = Library::check(Loader::standard(crate::standard_path()).unwrap()).unwrap();
        let checked = library.earlier.typed.clone();
        let entry =
            Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/benchmarks-game/n-body/main.fn");
        let (loaded, mut earlier) = library
            .rest(&entry, &crate::test_host(), &Packages::default())
            .unwrap();
        let (program, mut cx) = crate::resolve_after(loaded, &mut earlier).unwrap();
        crate::checked_after(program, &mut cx, &mut earlier).unwrap();
        let whole = &earlier.typed;
        let functions = checked.functions.len();
        assert!(whole.functions.len() > functions);
        assert_eq!(
            format!("{:?}", &whole.functions[..functions]),
            format!("{:?}", checked.functions)
        );
        for (name, data) in &checked.data {
            assert_eq!(format!("{:?}", whole.data[name]), format!("{data:?}"));
        }
        for (member, name) in &checked.members {
            assert_eq!(whole.members[member], *name);
        }
    }

    /// The built-in library checked alone, from its text, as a snapshot.
    fn snapshot() -> Vec<u8> {
        let root = crate::standard::built_in_root();
        Library::check(Loader::standard(&root).unwrap())
            .unwrap()
            .write()
    }

    /// What step one leaves, written and read back, is what was written:
    /// written again, it is the same bytes.
    #[test]
    fn a_snapshot_read_back_is_the_library_written() {
        let written = snapshot();
        assert_eq!(Library::read(&written).unwrap().write(), written);
    }

    /// Every example compiles to the same Barb, or is refused alike,
    /// whether the library is read from a snapshot or checked from its
    /// text.
    #[test]
    fn the_examples_compile_alike_from_a_snapshot_and_from_text() {
        let snapshot = snapshot();
        let examples = Path::new(env!("CARGO_MANIFEST_DIR")).join("examples");
        let mut entries = Vec::new();
        programs(&examples, &mut entries);
        entries.sort();
        let platform = crate::test_platform();
        let compile = |entry: &Path, snapshot: Option<&[u8]>| match crate::check_package_from(
            entry,
            &platform,
            &Packages::default(),
            snapshot,
        ) {
            Ok(crate::Package::Application(barb)) => Ok(Some(barb)),
            Ok(crate::Package::Library) => Ok(None),
            Err(refused) => Err(refused.to_string()),
        };
        let mut built = 0;
        for entry in &entries {
            let from_text = compile(entry, None);
            built += usize::from(matches!(from_text, Ok(Some(_))));
            assert!(
                compile(entry, Some(&snapshot)) == from_text,
                "{} compiles otherwise from the snapshot",
                entry.display()
            );
        }
        assert!(built > 40, "only {built} examples were built");
    }

    /// Every program under `directory` that enters by `main!`.
    fn programs(directory: &Path, found: &mut Vec<std::path::PathBuf>) {
        for entry in std::fs::read_dir(directory).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                programs(&path, found);
            } else if path.extension().is_some_and(|extension| extension == "fn")
                && std::fs::read_to_string(&path)
                    .unwrap()
                    .lines()
                    .any(|line| line.starts_with("main!("))
            {
                found.push(path);
            }
        }
    }
}
