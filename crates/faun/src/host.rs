//! Canonical identities for an application's entry and selected host interface.
//!
//! Host modules are ordinary source modules mounted at `std.host`. This module
//! discovers their identities once so entry validation and lowering do not
//! infer authority or providers from coincidental spellings elsewhere.

use std::fmt;

use crate::Symbol;
use crate::blessed::PreludeIds;
use crate::modules::LoadedProgram;

/// Source identities required by the initial host ABI.
///
/// `Host` is authority and carries no startup payload: startup values are
/// ordinary bodyless routines taking it, so nothing here names one.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HostIds {
    pub entry_module: crate::ModuleId,
    pub main: Symbol,
    pub host: Symbol,
    pub exit: Symbol,
    /// The prelude's `Nat`, which `exit!`'s status is written at.
    pub nat: Symbol,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HostError {
    pub message: String,
}

impl fmt::Display for HostError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for HostError {}

impl HostIds {
    /// Resolve the entry and selected host module's required interface.
    ///
    /// # Errors
    ///
    /// Rejects library loads, multiple application entries, malformed host
    /// interfaces, and entries without a bodyful `main!`.
    #[allow(clippy::too_many_lines)]
    pub fn resolve(program: &LoadedProgram, prelude: &PreludeIds) -> Result<Self, HostError> {
        let [entry] = program.entries.as_slice() else {
            return Err(error("an application must have exactly one entry module"));
        };
        let host_module = program
            .host
            .ok_or_else(|| error("an application requires a selected `std.host` module"))?;
        let entry_module = program.module(*entry);
        let entry_source = program
            .sources
            .get(entry_module.source)
            .ok_or_else(|| error("the entry module has no loaded source"))?
            .text();
        let defines_main = entry_module.syntax.items.iter().any(|item| {
            matches!(item, crate::ast::Item::Clause(clause) if clause.name.text(entry_source) == "main!")
        });
        if !defines_main {
            return Err(error("the entry module must define `main!`"));
        }
        let main_name = symbol(program, "main!")?;
        let main = entry_module
            .scope
            .values
            .get(&main_name)
            .copied()
            .ok_or_else(|| error("the entry module must define `main!`"))?;

        let host_name = symbol(program, "Host")?;
        let selected_host = program.module(host_module);
        let binding = selected_host
            .public
            .types
            .get(&host_name)
            .ok_or_else(|| error("the selected host module must export `Host`"))?;
        let exposes_constructor = program.modules.iter().any(|module| {
            module.public.types.values().any(|candidate| {
                candidate.canonical == binding.canonical && !candidate.constructors.is_empty()
            })
        });
        if exposes_constructor {
            return Err(error("the `Host` constructor must not be publicly exposed"));
        }
        let exit_name = symbol(program, "exit!")?;
        let exit = selected_host
            .public
            .values
            .get(&exit_name)
            .copied()
            .ok_or_else(|| error("the selected host module must export `exit!`"))?;
        if has_clause(program, exit)? {
            return Err(error(
                "the selected host module must declare bodyless `exit!`",
            ));
        }

        Ok(Self {
            entry_module: *entry,
            main,
            host: binding.canonical,
            exit,
            nat: prelude.nat,
        })
    }
}

fn has_clause(program: &LoadedProgram, canonical: Symbol) -> Result<bool, HostError> {
    for module in &program.modules {
        let source = program
            .sources
            .get(module.source)
            .ok_or_else(|| error("a loaded host dependency has no source"))?
            .text();
        for item in &module.syntax.items {
            let crate::ast::Item::Clause(clause) = item else {
                continue;
            };
            let Some(local) = program.symbols.find(clause.name.text(source)) else {
                continue;
            };
            if module.scope.values.get(&local) == Some(&canonical) {
                return Ok(true);
            }
        }
    }
    Ok(false)
}

fn symbol(program: &LoadedProgram, name: &str) -> Result<Symbol, HostError> {
    program
        .symbols
        .find(name)
        .ok_or_else(|| error(format!("host name `{name}` was never declared")))
}

fn error(message: impl Into<String>) -> HostError {
    HostError {
        message: message.into(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::modules;
    use std::fs;
    use std::path::PathBuf;
    use std::time::{SystemTime, UNIX_EPOCH};

    struct Fixture(PathBuf);

    impl Fixture {
        fn new() -> Self {
            let unique = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos();
            let root = std::env::temp_dir().join(format!("faun-host-{unique}"));
            fs::create_dir_all(&root).unwrap();
            Self(root)
        }

        fn write(&self, name: &str, source: &str) -> PathBuf {
            let path = self.0.join(name);
            fs::write(&path, source).unwrap();
            path
        }

        fn resolve(&self, host: &str, entry: &str) -> Result<HostIds, HostError> {
            let host = self.write("host.fn", host);
            let entry = self.write("main.fn", entry);
            let standard = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("standard/standard.fn");
            let loaded = modules::load_with_host(&[entry], Some(&standard), Some(&host)).unwrap();
            let prelude = PreludeIds::resolve(&loaded).unwrap();
            HostIds::resolve(&loaded, &prelude)
        }
    }

    impl Drop for Fixture {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    const ENTRY: &str =
        "import std.host {Host exit!}\nmain! : Host -> []\nmain!(host) -> exit!(host host.argc)\n";
    const HOST: &str = "exports {Host exit!}\nHost : {argc: Nat}\nexit! : Host Nat -> []\n";

    #[test]
    fn application_entry_requires_a_clause() {
        let fixture = Fixture::new();
        let failure = fixture
            .resolve(HOST, "import std.host {Host}\nmain! : Host -> []\n")
            .unwrap_err();
        assert!(failure.message.contains("define `main!`"));
    }

    #[test]
    fn host_authority_cannot_be_constructed_or_implemented_by_source() {
        let fixture = Fixture::new();
        let exported = fixture
            .resolve(
                "exports {Host.* exit!}\nHost : {argc: Nat}\nexit! : Host Nat -> []\n",
                ENTRY,
            )
            .unwrap_err();
        assert!(exported.message.contains("must not be publicly exposed"));

        let bodyful = fixture
            .resolve(
                "exports {Host exit!}\nHost : {argc: Nat}\nexit! : Host Nat -> []\nexit!(host code) -> exit!(host code)\n",
                ENTRY,
            )
            .unwrap_err();
        assert!(bodyful.message.contains("bodyless"));
    }
}
