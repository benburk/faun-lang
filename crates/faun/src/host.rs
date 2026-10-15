//! Canonical identities for the selected host interface and an entry's `main!`.
//!
//! Host modules are ordinary source modules mounted at `std.host`. This module
//! discovers their identities once so entry validation and lowering do not
//! infer authority or providers from coincidental spellings elsewhere.

use crate::ast::Span;
use crate::check::{CheckedProgram, InferredType};
use crate::diagnostic::Diagnostic;
use crate::hir as h;
use crate::modules::LoadedProgram;
use crate::{ModuleId, Symbol};

/// Source identities required by the initial host ABI.
///
/// `Host` is authority carrying the startup values its target produces, and
/// its bodyless methods are the effects the target answers for.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HostIds {
    pub host: Symbol,
    pub exit: Symbol,
}

impl HostIds {
    /// Find the selected host module's required interface.
    ///
    /// # Errors
    ///
    /// Rejects a host that does not export `Host`, exposes its constructor,
    /// or lacks a bodyless `exit!`.
    pub fn find_in(program: &LoadedProgram) -> Result<Self, Diagnostic> {
        let host_name = symbol(program, "Host")?;
        let selected_host = program.module(program.host);
        let binding = selected_host
            .public
            .types
            .get(&host_name)
            .ok_or_else(|| Diagnostic::new("the selected host module must export `Host`"))?;
        let exposes_constructor = program.modules.iter().any(|module| {
            module.public.types.values().any(|candidate| {
                candidate.canonical == binding.canonical && !candidate.constructors.is_empty()
            })
        });
        if exposes_constructor {
            return Err(Diagnostic::new(
                "the `Host` constructor must not be publicly exposed",
            ));
        }
        let exit_name = symbol(program, "exit!")?;
        let exit = binding.methods.get(&exit_name).copied().ok_or_else(|| {
            Diagnostic::new("the selected host's `Host` must have an `exit!` method")
        })?;
        if has_method_clause(program, program.host, "exit!")? {
            return Err(Diagnostic::new(
                "the selected host must declare `exit!` bodyless",
            ));
        }
        Ok(Self {
            host: binding.canonical,
            exit,
        })
    }

    /// The signature the ABI gives an entry `name`, spelled `spelling`:
    /// `Host -> []`.
    pub(crate) fn entry_signature(&self, span: Span, name: Symbol, spelling: Symbol) -> h::Item {
        h::Item::Signature(h::SignatureDecl {
            span,
            name,
            spelling,
            parameters: vec![h::Type::Named(self.host, Vec::new())],
            result: h::Type::Variants(Vec::new()),
            constraints: Vec::new(),
        })
    }
}

/// Give a `main!` written without a signature the ABI's, `Host -> []`.
///
/// Its `host` is then a `Host` from the start, and what it asks of it is
/// found on `Host`, whatever the entry imports.
pub fn sign_main(resolved: &mut crate::resolve::ResolvedProgram, host: &HostIds, main: &Main) {
    let items = || {
        resolved
            .program
            .modules
            .iter()
            .flat_map(|module| &module.items)
    };
    if items()
        .any(|item| matches!(item, h::Item::Signature(signature) if signature.name == main.symbol))
    {
        return;
    }
    let Some(span) = items().find_map(|item| match item {
        h::Item::Clause(clause) if clause.name == main.symbol => Some(clause.span),
        _ => None,
    }) else {
        return;
    };
    let Some(spelling) = resolved.symbols.find("main!") else {
        return;
    };
    let Some(module) = resolved
        .program
        .modules
        .iter_mut()
        .find(|module| module.source == main.module)
    else {
        return;
    };
    module
        .items
        .push(host.entry_signature(span, main.symbol, spelling));
}

/// Validate the selected host ABI and the application's `main!` signature.
///
/// # Errors
///
/// Rejects host declarations or an entry whose checked type differs from the
/// canonical `Host` and `U8` identities or the structural empty variant type.
pub fn check_application_abi(
    checked: &CheckedProgram,
    host: &HostIds,
    main: &Main,
) -> Result<(), Diagnostic> {
    let resolved = &checked.resolved;
    let functions = &resolved.program.functions;
    let span = functions
        .iter()
        .find(|function| function.name == main.symbol)
        .map_or_else(Span::default, |function| function.span);
    let refused = |message: String| resolved.diagnostic(main.module, span, message);
    // `Host` wraps the record of startup values its target produces.
    let wrapper = resolved
        .program
        .data
        .get(&host.host)
        .and_then(|data| data.wrapper.as_ref());
    if !wrapper.is_some_and(|wrapper| matches!(wrapper.field, h::Type::Record(..))) {
        let message = "the application ABI requires `Host` to wrap a record of startup values";
        return Err(refused(message.to_owned()));
    }
    let named = |name| InferredType::Named(name, Vec::new());
    let required = [
        (
            main.symbol,
            effect(vec![named(host.host)]),
            "main! : Host -> []",
        ),
        (
            host.exit,
            effect(vec![named(host.host), named(checked.prelude.u8_)]),
            "exit! : (Host, U8) -> []",
        ),
    ];
    for (name, expected, written) in required {
        let meets = functions.iter().any(|function| {
            function.name == name
                && function.scheme.variables.is_empty()
                && function.scheme.ty == expected
        });
        if !meets {
            return Err(refused(format!("the application ABI requires `{written}`")));
        }
    }
    Ok(())
}

/// An effect taking `parameters` and answering nothing, `[]`.
fn effect(parameters: Vec<InferredType>) -> InferredType {
    InferredType::Function(
        parameters,
        Box::new(InferredType::Variants(Vec::new(), None)),
    )
}

/// An application's entry point: the `main!` its entry module defines.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Main {
    pub module: ModuleId,
    pub symbol: Symbol,
}

impl Main {
    /// The entry module's `main!`, or `None` when it names none and so is a
    /// library, with nothing to build.
    ///
    /// # Errors
    ///
    /// Rejects a `main!` declared without a clause to run.
    pub fn find_in(program: &LoadedProgram) -> Result<Option<Self>, Diagnostic> {
        let module = program.module(program.entry);
        let Some(symbol) = program
            .symbols
            .find("main!")
            .and_then(|name| module.scope.values.get(&name).copied())
        else {
            return Ok(None);
        };
        let source = program
            .sources
            .get(module.source)
            .ok_or_else(|| Diagnostic::new("the entry module has no loaded source"))?
            .text();
        let defines_main = module.syntax.items.iter().any(|item| {
            matches!(item, crate::ast::Item::Clause(clause) if clause.name.text(source) == "main!")
        });
        if !defines_main {
            return Err(Diagnostic::new("the entry module must define `main!`")
                .help("write `main! : Host -> []` and a clause `main!(host) -> ...`"));
        }
        Ok(Some(Self {
            module: program.entry,
            symbol,
        }))
    }
}

/// Whether any type the host module declares gives a method `name` a body.
fn has_method_clause(
    program: &LoadedProgram,
    module: ModuleId,
    name: &str,
) -> Result<bool, Diagnostic> {
    let module = program.module(module);
    let source = program
        .sources
        .get(module.source)
        .ok_or_else(|| Diagnostic::new("the selected host module has no loaded source"))?
        .text();
    Ok(module.syntax.items.iter().any(|item| {
        matches!(item, crate::ast::Item::Data(data) if data.methods.iter().any(|method| {
            matches!(method, crate::ast::MethodItem::Clause(clause)
                if clause.name.text(source) == name)
        }))
    }))
}

fn symbol(program: &LoadedProgram, name: &str) -> Result<Symbol, Diagnostic> {
    program
        .symbols
        .find(name)
        .ok_or_else(|| Diagnostic::new(format!("host name `{name}` was never declared")))
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

        fn load(&self, host: &str, entry: &str) -> LoadedProgram {
            let host = self.write("host.fn", host);
            let entry = self.write("main.fn", entry);
            let standard = crate::standard_path();
            modules::load_program(&entry, standard, &host).unwrap()
        }
    }

    impl Drop for Fixture {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    const ENTRY: &str =
        "import std.host {Host}\nmain! : Host -> []\nmain!(host) -> host.exit!(host.argc)\n";
    const HOST: &str = "export {Host}\nHost : {argc: Nat}.(\n  exit! : (Host, Nat) -> []\n)\n";

    #[test]
    fn application_entry_requires_a_clause() {
        let fixture = Fixture::new();
        let loaded = fixture.load(HOST, "import std.host {Host}\nmain! : Host -> []\n");
        let failure = Main::find_in(&loaded).unwrap_err();
        assert!(failure.message.contains("define `main!`"));
    }

    #[test]
    fn an_entry_without_main_is_a_library() {
        let fixture = Fixture::new();
        let loaded = fixture.load(HOST, "double : Nat -> Nat\ndouble(n) -> n + n\n");
        assert_eq!(Main::find_in(&loaded).unwrap(), None);
        HostIds::find_in(&loaded).unwrap();
    }

    #[test]
    fn host_authority_cannot_be_constructed_or_implemented_by_source() {
        let fixture = Fixture::new();
        let exported = HostIds::find_in(&fixture.load(
            "export {Host.*}\nHost : {argc: Nat}.(\n  exit! : (Host, Nat) -> []\n)\n",
            ENTRY,
        ))
        .unwrap_err();
        assert!(exported.message.contains("must not be publicly exposed"));

        let bodyful = HostIds::find_in(&fixture.load(
                "export {Host}\nHost : {argc: Nat}.(\n  exit! : (Host, Nat) -> []\n  exit!(host, code) -> host.exit!(code)\n)\n",
                ENTRY,
            ))
            .unwrap_err();
        assert!(bodyful.message.contains("bodyless"));
    }
}
