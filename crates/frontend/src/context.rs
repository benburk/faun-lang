//! What every stage after resolution reads and none transforms.
//!
//! A stage takes the program as one tree and answers the next, `fn
//! stage(program, &cx) -> Result<Next, Diagnostic>`. Beside it, the
//! [`Context`] holds what the trees point into: the source text a
//! diagnostic quotes, the spelling of every symbol, which modules are the
//! package and the host, and the standard and host identities literals and
//! the entry are made of. A stage that makes new syntax interns its names
//! and numbers its sites here, so the context only grows.

use crate::ast::Span;
use crate::blessed::PreludeIds;
use crate::diagnostic::{Diagnostic, Location, Refusal};
use crate::hir as h;
use crate::host::HostIds;
use crate::{ModuleId, Source, SourceId, Sources, Symbols};

#[derive(Debug)]
pub struct Context {
    pub sources: Sources,
    pub symbols: Symbols,
    /// The next number for each occurrence a stage writes.
    pub(crate) sites: h::Sites,
    /// Each module's source, by module.
    pub(crate) module_sources: Vec<SourceId>,
    /// The entry's package, whose every definition is compiled, rather than
    /// only what reaches into it.
    pub package: Vec<ModuleId>,
    /// The module mounted at `std.host`, the one place a definition may be
    /// left for the target to answer.
    pub host_module: ModuleId,
    /// The standard identities literals and patterns are made of.
    pub prelude: PreludeIds,
    /// The host's `Host` and `exit!`.
    pub host: HostIds,
}

impl Context {
    /// A diagnostic at `span` in `module`.
    ///
    /// # Panics
    /// If `module` is not one of this program's.
    #[must_use]
    pub fn diagnostic(&self, module: ModuleId, span: Span, message: String) -> Diagnostic {
        Diagnostic::new(message).at(self.source(module), span)
    }

    /// A refusal as a diagnostic, at its places.
    ///
    /// # Panics
    /// If it names a module not one of this program's.
    pub(crate) fn told(&self, refusal: Refusal) -> Diagnostic {
        refusal.told(|module| self.source(module))
    }

    /// Where `span` is in `module`.
    ///
    /// # Panics
    /// If `module` is not one of this program's.
    #[must_use]
    pub fn location(&self, module: ModuleId, span: Span) -> Location {
        Location::of(self.source(module), span)
    }

    pub(crate) fn source(&self, module: ModuleId) -> &Source {
        self.sources
            .get(self.module_sources[module.index()])
            .expect("a resolved module has a source")
    }
}
