//! Package-rooted loading, public interfaces, and canonical declarations.
//!
//! Files remain separate parsed modules. Linking builds compact symbol tables;
//! it does not concatenate or rewrite source ASTs. This keeps source spans
//! local and lets resolution consume one immutable module at a time.

// Loading and interface construction keep their coordinated state transitions
// visible instead of scattering them among tiny mutation helpers.
#![allow(clippy::too_many_lines, clippy::useless_let_if_seq)]

use rustc_hash::FxHashMap as HashMap;
use std::fs;
use std::path::{Path, PathBuf};

use super::ast::{
    AliasDecl, ConstraintAliasDecl, DataDecl, DataRepresentation, Dependency, Export, HeaderDecl,
    HeaderValue, Item, MethodItem, Module, Name, Span,
};
use super::diagnostic::Diagnostic;
use super::packages::{PackageUrl, Packages};
use super::{ParseError, Source, SourceId, Sources, Symbol, Symbols, parse_in};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ModuleId(u32);

impl ModuleId {
    #[must_use]
    pub(crate) fn index(self) -> usize {
        usize::try_from(self.0).expect("u32 fits usize")
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypeBinding {
    pub canonical: Symbol,
    pub constructors: HashMap<Symbol, Symbol>,
    /// A sum's constructors in the order declared, each with how many
    /// fields it carries: what its name stands for as a constructor of its
    /// own. Empty for anything but a sum, and wherever its constructors are
    /// not visible.
    pub variants: Vec<(Symbol, usize)>,
    pub methods: HashMap<Symbol, Symbol>,
    /// Whether the name is a transparent alias, which owns nothing.
    pub alias: bool,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Interface {
    pub values: HashMap<Symbol, Symbol>,
    pub types: HashMap<Symbol, TypeBinding>,
    /// Each visible constructor word and every declared constructor it may
    /// name. Types are each their own constructor namespace, so a word may
    /// have several claimants; which one a use means is its position's to
    /// decide, when it is checked.
    pub constructors: HashMap<Symbol, Vec<Symbol>>,
}

impl Interface {
    /// Take in what `other` binds, refusing a name it binds to something
    /// this already binds it to.
    pub(crate) fn merge(&mut self, other: &Self) -> Result<(), Clash> {
        merge_map(&mut self.values, &other.values, "value")?;
        for (&word, claimants) in &other.constructors {
            for &canonical in claimants {
                claim(&mut self.constructors, word, canonical);
            }
        }
        for (&local, binding) in &other.types {
            if let Some(previous) = self.types.get(&local)
                && previous.canonical != binding.canonical
            {
                return Err(Clash {
                    kind: "type",
                    name: local,
                });
            }
            self.types.insert(local, binding.clone());
        }
        Ok(())
    }
}

/// A name two interfaces bind to different things.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Clash {
    /// `type` or `value`.
    pub kind: &'static str,
    pub name: Symbol,
}

#[derive(Clone, Debug)]
pub struct LoadedModule {
    pub id: ModuleId,
    pub path: PathBuf,
    pub source: SourceId,
    pub syntax: Module,
    pub namespace: Symbol,
    pub scope: Interface,
    pub public: Interface,
}

/// A linked set of source modules. `symbols` owns every identity in interfaces
/// and later resolved HIR.
#[derive(Clone, Debug)]
pub struct LoadedProgram {
    pub sources: Sources,
    pub symbols: Symbols,
    pub modules: Vec<LoadedModule>,
    pub entry: ModuleId,
    /// The entry's package: the entry and every module it imports by path,
    /// as opposed to the standard library and host, which it depends on.
    pub package: Vec<ModuleId>,
    pub prelude: ModuleId,
    /// The target-selected module mounted at `std.host`.
    pub host: ModuleId,
    /// The root modules of the packages the entry's package imports, each
    /// with whether its header names it in `test_uses`.
    pub dependencies: Vec<(ModuleId, bool)>,
}

impl LoadedProgram {
    #[must_use]
    pub fn module(&self, id: ModuleId) -> &LoadedModule {
        &self.modules[id.index()]
    }

    /// Its modules, as what is loaded so far is seen.
    pub(crate) fn view(&self) -> Modules<'_> {
        Modules {
            sources: &self.sources,
            symbols: &self.symbols,
            modules: &self.modules,
            prelude: self.prelude,
        }
    }
}

/// The modules loaded so far, and what their syntax and interfaces point
/// into: a whole program, or the standard package alone.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Modules<'a> {
    pub sources: &'a Sources,
    pub symbols: &'a Symbols,
    /// Each module, by identity.
    #[expect(
        clippy::struct_field_names,
        reason = "the modules loaded are what it is"
    )]
    pub modules: &'a [LoadedModule],
    /// The standard package's root module.
    pub prelude: ModuleId,
}

impl Modules<'_> {
    pub(crate) fn module(&self, id: ModuleId) -> &LoadedModule {
        &self.modules[id.index()]
    }
}

/// Load an entry file with the standard library at `prelude`, whose exports
/// every module sees, and the target-selected module at `host` mounted as
/// `std.host`.
///
/// Imports are rooted at the importing package directory. Each path component
/// maps to a directory and the final module is either `path.fn` or
/// `path/name.fn`; finding both is an error. The host is loaded as an
/// ordinary module, but its public interface is reached through the stable
/// virtual path `std.host` rather than its disk location.
///
/// A package's root module may name the packages it depends on in its header,
/// `package {uses: {md5: "../md5/src/md5"}}`, each a module base relative to
/// the header's file, and those only its expectations need in `test_uses`.
/// Every module of the package may then `import md5`, which is that
/// package's root, and not its inner modules, which are its own. A
/// dependency's modules resolve their imports from its root, with its own
/// header's dependencies. Only a root module has a header, and its `faun`
/// field names the language version it is written for, which may not be
/// newer than this compiler's. The entry's package is the modules loaded
/// from the entry's root, not its dependencies'.
///
/// # Errors
///
/// Reports I/O, parse, cycle, duplicate declaration, visibility, ambiguous
/// module-path, and conflicting or missing host import failures.
pub fn load_program(
    entry: &Path,
    prelude: &Path,
    host: &Path,
) -> Result<LoadedProgram, Diagnostic> {
    load_program_using(entry, prelude, host, &Packages::default())
}

/// [`load_program`], reading each URL dependency from where `packages`
/// says.
///
/// # Errors
///
/// Reports what [`load_program`] does, and a URL dependency `packages`
/// does not hold.
pub fn load_program_using(
    entry: &Path,
    prelude: &Path,
    host: &Path,
    packages: &Packages,
) -> Result<LoadedProgram, Diagnostic> {
    Loader::standard(prelude)?.rest(entry, host, packages)
}

/// Where a package's modules resolve their imports from: its root module's
/// directory, the packages its header depends on, by the name each is
/// imported as, and which package it is.
#[derive(Clone, Debug)]
struct Root {
    directory: PathBuf,
    /// Each dependency's root module, and whether it is in `test_uses`.
    dependencies: HashMap<String, (PathBuf, bool)>,
    package: usize,
}

/// A module being loaded: a package's root, whose header may name its
/// dependencies, or one of the modules within `Root`'s package.
enum Loading<'a> {
    Package(Root),
    Within(&'a Root),
}

/// Loading under way: the standard package first, alone, and then the
/// host and the entry's package, on from where it stopped.
#[derive(Debug, Default)]
pub(crate) struct Loader {
    pub(crate) sources: Sources,
    pub(crate) symbols: Symbols,
    /// Every module loaded so far, by its identity.
    pending: Vec<LoadedModule>,
    /// Which package each module belongs to; see [`Root`].
    packages_of: Vec<usize>,
    loaded: HashMap<PathBuf, ModuleId>,
    visiting: Vec<PathBuf>,
    /// The prelude's exports, once it has loaded; its own modules see none.
    prelude: Option<Interface>,
    /// The host module, once it has loaded; it cannot import itself.
    host: Option<ModuleId>,
    standard_root: Option<PathBuf>,
    /// How many packages have been given a root.
    packages: usize,
    /// Which package each URL dependency is read from.
    fetched: Packages,
    /// The standard package's root module, once it has loaded, and the
    /// path it was loaded by, which the host's package is rooted beside.
    standard: Option<(ModuleId, PathBuf)>,
    /// Each package's imported dependencies: the package, the dependency's
    /// root module, and whether it is in `test_uses`.
    imported: Vec<(usize, ModuleId, bool)>,
}

impl Loader {
    /// The standard package, rooted at `prelude`, loaded alone: whatever
    /// is loaded after it sees its exports.
    ///
    /// # Errors
    /// Reports what loading any module does.
    pub(crate) fn standard(prelude: &Path) -> Result<Self, Diagnostic> {
        let mut loader = Self::default();
        let root = loader.package_at(prelude);
        let id = loader.load_module(prelude, Loading::Package(root), true)?;
        loader.prelude = Some(loader.pending[id.index()].public.clone());
        loader.standard = Some((id, prelude.to_path_buf()));
        Ok(loader)
    }

    /// The modules loaded so far.
    pub(crate) fn view(&self) -> Modules<'_> {
        Modules {
            sources: &self.sources,
            symbols: &self.symbols,
            modules: &self.pending,
            prelude: self.prelude(),
        }
    }

    /// The modules loaded so far, the sources they are read from, and the
    /// symbols they and whatever names them intern.
    pub(crate) fn parts(&mut self) -> (&[LoadedModule], &Sources, &mut Symbols) {
        (&self.pending, &self.sources, &mut self.symbols)
    }

    /// Drop the syntax of every module loaded so far, once it is checked:
    /// what is loaded after reads only their interfaces.
    pub(crate) fn forget_syntax(&mut self) {
        for module in &mut self.pending {
            module.syntax.items = Vec::new();
        }
    }

    /// The standard package's root module.
    pub(crate) const fn prelude(&self) -> ModuleId {
        self.standard
            .as_ref()
            .expect("the standard package loads first")
            .0
    }

    /// Whether the module at `path` is already loaded, as one of the
    /// standard package's is once it has.
    pub(crate) fn holds(&self, path: &Path) -> bool {
        crate::standard::built_in(path).map_or_else(
            || {
                path.canonicalize()
                    .is_ok_and(|path| self.loaded.contains_key(&path))
            },
            |_| self.loaded.contains_key(path),
        )
    }

    /// Go on to load the target's `host`, mounted as `std.host`, and the
    /// package at `entry`, reading each URL dependency from where
    /// `packages` says.
    ///
    /// # Errors
    /// Reports what loading any module does.
    pub(crate) fn rest(
        mut self,
        entry: &Path,
        host: &Path,
        packages: &Packages,
    ) -> Result<LoadedProgram, Diagnostic> {
        self.fetched = packages.clone();
        let (prelude, written) = self
            .standard
            .clone()
            .expect("the standard package loads first");
        let root = self.package_at(&written);
        let host_id = self.load_module(host, Loading::Package(root), false)?;
        self.host = Some(host_id);
        // The standard library as the entry is its own package.
        let root = self.package_at(entry);
        let entry_id = self.load_module(entry, Loading::Package(root), false)?;
        Ok(self.into_loaded_program(entry_id, prelude, host_id))
    }

    /// A new package rooted where the module at `path` is.
    fn package_at(&mut self, path: &Path) -> Root {
        self.packages += 1;
        Root {
            directory: path
                .parent()
                .unwrap_or_else(|| Path::new("."))
                .to_path_buf(),
            dependencies: HashMap::default(),
            package: self.packages,
        }
    }

    fn into_loaded_program(
        self,
        entry: ModuleId,
        prelude: ModuleId,
        host: ModuleId,
    ) -> LoadedProgram {
        let own = self.packages_of[entry.index()];
        let mut dependencies: Vec<(ModuleId, bool)> = self
            .imported
            .iter()
            .filter(|&&(package, ..)| package == own)
            .map(|&(_, module, test)| (module, test))
            .collect();
        dependencies.sort_unstable();
        dependencies.dedup();
        let package = self
            .pending
            .iter()
            .zip(&self.packages_of)
            .filter(|&(_, &package)| package == own)
            .map(|(module, _)| module.id)
            .collect();
        LoadedProgram {
            sources: self.sources,
            symbols: self.symbols,
            modules: self.pending,
            entry,
            package,
            prelude,
            host,
            dependencies,
        }
    }

    fn load_module(
        &mut self,
        written: &Path,
        loading: Loading<'_>,
        standard_root: bool,
    ) -> Result<ModuleId, Diagnostic> {
        // A built-in module's name is already the one it is known by.
        let built_in = crate::standard::built_in(written);
        let path = match built_in {
            Some(_) => written.to_path_buf(),
            None => written.canonicalize().map_err(|error| {
                Diagnostic::new(format!("cannot read `{}`: {error}", written.display()))
            })?,
        };
        if let Some(&id) = self.loaded.get(&path) {
            return Ok(id);
        }
        if self.visiting.contains(&path) {
            return Err(Diagnostic::new(format!(
                "import cycle through `{}`",
                path.display()
            )));
        }
        if standard_root {
            self.standard_root = path.parent().map(Path::to_path_buf);
        }
        let text = match built_in {
            Some(text) => text.to_owned(),
            // Only a file is a module: a device or a pipe may never end.
            None if !path.is_file() => {
                return Err(Diagnostic::new(format!(
                    "cannot read `{}`: not a file",
                    path.display()
                )));
            }
            None => fs::read_to_string(&path).map_err(|error| {
                Diagnostic::new(format!("cannot read `{}`: {error}", path.display()))
            })?,
        };
        let name = self.shown(&path);
        let source = self.sources.add(name, text.clone());
        let syntax = parse_in(&text, source).map_err(|error| {
            let text = self.sources.get(source).expect("the source just added");
            let told = |error: &ParseError| {
                Diagnostic::new(error.message.clone())
                    .at(text, Span::new(error.offset, error.end))
                    .advised((*error.advice).clone())
            };
            let mut diagnostic = told(&error);
            diagnostic.also = error.also.iter().map(told).collect();
            diagnostic
        })?;
        let file = self
            .sources
            .get(source)
            .expect("the source just added")
            .clone();
        let root = self.root(loading, &syntax, &path, source)?;
        let id =
            ModuleId(u32::try_from(self.pending.len()).expect("fewer than 2^32 loaded modules"));
        let namespace_text = self.namespace(&path, id);
        let namespace = self.symbols.intern(&namespace_text);
        let own = declarations(&syntax, &file, namespace, &mut self.symbols)?;

        // Reserve the slot before descending so module IDs remain stable and a
        // cycle can name the module being visited.
        self.pending.push(LoadedModule {
            id,
            path: path.clone(),
            source,
            syntax,
            namespace,
            scope: Interface::default(),
            public: Interface::default(),
        });
        self.packages_of.push(root.package);
        self.visiting.push(path.clone());

        let imports: Vec<(usize, Span, Vec<String>)> = self.pending[id.index()]
            .syntax
            .items
            .iter()
            .enumerate()
            .filter_map(|(index, item)| match item {
                Item::Import(import) => Some((
                    index,
                    import.span,
                    import
                        .path
                        .iter()
                        .map(|part| part.text(&text).to_string())
                        .collect(),
                )),
                _ => None,
            })
            .collect();
        let mut linked_imports = Vec::with_capacity(imports.len());
        for (index, span, path_parts) in imports {
            let dependency = if path_parts == ["std", "host"] {
                self.host.ok_or_else(|| {
                    Diagnostic::new("the host module cannot import `std.host`, which is itself")
                        .at(&file, span)
                })?
            } else if let Some((dependency, for_tests)) = root.dependencies.get(&path_parts[0]) {
                if path_parts.len() > 1 {
                    let package = &path_parts[0];
                    let message = format!(
                        "`{}` is inside the package `{package}`",
                        path_parts.join(".")
                    );
                    return Err(Diagnostic::new(message)
                        .at(&file, span)
                        .note("a package this one depends on keeps its modules its own")
                        .help(format!("import `{package}` itself")));
                }
                let (dependency, for_tests) = (dependency.clone(), *for_tests);
                let package = self.package_at(&dependency);
                let module = self.load_module(&dependency, Loading::Package(package), false)?;
                self.imported.push((root.package, module, for_tests));
                module
            } else {
                let module = module_path(&root.directory, &path_parts).map_err(|diagnostic| {
                    if diagnostic.location().is_some() {
                        diagnostic
                    } else {
                        diagnostic.at(&file, span)
                    }
                })?;
                self.load_module(&module, Loading::Within(&root), false)?
            };
            linked_imports.push((index, dependency));
        }
        self.visiting.pop();

        let mut scope = self.prelude.clone().unwrap_or_default();
        for &(item_index, dependency) in &linked_imports {
            let Item::Import(import) = &self.pending[id.index()].syntax.items[item_index] else {
                unreachable!("recorded imports remain imports")
            };
            let face = self.pending[dependency.index()].public.clone();
            expose_import(&mut scope, &face, import, &file, &mut self.symbols)?;
        }
        scope
            .merge(&own)
            .map_err(|clash| self.clash(clash, &file, &self.pending[id.index()].syntax))?;
        let public = exports(
            &self.pending[id.index()].syntax,
            &file,
            &scope,
            &mut self.symbols,
        )?;

        let module = &mut self.pending[id.index()];
        module.scope = scope;
        module.public = public;
        self.loaded.insert(path, id);
        Ok(id)
    }

    /// A module declaring a name its scope already has from the prelude or
    /// an import, told at the declaration.
    fn clash(&self, clash: Clash, file: &Source, syntax: &Module) -> Diagnostic {
        let name = self.symbols.text(clash.name);
        let kind = clash.kind;
        let source = file.text();
        let declared = syntax.items.iter().find_map(|item| {
            let declared = match (kind, item) {
                ("type", Item::Data(data)) => data.name,
                (
                    "type",
                    Item::Alias(AliasDecl { name, .. })
                    | Item::Constraints(ConstraintAliasDecl { name, .. }),
                ) => *name,
                ("value", Item::Signature(signature)) => signature.name,
                ("value", Item::Clause(clause)) => clause.name,
                _ => return None,
            };
            (declared.text(source) == name).then_some(declared.0)
        });
        // Where it is imported, the last part of the module it is imported
        // from, and whether its constructors come with it.
        let imported = syntax.items.iter().find_map(|item| match item {
            Item::Import(import) => {
                let exposure = import
                    .exposures
                    .iter()
                    .find(|exposure| exposure.local.text(source) == name)?;
                let module = import.path.last().map_or("other", |part| part.text(source));
                Some((exposure.local.0, module, exposure.constructors))
            }
            _ => None,
        });
        let diagnostic = match imported {
            Some(_) => Diagnostic::new(format!("{kind} `{name}` is both imported and declared")),
            None => Diagnostic::new(format!("the prelude already has a {kind} `{name}`")),
        };
        let Some(declared) = declared else {
            return diagnostic;
        };
        let diagnostic = diagnostic.at(file, declared).label("declared here");
        match imported {
            Some((imported, module, constructors)) => {
                // A renamed name keeps its case, so a value's new name is
                // lowercase and a type's capitalised: `helpers_double`, and
                // `ShapesShape`, each led by the module it comes from.
                let renamed = if kind == "value" {
                    format!("{module}_{name}")
                } else {
                    format!("{}{name}", capitalised_words(module))
                };
                let constructors = if constructors { ".*" } else { "" };
                diagnostic
                    .secondary(file, imported, "imported here")
                    .help(format!(
                        "import it under another name, as `{{{name}{constructors}: {renamed}}}`"
                    ))
            }
            None => diagnostic
                .note("every module sees the prelude's types and values")
                .help("name it something else"),
        }
    }

    /// The root a module resolves its imports from: its package's, with the
    /// dependencies its header names where it is the package's root.
    fn root(
        &self,
        loading: Loading<'_>,
        syntax: &Module,
        path: &Path,
        source: SourceId,
    ) -> Result<Root, Diagnostic> {
        let header = syntax.items.iter().find_map(|item| match item {
            Item::Header(header) => Some(header),
            _ => None,
        });
        let text = self.sources.get(source).expect("the source just added");
        match (loading, header) {
            (Loading::Within(root), None) => Ok(root.clone()),
            (Loading::Package(root), None) => Ok(root),
            (Loading::Within(_), Some(header)) => Err(Diagnostic::new(
                "only a package's root module has a `package` header",
            )
            .at(text, header.span)
            .label("this module is inside its package")),
            (Loading::Package(mut root), Some(header)) => {
                let directory = path.parent().unwrap_or_else(|| Path::new("."));
                for (dependency, for_tests) in header_fields(header, text)? {
                    let name = dependency.name.text(text.text()).to_owned();
                    let written = decoded(&dependency.path, text)
                        .map_err(|message| Diagnostic::new(message).at(text, dependency.span))?;
                    let module = if url_scheme(&written).is_some() {
                        PackageUrl::parse(&written).map_err(|message| {
                            Diagnostic::new(format!("dependency `{name}` {message}"))
                                .at(text, dependency.span)
                        })?;
                        self.fetched
                            .root(&written)
                            .ok_or_else(|| {
                                Diagnostic::new(format!("dependency `{name}` is not fetched"))
                                    .at(text, dependency.span)
                                    .help("fetch it with `faun fetch`, or build with the `faun` command, which fetches")
                            })?
                            .to_path_buf()
                    } else {
                        module_base(directory, &directory.join(&written)).map_err(|error| {
                            Diagnostic::new(format!("dependency `{name}` {}", error.message))
                                .at(text, dependency.span)
                        })?
                    };
                    if root
                        .dependencies
                        .insert(name.clone(), (module, for_tests))
                        .is_some()
                    {
                        return Err(Diagnostic::new(format!(
                            "the package depends on `{name}` more than once"
                        ))
                        .at(text, dependency.span));
                    }
                }
                Ok(root)
            }
        }
    }

    /// How a diagnostic names the module at `path`: the standard library's
    /// as `std/`, wherever it is installed, as it is imported; any other by
    /// where it is.
    fn shown(&self, path: &Path) -> PathBuf {
        if let Some(root) = &self.standard_root
            && let Ok(relative) = path.strip_prefix(root)
        {
            return Path::new("std").join(relative);
        }
        path.to_path_buf()
    }

    fn namespace(&self, path: &Path, id: ModuleId) -> String {
        if let Some(root) = &self.standard_root
            && let Ok(relative) = path.strip_prefix(root)
        {
            let mut name = relative
                .with_extension("")
                .to_string_lossy()
                .replace(['/', '\\', '-'], "_");
            if name == "standard" {
                name = "root".to_string();
            }
            return format!("Mstd_{name}");
        }
        format!("M{}", id.0)
    }
}

/// The language version this compiler reads, `MAJOR.MINOR`: its own.
fn language_version() -> (u64, u64) {
    let part = |text: &str| {
        text.parse()
            .expect("Cargo writes a version's parts as numbers")
    };
    (
        part(env!("CARGO_PKG_VERSION_MAJOR")),
        part(env!("CARGO_PKG_VERSION_MINOR")),
    )
}

/// A header's dependencies, each with whether it is in `test_uses`, once
/// its fields are each known and written once, and its `faun` version is
/// one this compiler reads.
pub(crate) fn header_fields<'a>(
    header: &'a HeaderDecl,
    file: &Source,
) -> Result<Vec<(&'a Dependency, bool)>, Diagnostic> {
    let text = file.text();
    let mut seen = Vec::new();
    let mut dependencies = Vec::new();
    for field in &header.fields {
        let name = field.name.text(text);
        if seen.contains(&name) {
            return Err(
                Diagnostic::new(format!("the header names `{name}` more than once"))
                    .at(file, field.span),
            );
        }
        seen.push(name);
        match (name, &field.value) {
            ("faun", HeaderValue::Text(written)) => {
                let written = decoded(written, file)
                    .map_err(|message| Diagnostic::new(message).at(file, field.span))?;
                let wanted = written
                    .split_once('.')
                    .and_then(|(major, minor)| {
                        let number = |part: &str| {
                            (!part.is_empty() && part.bytes().all(|byte| byte.is_ascii_digit()))
                                .then(|| part.parse::<u64>().ok())
                                .flatten()
                        };
                        Some((number(major)?, number(minor)?))
                    })
                    .ok_or_else(|| {
                        Diagnostic::new(format!("`{written}` is not a language version"))
                            .at(file, field.span)
                            .help("write a version as `MAJOR.MINOR`, as `faun: \"0.1\"`")
                    })?;
                let (major, minor) = language_version();
                if wanted > (major, minor) {
                    return Err(Diagnostic::new(format!(
                        "the package is written for Faun {written}, newer than this compiler's {major}.{minor}"
                    ))
                    .at(file, field.span)
                    .help(format!("build it with a compiler for Faun {written} or later")));
                }
            }
            ("uses" | "test_uses", HeaderValue::Packages(packages)) => {
                let for_tests = name == "test_uses";
                dependencies.extend(packages.iter().map(|dependency| (dependency, for_tests)));
            }
            ("faun", HeaderValue::Packages(_)) => {
                return Err(
                    Diagnostic::new("`faun` is a language version, not packages")
                        .at(file, field.span)
                        .help("write it as a string, as `faun: \"0.1\"`"),
                );
            }
            ("uses" | "test_uses", HeaderValue::Text(_)) => {
                return Err(Diagnostic::new(format!("`{name}` holds packages, not a string"))
                    .at(file, field.span)
                    .help(format!(
                        "name each package and its path, as `{name}: {{md5: \"../md5/src/md5\"}}`"
                    )));
            }
            _ => {
                return Err(Diagnostic::new(format!("a header has no field `{name}`"))
                    .at(file, field.span)
                    .note("a header's fields are `faun`, `uses` and `test_uses`"));
            }
        }
    }
    Ok(dependencies)
}

/// A string's text, its escapes decoded.
pub(crate) fn decoded(parts: &[Span], file: &Source) -> Result<String, String> {
    parts
        .iter()
        .map(|part| {
            crate::literal::decode_text(part.text(file.text())).map(std::borrow::Cow::into_owned)
        })
        .collect()
}

fn module_path(root: &Path, parts: &[String]) -> Result<PathBuf, Diagnostic> {
    if parts.is_empty() {
        return Err(Diagnostic::new("an import names no module"));
    }
    let joined = parts
        .iter()
        .fold(root.to_path_buf(), |path, part| path.join(part));
    module_base(root, &joined)
        .map_err(|error| Diagnostic::new(format!("import `{}` {}", parts.join("."), error.message)))
}

/// The scheme of `written` where it is a URL, as `https` of
/// `https://example.com/foo`: letters, then letters, digits, `+`, `-` or
/// `.`, before `://`.
pub(crate) fn url_scheme(written: &str) -> Option<&str> {
    let (scheme, _) = written.split_once("://")?;
    let mut characters = scheme.chars();
    let first = characters.next()?;
    let rest_fits = characters.all(|c| c.is_ascii_alphanumeric() || matches!(c, '+' | '-' | '.'));
    (first.is_ascii_alphabetic() && rest_fits).then_some(scheme)
}

/// The module at the base `joined`: `joined.fn`, or `name.fn` in the
/// directory `joined`, where `name` is its last part, and not both. Where
/// neither or both are there, they are named from `from`, the directory
/// the base was written relative to.
pub(crate) fn module_base(from: &Path, joined: &Path) -> Result<PathBuf, Diagnostic> {
    let flat = joined.with_extension("fn");
    let nested = joined
        .join(joined.file_name().unwrap_or_default())
        .with_extension("fn");
    let shown = |path: &Path| {
        let relative = path.strip_prefix(from).unwrap_or(path);
        format!("`{}`", relative.display())
    };
    match (
        crate::standard::is_module(&flat),
        crate::standard::is_module(&nested),
    ) {
        (true, false) => Ok(flat),
        (false, true) => Ok(nested),
        (true, true) => Err(Diagnostic::new(format!(
            "is ambiguous between {} and {}",
            shown(&flat),
            shown(&nested)
        ))),
        (false, false) => Err(Diagnostic::new(format!(
            "finds neither {} nor {}",
            shown(&flat),
            shown(&nested)
        ))),
    }
}

fn declarations(
    module: &Module,
    file: &Source,
    namespace: Symbol,
    symbols: &mut Symbols,
) -> Result<Interface, Diagnostic> {
    let source = file.text();
    let namespace = symbols.text(namespace).to_string();
    let mut own = Interface::default();
    for item in &module.items {
        match item {
            Item::Data(data) => declare_data(&mut own, data, file, &namespace, symbols)?,
            // A constraint alias shares the types' namespace, so that it is
            // exported and imported as one is, and owns as little as an alias.
            Item::Alias(AliasDecl { name, .. })
            | Item::Constraints(ConstraintAliasDecl { name, .. }) => {
                let local = symbols.intern(name.text(source));
                if own.types.contains_key(&local) {
                    let message =
                        format!("type `{}` is declared more than once", name.text(source));
                    return Err(Diagnostic::new(message)
                        .at(file, name.0)
                        .label("declared again here"));
                }
                let canonical = symbols.intern(&format!("{namespace}$${}", name.text(source)));
                own.types.insert(
                    local,
                    TypeBinding {
                        canonical,
                        constructors: HashMap::default(),
                        variants: Vec::new(),
                        methods: HashMap::default(),
                        alias: true,
                    },
                );
            }
            Item::Signature(signature) => {
                declare_value(&mut own, signature.name, file, &namespace, symbols)?;
            }
            Item::Clause(clause) => {
                declare_value(&mut own, clause.name, file, &namespace, symbols)?;
            }
            // An expectation is named by nothing a program can write.
            Item::Header(_) | Item::Import(_) | Item::Exports(_) | Item::Expect(_) => {}
        }
    }
    Ok(own)
}

fn declare_data(
    own: &mut Interface,
    data: &DataDecl,
    file: &Source,
    namespace: &str,
    symbols: &mut Symbols,
) -> Result<(), Diagnostic> {
    let source = file.text();
    let local = symbols.intern(data.name.text(source));
    if own.types.contains_key(&local) {
        let message = format!(
            "type `{}` is declared more than once",
            data.name.text(source)
        );
        return Err(Diagnostic::new(message)
            .at(file, data.name.0)
            .label("declared again here"));
    }
    let canonical = symbols.intern(&format!("{namespace}$${}", data.name.text(source)));
    let mut binding = TypeBinding {
        canonical,
        constructors: HashMap::default(),
        variants: Vec::new(),
        methods: HashMap::default(),
        alias: false,
    };
    match &data.representation {
        DataRepresentation::Sum(constructors) => {
            for constructor in constructors {
                let spelling = symbols.intern(constructor.name.text(source));
                let canonical = symbols.intern(&format!(
                    "{namespace}$${}$${}",
                    data.name.text(source),
                    constructor.name.text(source)
                ));
                if binding.constructors.insert(spelling, canonical).is_some() {
                    let message = format!(
                        "type `{}` declares constructor `{}` more than once",
                        data.name.text(source),
                        constructor.name.text(source)
                    );
                    return Err(Diagnostic::new(message)
                        .at(file, constructor.name.0)
                        .label("declared again here"));
                }
                claim(&mut own.constructors, spelling, canonical);
                binding.variants.push((canonical, constructor.fields.len()));
            }
        }
        DataRepresentation::Wrapper(representation) => {
            intern_record_fields(representation, source, symbols);
            let canonical = symbols.intern(&format!(
                "{namespace}$${}$${}",
                data.name.text(source),
                data.name.text(source)
            ));
            binding.constructors.insert(local, canonical);
            claim(&mut own.constructors, local, canonical);
        }
    }
    for method in &data.methods {
        let method_name = match method {
            MethodItem::Signature(signature) => signature.name,
            MethodItem::Clause(clause) => clause.name,
        };
        let spelling = symbols.intern(method_name.text(source));
        let canonical = symbols.intern(&format!(
            "{namespace}$${}.{}",
            data.name.text(source),
            method_name.text(source)
        ));
        if let Some(previous) = binding.methods.get(&spelling)
            && *previous != canonical
        {
            let message = format!(
                "method `{}` is declared by conflicting definitions",
                method_name.text(source)
            );
            return Err(Diagnostic::new(message).at(file, method_name.0));
        }
        binding.methods.insert(spelling, canonical);
    }
    // An ordered type's `equals` is its `cmp`'s `Eq`, declared or not.
    let cmp = symbols.intern("cmp");
    let equals = symbols.intern("equals");
    if binding.methods.contains_key(&cmp) && !binding.methods.contains_key(&equals) {
        let canonical = symbols.intern(&format!("{namespace}$${}.equals", data.name.text(source)));
        binding.methods.insert(equals, canonical);
    }
    own.types.insert(local, binding);
    Ok(())
}

fn intern_record_fields(ty: &super::ast::Type, source: &str, symbols: &mut Symbols) {
    match ty {
        super::ast::Type::Named { arguments, .. } => {
            for argument in arguments {
                intern_record_fields(argument, source, symbols);
            }
        }
        super::ast::Type::Tuple { members, .. } => {
            for member in members {
                intern_record_fields(member, source, symbols);
            }
        }
        super::ast::Type::Function {
            parameters, result, ..
        } => {
            for parameter in parameters {
                intern_record_fields(parameter, source, symbols);
            }
            intern_record_fields(result, source, symbols);
        }
        super::ast::Type::Variants { constructors, .. } => {
            for constructor in constructors {
                for field in &constructor.fields {
                    intern_record_fields(field, source, symbols);
                }
            }
        }
        super::ast::Type::Record { fields, .. } => {
            for (name, field) in fields {
                symbols.intern(name.text(source));
                intern_record_fields(field, source, symbols);
            }
        }
        super::ast::Type::Hole { .. } => {}
    }
}

fn declare_value(
    own: &mut Interface,
    name: Name,
    file: &Source,
    namespace: &str,
    symbols: &mut Symbols,
) -> Result<(), Diagnostic> {
    let source = file.text();
    let local = symbols.intern(name.text(source));
    let canonical = symbols.intern(&format!("{namespace}$${}", name.text(source)));
    if let Some(previous) = own.values.get(&local)
        && *previous != canonical
    {
        let message = format!("value `{}` is declared more than once", name.text(source));
        return Err(Diagnostic::new(message)
            .at(file, name.0)
            .label("declared again here"));
    }
    own.values.insert(local, canonical);
    Ok(())
}

fn exports(
    module: &Module,
    file: &Source,
    scope: &Interface,
    symbols: &mut Symbols,
) -> Result<Interface, Diagnostic> {
    let source = file.text();
    let declarations: Vec<&Export> = module
        .items
        .iter()
        .filter_map(|item| match item {
            Item::Exports(exports) => Some(exports.exports.iter()),
            _ => None,
        })
        .flatten()
        .collect();
    if declarations.is_empty() {
        return Ok(Interface::default());
    }
    let mut public = Interface::default();
    for export in declarations {
        let local = symbols.intern(export.name.text(source));
        if let Some(&canonical) = scope.values.get(&local) {
            insert_unique(
                &mut public.values,
                local,
                canonical,
                symbols,
                "exported value",
            )
            .map_err(|diagnostic| diagnostic.at(file, export.name.0))?;
        }
        if let Some(binding) = scope.types.get(&local) {
            if binding.alias && export.constructors {
                let name = export.name.text(source);
                let message = format!("`{name}` is an alias, which owns no constructors");
                return Err(Diagnostic::new(message)
                    .at(file, export.name.0)
                    .label("`.*` exports a type's constructors")
                    .help(format!("export `{name}` without `.*`")));
            }
            let mut visible = binding.clone();
            if !export.constructors {
                visible.constructors.clear();
                visible.variants.clear();
            }
            public.types.insert(local, visible.clone());
            if export.constructors {
                for (&name, &canonical) in &visible.constructors {
                    claim(&mut public.constructors, name, canonical);
                }
            }
        }
        if !scope.values.contains_key(&local) && !scope.types.contains_key(&local) {
            let message = format!(
                "`{}` is not visible and cannot be exported",
                export.name.text(source)
            );
            return Err(Diagnostic::new(message).at(file, export.name.0));
        }
    }
    Ok(public)
}

fn expose_import(
    scope: &mut Interface,
    face: &Interface,
    import: &super::ast::ImportDecl,
    file: &Source,
    symbols: &mut Symbols,
) -> Result<(), Diagnostic> {
    let source = file.text();
    for exposure in &import.exposures {
        renamed_alike(exposure, file)?;
        let exported = symbols.intern(exposure.exported.text(source));
        let local = symbols.intern(exposure.local.text(source));
        let mut found = false;
        if let Some(&canonical) = face.values.get(&exported) {
            insert_unique(
                &mut scope.values,
                local,
                canonical,
                symbols,
                "imported value",
            )
            .map_err(|diagnostic| diagnostic.at(file, exposure.local.0))?;
            found = true;
        }
        if let Some(binding) = face.types.get(&exported) {
            // The type keeps the constructors its module exports, which
            // `Type.Ctor` names; only `.*` also makes their bare words visible.
            let imported = binding.clone();
            if let Some(previous) = scope.types.get(&local)
                && previous.canonical != imported.canonical
            {
                let message = format!(
                    "imported type `{}` conflicts with an existing type",
                    symbols.text(local)
                );
                return Err(Diagnostic::new(message).at(file, exposure.local.0));
            }
            if exposure.constructors {
                for (&name, &canonical) in &imported.constructors {
                    claim(&mut scope.constructors, name, canonical);
                }
            }
            scope.types.insert(local, imported);
            found = true;
        }
        // A constructor exported with its type's `.*` may be selected by
        // itself, without the type or its other constructors.
        if !exposure.constructors
            && let Some(claimants) = face.constructors.get(&exported)
        {
            for &canonical in claimants {
                claim(&mut scope.constructors, local, canonical);
            }
            found = true;
        }
        if !found {
            let module = import
                .path
                .iter()
                .map(|part| part.text(source))
                .collect::<Vec<_>>()
                .join(".");
            let message = format!(
                "`{}` is not exported by `{module}`",
                exposure.exported.text(source)
            );
            return Err(Diagnostic::new(message)
                .at(file, exposure.exported.0)
                .label(format!("`{module}` does not export this")));
        }
    }
    Ok(())
}

/// Refuse a rename that changes whether a name is capitalised: a
/// capitalised word is a type's or a constructor's and a lowercase one a
/// value's, so a renamed name keeps the case it was exported with.
fn renamed_alike(exposure: &super::ast::Exposure, file: &Source) -> Result<(), Diagnostic> {
    let source = file.text();
    let exported = exposure.exported.text(source);
    let local = exposure.local.text(source);
    let capitalised = |name: &str| name.starts_with(|c: char| c.is_ascii_uppercase());
    if capitalised(exported) == capitalised(local) {
        return Ok(());
    }
    let mut characters = local.chars();
    let first = characters.next().unwrap_or_default();
    let rest = characters.as_str();
    let (wanted, label, first) = if capitalised(exported) {
        let label = "a type or constructor is named in capitals";
        ("capitalised", label, first.to_ascii_uppercase())
    } else {
        let label = "a value or function is named in lowercase";
        ("lowercase", label, first.to_ascii_lowercase())
    };
    let suggested = format!("{first}{rest}");
    let constructors = if exposure.constructors { ".*" } else { "" };
    // Where the new name in the right case is the old one, as `shape` for
    // `Shape`, the rename asks for nothing the name does not already have.
    let help = if suggested == exported {
        format!("import it under its own name, as `{{{exported}{constructors}}}`")
    } else {
        format!("rename it as `{{{exported}{constructors}: {suggested}}}`")
    };
    let message = format!("`{exported}` is imported as `{local}`, which is not {wanted}");
    Err(Diagnostic::new(message)
        .at(file, exposure.local.0)
        .label(label)
        .note("a capitalised word names a type or constructor, and a lowercase one a value or function")
        .help(help))
}

/// `words` with each word between underscores capitalised and the
/// underscores dropped: `shapes` is `Shapes`, and `flat_shapes` is
/// `FlatShapes`.
fn capitalised_words(words: &str) -> String {
    let mut joined = String::with_capacity(words.len());
    for word in words.split('_') {
        let mut characters = word.chars();
        let Some(first) = characters.next() else {
            continue;
        };
        joined.push(first.to_ascii_uppercase());
        joined.push_str(characters.as_str());
    }
    joined
}

fn merge_map(
    into: &mut HashMap<Symbol, Symbol>,
    from: &HashMap<Symbol, Symbol>,
    kind: &'static str,
) -> Result<(), Clash> {
    for (&local, &canonical) in from {
        if let Some(previous) = into.get(&local)
            && *previous != canonical
        {
            return Err(Clash { kind, name: local });
        }
        into.insert(local, canonical);
    }
    Ok(())
}

/// Add `canonical` to the declarations `word` may name.
fn claim(map: &mut HashMap<Symbol, Vec<Symbol>>, word: Symbol, canonical: Symbol) {
    let claimants = map.entry(word).or_default();
    if !claimants.contains(&canonical) {
        claimants.push(canonical);
    }
}

fn insert_unique(
    map: &mut HashMap<Symbol, Symbol>,
    local: Symbol,
    canonical: Symbol,
    symbols: &Symbols,
    kind: &str,
) -> Result<(), Diagnostic> {
    if let Some(previous) = map.get(&local)
        && *previous != canonical
    {
        return Err(Diagnostic::new(format!(
            "{kind} `{}` conflicts with another declaration",
            symbols.text(local)
        )));
    }
    map.insert(local, canonical);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::{SystemTime, UNIX_EPOCH};

    struct Fixture {
        root: PathBuf,
    }

    impl Fixture {
        fn new() -> Self {
            let unique = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos();
            let root = std::env::temp_dir().join(format!("faun-modules-{unique}"));
            fs::create_dir_all(&root).unwrap();
            Self { root }
        }

        /// A standard library that exports nothing, beside the fixture's own
        /// package so it does not claim the fixture's namespaces.
        fn empty_prelude(&self) -> PathBuf {
            self.write("prelude/standard.fn", "package {}\nexport {}\n")
        }

        /// A host exporting `Host`, beside the fixture's own package.
        fn host(&self) -> PathBuf {
            self.write("host/host.fn", "export {Host}\nHost : {argc: Nat}\n")
        }

        fn write(&self, name: &str, source: &str) -> PathBuf {
            let path = self.root.join(name);
            if let Some(parent) = path.parent() {
                fs::create_dir_all(parent).unwrap();
            }
            fs::write(&path, source).unwrap();
            path
        }
    }

    impl Drop for Fixture {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.root);
        }
    }

    #[test]
    fn imports_only_the_public_interface() {
        let fixture = Fixture::new();
        fixture.write(
            "numbers.fn",
            "export {Nat.*}\nNat : [Zero, Succ(Nat)]\nsecret = Zero\n",
        );
        let entry = fixture.write("main.fn", "import numbers {Nat.*}\nid(x) -> Succ(x)\n");
        let loaded = load_program(&entry, &fixture.empty_prelude(), &fixture.host()).unwrap();
        let entry = loaded.module(loaded.entry);
        let succ = loaded.symbols.find("Succ").unwrap();
        let secret = loaded.symbols.find("secret").unwrap();
        assert!(entry.scope.constructors.contains_key(&succ));
        assert!(!entry.scope.values.contains_key(&secret));
    }

    #[test]
    fn private_names_cannot_be_imported() {
        let fixture = Fixture::new();
        fixture.write("hidden.fn", "secret = 0\n");
        let entry = fixture.write("main.fn", "import hidden {secret}\nmain = secret\n");
        let error = load_program(&entry, &fixture.empty_prelude(), &fixture.host()).unwrap_err();
        assert!(error.message.contains("not exported"));
    }

    #[test]
    fn import_cycles_are_rejected_before_reloading_a_source() {
        let fixture = Fixture::new();
        let first = fixture.write("first.fn", "import second {}\n");
        fixture.write("second.fn", "import first {}\n");
        let error = load_program(&first, &fixture.empty_prelude(), &fixture.host()).unwrap_err();
        assert!(error.message.contains("import cycle"));
    }

    #[test]
    fn std_host_is_a_compiler_selected_virtual_module() {
        let fixture = Fixture::new();
        let host = fixture.write("target/host.fn", "export {Host}\nHost : {argc: Nat}\n");
        let entry = fixture.write(
            "main.fn",
            "import std.host {Host}\nid : Host -> Host\nid(h) -> h\n",
        );
        let loaded = load_program(&entry, crate::standard_path(), &host).unwrap();
        let canonical = host.canonicalize().unwrap();
        assert_eq!(loaded.module(loaded.host).path, canonical);

        let circular = fixture.write(
            "target/circular.fn",
            "import std.host {Host}\nexport {Host}\n",
        );
        let error = load_program(&entry, crate::standard_path(), &circular).unwrap_err();
        assert!(error.message.contains("cannot import `std.host`"));
    }

    #[test]
    fn standard_namespaces_are_path_stable() {
        let fixture = Fixture::new();
        fixture.write("nat.fn", "export {Nat.*}\nNat : [Zero, Succ(Nat)]\n");
        let root = fixture.write(
            "standard.fn",
            "package {}\nimport nat {Nat.*}\nexport {Nat.*}\n",
        );
        let entry = fixture.write("main.fn", "id(x) -> x\n");
        let loaded = load_program(&entry, &root, &fixture.host()).unwrap();
        let nat = loaded
            .modules
            .iter()
            .find(|module| module.path.ends_with("nat.fn"))
            .unwrap();
        assert_eq!(loaded.symbols.text(nat.namespace), "Mstd_nat");
    }

    #[test]
    fn a_module_s_words_lead_a_type_s_new_name_capitalised() {
        assert_eq!(capitalised_words("shapes"), "Shapes");
        assert_eq!(capitalised_words("flat_shapes"), "FlatShapes");
        assert_eq!(capitalised_words("v2__io_"), "V2Io");
    }
}
