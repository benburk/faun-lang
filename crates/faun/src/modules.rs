//! Package-rooted loading, public interfaces, and canonical declarations.
//!
//! Files remain separate parsed modules. Linking builds compact symbol tables;
//! it does not concatenate or rewrite source ASTs. This keeps source spans
//! local and lets resolution consume one immutable module at a time.

// Loading and interface construction keep their coordinated state transitions
// visible instead of scattering them among tiny mutation helpers.
#![allow(clippy::too_many_lines, clippy::useless_let_if_seq)]

use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};

use super::ast::{
    AliasDecl, ConstraintAliasDecl, DataDecl, DataRepresentation, Export, Item, MethodItem, Module,
    Name, Span,
};
use super::diagnostic::Diagnostic;
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
}

impl LoadedProgram {
    #[must_use]
    pub fn module(&self, id: ModuleId) -> &LoadedModule {
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
/// `package {md5: "../md5/src/md5"}`, each a module base relative to the
/// header's file. Every module of the package may then `import md5`, which is
/// that package's root, and not its inner modules, which are its own. A
/// dependency's modules resolve their imports from its root, with its own
/// header's dependencies. Only a root module has a header. The entry's
/// package is the modules loaded from the entry's root, not its dependencies'.
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
    let mut loader = Loader::default();
    let root = loader.package_at(prelude);
    let prelude_id = loader.load_module(prelude, Loading::Package(root), true)?;
    loader.prelude = Some(loader.pending[prelude_id.index()].public.clone());
    let root = loader.package_at(prelude);
    let host_id = loader.load_module(host, Loading::Package(root), false)?;
    loader.host = Some(host_id);
    // The standard library as the entry is its own package.
    let root = loader.package_at(entry);
    let entry_id = loader.load_module(entry, Loading::Package(root), false)?;
    Ok(loader.into_loaded_program(entry_id, prelude_id, host_id))
}

/// Where a package's modules resolve their imports from: its root module's
/// directory, the packages its header depends on, by the name each is
/// imported as, and which package it is.
#[derive(Clone, Debug)]
struct Root {
    directory: PathBuf,
    dependencies: HashMap<String, PathBuf>,
    package: usize,
}

/// A module being loaded: a package's root, whose header may name its
/// dependencies, or one of the modules within `Root`'s package.
enum Loading<'a> {
    Package(Root),
    Within(&'a Root),
}

#[derive(Debug)]
struct PendingModule {
    id: ModuleId,
    /// Which package it belongs to; see [`Root`].
    package: usize,
    path: PathBuf,
    source: SourceId,
    syntax: Module,
    namespace: Symbol,
    imports: Vec<(usize, ModuleId)>,
    scope: Interface,
    public: Interface,
}

#[derive(Default)]
struct Loader {
    sources: Sources,
    symbols: Symbols,
    pending: Vec<PendingModule>,
    loaded: HashMap<PathBuf, ModuleId>,
    visiting: Vec<PathBuf>,
    /// The prelude's exports, once it has loaded; its own modules see none.
    prelude: Option<Interface>,
    /// The host module, once it has loaded; it cannot import itself.
    host: Option<ModuleId>,
    standard_root: Option<PathBuf>,
    /// How many packages have been given a root.
    packages: usize,
}

impl Loader {
    /// A new package rooted where the module at `path` is.
    fn package_at(&mut self, path: &Path) -> Root {
        self.packages += 1;
        Root {
            directory: path
                .parent()
                .unwrap_or_else(|| Path::new("."))
                .to_path_buf(),
            dependencies: HashMap::new(),
            package: self.packages,
        }
    }

    fn into_loaded_program(
        self,
        entry: ModuleId,
        prelude: ModuleId,
        host: ModuleId,
    ) -> LoadedProgram {
        let own = self.pending[entry.index()].package;
        let package = self
            .pending
            .iter()
            .filter(|module| module.package == own)
            .map(|module| module.id)
            .collect();
        let modules = self
            .pending
            .into_iter()
            .map(|module| LoadedModule {
                id: module.id,
                path: module.path,
                source: module.source,
                syntax: module.syntax,
                namespace: module.namespace,
                scope: module.scope,
                public: module.public,
            })
            .collect();
        LoadedProgram {
            sources: self.sources,
            symbols: self.symbols,
            modules,
            entry,
            package,
            prelude,
            host,
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
                Diagnostic::new(format!("cannot read {}: {error}", written.display()))
            })?,
        };
        if let Some(&id) = self.loaded.get(&path) {
            return Ok(id);
        }
        if self.visiting.contains(&path) {
            return Err(Diagnostic::new(format!(
                "import cycle through {}",
                path.display()
            )));
        }
        if standard_root {
            self.standard_root = path.parent().map(Path::to_path_buf);
        }
        let text = match built_in {
            Some(text) => text.to_owned(),
            None => fs::read_to_string(&path).map_err(|error| {
                Diagnostic::new(format!("cannot read {}: {error}", path.display()))
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
        self.pending.push(PendingModule {
            id,
            package: root.package,
            path: path.clone(),
            source,
            syntax,
            namespace,
            imports: Vec::new(),
            scope: Interface::default(),
            public: Interface::default(),
        });
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
            } else if let Some(dependency) = root.dependencies.get(&path_parts[0]) {
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
                let dependency = dependency.clone();
                let package = self.package_at(&dependency);
                self.load_module(&dependency, Loading::Package(package), false)?
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
        module.imports = linked_imports;
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
        let imported = syntax.items.iter().find_map(|item| match item {
            Item::Import(import) => import
                .exposures
                .iter()
                .find(|exposure| exposure.local.text(source) == name)
                .map(|exposure| exposure.local.0),
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
            Some(imported) => diagnostic
                .secondary(file, imported, "imported here")
                .help(format!(
                    "import it under another name, as `{{{name}: Other}}`"
                )),
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
                for dependency in &header.dependencies {
                    let name = dependency.name.text(text.text()).to_owned();
                    let written: String = dependency
                        .path
                        .iter()
                        .map(|part| {
                            crate::literal::decode_text(part.text(text.text()))
                                .map(std::borrow::Cow::into_owned)
                        })
                        .collect::<Result<_, _>>()
                        .map_err(|message| Diagnostic::new(message).at(text, dependency.span))?;
                    let module =
                        module_base(directory, &directory.join(&written)).map_err(|error| {
                            Diagnostic::new(format!("dependency `{name}` {}", error.message))
                                .at(text, dependency.span)
                        })?;
                    if root.dependencies.insert(name.clone(), module).is_some() {
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

/// The module at the base `joined`: `joined.fn`, or `name.fn` in the
/// directory `joined`, where `name` is its last part, and not both. Where
/// neither or both are there, they are named from `from`, the directory
/// the base was written relative to.
fn module_base(from: &Path, joined: &Path) -> Result<PathBuf, Diagnostic> {
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
                        constructors: HashMap::new(),
                        methods: HashMap::new(),
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
        constructors: HashMap::new(),
        methods: HashMap::new(),
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
            "export {Nat.*}\nNat : [Zero, Succ(Nat)]\nsecret() -> Zero\n",
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
        fixture.write("hidden.fn", "secret() -> 0\n");
        let entry = fixture.write("main.fn", "import hidden {secret}\nmain() -> secret()\n");
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
}
