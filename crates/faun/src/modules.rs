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
use super::{SourceId, Sources, Symbol, Symbols, parse_in};

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
    pub(crate) fn merge(
        &mut self,
        other: &Self,
        symbols: &Symbols,
        context: &str,
    ) -> Result<(), Diagnostic> {
        merge_map(&mut self.values, &other.values, symbols, context, "value")?;
        for (&word, claimants) in &other.constructors {
            for &canonical in claimants {
                claim(&mut self.constructors, word, canonical);
            }
        }
        for (&local, binding) in &other.types {
            if let Some(previous) = self.types.get(&local)
                && previous.canonical != binding.canonical
            {
                return Err(Diagnostic::new(format!(
                    "{context} binds type `{}` more than once",
                    symbols.text(local)
                )));
            }
            self.types.insert(local, binding.clone());
        }
        Ok(())
    }
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
        let path = written.canonicalize().map_err(|error| {
            Diagnostic::new(format!("cannot read {}: {error}", written.display()))
        })?;
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
        let text = fs::read_to_string(&path)
            .map_err(|error| Diagnostic::new(format!("cannot read {}: {error}", path.display())))?;
        let source = self.sources.add(path.clone(), text.clone());
        let syntax = parse_in(&text, source).map_err(|error| {
            let at = Span::new(error.offset, error.end);
            let text = self.sources.get(source).expect("the source just added");
            Diagnostic::new(error.message).at(text, at)
        })?;
        let root = self.root(loading, &syntax, &path, source)?;
        let id =
            ModuleId(u32::try_from(self.pending.len()).expect("fewer than 2^32 loaded modules"));
        let namespace_text = self.namespace(&path, id);
        let namespace = self.symbols.intern(&namespace_text);
        let own = declarations(&syntax, &text, namespace, &mut self.symbols)?;

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

        let imports: Vec<(usize, Vec<String>)> = self.pending[id.index()]
            .syntax
            .items
            .iter()
            .enumerate()
            .filter_map(|(index, item)| match item {
                Item::Import(import) => Some((
                    index,
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
        for (index, path_parts) in imports {
            let dependency = if path_parts == ["std", "host"] {
                self.host.ok_or_else(|| {
                    Diagnostic::new("the host module cannot import `std.host`, which is itself")
                })?
            } else if let Some(dependency) = root.dependencies.get(&path_parts[0]) {
                if path_parts.len() > 1 {
                    return Err(Diagnostic::new(format!(
                        "`{}` is a package this one depends on, whose modules are its own: import `{}` itself",
                        path_parts[0], path_parts[0]
                    )));
                }
                let dependency = dependency.clone();
                let package = self.package_at(&dependency);
                self.load_module(&dependency, Loading::Package(package), false)?
            } else {
                let module = module_path(&root.directory, &path_parts)?;
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
            expose_import(&mut scope, &face, import, &text, &mut self.symbols)?;
        }
        scope.merge(&own, &self.symbols, &format!("module `{}`", path.display()))?;
        let public = exports(
            &self.pending[id.index()].syntax,
            &text,
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
                "only a package's root module has a `package` header; this module is inside its package",
            )
            .at(text, header.span)),
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
                    let module = module_base(&directory.join(&written)).map_err(|error| {
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
    module_base(&joined)
        .map_err(|error| Diagnostic::new(format!("import `{}` {}", parts.join("."), error.message)))
}

/// The module at the base `joined`: `joined.fn`, or `name.fn` in the
/// directory `joined`, where `name` is its last part, and not both.
fn module_base(joined: &Path) -> Result<PathBuf, Diagnostic> {
    let flat = joined.with_extension("fn");
    let nested = joined
        .join(joined.file_name().unwrap_or_default())
        .with_extension("fn");
    match (flat.is_file(), nested.is_file()) {
        (true, false) => Ok(flat),
        (false, true) => Ok(nested),
        (true, true) => Err(Diagnostic::new(format!(
            "is ambiguous between {} and {}",
            flat.display(),
            nested.display()
        ))),
        (false, false) => Err(Diagnostic::new(format!(
            "finds neither {} nor {}",
            flat.display(),
            nested.display()
        ))),
    }
}

fn declarations(
    module: &Module,
    source: &str,
    namespace: Symbol,
    symbols: &mut Symbols,
) -> Result<Interface, Diagnostic> {
    let namespace = symbols.text(namespace).to_string();
    let mut own = Interface::default();
    for item in &module.items {
        match item {
            Item::Data(data) => declare_data(&mut own, data, source, &namespace, symbols)?,
            // A constraint alias shares the types' namespace, so that it is
            // exported and imported as one is, and owns as little as an alias.
            Item::Alias(AliasDecl { name, .. })
            | Item::Constraints(ConstraintAliasDecl { name, .. }) => {
                let local = symbols.intern(name.text(source));
                if own.types.contains_key(&local) {
                    return Err(Diagnostic::new(format!(
                        "type `{}` is declared more than once",
                        name.text(source)
                    )));
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
                declare_value(&mut own, signature.name, source, &namespace, symbols)?;
            }
            Item::Clause(clause) => {
                declare_value(&mut own, clause.name, source, &namespace, symbols)?;
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
    source: &str,
    namespace: &str,
    symbols: &mut Symbols,
) -> Result<(), Diagnostic> {
    let local = symbols.intern(data.name.text(source));
    if own.types.contains_key(&local) {
        return Err(Diagnostic::new(format!(
            "type `{}` is declared more than once",
            data.name.text(source)
        )));
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
                    return Err(Diagnostic::new(format!(
                        "type `{}` declares constructor `{}` more than once",
                        data.name.text(source),
                        constructor.name.text(source)
                    )));
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
            return Err(Diagnostic::new(format!(
                "method `{}` is declared by conflicting definitions",
                method_name.text(source)
            )));
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
    }
}

fn declare_value(
    own: &mut Interface,
    name: Name,
    source: &str,
    namespace: &str,
    symbols: &mut Symbols,
) -> Result<(), Diagnostic> {
    let local = symbols.intern(name.text(source));
    let canonical = symbols.intern(&format!("{namespace}$${}", name.text(source)));
    if let Some(previous) = own.values.get(&local)
        && *previous != canonical
    {
        return Err(Diagnostic::new(format!(
            "value `{}` is declared more than once",
            name.text(source)
        )));
    }
    own.values.insert(local, canonical);
    Ok(())
}

fn exports(
    module: &Module,
    source: &str,
    scope: &Interface,
    symbols: &mut Symbols,
) -> Result<Interface, Diagnostic> {
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
            )?;
        }
        if let Some(binding) = scope.types.get(&local) {
            if binding.alias && export.constructors {
                return Err(Diagnostic::new(format!(
                    "`{}` is an alias, which owns no constructors for `.*` to export",
                    export.name.text(source)
                )));
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
            return Err(Diagnostic::new(format!(
                "`{}` is not visible and cannot be exported",
                export.name.text(source)
            )));
        }
    }
    Ok(public)
}

fn expose_import(
    scope: &mut Interface,
    face: &Interface,
    import: &super::ast::ImportDecl,
    source: &str,
    symbols: &mut Symbols,
) -> Result<(), Diagnostic> {
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
            )?;
            found = true;
        }
        if let Some(binding) = face.types.get(&exported) {
            let mut imported = binding.clone();
            if !exposure.constructors {
                imported.constructors.clear();
            }
            if let Some(previous) = scope.types.get(&local)
                && previous.canonical != imported.canonical
            {
                return Err(Diagnostic::new(format!(
                    "imported type `{}` conflicts with an existing type",
                    symbols.text(local)
                )));
            }
            if exposure.constructors {
                for (&name, &canonical) in &imported.constructors {
                    claim(&mut scope.constructors, name, canonical);
                }
            }
            scope.types.insert(local, imported);
            found = true;
        }
        if !found {
            return Err(Diagnostic::new(format!(
                "`{}` is not exported by import `{}`",
                exposure.exported.text(source),
                import
                    .path
                    .iter()
                    .map(|part| part.text(source))
                    .collect::<Vec<_>>()
                    .join(".")
            )));
        }
    }
    Ok(())
}

fn merge_map(
    into: &mut HashMap<Symbol, Symbol>,
    from: &HashMap<Symbol, Symbol>,
    symbols: &Symbols,
    context: &str,
    kind: &str,
) -> Result<(), Diagnostic> {
    for (&local, &canonical) in from {
        if let Some(previous) = into.get(&local)
            && *previous != canonical
        {
            return Err(Diagnostic::new(format!(
                "{context} binds {kind} `{}` more than once",
                symbols.text(local)
            )));
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
            self.write("prelude/standard.fn", "package {}\nexports {}\n")
        }

        /// A host exporting `Host`, beside the fixture's own package.
        fn host(&self) -> PathBuf {
            self.write("host/host.fn", "exports {Host}\nHost : {argc: Nat}\n")
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
            "exports {Nat.*}\nNat : [Zero Succ(Nat)]\nsecret() -> Zero\n",
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
        let host = fixture.write("target/host.fn", "exports {Host}\nHost : {argc: Nat}\n");
        let entry = fixture.write(
            "main.fn",
            "import std.host {Host}\nid : Host -> Host\nid(h) -> h\n",
        );
        let loaded = load_program(&entry, crate::standard_path(), &host).unwrap();
        let canonical = host.canonicalize().unwrap();
        assert_eq!(loaded.module(loaded.host).path, canonical);

        let circular = fixture.write(
            "target/circular.fn",
            "import std.host {Host}\nexports {Host}\n",
        );
        let error = load_program(&entry, crate::standard_path(), &circular).unwrap_err();
        assert!(error.message.contains("cannot import `std.host`"));
    }

    #[test]
    fn standard_namespaces_are_path_stable() {
        let fixture = Fixture::new();
        fixture.write("nat.fn", "exports {Nat.*}\nNat : [Zero Succ(Nat)]\n");
        let root = fixture.write(
            "standard.fn",
            "package {}\nimport nat {Nat.*}\nexports {Nat.*}\n",
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
