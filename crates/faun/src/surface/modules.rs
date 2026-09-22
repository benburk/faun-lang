//! Package-rooted loading, public interfaces, and canonical declarations.
//!
//! Files remain separate parsed modules. Linking builds compact symbol tables;
//! it does not concatenate or rewrite source ASTs. This keeps source spans
//! local and lets resolution consume one immutable module at a time.

// Loading and interface construction keep their coordinated state transitions
// visible instead of scattering them among tiny mutation helpers.
#![allow(clippy::too_many_lines, clippy::useless_let_if_seq)]

use std::collections::HashMap;
use std::fmt;
use std::fs;
use std::path::{Path, PathBuf};

use super::ast::{DataDecl, DataRepresentation, Export, Item, MethodItem, Module, Name};
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
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Interface {
    pub values: HashMap<Symbol, Symbol>,
    pub types: HashMap<Symbol, TypeBinding>,
    pub constructors: HashMap<Symbol, Symbol>,
}

impl Interface {
    pub(crate) fn merge(
        &mut self,
        other: &Self,
        symbols: &Symbols,
        context: &str,
    ) -> Result<(), LoadError> {
        merge_map(&mut self.values, &other.values, symbols, context, "value")?;
        merge_map(
            &mut self.constructors,
            &other.constructors,
            symbols,
            context,
            "constructor",
        )?;
        for (&local, binding) in &other.types {
            if let Some(previous) = self.types.get(&local)
                && previous.canonical != binding.canonical
            {
                return Err(LoadError::new(format!(
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
    pub entries: Vec<ModuleId>,
    pub prelude: Option<ModuleId>,
}

impl LoadedProgram {
    #[must_use]
    pub fn module(&self, id: ModuleId) -> &LoadedModule {
        &self.modules[id.index()]
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LoadError {
    pub message: String,
}

impl LoadError {
    fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

impl fmt::Display for LoadError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for LoadError {}

/// Load entry files and an optional standard-library root.
///
/// Imports are rooted at the importing package directory. Each path component
/// maps to a directory and the final module is either `path.ori` or
/// `path/name.ori`; finding both is an error.
///
/// # Errors
///
/// Reports I/O, parse, cycle, duplicate declaration, visibility, and ambiguous
/// module-path failures.
pub fn load(entries: &[PathBuf], prelude: Option<&Path>) -> Result<LoadedProgram, LoadError> {
    let mut loader = Loader::default();
    let prelude_id = match prelude {
        Some(path) => Some(loader.load_module(path, &Root::at(path), true)?),
        None => None,
    };
    loader.prelude = prelude_id.map(|id| loader.pending[id.index()].public.clone());
    let mut entry_ids = Vec::with_capacity(entries.len());
    for entry in entries {
        entry_ids.push(loader.load_module(entry, &Root::at(entry), false)?);
    }
    Ok(loader.finish(entry_ids, prelude_id))
}

#[derive(Clone, Debug)]
struct Root {
    directory: PathBuf,
}

impl Root {
    fn at(path: &Path) -> Self {
        Self {
            directory: path
                .parent()
                .unwrap_or_else(|| Path::new("."))
                .to_path_buf(),
        }
    }
}

#[derive(Debug)]
struct PendingModule {
    id: ModuleId,
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
    prelude: Option<Interface>,
    standard_root: Option<PathBuf>,
}

impl Loader {
    fn finish(self, entries: Vec<ModuleId>, prelude: Option<ModuleId>) -> LoadedProgram {
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
            entries,
            prelude,
        }
    }

    fn load_module(
        &mut self,
        written: &Path,
        root: &Root,
        standard_root: bool,
    ) -> Result<ModuleId, LoadError> {
        let path = written.canonicalize().map_err(|error| {
            LoadError::new(format!("cannot read {}: {error}", written.display()))
        })?;
        if let Some(&id) = self.loaded.get(&path) {
            return Ok(id);
        }
        if self.visiting.contains(&path) {
            return Err(LoadError::new(format!(
                "import cycle through {}",
                path.display()
            )));
        }
        if standard_root {
            self.standard_root = path.parent().map(Path::to_path_buf);
        }
        let text = fs::read_to_string(&path)
            .map_err(|error| LoadError::new(format!("cannot read {}: {error}", path.display())))?;
        let source = self.sources.add(path.clone(), text.clone());
        let syntax = parse_in(&text, source)
            .map_err(|error| LoadError::new(format!("{}:{error}", path.display())))?;
        let id =
            ModuleId(u32::try_from(self.pending.len()).expect("fewer than 2^32 loaded modules"));
        let namespace_text = self.namespace(&path, id);
        let namespace = self.symbols.intern(&namespace_text);
        let own = declarations(&syntax, &text, namespace, &mut self.symbols)?;

        // Reserve the slot before descending so module IDs remain stable and a
        // cycle can name the module being visited.
        self.pending.push(PendingModule {
            id,
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
            let dependency_path = module_path(&root.directory, &path_parts)?;
            let dependency = self.load_module(&dependency_path, root, false)?;
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

fn module_path(root: &Path, parts: &[String]) -> Result<PathBuf, LoadError> {
    if parts.is_empty() {
        return Err(LoadError::new("an import names no module"));
    }
    let joined = parts
        .iter()
        .fold(root.to_path_buf(), |path, part| path.join(part));
    let flat = joined.with_extension("ori");
    let nested = joined
        .join(parts.last().expect("nonempty path"))
        .with_extension("ori");
    match (flat.is_file(), nested.is_file()) {
        (true, false) => Ok(flat),
        (false, true) => Ok(nested),
        (true, true) => Err(LoadError::new(format!(
            "import `{}` is ambiguous between {} and {}",
            parts.join("."),
            flat.display(),
            nested.display()
        ))),
        (false, false) => Err(LoadError::new(format!(
            "import `{}` finds neither {} nor {}",
            parts.join("."),
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
) -> Result<Interface, LoadError> {
    let namespace = symbols.text(namespace).to_string();
    let mut own = Interface::default();
    for item in &module.items {
        match item {
            Item::Data(data) => declare_data(&mut own, data, source, &namespace, symbols)?,
            Item::Signature(signature) => {
                declare_value(&mut own, signature.name, source, &namespace, symbols)?;
            }
            Item::Clause(clause) => {
                declare_value(&mut own, clause.name, source, &namespace, symbols)?;
            }
            Item::Header(_) | Item::Import(_) | Item::Exports(_) => {}
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
) -> Result<(), LoadError> {
    let local = symbols.intern(data.name.text(source));
    if own.types.contains_key(&local) {
        return Err(LoadError::new(format!(
            "type `{}` is declared more than once",
            data.name.text(source)
        )));
    }
    let canonical = symbols.intern(&format!("{namespace}$${}", data.name.text(source)));
    let mut binding = TypeBinding {
        canonical,
        constructors: HashMap::new(),
        methods: HashMap::new(),
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
                insert_unique(
                    &mut own.constructors,
                    spelling,
                    canonical,
                    symbols,
                    "constructor",
                )?;
                binding.constructors.insert(spelling, canonical);
            }
        }
        DataRepresentation::Wrapper(_) => {
            let canonical = symbols.intern(&format!(
                "{namespace}$${}$${}",
                data.name.text(source),
                data.name.text(source)
            ));
            binding.constructors.insert(local, canonical);
            insert_unique(
                &mut own.constructors,
                local,
                canonical,
                symbols,
                "constructor",
            )?;
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
            return Err(LoadError::new(format!(
                "method `{}` is declared by conflicting definitions",
                method_name.text(source)
            )));
        }
        binding.methods.insert(spelling, canonical);
    }
    own.types.insert(local, binding);
    Ok(())
}

fn declare_value(
    own: &mut Interface,
    name: Name,
    source: &str,
    namespace: &str,
    symbols: &mut Symbols,
) -> Result<(), LoadError> {
    let local = symbols.intern(name.text(source));
    let canonical = symbols.intern(&format!("{namespace}$${}", name.text(source)));
    if let Some(previous) = own.values.get(&local)
        && *previous != canonical
    {
        return Err(LoadError::new(format!(
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
) -> Result<Interface, LoadError> {
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
            let mut visible = binding.clone();
            if !export.constructors {
                visible.constructors.clear();
            }
            public.types.insert(local, visible.clone());
            if export.constructors {
                for (&name, &canonical) in &visible.constructors {
                    insert_unique(
                        &mut public.constructors,
                        name,
                        canonical,
                        symbols,
                        "exported constructor",
                    )?;
                }
            }
        }
        if !scope.values.contains_key(&local) && !scope.types.contains_key(&local) {
            return Err(LoadError::new(format!(
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
) -> Result<(), LoadError> {
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
                return Err(LoadError::new(format!(
                    "imported type `{}` conflicts with an existing type",
                    symbols.text(local)
                )));
            }
            if exposure.constructors {
                for (&name, &canonical) in &imported.constructors {
                    insert_unique(
                        &mut scope.constructors,
                        name,
                        canonical,
                        symbols,
                        "imported constructor",
                    )?;
                }
            }
            scope.types.insert(local, imported);
            found = true;
        }
        if !found {
            return Err(LoadError::new(format!(
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
) -> Result<(), LoadError> {
    for (&local, &canonical) in from {
        if let Some(previous) = into.get(&local)
            && *previous != canonical
        {
            return Err(LoadError::new(format!(
                "{context} binds {kind} `{}` more than once",
                symbols.text(local)
            )));
        }
        into.insert(local, canonical);
    }
    Ok(())
}

fn insert_unique(
    map: &mut HashMap<Symbol, Symbol>,
    local: Symbol,
    canonical: Symbol,
    symbols: &Symbols,
    kind: &str,
) -> Result<(), LoadError> {
    if let Some(previous) = map.get(&local)
        && *previous != canonical
    {
        return Err(LoadError::new(format!(
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
            "numbers.ori",
            "exports {Nat.*}\nNat : [Zero Succ(Nat)]\nsecret() -> Zero\n",
        );
        let entry = fixture.write("main.ori", "import numbers {Nat.*}\nid(x) -> Succ(x)\n");
        let loaded = load(&[entry], None).unwrap();
        let entry = loaded.module(loaded.entries[0]);
        let succ = loaded.symbols.find("Succ").unwrap();
        let secret = loaded.symbols.find("secret").unwrap();
        assert!(entry.scope.constructors.contains_key(&succ));
        assert!(!entry.scope.values.contains_key(&secret));
    }

    #[test]
    fn private_names_cannot_be_imported() {
        let fixture = Fixture::new();
        fixture.write("hidden.ori", "secret() -> 0\n");
        let entry = fixture.write("main.ori", "import hidden {secret}\nmain() -> secret()\n");
        let error = load(&[entry], None).unwrap_err();
        assert!(error.message.contains("not exported"));
    }

    #[test]
    fn import_cycles_are_rejected_before_reloading_a_source() {
        let fixture = Fixture::new();
        let first = fixture.write("first.ori", "import second {}\n");
        fixture.write("second.ori", "import first {}\n");
        let error = load(&[first], None).unwrap_err();
        assert!(error.message.contains("import cycle"));
    }

    #[test]
    fn standard_namespaces_are_path_stable() {
        let fixture = Fixture::new();
        fixture.write("nat.ori", "exports {Nat.*}\nNat : [Zero Succ(Nat)]\n");
        let root = fixture.write(
            "standard.ori",
            "lib {}\nimport nat {Nat.*}\nexports {Nat.*}\n",
        );
        let entry = fixture.write("main.ori", "id(x) -> x\n");
        let loaded = load(&[entry], Some(&root)).unwrap();
        let nat = loaded
            .modules
            .iter()
            .find(|module| module.path.ends_with("nat.ori"))
            .unwrap();
        assert_eq!(loaded.symbols.text(nat.namespace), "Mstd_nat");
    }
}
