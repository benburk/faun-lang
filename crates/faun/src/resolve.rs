//! Resolve module-local source names into canonical globals and compact locals.

// Resolution is a pair of cohesive exhaustive walks. Keeping each match whole
// makes omissions visible when surface syntax gains a variant.
#![allow(clippy::too_many_lines)]

use std::collections::{HashMap, HashSet};
use std::fmt;

use super::ast as s;
use super::diagnostic::{Advice, Advised, Diagnostic, Location, LowerError, Unplaced};
use super::hir as h;
use super::literal;
use super::modules::{Interface, LoadedModule, LoadedProgram, ModuleId, TypeBinding};
use super::{Source, SourceId, Sources, Symbol, Symbols};

#[derive(Clone, Debug)]
pub struct ResolvedProgram<P = h::Program> {
    pub(crate) sites: h::Sites,
    pub sources: Sources,
    pub symbols: Symbols,
    pub program: P,
    /// The entry's package, whose every definition is compiled, rather than
    /// only what reaches into it.
    pub package: Vec<ModuleId>,
    /// Each module's source, by module.
    module_sources: Vec<SourceId>,
}

impl<P> ResolvedProgram<P> {
    /// Replace the representation while retaining its source and symbol owners.
    pub(crate) fn map<Q>(mut self, pass: impl FnOnce(P, &mut h::Sites) -> Q) -> ResolvedProgram<Q> {
        ResolvedProgram {
            program: pass(self.program, &mut self.sites),
            sites: self.sites,
            sources: self.sources,
            symbols: self.symbols,
            package: self.package,
            module_sources: self.module_sources,
        }
    }

    /// A diagnostic at `span` in `module`.
    ///
    /// # Panics
    /// If `module` is not one of this program's.
    #[must_use]
    pub fn diagnostic(&self, module: ModuleId, span: s::Span, message: String) -> Diagnostic {
        Diagnostic::new(message).at(self.source(module), span)
    }

    /// A lowering failure as a diagnostic, at its place where it names one.
    ///
    /// # Panics
    /// If it names a module not one of this program's.
    pub(crate) fn told(&self, error: LowerError) -> Diagnostic {
        let diagnostic = match error.at {
            Some((module, span)) => self.diagnostic(module, span, error.message),
            None => Diagnostic::new(error.message),
        };
        let mut diagnostic = diagnostic.advised(*error.advice);
        for ((module, span), text) in error.secondary {
            diagnostic = diagnostic.secondary(self.source(module), span, text);
        }
        diagnostic
    }

    /// Where `span` is in `module`.
    ///
    /// # Panics
    /// If `module` is not one of this program's.
    #[must_use]
    pub fn location(&self, module: ModuleId, span: s::Span) -> Location {
        Location::of(self.source(module), span)
    }

    pub(crate) fn source(&self, module: ModuleId) -> &Source {
        self.sources
            .get(self.module_sources[module.index()])
            .expect("a resolved module has a source")
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResolveError {
    pub module: ModuleId,
    pub span: s::Span,
    pub message: String,
    pub advice: Advice,
}

impl Advised for ResolveError {
    fn advice(&mut self) -> &mut Advice {
        &mut self.advice
    }
}

impl fmt::Display for ResolveError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for ResolveError {}

/// Resolve every loaded module without mutating or concatenating its surface AST.
///
/// # Errors
///
/// Reports an unknown or duplicate local, global, constructor, type, or method,
/// at the span it is written.
///
/// # Panics
///
/// Panics only if a [`LoadedProgram`] was manually built with a module whose
/// source identity is absent from its source collection.
pub fn resolve_names(mut loaded: LoadedProgram) -> Result<ResolvedProgram, Diagnostic> {
    let prelude = loaded.module(loaded.prelude).public.clone();
    let mut modules = Vec::with_capacity(loaded.modules.len());
    let mut sites = h::Sites::default();
    let mut aliases = HashMap::new();
    let mut constraint_aliases = HashMap::new();
    let mut scopes = Vec::with_capacity(loaded.modules.len());
    for module in &loaded.modules {
        let mut scope = prelude.clone();
        scope.merge(&module.scope).map_err(|clash| {
            let name = loaded.symbols.text(clash.name);
            Diagnostic::new(format!("module scope binds {} `{name}` twice", clash.kind))
        })?;
        scopes.push(scope);
    }
    let values = values(&loaded, &scopes);
    for (module, scope) in loaded.modules.iter().zip(&scopes) {
        let source = loaded
            .sources
            .get(module.source)
            .expect("loaded module has source")
            .text();
        let resolved = resolve_module(
            module,
            source,
            (scope, &values),
            (&mut loaded.symbols, &mut sites),
            (&mut aliases, &mut constraint_aliases),
        );
        modules.push(resolved.map_err(|error| located(&loaded, error))?);
    }
    expand_aliases(
        &mut modules,
        (&aliases, &constraint_aliases),
        &mut loaded.symbols,
    )
    .map_err(|error| located(&loaded, error))?;
    crate::builders::desugar(&mut modules, &mut sites);
    Ok(ResolvedProgram {
        sites,
        module_sources: loaded.modules.iter().map(|module| module.source).collect(),
        package: loaded.package,
        sources: loaded.sources,
        symbols: loaded.symbols,
        program: h::Program { modules },
    })
}

/// The definitions written `name = value`, which take no parameters: a
/// use of one is its value, and calling it is refused.
type Values = HashSet<Symbol>;

/// Every value the program defines, top-level or a type's.
fn values(loaded: &LoadedProgram, scopes: &[Interface]) -> Values {
    let mut values = Values::new();
    for (module, scope) in loaded.modules.iter().zip(scopes) {
        let source = loaded
            .sources
            .get(module.source)
            .expect("loaded module has source")
            .text();
        let spelled = |name: s::Name| loaded.symbols.find(name.text(source));
        for item in &module.syntax.items {
            match item {
                s::Item::Clause(clause) if clause.patterns.is_empty() => {
                    let global = spelled(clause.name).and_then(|name| scope.values.get(&name));
                    values.extend(global);
                }
                s::Item::Data(data) => {
                    let Some(binding) = spelled(data.name).and_then(|name| scope.types.get(&name))
                    else {
                        continue;
                    };
                    for method in &data.methods {
                        if let s::MethodItem::Clause(clause) = method
                            && clause.patterns.is_empty()
                        {
                            let method =
                                spelled(clause.name).and_then(|name| binding.methods.get(&name));
                            values.extend(method);
                        }
                    }
                }
                _ => {}
            }
        }
    }
    values
}

/// A resolve error as a diagnostic at the place it names.
fn located(loaded: &LoadedProgram, error: ResolveError) -> Diagnostic {
    let module = loaded.module(error.module);
    let source = loaded
        .sources
        .get(module.source)
        .expect("loaded module has source");
    Diagnostic::new(error.message)
        .at(source, error.span)
        .advised(error.advice)
}

/// An alias, `Name = type` or `Name(a) = type`: its parameters, and the
/// type it names, resolved in the module that wrote it.
struct Alias {
    parameters: Vec<Symbol>,
    ty: h::Type,
    module: ModuleId,
    span: s::Span,
}

type Aliases = HashMap<Symbol, Alias>;

/// A constraint alias, `Name(a) = where ...`: its parameters, and what it
/// requires of them, applications of other aliases included.
struct ConstraintAlias {
    parameters: Vec<Symbol>,
    constraints: Vec<h::Constraint>,
    module: ModuleId,
    span: s::Span,
}

type ConstraintAliases = HashMap<Symbol, ConstraintAlias>;

fn resolve_module(
    module: &LoadedModule,
    source: &str,
    (scope, values): (&Interface, &Values),
    (symbols, sites): (&mut Symbols, &mut h::Sites),
    (aliases, constraint_aliases): (&mut Aliases, &mut ConstraintAliases),
) -> Result<h::Module, ResolveError> {
    let mut items = Vec::new();
    let mut expectations = Vec::new();
    for item in &module.syntax.items {
        match item {
            s::Item::Data(data) => items.push(h::Item::Data(resolve_data(
                module.id,
                data,
                source,
                (scope, values),
                symbols,
                sites,
            )?)),
            s::Item::Signature(signature) => {
                let name = global_value(module.id, signature.name, source, scope, symbols)?;
                items.push(h::Item::Signature(resolve_signature(
                    module.id, signature, name, source, scope, symbols,
                )?));
            }
            s::Item::Clause(clause) => {
                let name = global_value(module.id, clause.name, source, scope, symbols)?;
                let clauses = resolve_clauses(
                    module.id,
                    clause,
                    name,
                    source,
                    (scope, values),
                    None,
                    (symbols, sites),
                )?;
                items.extend(clauses.into_iter().map(h::Item::Clause));
            }
            s::Item::Expect(clause) => {
                let name = symbols.intern(&format!(
                    "{}$$expect {}",
                    symbols.text(module.namespace),
                    expectations.len() + 1
                ));
                let spelling = symbols.intern("expect");
                let boolean = symbols.intern("Bool");
                let Some(boolean) = scope.types.get(&boolean) else {
                    return Err(error(
                        module.id,
                        clause.span,
                        "an `expect` answers a `Bool`, and none is in scope",
                    ));
                };
                items.push(h::Item::Signature(h::SignatureDecl {
                    span: clause.span,
                    name,
                    spelling,
                    parameters: Vec::new(),
                    result: h::Type::Named(boolean.canonical, Vec::new()),
                    constraints: Vec::new(),
                }));
                items.push(h::Item::Clause(resolve_clause(
                    module.id,
                    clause,
                    name,
                    source,
                    (scope, values),
                    (None, None),
                    (symbols, sites),
                )?));
                expectations.push(name);
            }
            s::Item::Alias(alias) => {
                let local = symbols.intern(alias.name.text(source));
                let canonical = scope.types[&local].canonical;
                let ty = written_type(module.id, &alias.ty, source, scope, symbols)?;
                let parameters = alias_parameters(module.id, alias, &ty, source, symbols)?;
                aliases.insert(
                    canonical,
                    Alias {
                        parameters,
                        ty,
                        module: module.id,
                        span: alias.span,
                    },
                );
            }
            s::Item::Constraints(alias) => {
                let local = symbols.intern(alias.name.text(source));
                let canonical = scope.types[&local].canonical;
                let mut parameters = Vec::with_capacity(alias.parameters.len());
                for parameter in &alias.parameters {
                    let parameter = symbols.intern(parameter.text(source));
                    if parameters.contains(&parameter) {
                        return Err(error(
                            module.id,
                            alias.span,
                            format!(
                                "constraint alias `{}` names its parameter `{}` twice",
                                alias.name.text(source),
                                symbols.text(parameter)
                            ),
                        ));
                    }
                    parameters.push(parameter);
                }
                let constraints = alias
                    .constraints
                    .iter()
                    .map(|constraint| {
                        resolve_constraint(module.id, constraint, source, scope, symbols)
                    })
                    .collect::<Result<_, _>>()?;
                constraint_aliases.insert(
                    canonical,
                    ConstraintAlias {
                        parameters,
                        constraints,
                        module: module.id,
                        span: alias.span,
                    },
                );
            }
            s::Item::Header(_) | s::Item::Import(_) | s::Item::Exports(_) => {}
        }
    }
    let mut visible_methods: Vec<_> = scope
        .types
        .values()
        .flat_map(|binding| binding.methods.values().copied())
        .collect();
    visible_methods.sort_unstable();
    visible_methods.dedup();
    Ok(h::Module {
        source: module.id,
        visible_methods,
        items,
        expectations,
    })
}

/// An alias's parameters, each once, where its type names each and no
/// other variable. A transparent alias cannot keep types apart, so one
/// whose parameter goes unused would make `Id(Str)` and `Id(Bool)` one type.
fn alias_parameters(
    module: ModuleId,
    alias: &s::AliasDecl,
    ty: &h::Type,
    source: &str,
    symbols: &mut Symbols,
) -> Result<Vec<Symbol>, ResolveError> {
    let name = alias.name.text(source);
    let mut parameters = Vec::with_capacity(alias.params.len());
    for parameter in &alias.params {
        let parameter = symbols.intern(parameter.text(source));
        if parameters.contains(&parameter) {
            let message = format!(
                "alias `{name}` names its parameter `{}` twice",
                symbols.text(parameter)
            );
            return Err(error(module, alias.span, message));
        }
        parameters.push(parameter);
    }
    let mut named = Vec::new();
    variables(ty, &mut named);
    if let Some(stray) = named.iter().find(|variable| !parameters.contains(variable)) {
        let stray = symbols.text(*stray);
        let message = format!("`{stray}` is not among the parameters of alias `{name}`");
        return Err(error(module, alias.span, message).help(format!(
            "write it among them, `{name}({stray})`, or name a type"
        )));
    }
    if let Some(unused) = parameters
        .iter()
        .find(|parameter| !named.contains(parameter))
    {
        let unused = symbols.text(*unused);
        let message = format!("alias `{name}` never uses its parameter `{unused}`");
        return Err(error(module, alias.span, message).help(
            "an alias is the type it names, so it cannot tell types apart by a parameter it \
             leaves out: declare a type with `:` to keep them apart",
        ));
    }
    Ok(parameters)
}

/// Every type variable `ty` names, into `found`.
fn variables(ty: &h::Type, found: &mut Vec<Symbol>) {
    let inner: Vec<&h::Type> = match ty {
        h::Type::Variable(variable) => {
            if !found.contains(variable) {
                found.push(*variable);
            }
            return;
        }
        h::Type::Hole => return,
        h::Type::Named(_, types) | h::Type::Tuple(types) => types.iter().collect(),
        h::Type::Function(parameters, result) => parameters
            .iter()
            .chain(std::iter::once(&**result))
            .collect(),
        h::Type::Variants(tags) => tags.iter().flat_map(|tag| &tag.fields).collect(),
        h::Type::Record(fields, _) => fields.iter().map(|(_, field)| field).collect(),
    };
    for each in inner {
        variables(each, found);
    }
}

/// `ty` with each variable `replacements` names replaced.
fn substituted(ty: &h::Type, replacements: &HashMap<Symbol, h::Type>) -> h::Type {
    let each = |types: &[h::Type]| {
        types
            .iter()
            .map(|ty| substituted(ty, replacements))
            .collect()
    };
    match ty {
        h::Type::Variable(variable) => replacements
            .get(variable)
            .cloned()
            .unwrap_or_else(|| ty.clone()),
        h::Type::Named(name, arguments) => h::Type::Named(*name, each(arguments)),
        h::Type::Function(parameters, result) => h::Type::Function(
            each(parameters),
            Box::new(substituted(result, replacements)),
        ),
        h::Type::Variants(tags) => h::Type::Variants(
            tags.iter()
                .map(|tag| h::ConstructorDecl {
                    name: tag.name,
                    fields: each(&tag.fields),
                })
                .collect(),
        ),
        h::Type::Record(fields, open) => h::Type::Record(
            fields
                .iter()
                .map(|(name, field)| (*name, substituted(field, replacements)))
                .collect(),
            *open,
        ),
        h::Type::Tuple(members) => h::Type::Tuple(each(members)),
        h::Type::Hole => h::Type::Hole,
    }
}

/// Replace every alias in the program's written types by what it names.
/// An alias is transparent: `Point = {x: Nat, y: Nat}` is the record type,
/// so a bare record already has it, and nothing downstream sees the alias.
fn expand_aliases(
    modules: &mut [h::Module],
    (aliases, constraint_aliases): (&Aliases, &ConstraintAliases),
    symbols: &mut Symbols,
) -> Result<(), ResolveError> {
    // Every constraint alias is expanded once over its own parameters, so
    // one applying itself, or applied wrongly, is refused where it is
    // declared whether or not anything applies it.
    for (&name, alias) in constraint_aliases {
        let applied = h::Constraint::Alias {
            name,
            arguments: alias
                .parameters
                .iter()
                .map(|&parameter| h::Type::Variable(parameter))
                .collect(),
        };
        expand_constraints(&[applied], constraint_aliases, symbols)
            .map_err(|message| error(alias.module, alias.span, message))?;
    }
    // Each alias is expanded over its own parameters, so one naming
    // itself is refused where it is declared.
    let mut expanded = Aliases::new();
    for (&name, alias) in aliases {
        let own = alias
            .parameters
            .iter()
            .map(|&parameter| h::Type::Variable(parameter))
            .collect();
        let ty = expand(
            &h::Type::Named(name, own),
            aliases,
            symbols,
            &mut Vec::new(),
        )
        .map_err(|message| error(alias.module, alias.span, message))?;
        expanded.insert(
            name,
            Alias {
                parameters: alias.parameters.clone(),
                ty,
                module: alias.module,
                span: alias.span,
            },
        );
    }
    for module in modules {
        let id = module.source;
        for item in &mut module.items {
            match item {
                h::Item::Data(data) => {
                    let span = data.span;
                    let fields = data
                        .constructors
                        .iter_mut()
                        .flat_map(|constructor| &mut constructor.fields)
                        .chain(data.wrapper.iter_mut().map(|wrapper| &mut wrapper.field));
                    for field in fields {
                        *field = expand(field, &expanded, symbols, &mut Vec::new())
                            .and_then(|field| Ok(typed(field, constraint_aliases, symbols)?))
                            .map_err(|message| error(id, span, message))?;
                    }
                    for method in &mut data.methods {
                        if let h::MethodItem::Signature(signature) = method {
                            expand_signature(signature, (&expanded, constraint_aliases), symbols)
                                .map_err(|message| error(id, signature.span, message))?;
                        }
                    }
                }
                h::Item::Signature(signature) => {
                    expand_signature(signature, (&expanded, constraint_aliases), symbols)
                        .map_err(|message| error(id, signature.span, message))?;
                }
                h::Item::Clause(_) => {}
            }
        }
    }
    Ok(())
}

fn expand_signature(
    signature: &mut h::SignatureDecl,
    (aliases, constraint_aliases): (&Aliases, &ConstraintAliases),
    symbols: &mut Symbols,
) -> Result<(), Unplaced> {
    signature.constraints =
        expand_constraints(&signature.constraints, constraint_aliases, symbols)?;
    let written = signature
        .parameters
        .iter_mut()
        .chain(std::iter::once(&mut signature.result))
        .chain(
            signature
                .constraints
                .iter_mut()
                .flat_map(|constraint| match constraint {
                    h::Constraint::Member { ty, .. } => std::slice::from_mut(ty),
                    h::Constraint::Alias { arguments, .. } => arguments.as_mut_slice(),
                }),
        );
    for ty in written {
        *ty = typed(
            expand(ty, aliases, symbols, &mut Vec::new())?,
            constraint_aliases,
            symbols,
        )?;
    }
    // `f : Step`, where `Step` is a function type, declares the function
    // `Step` is, as it would written out: its parameters are the function's.
    if signature.parameters.is_empty()
        && let h::Type::Function(parameters, result) = &signature.result
    {
        let (parameters, result) = (parameters.clone(), (**result).clone());
        signature.parameters = parameters;
        signature.result = result;
    }
    Ok(())
}

/// `ty`, where it names no constraint alias as a type.
fn typed(
    ty: h::Type,
    constraint_aliases: &ConstraintAliases,
    symbols: &Symbols,
) -> Result<h::Type, String> {
    fn named(ty: &h::Type, constraint_aliases: &ConstraintAliases) -> Option<Symbol> {
        let each = |types: &[h::Type]| types.iter().find_map(|ty| named(ty, constraint_aliases));
        match ty {
            h::Type::Named(name, _) if constraint_aliases.contains_key(name) => Some(*name),
            h::Type::Named(_, arguments) | h::Type::Tuple(arguments) => each(arguments),
            h::Type::Variable(_) | h::Type::Hole => None,
            h::Type::Function(parameters, result) => {
                each(parameters).or_else(|| named(result, constraint_aliases))
            }
            h::Type::Variants(tags) => tags.iter().find_map(|tag| each(&tag.fields)),
            h::Type::Record(fields, _) => fields
                .iter()
                .find_map(|(_, field)| named(field, constraint_aliases)),
        }
    }
    named(&ty, constraint_aliases).map_or(Ok(ty), |alias| {
        Err(format!(
            "`{}` is a constraint alias, which is applied in a `where` clause and is no type",
            spelled(alias, symbols)
        ))
    })
}

/// A `where` clause with each constraint alias it applies replaced by the
/// members that alias requires. A variable an alias's body names besides
/// its parameters is the alias's own: renamed apart from the clause's, and
/// the same in every constraint of one application, so an application
/// written twice requires the same thing twice. A member required twice
/// alike is required once; required twice differently, it is refused.
fn expand_constraints(
    written: &[h::Constraint],
    aliases: &ConstraintAliases,
    symbols: &mut Symbols,
) -> Result<Vec<h::Constraint>, String> {
    let mut expansion = Expansion {
        aliases,
        applications: Vec::new(),
        expanding: Vec::new(),
        through: None,
        members: Vec::new(),
    };
    for constraint in written {
        expansion.add(constraint.clone(), symbols)?;
    }
    Ok(expansion.members)
}

struct Expansion<'a> {
    aliases: &'a ConstraintAliases,
    /// Each application met, by alias and arguments: where it stands here
    /// names the variables of its own.
    applications: Vec<(Symbol, String)>,
    /// The aliases being expanded, innermost last.
    expanding: Vec<Symbol>,
    /// The outermost application being expanded, where it is of an alias of
    /// one parameter at a variable: the alias, and the variable.
    through: Option<(Symbol, Symbol)>,
    /// The members required so far, each once.
    members: Vec<h::Constraint>,
}

impl Expansion<'_> {
    fn add(&mut self, constraint: h::Constraint, symbols: &mut Symbols) -> Result<(), String> {
        let (variable, member, ty) = match constraint {
            h::Constraint::Member {
                variable,
                member,
                ty,
                ..
            } => (variable, member, ty),
            h::Constraint::Alias { name, arguments } => {
                return self.apply(name, &arguments, symbols);
            }
        };
        let earlier = self.members.iter().find_map(|required| match required {
            h::Constraint::Member {
                variable: other,
                member: named,
                ty,
                ..
            } if *other == variable && *named == member => Some(ty),
            _ => None,
        });
        match earlier {
            Some(earlier) if *earlier == ty => Ok(()),
            Some(_) => Err(format!(
                "`{}.{}` is required twice, at two different types",
                symbols.text(variable),
                symbols.text(member)
            )),
            None => {
                let through = self
                    .through
                    .filter(|&(_, applied)| applied == variable)
                    .map(|(alias, _)| alias);
                self.members.push(h::Constraint::Member {
                    variable,
                    member,
                    ty,
                    through,
                });
                Ok(())
            }
        }
    }

    fn apply(
        &mut self,
        name: Symbol,
        arguments: &[h::Type],
        symbols: &mut Symbols,
    ) -> Result<(), String> {
        let aliases = self.aliases;
        let spelled = spelled(name, symbols);
        let alias = aliases
            .get(&name)
            .ok_or_else(|| format!("`{spelled}` is not a constraint alias"))?;
        if alias.parameters.len() != arguments.len() {
            return Err(format!(
                "constraint alias `{spelled}` takes {} arguments, and is given {}",
                alias.parameters.len(),
                arguments.len()
            ));
        }
        if self.expanding.contains(&name) {
            return Err(format!("constraint alias `{spelled}` applies itself"));
        }
        let application = (name, format!("{arguments:?}"));
        let index = self
            .applications
            .iter()
            .position(|known| *known == application)
            .unwrap_or_else(|| {
                self.applications.push(application);
                self.applications.len() - 1
            });
        let mut substitution: HashMap<Symbol, h::Type> = alias
            .parameters
            .iter()
            .copied()
            .zip(arguments.iter().cloned())
            .collect();
        let mut own = Vec::new();
        for constraint in &alias.constraints {
            match constraint {
                h::Constraint::Member { variable, ty, .. } => {
                    own.push(*variable);
                    type_variables(ty, &mut own);
                }
                h::Constraint::Alias { arguments, .. } => {
                    for argument in arguments {
                        type_variables(argument, &mut own);
                    }
                }
            }
        }
        for variable in own {
            // A quote is in no identifier, so the renamed variable is no
            // name a clause could write.
            substitution.entry(variable).or_insert_with(|| {
                let renamed = format!("{}'{index}", symbols.text(variable));
                h::Type::Variable(symbols.intern(&renamed))
            });
        }
        let outermost = self.expanding.is_empty();
        if outermost && let [h::Type::Variable(applied)] = arguments {
            self.through = Some((name, *applied));
        }
        self.expanding.push(name);
        for constraint in &alias.constraints {
            let constraint = match constraint {
                h::Constraint::Member {
                    variable,
                    member,
                    ty,
                    ..
                } => {
                    let h::Type::Variable(variable) = substitution[variable] else {
                        return Err(format!(
                            "constraint alias `{spelled}` bounds `{}`, which is given a type rather than a type variable",
                            symbols.text(*variable)
                        ));
                    };
                    h::Constraint::Member {
                        variable,
                        member: *member,
                        ty: substitute(ty, &substitution),
                        through: None,
                    }
                }
                h::Constraint::Alias { name, arguments } => h::Constraint::Alias {
                    name: *name,
                    arguments: arguments
                        .iter()
                        .map(|argument| substitute(argument, &substitution))
                        .collect(),
                },
            };
            self.add(constraint, symbols)?;
        }
        self.expanding.pop();
        if outermost {
            self.through = None;
        }
        Ok(())
    }
}

/// A declared name as it was written, without its module's prefix.
fn spelled(name: Symbol, symbols: &Symbols) -> String {
    let text = symbols.text(name);
    text.rsplit_once("$$")
        .map_or(text, |(_, spelled)| spelled)
        .to_owned()
}

/// Every type variable `ty` names, in the order written.
fn type_variables(ty: &h::Type, out: &mut Vec<Symbol>) {
    match ty {
        h::Type::Variable(variable) => out.push(*variable),
        h::Type::Named(_, arguments) | h::Type::Tuple(arguments) => {
            for argument in arguments {
                type_variables(argument, out);
            }
        }
        h::Type::Function(parameters, result) => {
            for parameter in parameters {
                type_variables(parameter, out);
            }
            type_variables(result, out);
        }
        h::Type::Variants(tags) => {
            for field in tags.iter().flat_map(|tag| &tag.fields) {
                type_variables(field, out);
            }
        }
        h::Type::Record(fields, _) => {
            for (_, field) in fields {
                type_variables(field, out);
            }
        }
        h::Type::Hole => {}
    }
}

/// `ty` with each variable `substitution` names replaced.
fn substitute(ty: &h::Type, substitution: &HashMap<Symbol, h::Type>) -> h::Type {
    let each = |types: &[h::Type]| -> Vec<h::Type> {
        types
            .iter()
            .map(|ty| substitute(ty, substitution))
            .collect()
    };
    match ty {
        h::Type::Variable(variable) => substitution
            .get(variable)
            .cloned()
            .unwrap_or_else(|| ty.clone()),
        h::Type::Hole => h::Type::Hole,
        h::Type::Named(name, arguments) => h::Type::Named(*name, each(arguments)),
        h::Type::Tuple(members) => h::Type::Tuple(each(members)),
        h::Type::Function(parameters, result) => {
            h::Type::Function(each(parameters), Box::new(substitute(result, substitution)))
        }
        h::Type::Variants(tags) => h::Type::Variants(
            tags.iter()
                .map(|tag| h::ConstructorDecl {
                    name: tag.name,
                    fields: each(&tag.fields),
                })
                .collect(),
        ),
        h::Type::Record(fields, open) => h::Type::Record(
            fields
                .iter()
                .map(|(name, field)| (*name, substitute(field, substitution)))
                .collect(),
            *open,
        ),
    }
}

/// `ty` with every alias replaced by its definition, refusing an alias
/// given arguments or one reached again while it is being expanded.
fn expand(
    ty: &h::Type,
    aliases: &Aliases,
    symbols: &Symbols,
    expanding: &mut Vec<Symbol>,
) -> Result<h::Type, Unplaced> {
    let spelled = |name: Symbol| {
        let text = symbols.text(name);
        text.rsplit_once("$$")
            .map_or(text, |(_, spelled)| spelled)
            .to_owned()
    };
    Ok(match ty {
        h::Type::Named(name, arguments) if aliases.contains_key(name) => {
            let alias = &aliases[name];
            if arguments.len() != alias.parameters.len() {
                let message = match alias.parameters.len() {
                    0 => format!("`{}` is an alias and takes no arguments", spelled(*name)),
                    wanted => format!(
                        "alias `{}` takes {wanted} type{}, and is given {}",
                        spelled(*name),
                        if wanted == 1 { "" } else { "s" },
                        arguments.len()
                    ),
                };
                return Err(Unplaced::from(message));
            }
            if expanding.contains(name) {
                let message = format!("alias `{}` names itself", spelled(*name));
                return Err(Unplaced::from(message).help("declare a recursive type with `:`"));
            }
            let arguments = arguments
                .iter()
                .map(|argument| expand(argument, aliases, symbols, expanding))
                .collect::<Result<Vec<_>, _>>()?;
            expanding.push(*name);
            let definition = expand(&alias.ty, aliases, symbols, expanding)?;
            expanding.pop();
            let replacements = alias.parameters.iter().copied().zip(arguments).collect();
            substituted(&definition, &replacements)
        }
        h::Type::Named(name, arguments) => h::Type::Named(
            *name,
            arguments
                .iter()
                .map(|argument| expand(argument, aliases, symbols, expanding))
                .collect::<Result<_, _>>()?,
        ),
        h::Type::Variable(_) | h::Type::Hole => ty.clone(),
        h::Type::Function(parameters, result) => h::Type::Function(
            parameters
                .iter()
                .map(|parameter| expand(parameter, aliases, symbols, expanding))
                .collect::<Result<_, _>>()?,
            Box::new(expand(result, aliases, symbols, expanding)?),
        ),
        h::Type::Variants(tags) => h::Type::Variants(
            tags.iter()
                .map(|tag| {
                    Ok(h::ConstructorDecl {
                        name: tag.name,
                        fields: tag
                            .fields
                            .iter()
                            .map(|field| expand(field, aliases, symbols, expanding))
                            .collect::<Result<_, Unplaced>>()?,
                    })
                })
                .collect::<Result<_, Unplaced>>()?,
        ),
        h::Type::Record(fields, open) => h::Type::Record(
            fields
                .iter()
                .map(|(name, field)| Ok((*name, expand(field, aliases, symbols, expanding)?)))
                .collect::<Result<_, Unplaced>>()?,
            *open,
        ),
        h::Type::Tuple(members) => h::Type::Tuple(
            members
                .iter()
                .map(|member| expand(member, aliases, symbols, expanding))
                .collect::<Result<_, Unplaced>>()?,
        ),
    })
}

fn resolve_data(
    module: ModuleId,
    data: &s::DataDecl,
    source: &str,
    (scope, values): (&Interface, &Values),
    symbols: &mut Symbols,
    sites: &mut h::Sites,
) -> Result<h::DataDecl, ResolveError> {
    let local = symbols
        .find(data.name.text(source))
        .expect("declaration collection interns type names");
    let binding = scope.types.get(&local).ok_or_else(|| {
        error(
            module,
            data.name.0,
            format!("unknown type `{}`", data.name.text(source)),
        )
    })?;
    let parameters = data
        .params
        .iter()
        .map(|parameter| symbols.intern(parameter.text(source)))
        .collect();
    let (constructors, wrapper) = match &data.representation {
        s::DataRepresentation::Sum(constructors) => (
            constructors
                .iter()
                .map(|constructor| {
                    let spelling = symbols.intern(constructor.name.text(source));
                    let name = binding.constructors[&spelling];
                    let fields = constructor
                        .fields
                        .iter()
                        .map(|field| written_type(module, field, source, scope, symbols))
                        .collect::<Result<_, _>>()?;
                    Ok(h::ConstructorDecl { name, fields })
                })
                .collect::<Result<_, ResolveError>>()?,
            None,
        ),
        s::DataRepresentation::Wrapper(representation) => (
            Vec::new(),
            Some(h::WrapperDecl {
                constructor: binding.constructors[&local],
                field: written_type(module, representation, source, scope, symbols)?,
            }),
        ),
    };
    let mut methods = Vec::with_capacity(data.methods.len());
    for method in &data.methods {
        match method {
            s::MethodItem::Signature(signature) => {
                let name = method_name(module, signature.name, source, binding, symbols)?;
                methods.push(h::MethodItem::Signature(resolve_signature(
                    module, signature, name, source, scope, symbols,
                )?));
            }
            s::MethodItem::Clause(clause) => {
                let name = method_name(module, clause.name, source, binding, symbols)?;
                let clauses = resolve_clauses(
                    module,
                    clause,
                    name,
                    source,
                    (scope, values),
                    Some(binding),
                    (symbols, sites),
                )?;
                methods.extend(clauses.into_iter().map(h::MethodItem::Clause));
            }
        }
    }
    Ok(h::DataDecl {
        span: data.span,
        name: binding.canonical,
        parameters,
        constructors,
        wrapper,
        methods,
    })
}

fn resolve_signature(
    module: ModuleId,
    signature: &s::SignatureDecl,
    name: Symbol,
    source: &str,
    scope: &Interface,
    symbols: &mut Symbols,
) -> Result<h::SignatureDecl, ResolveError> {
    Ok(h::SignatureDecl {
        span: signature.span,
        name,
        spelling: symbols.intern(signature.name.text(source)),
        parameters: signature
            .parameters
            .iter()
            .map(|ty| resolve_type(module, ty, source, scope, symbols))
            .collect::<Result<_, _>>()?,
        result: resolve_type(module, &signature.result, source, scope, symbols)?,
        constraints: signature
            .constraints
            .iter()
            .map(|constraint| resolve_constraint(module, constraint, source, scope, symbols))
            .collect::<Result<_, ResolveError>>()?,
    })
}

fn resolve_constraint(
    module: ModuleId,
    constraint: &s::Constraint,
    source: &str,
    scope: &Interface,
    symbols: &mut Symbols,
) -> Result<h::Constraint, ResolveError> {
    Ok(match constraint {
        s::Constraint::Member {
            variable,
            member,
            parameters,
            result,
            ..
        } => h::Constraint::Member {
            variable: symbols.intern(variable.text(source)),
            member: symbols.intern(member.text(source)),
            ty: h::Type::Function(
                parameters
                    .iter()
                    .map(|ty| written_type(module, ty, source, scope, symbols))
                    .collect::<Result<_, _>>()?,
                Box::new(written_type(module, result, source, scope, symbols)?),
            ),
            through: None,
        },
        s::Constraint::Alias {
            span,
            name,
            arguments,
        } => {
            let spelling = symbols.intern(name.text(source));
            let binding = scope.types.get(&spelling).ok_or_else(|| {
                error(
                    module,
                    *span,
                    format!("unknown constraint alias `{}`", name.text(source)),
                )
            })?;
            h::Constraint::Alias {
                name: binding.canonical,
                arguments: arguments
                    .iter()
                    .map(|ty| written_type(module, ty, source, scope, symbols))
                    .collect::<Result<_, _>>()?,
            }
        }
    })
}

/// A type written anywhere but a function's own signature, which says
/// what it is in full: `_` leaves a signature's rest to its clauses, and
/// nothing else has clauses to leave it to.
fn written_type(
    module: ModuleId,
    ty: &s::Type,
    source: &str,
    scope: &Interface,
    symbols: &mut Symbols,
) -> Result<h::Type, ResolveError> {
    if let Some(span) = hole(ty) {
        return Err(error(
            module,
            span,
            "`_` stands for a type only in a function's signature, whose clauses say what it is",
        ));
    }
    resolve_type(module, ty, source, scope, symbols)
}

/// Where `ty` writes `_`, if it does.
fn hole(ty: &s::Type) -> Option<crate::ast::Span> {
    let each = |types: &[s::Type]| types.iter().find_map(hole);
    match ty {
        s::Type::Hole { span } => Some(*span),
        s::Type::Named { arguments, .. } => each(arguments),
        s::Type::Tuple { members, .. } => each(members),
        s::Type::Function {
            parameters, result, ..
        } => each(parameters).or_else(|| hole(result)),
        s::Type::Variants { constructors, .. } => constructors
            .iter()
            .find_map(|constructor| each(&constructor.fields)),
        s::Type::Record { fields, .. } => fields.iter().find_map(|(_, field)| hole(field)),
    }
}

fn resolve_type(
    module: ModuleId,
    ty: &s::Type,
    source: &str,
    scope: &Interface,
    symbols: &mut Symbols,
) -> Result<h::Type, ResolveError> {
    match ty {
        s::Type::Named {
            span,
            name,
            arguments,
        } => {
            let spelling = symbols.intern(name.text(source));
            let arguments: Vec<h::Type> = arguments
                .iter()
                .map(|argument| resolve_type(module, argument, source, scope, symbols))
                .collect::<Result<_, _>>()?;
            if name
                .text(source)
                .starts_with(|character: char| character.is_ascii_lowercase())
            {
                if arguments.is_empty() {
                    Ok(h::Type::Variable(spelling))
                } else {
                    Err(error(
                        module,
                        *span,
                        "a type variable cannot take arguments",
                    ))
                }
            } else {
                scope
                    .types
                    .get(&spelling)
                    .map(|binding| h::Type::Named(binding.canonical, arguments))
                    .ok_or_else(|| {
                        error(
                            module,
                            *span,
                            format!("unknown type `{}`", name.text(source)),
                        )
                    })
            }
        }
        s::Type::Function {
            parameters, result, ..
        } => Ok(h::Type::Function(
            parameters
                .iter()
                .map(|parameter| resolve_type(module, parameter, source, scope, symbols))
                .collect::<Result<_, _>>()?,
            Box::new(resolve_type(module, result, source, scope, symbols)?),
        )),
        s::Type::Variants { constructors, .. } => Ok(h::Type::Variants(
            constructors
                .iter()
                .map(|constructor| {
                    Ok(h::ConstructorDecl {
                        name: symbols.intern(constructor.name.text(source)),
                        fields: constructor
                            .fields
                            .iter()
                            .map(|field| resolve_type(module, field, source, scope, symbols))
                            .collect::<Result<_, _>>()?,
                    })
                })
                .collect::<Result<_, ResolveError>>()?,
        )),
        s::Type::Tuple { members, .. } => Ok(h::Type::Tuple(
            members
                .iter()
                .map(|member| resolve_type(module, member, source, scope, symbols))
                .collect::<Result<_, _>>()?,
        )),
        s::Type::Record { span, fields, open } => {
            let mut resolved = fields
                .iter()
                .map(|(name, ty)| {
                    Ok((
                        symbols.intern(name.text(source)),
                        resolve_type(module, ty, source, scope, symbols)?,
                    ))
                })
                .collect::<Result<Vec<_>, ResolveError>>()?;
            resolved.sort_by_key(|(name, _)| *name);
            if resolved.windows(2).any(|pair| pair[0].0 == pair[1].0) {
                return Err(error(module, *span, "record type repeats a field"));
            }
            Ok(h::Type::Record(resolved, *open))
        }
        s::Type::Hole { .. } => Ok(h::Type::Hole),
    }
}

/// A clause, or, where its head names a sum by its own name, `Bot(bot)`,
/// one copy of it for each of that sum's constructors, in the order they are
/// declared. That name stands for the constructor each copy matches, in its
/// head and wherever its body or guard applies it, so `Bot(next)` puts back
/// the constructor that was taken apart. Each copy is resolved, and so
/// typed, apart: its payload has the one type its constructor carries, and
/// no type for the union of them is ever needed.
fn resolve_clauses(
    module: ModuleId,
    clause: &s::Clause,
    name: Symbol,
    source: &str,
    (scope, values): (&Interface, &Values),
    methods: Option<&TypeBinding>,
    (symbols, sites): (&mut Symbols, &mut h::Sites),
) -> Result<Vec<h::Clause>, ResolveError> {
    let mut named = Vec::new();
    for pattern in &clause.patterns {
        standing_in(pattern, source, scope, symbols, &mut named);
    }
    let Some(&(spelling, bound, span)) = named.first() else {
        let resolved = resolve_clause(
            module,
            clause,
            name,
            source,
            (scope, values),
            (methods, None),
            (symbols, sites),
        )?;
        return Ok(vec![resolved]);
    };
    let shown = symbols.text(spelling).to_owned();
    if let Some(&(_, _, again)) = named.get(1) {
        return Err(error(
            module,
            again,
            format!(
                "this clause names `{shown}`'s payload twice, so `{shown}(…)` in its body \
                 would have no one constructor to put back"
            ),
        )
        .help("match the constructors instead"));
    }
    let variants = &scope.types[&spelling].variants;
    // Each copy binds as many fields as the clause names, so every
    // constructor has to carry that many: one carrying fewer has nothing to
    // bind somewhere, and one carrying more has a field the clause never
    // named.
    if let Some(&(constructor, carried)) = variants.iter().find(|(_, carried)| *carried != bound) {
        let constructor = spelled(constructor, symbols);
        return Err(error(
            module,
            span,
            format!(
                "`{constructor}` carries {carried} field{}, so `{shown}` binding {bound} cannot \
                 stand for it",
                if carried == 1 { "" } else { "s" }
            ),
        )
        .help(format!(
            "`{shown}(…)` covers every constructor only where each carries as many fields as \
             it names; match the constructors instead"
        )));
    }
    variants
        .iter()
        .map(|&(constructor, _)| {
            resolve_clause(
                module,
                clause,
                name,
                source,
                (scope, values),
                (methods, Some((spelling, constructor))),
                (&mut *symbols, &mut *sites),
            )
        })
        .collect()
}

/// The sum `spelling` names, where that word may stand for its
/// constructors: a type with visible constructors, which no constructor in
/// scope is also spelled as. A word naming a constructor means that
/// constructor, as a wrapper's own name does.
fn standing_sum(scope: &Interface, spelling: Symbol) -> Option<&TypeBinding> {
    if scope.constructors.contains_key(&spelling) {
        return None;
    }
    scope
        .types
        .get(&spelling)
        .filter(|binding| !binding.variants.is_empty())
}

/// Every place in `pattern` a sum's name stands for its constructors, at
/// any depth, with how many fields it binds there.
fn standing_in(
    pattern: &s::Pattern,
    source: &str,
    scope: &Interface,
    symbols: &Symbols,
    found: &mut Vec<(Symbol, usize, s::Span)>,
) {
    match pattern {
        s::Pattern::Constructor {
            span,
            qualifier,
            name,
            fields,
        } => {
            if qualifier.is_none()
                && !fields.is_empty()
                && let Some(spelling) = symbols.find(name.text(source))
                && standing_sum(scope, spelling).is_some()
            {
                found.push((spelling, fields.len(), *span));
            }
            for field in fields {
                standing_in(field, source, scope, symbols, found);
            }
        }
        s::Pattern::Tuple { members, .. } => {
            for member in members {
                standing_in(member, source, scope, symbols, found);
            }
        }
        s::Pattern::Or { alternatives, .. } => {
            for alternative in alternatives {
                standing_in(alternative, source, scope, symbols, found);
            }
        }
        s::Pattern::List { elements, rest, .. } => {
            for element in elements.iter().chain(rest.as_deref()) {
                standing_in(element, source, scope, symbols, found);
            }
        }
        s::Pattern::Ending { front, last, .. } => {
            for element in std::iter::once(&**front).chain(last) {
                standing_in(element, source, scope, symbols, found);
            }
        }
        s::Pattern::Record { fields, .. } => {
            for (_, field) in fields {
                standing_in(field, source, scope, symbols, found);
            }
        }
        s::Pattern::Wild(_)
        | s::Pattern::Bind(_)
        | s::Pattern::Number { .. }
        | s::Pattern::Range { .. }
        | s::Pattern::String { .. } => {}
    }
}

/// One clause, where `standing` is the sum's name its head takes apart and
/// the constructor that name stands for in this copy of it.
fn resolve_clause(
    module: ModuleId,
    clause: &s::Clause,
    name: Symbol,
    source: &str,
    (scope, values): (&Interface, &Values),
    (methods, standing): (Option<&TypeBinding>, Option<(Symbol, Symbol)>),
    (symbols, sites): (&mut Symbols, &mut h::Sites),
) -> Result<h::Clause, ResolveError> {
    let mut resolver = ClauseResolver {
        module,
        source,
        scope,
        values,
        methods,
        standing,
        symbols,
        sites,
        locals: HashMap::new(),
        next_local: 0,
        alternative: None,
        shadowing: None,
        repeated: Some(Vec::new()),
        testing: false,
        hidden: HashMap::new(),
    };
    let patterns = clause
        .patterns
        .iter()
        .map(|pattern| resolver.pattern(pattern))
        .collect::<Result<_, _>>()?;
    let repeated = resolver.repeated.take().unwrap_or_default();
    let written = clause
        .guard
        .as_ref()
        .map(|guard| resolver.expr(guard))
        .transpose()?;
    let guard = matched_alike(repeated, written, resolver.sites);
    let body = resolver.body(&clause.body)?;
    Ok(h::Clause {
        site: resolver.sites.fresh(),
        span: clause.span,
        name,
        patterns,
        guard,
        body,
        locals: resolver.next_local,
    })
}

/// A clause's guard with the equalities its head asks first: a name bound
/// twice there matches only values equal by their type's `equals`, as
/// `doubled([a, a])` reads.
fn matched_alike(
    repeated: Vec<(h::LocalId, h::LocalId, s::Span)>,
    written: Option<h::Expr>,
    sites: &mut h::Sites,
) -> Option<h::Expr> {
    let mut guard = None;
    for (first, again, span) in repeated {
        let first = sites.expr(span, h::ExprKind::Local(first));
        let again = sites.expr(span, h::ExprKind::Local(again));
        let equal = sites.expr(
            span,
            h::ExprKind::Binary(s::BinaryOp::Equal, Box::new(first), Box::new(again)),
        );
        guard = Some(match guard {
            None => equal,
            Some(asked) => sites.expr(
                span,
                h::ExprKind::Binary(s::BinaryOp::And, Box::new(asked), Box::new(equal)),
            ),
        });
    }
    match (guard, written) {
        (Some(asked), Some(written)) => Some(sites.expr(
            asked.span.through(written.span),
            h::ExprKind::Binary(s::BinaryOp::And, Box::new(asked), Box::new(written)),
        )),
        (guard, None) | (None, guard) => guard,
    }
}

struct ClauseResolver<'a> {
    module: ModuleId,
    source: &'a str,
    scope: &'a Interface,
    values: &'a Values,
    methods: Option<&'a TypeBinding>,
    /// In one copy of a clause whose head takes a sum apart by its own name,
    /// that name, and the constructor it stands for in this copy.
    standing: Option<(Symbol, Symbol)>,
    symbols: &'a mut Symbols,
    /// Identities for every HIR occurrence in the program.
    sites: &'a mut h::Sites,
    locals: HashMap<Symbol, h::LocalId>,
    next_local: u32,
    /// Inside an alternative of an `|` after its first, the locals the first
    /// bound, which a name bound again here is, rather than a new one.
    alternative: Option<HashMap<Symbol, h::LocalId>>,
    /// While a binding's pattern is resolved, the names it has bound so
    /// far: a binding may shadow a name already in scope, though not one it
    /// binds itself.
    shadowing: Option<HashSet<Symbol>>,
    /// Whether a test's pattern is being resolved, whose names would be
    /// taken for comparisons where they are bound again.
    testing: bool,
    /// Names a test bound that are out of sight here, where it is not known
    /// to have held, and where the test was: what a use of one is told.
    hidden: HashMap<Symbol, s::Span>,
    /// While a clause's head is resolved, outside any `|`, each name bound
    /// again there: the local it was bound as, the one it is bound as now,
    /// and where. Elsewhere, a pattern binds each name once.
    repeated: Option<Vec<(h::LocalId, h::LocalId, s::Span)>>,
}

impl ClauseResolver<'_> {
    /// Mark what was bound since `before` as out of sight from here on,
    /// bound by the test at `span`.
    fn hide(&mut self, before: &HashMap<Symbol, h::LocalId>, span: s::Span) {
        for (name, local) in &self.locals {
            if before.get(name) != Some(local) {
                self.hidden.insert(*name, span);
            }
        }
    }

    /// A condition whose tests bind into the current scope: those of a
    /// test, and along a chain of `&`, those of each part. Anything else
    /// binds for nothing outside it.
    fn condition(&mut self, expression: &s::Expr) -> Result<h::Expr, ResolveError> {
        let kind = match &expression.kind {
            s::ExprKind::Is(value, pattern) => {
                let value = self.expr(value)?;
                let outer = std::mem::replace(&mut self.testing, true);
                self.shadowing = Some(HashSet::new());
                let pattern = self.pattern(pattern);
                self.shadowing = None;
                self.testing = outer;
                h::ExprKind::Is(Box::new(value), pattern?)
            }
            s::ExprKind::Binary(s::BinaryOp::And, left, right) => h::ExprKind::Binary(
                s::BinaryOp::And,
                Box::new(self.condition(left)?),
                Box::new(self.condition(right)?),
            ),
            _ => return self.expr(expression),
        };
        Ok(self.sites.expr(expression.span, kind))
    }

    /// A body's bindings in order, then its answer: each binding's value
    /// reads the names as they were, and what follows reads the ones it
    /// binds, a name it rebinds shadowing the one before.
    fn body(&mut self, body: &s::Body) -> Result<h::Body, ResolveError> {
        let mut bindings = Vec::with_capacity(body.bindings.len());
        for binding in &body.bindings {
            let value = self.expr(&binding.value)?;
            self.shadowing = Some(HashSet::new());
            let pattern = self.total_pattern(&binding.pattern);
            self.shadowing = None;
            bindings.push(h::Binding {
                pattern: pattern?,
                value,
            });
        }
        let result = self.expr(&body.result)?;
        Ok(h::Body { bindings, result })
    }

    /// Either alternative, each binding the same names, which are the same
    /// locals in every one of them.
    fn alternatives(
        &mut self,
        span: s::Span,
        alternatives: &[s::Pattern],
    ) -> Result<h::Pattern, ResolveError> {
        let before = self.locals.clone();
        let newly = |locals: &HashMap<Symbol, h::LocalId>| -> HashMap<Symbol, h::LocalId> {
            locals
                .iter()
                .filter(|(name, _)| !before.contains_key(*name))
                .map(|(&name, &local)| (name, local))
                .collect()
        };
        // A name bound twice asks an equality of the whole clause, which an
        // alternative not binding it could not answer.
        let repeating = self.repeated.take();
        let first = self.pattern(&alternatives[0]);
        self.repeated = repeating;
        let first = first?;
        let bound = newly(&self.locals);
        let outer = self.alternative.replace(bound.clone());
        let mut resolved = vec![first];
        for alternative in &alternatives[1..] {
            let after_first = std::mem::replace(&mut self.locals, before.clone());
            let repeating = self.repeated.take();
            let pattern = self.pattern(alternative);
            self.repeated = repeating;
            let pattern = pattern?;
            let these = newly(&self.locals);
            if let Some(name) = bound
                .keys()
                .chain(these.keys())
                .find(|name| bound.get(name) != these.get(name))
            {
                return Err(error(
                    self.module,
                    span,
                    format!(
                        "`{}` is bound by some alternatives of this `|` and not others",
                        self.symbols.text(*name)
                    ),
                ));
            }
            self.locals = after_first;
            resolved.push(pattern);
        }
        self.alternative = outer;
        Ok(h::Pattern::Or(resolved))
    }

    /// A pattern that must match whatever it is handed, a binding's or a
    /// lambda's, which no `|` may choose within.
    fn total_pattern(&mut self, pattern: &s::Pattern) -> Result<h::Pattern, ResolveError> {
        let resolved = self.pattern(pattern)?;
        if resolved.has_alternatives() {
            return Err(error(
                self.module,
                pattern.span(),
                "an `|` pattern may stand only among a clause's parameters",
            ));
        }
        Ok(resolved)
    }

    fn pattern(&mut self, pattern: &s::Pattern) -> Result<h::Pattern, ResolveError> {
        match pattern {
            s::Pattern::Wild(_) => Ok(h::Pattern::Wild),
            s::Pattern::Bind(name) => {
                let spelling = self.symbols.intern(name.text(self.source));
                // A name means one value for its whole scope: a binding's or a
                // test's pattern binds none already seen. A clause's head and a
                // lambda's parameters see none of their own but what they
                // bind, which the checks below look after.
                if let Some(bound) = &self.shadowing
                    && !bound.contains(&spelling)
                    && self.locals.contains_key(&spelling)
                    && !self
                        .alternative
                        .as_ref()
                        .is_some_and(|first| first.contains_key(&spelling))
                {
                    let shown = name.text(self.source);
                    if self.testing {
                        return Err(error(
                            self.module,
                            name.0,
                            format!("`{shown}` is a name already, and a test binds it anew rather than comparing with it"),
                        )
                        .label("bound again here")
                        .help(format!("to compare, bind another name and ask: `x is Ok(n) & n == {shown}`")));
                    }
                    return Err(error(
                        self.module,
                        name.0,
                        format!("`{shown}` is a name already, and a name means one value for its whole scope"),
                    )
                    .label("bound again here")
                    .help("give this value a name of its own"));
                }
                // An alternative after the first binds the names the first did.
                let alternate = self
                    .alternative
                    .as_ref()
                    .is_some_and(|first| first.contains_key(&spelling));
                let again_here = match &mut self.shadowing {
                    Some(bound) => !bound.insert(spelling) && !alternate,
                    None => self.locals.contains_key(&spelling),
                };
                // In a clause's head, a name bound again is a fresh local the
                // guard asks equal to the first; what reads it reads the first.
                if again_here
                    && self.shadowing.is_none()
                    && let Some(first) = self.locals.get(&spelling).copied()
                    && let Some(repeated) = self.repeated.as_mut()
                {
                    let again = h::LocalId(self.next_local);
                    self.next_local = self
                        .next_local
                        .checked_add(1)
                        .expect("fewer than 2^32 locals");
                    repeated.push((first, again, name.0));
                    return Ok(h::Pattern::Bind(again));
                }
                if again_here {
                    return Err(error(
                        self.module,
                        name.0,
                        format!("local `{}` is bound more than once", name.text(self.source)),
                    ));
                }
                let again = self
                    .alternative
                    .as_ref()
                    .and_then(|first| first.get(&spelling).copied());
                let local = again.unwrap_or_else(|| {
                    let local = h::LocalId(self.next_local);
                    self.next_local = self
                        .next_local
                        .checked_add(1)
                        .expect("fewer than 2^32 locals");
                    local
                });
                self.locals.insert(spelling, local);
                Ok(h::Pattern::Bind(local))
            }
            s::Pattern::Constructor {
                span,
                qualifier,
                name,
                fields,
            } => {
                let spelling = self.symbols.intern(name.text(self.source));
                let fields = fields
                    .iter()
                    .map(|field| self.pattern(field))
                    .collect::<Result<_, _>>()?;
                if let Some(qualifier) = qualifier {
                    let constructor = self.qualified(*qualifier, *name)?;
                    return Ok(h::Pattern::Constructor(constructor, fields));
                }
                if let Some((sum, constructor)) = self.standing
                    && sum == spelling
                {
                    return Ok(h::Pattern::Constructor(constructor, fields));
                }
                // Anywhere else, a pattern must always match, and a sum's
                // name matches one constructor at a time.
                if !fields.is_empty() && standing_sum(self.scope, spelling).is_some() {
                    let shown = name.text(self.source);
                    return Err(error(
                        self.module,
                        *span,
                        format!(
                            "`{shown}(…)` stands for each of `{shown}`'s constructors only \
                             among a clause's parameters"
                        ),
                    )
                    .help("take the value apart in a clause of its own"));
                }
                // A word no visible declaration claims is a structural tag;
                // one some declaration claims is its position's to decide.
                Ok(match self.scope.constructors.get(&spelling) {
                    Some(candidates) => h::Pattern::Dual(self.dual(spelling, candidates), fields),
                    None if capitalised(name.text(self.source)) => {
                        h::Pattern::Tag(spelling, fields)
                    }
                    None => {
                        return Err(error(
                            self.module,
                            *span,
                            format!("unknown constructor `{}`", name.text(self.source)),
                        ));
                    }
                })
            }
            s::Pattern::Number {
                numeral, negative, ..
            } => Ok(h::Pattern::Number {
                magnitude: literal::magnitude(*numeral, self.source)
                    .expect("literals were validated while parsing"),
                negative: *negative,
            }),
            s::Pattern::Range { start, end, .. } => {
                let bound = |bound: &Option<s::Bound>| {
                    bound.map(|bound| h::Bound {
                        magnitude: literal::magnitude(bound.numeral, self.source)
                            .expect("literals were validated while parsing"),
                        negative: bound.negative,
                    })
                };
                Ok(h::Pattern::Range(bound(start), bound(end)))
            }
            s::Pattern::List { elements, rest, .. } => Ok(h::Pattern::List(
                elements
                    .iter()
                    .map(|element| self.pattern(element))
                    .collect::<Result<_, _>>()?,
                rest.as_deref()
                    .map(|rest| self.pattern(rest).map(Box::new))
                    .transpose()?,
            )),
            s::Pattern::Ending { front, last, .. } => Ok(h::Pattern::Ending(
                Box::new(self.pattern(front)?),
                last.iter()
                    .map(|element| self.pattern(element))
                    .collect::<Result<_, _>>()?,
            )),
            s::Pattern::String { parts, .. } => Ok(h::Pattern::String(
                parts
                    .iter()
                    .flat_map(|span| {
                        literal::decode_text(span.text(self.source))
                            .expect("literals were validated while parsing")
                            .into_owned()
                            .into_bytes()
                    })
                    .collect(),
            )),
            s::Pattern::Tuple { members, .. } => Ok(h::Pattern::Tuple(
                members
                    .iter()
                    .map(|member| self.pattern(member))
                    .collect::<Result<_, _>>()?,
            )),
            s::Pattern::Record { span, fields, open } => {
                let mut resolved = fields
                    .iter()
                    .map(|(name, pattern)| {
                        Ok((
                            self.symbols.intern(name.text(self.source)),
                            self.pattern(pattern)?,
                        ))
                    })
                    .collect::<Result<Vec<_>, ResolveError>>()?;
                resolved.sort_by_key(|(name, _)| *name);
                if resolved.windows(2).any(|pair| pair[0].0 == pair[1].0) {
                    return Err(error(self.module, *span, "record pattern repeats a field"));
                }
                Ok(h::Pattern::Record(resolved, *open))
            }
            s::Pattern::Or { span, alternatives } => self.alternatives(*span, alternatives),
        }
    }

    fn expr(&mut self, expression: &s::Expr) -> Result<h::Expr, ResolveError> {
        let kind = match &expression.kind {
            s::ExprKind::Name(name) => self.name(*name)?,
            s::ExprKind::Number(numeral) if numeral.kind == s::NumeralKind::Decimal => {
                let (digits, scale) = literal::decimal(*numeral, self.source)
                    .expect("literals were validated while parsing");
                h::ExprKind::Decimal(digits, scale)
            }
            s::ExprKind::Number(numeral) => h::ExprKind::Number(
                literal::magnitude(*numeral, self.source)
                    .expect("literals were validated while parsing"),
            ),
            s::ExprKind::String(parts) => h::ExprKind::String(
                parts
                    .iter()
                    .map(|part| match part {
                        s::StringPart::Text(span) => Ok(h::StringPart::Text(
                            literal::decode_text(span.text(self.source))
                                .expect("literals were validated while parsing")
                                .as_bytes()
                                .to_vec(),
                        )),
                        s::StringPart::Splice(expression, width) => {
                            let value = self.expr(expression)?;
                            let to_str = self.symbols.intern("to_str");
                            let text = self.sites.expr(
                                expression.span,
                                h::ExprKind::Method(Box::new(value), to_str, Vec::new()),
                            );
                            let Some(width) = width else {
                                return Ok(h::StringPart::Splice(text));
                            };
                            // `${value:>7}` is `value.to_str().pad_start(7)`.
                            let pad = self.symbols.intern(match width.align {
                                s::Align::Left => "pad_end",
                                s::Align::Right => "pad_start",
                            });
                            let columns = self.sites.expr(
                                width.columns.span,
                                h::ExprKind::Number(
                                    literal::magnitude(width.columns, self.source)
                                        .expect("literals were validated while parsing"),
                                ),
                            );
                            let padded = self.sites.expr(
                                expression.span,
                                h::ExprKind::Method(Box::new(text), pad, vec![columns]),
                            );
                            Ok(h::StringPart::Splice(padded))
                        }
                    })
                    .collect::<Result<_, ResolveError>>()?,
            ),
            s::ExprKind::List(elements, rest) => h::ExprKind::List(
                elements
                    .iter()
                    .map(|element| self.expr(element))
                    .collect::<Result<_, _>>()?,
                rest.as_deref()
                    .map(|rest| self.expr(rest).map(Box::new))
                    .transpose()?,
            ),
            s::ExprKind::Record(fields) => {
                h::ExprKind::Record(self.record_fields(fields, expression.span)?)
            }
            s::ExprKind::Update(fields, base) => {
                let base = Box::new(self.expr(base)?);
                h::ExprKind::Update(base, self.record_fields(fields, expression.span)?)
            }
            s::ExprKind::Lambda(patterns, body) => {
                let saved = self.locals.clone();
                let patterns = patterns
                    .iter()
                    .map(|pattern| self.total_pattern(pattern))
                    .collect::<Result<_, _>>()?;
                let body = self.expr(body)?;
                self.locals = saved;
                h::ExprKind::Lambda(patterns, Box::new(body))
            }
            // A block's names leave with it, as a lambda's do.
            s::ExprKind::Block(body) => {
                let saved = self.locals.clone();
                let body = self.body(body)?;
                self.locals = saved;
                h::ExprKind::Block(Box::new(body))
            }
            s::ExprKind::Call(head, arguments) => {
                let applied = self.applied(head)?;
                if matches!(head.kind, s::ExprKind::Name(_)) && self.used_value(&applied.kind) {
                    return Err(self.called_value(head.span));
                }
                h::ExprKind::Call(
                    Box::new(applied),
                    arguments
                        .iter()
                        .map(|argument| self.expr(argument))
                        .collect::<Result<_, _>>()?,
                )
            }
            s::ExprKind::Member(head, member) => {
                if let Some(found) = self.static_member(head, *member) {
                    self.value_or(expression.span, found?)
                } else if let Some(variable) = self.type_variable(head) {
                    // `a.zero`: a value a `where` bound on `a` names.
                    h::ExprKind::Associated(variable, self.symbols.intern(member.text(self.source)))
                } else {
                    h::ExprKind::Member(
                        Box::new(self.expr(head)?),
                        self.symbols.intern(member.text(self.source)),
                    )
                }
            }
            s::ExprKind::Method(head, member, arguments) => {
                let arguments = arguments
                    .iter()
                    .map(|argument| self.expr(argument))
                    .collect::<Result<Vec<_>, _>>()?;
                if let Some(found) = self.static_member(head, *member) {
                    let found = found?;
                    if matches!(found, h::ExprKind::Global(global) if self.values.contains(&global))
                    {
                        return Err(self.called_value(head.span.through(member.0)));
                    }
                    h::ExprKind::Call(
                        Box::new(h::Expr {
                            site: self.sites.fresh(),
                            span: head.span.through(member.0),
                            kind: found,
                        }),
                        arguments,
                    )
                } else if let Some(variable) = self.type_variable(head) {
                    // `a.of_nat(n)`: a member a `where` bound on `a` names.
                    h::ExprKind::Call(
                        Box::new(h::Expr {
                            site: self.sites.fresh(),
                            span: head.span.through(member.0),
                            kind: h::ExprKind::Associated(
                                variable,
                                self.symbols.intern(member.text(self.source)),
                            ),
                        }),
                        arguments,
                    )
                } else {
                    h::ExprKind::Method(
                        Box::new(self.expr(head)?),
                        self.symbols.intern(member.text(self.source)),
                        arguments,
                    )
                }
            }
            s::ExprKind::Unary(operator, value) => {
                h::ExprKind::Unary(*operator, Box::new(self.expr(value)?))
            }
            s::ExprKind::Try(value) => h::ExprKind::Try(Box::new(self.expr(value)?)),
            // What the condition binds is seen by `yes` alone.
            s::ExprKind::If(condition, yes, no) => {
                let before = self.locals.clone();
                let asked = condition.span;
                let condition = self.condition(condition);
                let yes = condition.and_then(|condition| Ok((condition, self.expr(yes)?)));
                self.hide(&before, asked);
                self.locals = before;
                let (condition, yes) = yes?;
                h::ExprKind::If(Box::new(condition), Box::new(yes), Box::new(self.expr(no)?))
            }
            // Alone, a test binds for nothing after it.
            s::ExprKind::Is(..) => {
                let before = self.locals.clone();
                let tested = self.condition(expression);
                self.hide(&before, expression.span);
                self.locals = before;
                return tested;
            }
            // What the left binds is seen by the right, and no further.
            s::ExprKind::Binary(s::BinaryOp::And, left, right) => {
                let before = self.locals.clone();
                let both = self
                    .condition(left)
                    .and_then(|left| Ok((left, self.condition(right)?)));
                self.hide(&before, expression.span);
                self.locals = before;
                let (left, right) = both?;
                h::ExprKind::Binary(s::BinaryOp::And, Box::new(left), Box::new(right))
            }
            s::ExprKind::Wild | s::ExprKind::Range(..) | s::ExprKind::Ending(..) => {
                unreachable!("the parser refuses a pattern's form outside a pattern")
            }
            s::ExprKind::Tuple(members) => h::ExprKind::Tuple(
                members
                    .iter()
                    .map(|member| self.expr(member))
                    .collect::<Result<_, _>>()?,
            ),
            s::ExprKind::Binary(operator, left, right) => h::ExprKind::Binary(
                *operator,
                Box::new(self.expr(left)?),
                Box::new(self.expr(right)?),
            ),
        };
        Ok(h::Expr {
            site: self.sites.fresh(),
            span: expression.span,
            kind,
        })
    }

    /// What a call's head names. A sum's own name applied is the
    /// constructor its clause's head took apart, in this copy of it.
    fn applied(&mut self, head: &s::Expr) -> Result<h::Expr, ResolveError> {
        let s::ExprKind::Name(name) = &head.kind else {
            return self.expr(head);
        };
        let Some(spelling) = self.symbols.find(name.text(self.source)) else {
            return self.expr(head);
        };
        if let Some((sum, constructor)) = self.standing
            && sum == spelling
        {
            return Ok(self
                .sites
                .expr(head.span, h::ExprKind::Constructor(constructor)));
        }
        if standing_sum(self.scope, spelling).is_some() {
            let shown = name.text(self.source);
            return Err(error(
                self.module,
                head.span,
                format!(
                    "`{shown}(…)` builds the constructor its clause took apart, and this \
                     clause takes none apart as `{shown}`"
                ),
            )
            .help(format!(
                "name the constructor, or take the value apart as `{shown}(…)` among the \
                 clause's parameters"
            )));
        }
        self.expr(head)
    }

    fn name(&mut self, name: s::Name) -> Result<h::ExprKind, ResolveError> {
        let spelling = self.symbols.intern(name.text(self.source));
        if let Some(&local) = self.locals.get(&spelling) {
            return Ok(h::ExprKind::Local(local));
        }
        if let Some(&global) = self.scope.values.get(&spelling) {
            return Ok(self.value_or(name.0, h::ExprKind::Global(global)));
        }
        if let Some(methods) = self.methods
            && let Some(&method) = methods.methods.get(&spelling)
        {
            return Ok(self.value_or(name.0, h::ExprKind::Global(method)));
        }
        if let Some(candidates) = self.scope.constructors.get(&spelling) {
            return Ok(h::ExprKind::Dual(self.dual(spelling, candidates)));
        }
        // A capitalised word nothing visible declares is a structural tag: it
        // exists by being written, and belongs to no module.
        if capitalised(name.text(self.source)) {
            return Ok(h::ExprKind::Tag(spelling));
        }
        if self.hidden.contains_key(&spelling) {
            return Err(error(
                self.module,
                name.0,
                format!(
                    "`{}` is bound by a test, and seen only where that test is known to have held",
                    name.text(self.source)
                ),
            )
            .label("not known to hold here")
            .help("a test binds for the rest of its `&` chain and its `if`'s `then`; under `|`, `!` or in `else`, it may not have held"));
        }
        Err(error(
            self.module,
            name.0,
            format!("unknown name `{}`", name.text(self.source)),
        ))
    }

    /// A use of `found`: where it is a value, its definition called, and
    /// otherwise `found` itself.
    fn value_or(&mut self, span: s::Span, found: h::ExprKind) -> h::ExprKind {
        match found {
            h::ExprKind::Global(global) if self.values.contains(&global) => {
                let definition = self.sites.expr(span, found);
                h::ExprKind::Call(Box::new(definition), Vec::new())
            }
            found => found,
        }
    }

    /// Whether `resolved` is a value's use, as [`Self::value_or`] makes it.
    fn used_value(&self, resolved: &h::ExprKind) -> bool {
        matches!(resolved, h::ExprKind::Call(definition, arguments)
            if arguments.is_empty()
                && matches!(definition.kind, h::ExprKind::Global(global) if self.values.contains(&global)))
    }

    /// A value, at `span`, written as a function called.
    fn called_value(&self, span: s::Span) -> ResolveError {
        let shown = span.text(self.source);
        error(
            self.module,
            span,
            format!("`{shown}` is a value, not a function: write `{shown}`"),
        )
    }

    /// The type variable a head spells, where it is a lowercase word naming
    /// no local and no value: only a `where` bound can mean it.
    fn type_variable(&mut self, head: &s::Expr) -> Option<Symbol> {
        let s::ExprKind::Name(name) = &head.kind else {
            return None;
        };
        let text = name.text(self.source);
        if !text.starts_with(|character: char| character.is_ascii_lowercase()) {
            return None;
        }
        let spelling = self.symbols.intern(text);
        let named = self.locals.contains_key(&spelling)
            || self.scope.values.contains_key(&spelling)
            || self
                .methods
                .is_some_and(|binding| binding.methods.contains_key(&spelling));
        (!named).then_some(spelling)
    }

    /// A record expression's fields, each named once.
    fn record_fields(
        &mut self,
        fields: &[(s::Name, s::Expr)],
        span: s::Span,
    ) -> Result<Vec<(Symbol, h::Expr)>, ResolveError> {
        let mut seen = HashSet::new();
        let mut resolved = Vec::with_capacity(fields.len());
        for (name, value) in fields {
            let name = self.symbols.intern(name.text(self.source));
            if !seen.insert(name) {
                return Err(error(
                    self.module,
                    span,
                    "record expression repeats a field",
                ));
            }
            resolved.push((name, self.expr(value)?));
        }
        Ok(resolved)
    }

    /// A word some declaration claims, numbered so checking can say which
    /// reading its position chose.
    fn dual(&mut self, spelling: Symbol, candidates: &[Symbol]) -> h::Dual {
        let site = self.sites.fresh();
        h::Dual {
            site,
            spelling,
            candidates: candidates.to_vec(),
            home: self
                .methods
                .and_then(|binding| binding.constructors.get(&spelling).copied()),
        }
    }

    /// What `Type.member` names, where the head is a visible type: one of
    /// its methods, or one of the constructors it exports.
    fn static_member(
        &mut self,
        head: &s::Expr,
        member: s::Name,
    ) -> Option<Result<h::ExprKind, ResolveError>> {
        let s::ExprKind::Name(owner) = &head.kind else {
            return None;
        };
        let owner_spelling = self.symbols.intern(owner.text(self.source));
        let binding = self.scope.types.get(&owner_spelling)?;
        if capitalised(member.text(self.source)) {
            return Some(self.qualified(*owner, member).map(h::ExprKind::Constructor));
        }
        let member_spelling = self.symbols.intern(member.text(self.source));
        Some(
            binding
                .methods
                .get(&member_spelling)
                .copied()
                .map(h::ExprKind::Global)
                .ok_or_else(|| {
                    error(
                        self.module,
                        member.0,
                        format!(
                            "type `{}` has no method `{}`",
                            owner.text(self.source),
                            member.text(self.source)
                        ),
                    )
                }),
        )
    }

    /// The constructor `Type.Ctor` names: that type's, outright, never a
    /// structural tag. A constructor the type does not export here is
    /// private, and naming it qualified is no way round that.
    fn qualified(&mut self, owner: s::Name, member: s::Name) -> Result<Symbol, ResolveError> {
        let owner_spelling = self.symbols.intern(owner.text(self.source));
        let member_spelling = self.symbols.intern(member.text(self.source));
        self.scope
            .types
            .get(&owner_spelling)
            .ok_or_else(|| {
                error(
                    self.module,
                    owner.0,
                    format!("unknown type `{}`", owner.text(self.source)),
                )
            })?
            .constructors
            .get(&member_spelling)
            .copied()
            .ok_or_else(|| {
                error(
                    self.module,
                    member.0,
                    format!(
                        "type `{}` has no constructor `{}` visible here",
                        owner.text(self.source),
                        member.text(self.source)
                    ),
                )
            })
    }
}

/// Whether a word is spelled as a type, constructor or tag is: capitalised.
fn capitalised(word: &str) -> bool {
    word.starts_with(|character: char| character.is_ascii_uppercase())
}

fn global_value(
    module: ModuleId,
    name: s::Name,
    source: &str,
    scope: &Interface,
    symbols: &mut Symbols,
) -> Result<Symbol, ResolveError> {
    let spelling = symbols.intern(name.text(source));
    scope.values.get(&spelling).copied().ok_or_else(|| {
        error(
            module,
            name.0,
            format!("unknown value `{}`", name.text(source)),
        )
    })
}

fn method_name(
    module: ModuleId,
    name: s::Name,
    source: &str,
    binding: &TypeBinding,
    symbols: &mut Symbols,
) -> Result<Symbol, ResolveError> {
    let spelling = symbols.intern(name.text(source));
    binding.methods.get(&spelling).copied().ok_or_else(|| {
        error(
            module,
            name.0,
            format!("unknown method `{}`", name.text(source)),
        )
    })
}

fn error(module: ModuleId, span: s::Span, said: impl Into<Unplaced>) -> ResolveError {
    let said = said.into();
    ResolveError {
        module,
        span,
        message: said.message,
        advice: said.advice,
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
            let root = std::env::temp_dir().join(format!("faun-resolve-{unique}"));
            fs::create_dir_all(&root).unwrap();
            Self(root)
        }

        fn write(&self, name: &str, source: &str) -> PathBuf {
            let path = self.0.join(name);
            fs::write(&path, source).unwrap();
            path
        }
    }

    impl Drop for Fixture {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    #[test]
    fn resolves_prelude_types_constructors_and_static_methods() {
        let fixture = Fixture::new();
        fixture.write(
            "nat.fn",
            "export {Nat.*}\nNat : [Zero, Succ(Nat)].(of_nat : Nat -> Nat\nof_nat(n) -> n)\n",
        );
        fixture.write(
            "int.fn",
            "export {Int.*}\nInt : [Pos(Nat), NegSucc(Nat)].(of_nat : Nat -> Int\nof_nat(n) -> Pos(n)\nneg : Int -> Int\nneg(i) -> i)\n",
        );
        fixture.write("u8.fn", "export {U8.*}\nU8 : Nat\n");
        fixture.write(
            "list.fn",
            "export {List.*}\nList(a) : [Nil, Cons(a, List(a))]\n",
        );
        fixture.write("str.fn", "export {Str}\nStr : List(U8)\n");
        let standard = fixture.write(
            "standard.fn",
            "package {}\nimport nat {Nat.*}\nimport int {Int.*}\nimport u8 {U8.*}\nimport list {List.*}\nimport str {Str}\nexport {Nat.*, Int.*, U8.*, List.*, Str}\n",
        );
        let entry = fixture.write(
            "main.fn",
            "number : Int\nnumber = Int.of_nat(42)\ntext : Str\ntext = \"é\"\n",
        );
        let host = fixture.write("host.fn", "export {Host}\nHost : {argc: Nat}\n");
        let loaded = modules::load_program(&entry, &standard, &host).unwrap();
        let resolved = resolve_names(loaded).unwrap();
        let entry = &resolved.program.modules.last().unwrap().items;
        let h::Item::Clause(number) = &entry[1] else {
            panic!("number clause")
        };
        let h::ExprKind::Call(head, arguments) = &number.body.result.kind else {
            panic!("static call")
        };
        assert!(matches!(head.kind, h::ExprKind::Global(_)));
        assert!(matches!(arguments[0].kind, h::ExprKind::Number(_)));
        let h::Item::Clause(text) = &entry[3] else {
            panic!("text clause")
        };
        let h::ExprKind::String(parts) = &text.body.result.kind else {
            panic!("string literal")
        };
        assert_eq!(parts, &[h::StringPart::Text(vec![0xc3, 0xa9])]);
    }

    #[test]
    fn rejects_an_unresolved_name_at_its_span() {
        let fixture = Fixture::new();
        let prelude = fixture.write("standard.fn", "package {}\nexport {}\n");
        let entry = fixture.write("main.fn", "f = missing\n");
        let host = fixture.write("host.fn", "export {Host}\nHost : {}\n");
        let loaded = modules::load_program(&entry, &prelude, &host).unwrap();
        let failure = resolve_names(loaded).unwrap_err();
        let at = failure.location().expect("a place in the source");
        assert_eq!((at.line, at.column, at.width), (1, 5, 7));
    }
}
