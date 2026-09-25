//! Resolve module-local source names into canonical globals and compact locals.

// Resolution is a pair of cohesive exhaustive walks. Keeping each match whole
// makes omissions visible when surface syntax gains a variant.
#![allow(clippy::too_many_lines)]

use std::collections::HashMap;
use std::fmt;

use super::ast as s;
use super::diagnostic::Diagnostic;
use super::hir as h;
use super::literal;
use super::modules::{Interface, LoadedModule, LoadedProgram, ModuleId, TypeBinding};
use super::{SourceId, Sources, Symbol, Symbols};

#[derive(Clone, Debug)]
pub struct ResolvedProgram {
    pub sources: Sources,
    pub symbols: Symbols,
    pub program: h::Program,
    /// The entry's package, whose every definition is compiled, rather than
    /// only what reaches into it.
    pub package: Vec<ModuleId>,
    /// Each module's source, by module.
    module_sources: Vec<SourceId>,
}

impl ResolvedProgram {
    /// A diagnostic at `span` in `module`.
    ///
    /// # Panics
    /// If `module` is not one of this program's.
    #[must_use]
    pub fn diagnostic(&self, module: ModuleId, span: s::Span, message: String) -> Diagnostic {
        let source = self.module_sources[module.index()];
        let source = self
            .sources
            .get(source)
            .expect("a resolved module has a source");
        Diagnostic::new(message).at(source, span)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResolveError {
    pub module: ModuleId,
    pub span: s::Span,
    pub message: String,
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
    let mut sites = 0;
    let mut aliases = HashMap::new();
    let mut constraint_aliases = HashMap::new();
    for module in &loaded.modules {
        let source = loaded
            .sources
            .get(module.source)
            .expect("loaded module has source")
            .text();
        let mut scope = prelude.clone();
        scope.merge(&module.scope, &loaded.symbols, "module scope")?;
        let resolved = resolve_module(
            module,
            source,
            &scope,
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
    Ok(ResolvedProgram {
        module_sources: loaded.modules.iter().map(|module| module.source).collect(),
        package: loaded.package,
        sources: loaded.sources,
        symbols: loaded.symbols,
        program: h::Program { modules },
    })
}

/// A resolve error as a diagnostic at the place it names.
fn located(loaded: &LoadedProgram, error: ResolveError) -> Diagnostic {
    let module = loaded.module(error.module);
    let source = loaded
        .sources
        .get(module.source)
        .expect("loaded module has source");
    Diagnostic::new(error.message).at(source, error.span)
}

/// Each alias's definition, resolved in the module that wrote it.
type Aliases = HashMap<Symbol, (h::Type, ModuleId, s::Span)>;

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
    scope: &Interface,
    (symbols, sites): (&mut Symbols, &mut u32),
    (aliases, constraint_aliases): (&mut Aliases, &mut ConstraintAliases),
) -> Result<h::Module, ResolveError> {
    let mut items = Vec::new();
    for item in &module.syntax.items {
        match item {
            s::Item::Data(data) => items.push(h::Item::Data(resolve_data(
                module.id, data, source, scope, symbols, sites,
            )?)),
            s::Item::Signature(signature) => {
                let name = global_value(module.id, signature.name, source, scope, symbols)?;
                items.push(h::Item::Signature(resolve_signature(
                    module.id, signature, name, source, scope, symbols,
                )?));
            }
            s::Item::Clause(clause) => {
                let name = global_value(module.id, clause.name, source, scope, symbols)?;
                items.push(h::Item::Clause(resolve_clause(
                    module.id,
                    clause,
                    name,
                    source,
                    scope,
                    None,
                    (symbols, sites),
                )?));
            }
            s::Item::Alias(alias) => {
                let local = symbols.intern(alias.name.text(source));
                let canonical = scope.types[&local].canonical;
                let ty = resolve_type(module.id, &alias.ty, source, scope, symbols)?;
                if has_variable(&ty) {
                    return Err(error(
                        module.id,
                        alias.span,
                        "an alias names one type and has no type variables; a type with parameters is declared with `:`",
                    ));
                }
                aliases.insert(canonical, (ty, module.id, alias.span));
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
    })
}

fn has_variable(ty: &h::Type) -> bool {
    match ty {
        h::Type::Variable(_) => true,
        h::Type::Named(_, arguments) => arguments.iter().any(has_variable),
        h::Type::Function(parameters, result) => {
            parameters.iter().any(has_variable) || has_variable(result)
        }
        h::Type::Variants(tags) => tags.iter().flat_map(|tag| &tag.fields).any(has_variable),
        h::Type::Record(fields, _) => fields.iter().any(|(_, field)| has_variable(field)),
        h::Type::Tuple(members) => members.iter().any(has_variable),
    }
}

/// Replace every alias in the program's written types by what it names.
/// An alias is transparent: `Point = {x: Nat y: Nat}` is the record type,
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
    let mut expanded = Aliases::new();
    for (&alias, &(_, module, span)) in aliases {
        let ty = expand(
            &h::Type::Named(alias, Vec::new()),
            aliases,
            symbols,
            &mut Vec::new(),
        )
        .map_err(|message| error(module, span, message))?;
        expanded.insert(alias, (ty, module, span));
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
                            .and_then(|field| typed(field, constraint_aliases, symbols))
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
) -> Result<(), String> {
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
            h::Type::Variable(_) => None,
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
                self.members.push(h::Constraint::Member {
                    variable,
                    member,
                    ty,
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
        self.expanding.push(name);
        for constraint in &alias.constraints {
            let constraint = match constraint {
                h::Constraint::Member {
                    variable,
                    member,
                    ty,
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
) -> Result<h::Type, String> {
    let spelled = |name: Symbol| {
        let text = symbols.text(name);
        text.rsplit_once("$$")
            .map_or(text, |(_, spelled)| spelled)
            .to_owned()
    };
    Ok(match ty {
        h::Type::Named(name, arguments) if aliases.contains_key(name) => {
            if !arguments.is_empty() {
                return Err(format!(
                    "`{}` is an alias and takes no arguments",
                    spelled(*name)
                ));
            }
            if expanding.contains(name) {
                return Err(format!(
                    "alias `{}` names itself; a recursive type is declared with `:`",
                    spelled(*name)
                ));
            }
            expanding.push(*name);
            let definition = expand(&aliases[name].0, aliases, symbols, expanding)?;
            expanding.pop();
            definition
        }
        h::Type::Named(name, arguments) => h::Type::Named(
            *name,
            arguments
                .iter()
                .map(|argument| expand(argument, aliases, symbols, expanding))
                .collect::<Result<_, _>>()?,
        ),
        h::Type::Variable(_) => ty.clone(),
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
                            .collect::<Result<_, String>>()?,
                    })
                })
                .collect::<Result<_, String>>()?,
        ),
        h::Type::Record(fields, open) => h::Type::Record(
            fields
                .iter()
                .map(|(name, field)| Ok((*name, expand(field, aliases, symbols, expanding)?)))
                .collect::<Result<_, String>>()?,
            *open,
        ),
        h::Type::Tuple(members) => h::Type::Tuple(
            members
                .iter()
                .map(|member| expand(member, aliases, symbols, expanding))
                .collect::<Result<_, String>>()?,
        ),
    })
}

fn resolve_data(
    module: ModuleId,
    data: &s::DataDecl,
    source: &str,
    scope: &Interface,
    symbols: &mut Symbols,
    sites: &mut u32,
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
                        .map(|field| resolve_type(module, field, source, scope, symbols))
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
                field: resolve_type(module, representation, source, scope, symbols)?,
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
                methods.push(h::MethodItem::Clause(resolve_clause(
                    module,
                    clause,
                    name,
                    source,
                    scope,
                    Some(binding),
                    (symbols, sites),
                )?));
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
                    .map(|ty| resolve_type(module, ty, source, scope, symbols))
                    .collect::<Result<_, _>>()?,
                Box::new(resolve_type(module, result, source, scope, symbols)?),
            ),
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
                    .map(|ty| resolve_type(module, ty, source, scope, symbols))
                    .collect::<Result<_, _>>()?,
            }
        }
    })
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
    }
}

fn resolve_clause(
    module: ModuleId,
    clause: &s::Clause,
    name: Symbol,
    source: &str,
    scope: &Interface,
    methods: Option<&TypeBinding>,
    (symbols, sites): (&mut Symbols, &mut u32),
) -> Result<h::Clause, ResolveError> {
    let mut resolver = ClauseResolver {
        module,
        source,
        scope,
        methods,
        symbols,
        sites,
        locals: HashMap::new(),
        next_local: 0,
    };
    let patterns = clause
        .patterns
        .iter()
        .map(|pattern| resolver.pattern(pattern))
        .collect::<Result<_, _>>()?;
    let guard = clause
        .guard
        .as_ref()
        .map(|guard| resolver.expr(guard))
        .transpose()?;
    let mut bindings = Vec::with_capacity(clause.body.bindings.len());
    for binding in &clause.body.bindings {
        let value = resolver.expr(&binding.value)?;
        let pattern = resolver.pattern(&binding.pattern)?;
        bindings.push(h::Binding { pattern, value });
    }
    let result = resolver.expr(&clause.body.result)?;
    Ok(h::Clause {
        span: clause.span,
        name,
        patterns,
        guard,
        body: h::Body { bindings, result },
        locals: resolver.next_local,
    })
}

struct ClauseResolver<'a> {
    module: ModuleId,
    source: &'a str,
    scope: &'a Interface,
    methods: Option<&'a TypeBinding>,
    symbols: &'a mut Symbols,
    /// How many dual sites the program has numbered so far.
    sites: &'a mut u32,
    locals: HashMap<Symbol, h::LocalId>,
    next_local: u32,
}

impl ClauseResolver<'_> {
    fn pattern(&mut self, pattern: &s::Pattern) -> Result<h::Pattern, ResolveError> {
        match pattern {
            s::Pattern::Wild(_) => Ok(h::Pattern::Wild),
            s::Pattern::Bind(name) => {
                let spelling = self.symbols.intern(name.text(self.source));
                if self.locals.contains_key(&spelling) {
                    return Err(error(
                        self.module,
                        name.0,
                        format!("local `{}` is bound more than once", name.text(self.source)),
                    ));
                }
                let local = h::LocalId(self.next_local);
                self.next_local = self
                    .next_local
                    .checked_add(1)
                    .expect("fewer than 2^32 locals");
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
            s::Pattern::Range { start, end, .. } => Ok(h::Pattern::Range(
                literal::magnitude(*start, self.source)
                    .expect("literals were validated while parsing"),
                literal::magnitude(*end, self.source)
                    .expect("literals were validated while parsing"),
            )),
            s::Pattern::List { elements, rest, .. } => Ok(h::Pattern::List(
                elements
                    .iter()
                    .map(|element| self.pattern(element))
                    .collect::<Result<_, _>>()?,
                rest.as_deref()
                    .map(|rest| self.pattern(rest).map(Box::new))
                    .transpose()?,
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
        }
    }

    fn expr(&mut self, expression: &s::Expr) -> Result<h::Expr, ResolveError> {
        let kind = match &expression.kind {
            s::ExprKind::Name(name) => self.name(*name)?,
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
                        s::StringPart::Splice(expression) => {
                            Ok(h::StringPart::Splice(self.expr(expression)?))
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
                    .map(|pattern| self.pattern(pattern))
                    .collect::<Result<_, _>>()?;
                let body = self.expr(body)?;
                self.locals = saved;
                h::ExprKind::Lambda(patterns, Box::new(body))
            }
            s::ExprKind::Call(head, arguments) => h::ExprKind::Call(
                Box::new(self.expr(head)?),
                arguments
                    .iter()
                    .map(|argument| self.expr(argument))
                    .collect::<Result<_, _>>()?,
            ),
            s::ExprKind::Member(head, member) => {
                if let Some(found) = self.static_member(head, *member) {
                    found?
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
                    h::ExprKind::Call(
                        Box::new(h::Expr {
                            span: head.span.through(member.0),
                            kind: found?,
                        }),
                        arguments,
                    )
                } else if let Some(variable) = self.type_variable(head) {
                    // `a.zero()`: a member a `where` bound on `a` names.
                    h::ExprKind::Call(
                        Box::new(h::Expr {
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
            span: expression.span,
            kind,
        })
    }

    fn name(&mut self, name: s::Name) -> Result<h::ExprKind, ResolveError> {
        let spelling = self.symbols.intern(name.text(self.source));
        if let Some(&local) = self.locals.get(&spelling) {
            return Ok(h::ExprKind::Local(local));
        }
        if let Some(&global) = self.scope.values.get(&spelling) {
            return Ok(h::ExprKind::Global(global));
        }
        if let Some(methods) = self.methods
            && let Some(&method) = methods.methods.get(&spelling)
        {
            return Ok(h::ExprKind::Global(method));
        }
        if let Some(candidates) = self.scope.constructors.get(&spelling) {
            return Ok(h::ExprKind::Dual(self.dual(spelling, candidates)));
        }
        // A capitalised word nothing visible declares is a structural tag: it
        // exists by being written, and belongs to no module.
        if capitalised(name.text(self.source)) {
            return Ok(h::ExprKind::Tag(spelling));
        }
        Err(error(
            self.module,
            name.0,
            format!("unknown name `{}`", name.text(self.source)),
        ))
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
        let mut seen = std::collections::HashSet::new();
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
        let site = h::SiteId(*self.sites);
        *self.sites = self
            .sites
            .checked_add(1)
            .expect("fewer than 2^32 dual sites");
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

fn error(module: ModuleId, span: s::Span, message: impl Into<String>) -> ResolveError {
    ResolveError {
        module,
        span,
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
            "exports {Nat.*}\nNat : [Zero Succ(Nat)].(of_nat : Nat -> Nat of_nat(n) -> n)\n",
        );
        fixture.write(
            "int.fn",
            "exports {Int.*}\nInt : [Pos(Nat) NegSucc(Nat)].(of_nat : Nat -> Int of_nat(n) -> Pos(n) neg : Int -> Int neg(i) -> i)\n",
        );
        fixture.write("u8.fn", "exports {U8.*}\nU8 : Nat\n");
        fixture.write(
            "list.fn",
            "exports {List.*}\nList(a) : [Nil Cons(a List(a))]\n",
        );
        fixture.write("str.fn", "exports {Str}\nStr : List(U8)\n");
        let standard = fixture.write(
            "standard.fn",
            "package {}\nimport nat {Nat.*}\nimport int {Int.*}\nimport u8 {U8.*}\nimport list {List.*}\nimport str {Str}\nexports {Nat.* Int.* U8.* List.* Str}\n",
        );
        let entry = fixture.write(
            "main.fn",
            "number : Int\nnumber() -> Int.of_nat(42)\ntext : Str\ntext() -> \"é\"\n",
        );
        let host = fixture.write("host.fn", "exports {Host}\nHost : {argc: Nat}\n");
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
        let prelude = fixture.write("standard.fn", "package {}\nexports {}\n");
        let entry = fixture.write("main.fn", "f() -> missing\n");
        let host = fixture.write("host.fn", "exports {Host}\nHost : {}\n");
        let loaded = modules::load_program(&entry, &prelude, &host).unwrap();
        let failure = resolve_names(loaded).unwrap_err();
        let at = failure.location.expect("a place in the source");
        assert_eq!((at.line, at.column, at.width), (1, 8, 7));
    }
}
