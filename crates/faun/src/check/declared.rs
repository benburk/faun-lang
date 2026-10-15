//! What a program declares, judged before inference: a definition left
//! without clauses outside the host, a type holding itself at a larger
//! type, and a type no value can be built of.

use std::collections::{HashMap, HashSet};

use super::failure;
use crate::declarations as n;
use crate::diagnostic::{Advised, Refusal};
use crate::hir as h;
use crate::{ModuleId, Symbol, Symbols};

/// Refuse the first declaration that cannot stand, in that order.
pub(super) fn check(
    program: &n::Program,
    host: ModuleId,
    symbols: &Symbols,
) -> Result<(), Refusal> {
    externals(program, host, symbols)?;
    regular(&program.data, symbols)?;
    inhabited(&program.data, symbols)
}

/// Refuse a definition left without clauses outside the host. A target
/// answers such a definition by its spelling alone, so one written anywhere
/// else would reach the target's routine at whatever type it claimed, and
/// with no capability in hand.
fn externals(program: &n::Program, host: ModuleId, symbols: &Symbols) -> Result<(), Refusal> {
    let bodyless = program
        .functions
        .iter()
        .find(|function| function.clauses.is_empty() && function.module != host);
    let Some(function) = bodyless else {
        return Ok(());
    };
    let span = function
        .signature
        .as_ref()
        .map_or_else(crate::ast::Span::default, |signature| signature.span);
    let name = symbols.spelling(function.name);
    Err(failure(
        function.module,
        span,
        format!("`{name}` has a signature and no clauses"),
    )
    .note("only the host leaves a definition for its target to answer")
    .help(format!("write the clauses of `{name}`")))
}

/// Refuse a declared type that holds itself, through whatever types it
/// holds, at a type larger than its parameters, as
/// `Nest(a) : [Flat(a), Deeper(Nest((a, a)))]` does. Every size of it
/// would be a type of its own, and a program holding one would ask for
/// them without end.
fn regular(data: &HashMap<Symbol, n::Data>, symbols: &Symbols) -> Result<(), Refusal> {
    let mut handed = Handed::new();
    for declared in data.values() {
        let fields = declared
            .constructors
            .iter()
            .flat_map(|constructor| &constructor.fields)
            .chain(declared.wrapper.iter().map(|wrapper| &wrapper.field));
        for field in fields {
            hands_on(field, declared, data, &mut handed);
        }
    }
    let mut declarations: Vec<_> = data.values().collect();
    declarations.sort_by_key(|declared| (declared.module, declared.span));
    for declared in declarations {
        for parameter in 0..declared.parameters.len() {
            let from = (declared.name, parameter);
            let grows = handed
                .get(&from)
                .into_iter()
                .flatten()
                .any(|&(to, wrapped)| wrapped && reaches(&handed, to, from));
            if grows {
                let name = symbols.spelling(declared.name);
                return Err(failure(
                    declared.module,
                    declared.span,
                    format!("`{name}` holds itself at a larger type"),
                )
                .note("every size of it would be a type of its own, without end")
                .help("hold it at the parameters it is declared with"));
            }
        }
    }
    Ok(())
}

/// Refuse a declared type no value can be built of: each way of building
/// one holds another of it, or of another such type, as
/// `Node : {file: File, next: Node}` does. Built up from the types some way
/// of building needs nothing of that kind for. A declared type is taken to
/// be buildable at any arguments where it is at its own.
fn inhabited(data: &HashMap<Symbol, n::Data>, symbols: &Symbols) -> Result<(), Refusal> {
    let mut built: HashSet<Symbol> = HashSet::new();
    loop {
        let before = built.len();
        for declared in data.values() {
            let mut ways = declared
                .constructors
                .iter()
                .map(|constructor| constructor.fields.iter().collect::<Vec<_>>())
                .chain(declared.wrapper.iter().map(|wrapper| vec![&wrapper.field]))
                .peekable();
            let any_way = ways.peek().is_none();
            if any_way
                || ways.any(|fields| fields.iter().all(|field| buildable(field, data, &built)))
            {
                built.insert(declared.name);
            }
        }
        if built.len() == before {
            break;
        }
    }
    let mut unbuilt: Vec<_> = data
        .values()
        .filter(|declared| !built.contains(&declared.name))
        .collect();
    unbuilt.sort_by_key(|declared| (declared.module, declared.span));
    let Some(declared) = unbuilt.first() else {
        return Ok(());
    };
    let name = symbols.spelling(declared.name);
    Err(failure(
        declared.module,
        declared.span,
        format!("`{name}` has no values: building one needs another"),
    )
    .help("give it a way of being built that holds none of it, as a list's empty one does"))
}

/// Whether a value of `ty` can be built, where the declared types in
/// `built` can. A type variable, a function and the empty row are taken
/// to be.
fn buildable(ty: &h::Type, data: &HashMap<Symbol, n::Data>, built: &HashSet<Symbol>) -> bool {
    match ty {
        h::Type::Named(name, _) => !data.contains_key(name) || built.contains(name),
        h::Type::Variable(_) | h::Type::Hole | h::Type::Function(..) => true,
        h::Type::Variants(tags) => {
            tags.is_empty()
                || tags
                    .iter()
                    .any(|tag| tag.fields.iter().all(|field| buildable(field, data, built)))
        }
        h::Type::Record(fields, _) => fields
            .iter()
            .all(|(_, field)| buildable(field, data, built)),
        h::Type::Tuple(members) => members.iter().all(|member| buildable(member, data, built)),
    }
}

/// Each declared type's parameter, by position, and the parameters of the
/// declared types it is handed to, with whether it is wrapped in another
/// type there rather than handed on whole.
type Handed = HashMap<(Symbol, usize), Vec<((Symbol, usize), bool)>>;

/// Record what `declared` hands each of its parameters to within `ty`.
fn hands_on(
    ty: &h::Type,
    declared: &n::Data,
    data: &HashMap<Symbol, n::Data>,
    handed: &mut Handed,
) {
    match ty {
        h::Type::Named(name, arguments) => {
            if data.contains_key(name) {
                for (at, argument) in arguments.iter().enumerate() {
                    for (index, parameter) in declared.parameters.iter().enumerate() {
                        if mentions(argument, *parameter) {
                            let wrapped = *argument != h::Type::Variable(*parameter);
                            handed
                                .entry((declared.name, index))
                                .or_default()
                                .push(((*name, at), wrapped));
                        }
                    }
                }
            }
            for argument in arguments {
                hands_on(argument, declared, data, handed);
            }
        }
        h::Type::Variable(_) | h::Type::Hole => {}
        h::Type::Function(parameters, result) => {
            for part in parameters.iter().chain([result.as_ref()]) {
                hands_on(part, declared, data, handed);
            }
        }
        h::Type::Variants(tags) => {
            for field in tags.iter().flat_map(|tag| &tag.fields) {
                hands_on(field, declared, data, handed);
            }
        }
        h::Type::Record(fields, _) => {
            for (_, field) in fields {
                hands_on(field, declared, data, handed);
            }
        }
        h::Type::Tuple(members) => {
            for member in members {
                hands_on(member, declared, data, handed);
            }
        }
    }
}

/// Whether `ty` names the type variable `variable` anywhere in it.
fn mentions(ty: &h::Type, variable: Symbol) -> bool {
    match ty {
        h::Type::Variable(name) => *name == variable,
        h::Type::Hole => false,
        h::Type::Named(_, parts) | h::Type::Tuple(parts) => {
            parts.iter().any(|part| mentions(part, variable))
        }
        h::Type::Function(parameters, result) => parameters
            .iter()
            .chain([result.as_ref()])
            .any(|part| mentions(part, variable)),
        h::Type::Variants(tags) => tags
            .iter()
            .flat_map(|tag| &tag.fields)
            .any(|field| mentions(field, variable)),
        h::Type::Record(fields, _) => fields.iter().any(|(_, field)| mentions(field, variable)),
    }
}

/// Whether a parameter handed on from `from` arrives, by any number of
/// steps, at `to`.
fn reaches(handed: &Handed, from: (Symbol, usize), to: (Symbol, usize)) -> bool {
    let mut seen = HashSet::new();
    let mut pending = vec![from];
    while let Some(at) = pending.pop() {
        if at == to {
            return true;
        }
        if seen.insert(at) {
            pending.extend(handed.get(&at).into_iter().flatten().map(|&(next, _)| next));
        }
    }
    false
}
