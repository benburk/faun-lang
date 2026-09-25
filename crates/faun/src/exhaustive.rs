//! Whether each definition's clauses cover every value its parameters hold.
//!
//! This runs on checked HIR, before specialization, so a generic definition
//! nothing calls is judged too: whether `[]` and `[x *rest]` cover a list
//! does not depend on what the list holds. It is Maranget's usefulness
//! ("Warnings for pattern matching", 2007): the clauses cover everything
//! exactly when a row of wildcards after them would match nothing, and when
//! it would, what it matches is an example the diagnostic names.
//!
//! A clause with a guard covers nothing here, since the guard may fail.
//! Numerals match as the `Nat` and `Int` constructors they stand for, so
//! `0` and `Succ(n)` cover a `Nat`; numerals alone never do. A column whose
//! constructors belong to no declared type is not judged.

use std::collections::HashMap;

use num_bigint::BigUint;

use crate::blessed::PreludeIds;
use crate::check::CheckError;
use crate::hir as h;
use crate::{Symbol, Symbols};

/// Refuse the first definition whose clauses leave some value unmatched.
pub(crate) fn exhaustive(
    program: &h::Program,
    symbols: &Symbols,
    prelude: &PreludeIds,
) -> Result<(), CheckError> {
    let checker = Coverage::new(program, prelude);
    for module in &program.modules {
        for (name, clauses) in definitions(module) {
            let width = clauses[0].patterns.len();
            let rows = clauses
                .iter()
                .filter(|clause| clause.guard.is_none())
                .map(|clause| clause.patterns.iter().map(|p| checker.pattern(p)).collect())
                .collect();
            if let Some(missing) = checker.missing(rows, width) {
                let example = checker.render_all(&missing, symbols);
                let spelled = spelling(symbols, name);
                return Err(CheckError {
                    module: module.source,
                    span: clauses[0].span,
                    message: format!(
                        "`{spelled}` does not cover every case: no clause matches `{spelled}({example})`"
                    ),
                });
            }
        }
    }
    Ok(())
}

/// Each definition's clauses in `module`, methods included, in the order
/// written.
fn definitions(module: &h::Module) -> Vec<(Symbol, Vec<&h::Clause>)> {
    let mut found: Vec<(Symbol, Vec<&h::Clause>)> = Vec::new();
    let clauses = module.items.iter().flat_map(|item| match item {
        h::Item::Clause(clause) => vec![clause],
        h::Item::Data(data) => data
            .methods
            .iter()
            .filter_map(|method| match method {
                h::MethodItem::Clause(clause) => Some(clause),
                h::MethodItem::Signature(_) => None,
            })
            .collect(),
        h::Item::Signature(_) => Vec::new(),
    });
    for clause in clauses {
        match found.iter_mut().find(|(name, _)| *name == clause.name) {
            Some((_, held)) => held.push(clause),
            None => found.push((clause.name, vec![clause])),
        }
    }
    found
}

/// A pattern as coverage reads it.
#[derive(Clone, Debug)]
enum Pattern {
    /// Matches anything: a wildcard or a binding.
    Wild,
    Constructor(Symbol, Vec<Self>),
    /// A numeral, read as constructors once its column's type is known.
    Number(BigUint, bool),
    /// A range, which covers no constructor wholly.
    Range,
    /// A record, its fields ordered by name.
    Record(Vec<(Symbol, Self)>),
}

struct Coverage<'a> {
    prelude: &'a PreludeIds,
    /// Each constructor's declared type.
    owners: HashMap<Symbol, Symbol>,
    /// Each declared type's constructors, and how many fields each takes.
    constructors: HashMap<Symbol, Vec<(Symbol, usize)>>,
}

impl<'a> Coverage<'a> {
    fn new(program: &h::Program, prelude: &'a PreludeIds) -> Self {
        let mut owners = HashMap::new();
        let mut constructors = HashMap::new();
        let declarations = program
            .modules
            .iter()
            .flat_map(|module| &module.items)
            .filter_map(|item| match item {
                h::Item::Data(data) => Some(data),
                _ => None,
            });
        for data in declarations {
            let mut held: Vec<_> = data
                .constructors
                .iter()
                .map(|constructor| (constructor.name, constructor.fields.len()))
                .collect();
            if let Some(wrapper) = &data.wrapper {
                held.push((wrapper.constructor, 1));
            }
            for (name, _) in &held {
                owners.insert(*name, data.name);
            }
            constructors.insert(data.name, held);
        }
        Self {
            prelude,
            owners,
            constructors,
        }
    }

    fn pattern(&self, pattern: &h::Pattern) -> Pattern {
        match pattern {
            h::Pattern::Wild | h::Pattern::Bind(_) => Pattern::Wild,
            h::Pattern::Constructor(name, fields) => Pattern::Constructor(
                *name,
                fields.iter().map(|field| self.pattern(field)).collect(),
            ),
            h::Pattern::Number {
                magnitude,
                negative,
            } => Pattern::Number(magnitude.clone(), *negative),
            h::Pattern::Range(_, _) => Pattern::Range,
            h::Pattern::List(elements, rest) => {
                let mut tail = rest.as_ref().map_or_else(
                    || Pattern::Constructor(self.prelude.list_nil, Vec::new()),
                    |rest| self.pattern(rest),
                );
                for element in elements.iter().rev() {
                    tail = Pattern::Constructor(
                        self.prelude.list_cons,
                        vec![self.pattern(element), tail],
                    );
                }
                tail
            }
            h::Pattern::Record(fields) => {
                let mut fields: Vec<_> = fields
                    .iter()
                    .map(|(name, field)| (*name, self.pattern(field)))
                    .collect();
                fields.sort_by_key(|(name, _)| *name);
                Pattern::Record(fields)
            }
        }
    }

    /// Values of `width` columns no row matches, as one example pattern per
    /// column, or `None` when the rows cover everything.
    fn missing(&self, rows: Vec<Vec<Pattern>>, width: usize) -> Option<Vec<Pattern>> {
        if width == 0 {
            return rows.is_empty().then(Vec::new);
        }
        let heads = || rows.iter().map(|row| &row[0]);
        if let Some(names) = heads().find_map(|head| match head {
            Pattern::Record(fields) => Some(fields.iter().map(|(name, _)| *name).collect()),
            _ => None,
        }) {
            return self.missing_record(rows, width, names);
        }
        let owner = heads().find_map(|head| match head {
            Pattern::Constructor(name, _) => Some(self.owners.get(name).copied()),
            _ => None,
        });
        match owner {
            // Constructors of no declared type: nothing to enumerate.
            Some(None) => None,
            Some(Some(owner)) => self.missing_constructor(&rows, width, owner),
            None => {
                let rest = rows
                    .into_iter()
                    .filter(|row| matches!(row[0], Pattern::Wild))
                    .map(|row| row[1..].to_vec())
                    .collect();
                let mut missing = self.missing(rest, width - 1)?;
                missing.insert(0, Pattern::Wild);
                Some(missing)
            }
        }
    }

    fn missing_record(
        &self,
        rows: Vec<Vec<Pattern>>,
        width: usize,
        names: Vec<Symbol>,
    ) -> Option<Vec<Pattern>> {
        let arity = names.len();
        let rows = rows
            .into_iter()
            .map(|mut row| {
                let rest = row.split_off(1);
                let mut fields = match row.pop() {
                    Some(Pattern::Record(fields)) => {
                        fields.into_iter().map(|(_, field)| field).collect()
                    }
                    _ => vec![Pattern::Wild; arity],
                };
                fields.extend(rest);
                fields
            })
            .collect();
        let mut missing = self.missing(rows, width - 1 + arity)?;
        let rest = missing.split_off(arity);
        let mut record = vec![Pattern::Record(names.into_iter().zip(missing).collect())];
        record.extend(rest);
        Some(record)
    }

    fn missing_constructor(
        &self,
        rows: &[Vec<Pattern>],
        width: usize,
        owner: Symbol,
    ) -> Option<Vec<Pattern>> {
        for &(constructor, arity) in &self.constructors[&owner] {
            let specialized = rows
                .iter()
                .filter_map(|row| {
                    let mut fields = match self.as_constructor(&row[0], owner)? {
                        Pattern::Wild => vec![Pattern::Wild; arity],
                        Pattern::Constructor(found, fields) if found == constructor => fields,
                        _ => return None,
                    };
                    fields.extend(row[1..].iter().cloned());
                    Some(fields)
                })
                .collect();
            if let Some(mut missing) = self.missing(specialized, width - 1 + arity) {
                let rest = missing.split_off(arity);
                let mut found = vec![Pattern::Constructor(constructor, missing)];
                found.extend(rest);
                return Some(found);
            }
        }
        None
    }

    /// A column head of `owner`'s type as a wildcard or one constructor, or
    /// `None` for a range, which covers no constructor wholly.
    fn as_constructor(&self, head: &Pattern, owner: Symbol) -> Option<Pattern> {
        match head {
            Pattern::Number(magnitude, negative) => self.numeral(magnitude, *negative, owner),
            Pattern::Range => None,
            other => Some(other.clone()),
        }
    }

    /// The outermost constructor a numeral of `owner`'s type is.
    fn numeral(&self, magnitude: &BigUint, negative: bool, owner: Symbol) -> Option<Pattern> {
        let constructors = &self.constructors[&owner];
        let [(first, _), (second, _)] = constructors.as_slice() else {
            return None;
        };
        if owner == self.prelude.nat {
            if *magnitude == BigUint::ZERO {
                return Some(Pattern::Constructor(*first, Vec::new()));
            }
            let smaller = Pattern::Number(magnitude - 1u8, false);
            return Some(Pattern::Constructor(*second, vec![smaller]));
        }
        if owner == self.prelude.int {
            if negative && *magnitude != BigUint::ZERO {
                let smaller = Pattern::Number(magnitude - 1u8, false);
                return Some(Pattern::Constructor(*second, vec![smaller]));
            }
            let natural = Pattern::Number(magnitude.clone(), false);
            return Some(Pattern::Constructor(*first, vec![natural]));
        }
        None
    }

    /// Example patterns side by side, as arguments are written.
    fn render_all(&self, patterns: &[Pattern], symbols: &Symbols) -> String {
        patterns
            .iter()
            .map(|pattern| self.render(pattern, symbols))
            .collect::<Vec<_>>()
            .join(" ")
    }

    /// An example pattern as the program would write it.
    fn render(&self, pattern: &Pattern, symbols: &Symbols) -> String {
        match pattern {
            Pattern::Wild | Pattern::Range | Pattern::Number(..) => "_".to_owned(),
            Pattern::Constructor(name, fields) if *name == self.prelude.list_nil => {
                debug_assert!(fields.is_empty());
                "[]".to_owned()
            }
            Pattern::Constructor(name, fields) if *name == self.prelude.list_cons => {
                let [head, tail] = fields.as_slice() else {
                    unreachable!("a list's cons takes a head and a tail")
                };
                format!(
                    "[{} *{}]",
                    self.render(head, symbols),
                    self.render(tail, symbols)
                )
            }
            Pattern::Constructor(name, fields) if fields.is_empty() => {
                spelling(symbols, *name).to_owned()
            }
            Pattern::Constructor(name, fields) => format!(
                "{}({})",
                spelling(symbols, *name),
                self.render_all(fields, symbols)
            ),
            Pattern::Record(fields) => format!(
                "{{{}}}",
                fields
                    .iter()
                    .map(|(name, field)| format!(
                        "{}: {}",
                        spelling(symbols, *name),
                        self.render(field, symbols)
                    ))
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
        }
    }
}

/// A global's name as the program spells it, without its module identity.
fn spelling(symbols: &Symbols, name: Symbol) -> &str {
    let canonical = symbols.text(name);
    canonical
        .rsplit_once("$$")
        .map_or(canonical, |(_, spelled)| spelled)
}
