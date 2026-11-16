//! What a test shows a value can hold. Where it holds, the value is one
//! the pattern matches; where it fails, one no row matches. Either way it
//! holds a resource only where some value it can still be holds one.
//!
//! Where it fails is Maranget's usefulness ("Warnings for pattern
//! matching", 2007), as coverage asks it, with one more demand: the value
//! no row matches must hold a resource. That demand is followed into the
//! fields of each constructor that can hold one. A row with a guard matches
//! nothing here, since the guard may fail, and a number, a range or a
//! string matches nothing whole, so a test of one never empties a value.

use super::Facts;
use crate::Symbol;
use crate::specialize::{Pattern, Split, Type};

/// A pattern as narrowing reads it, a list's as its constructors.
#[derive(Clone, Debug)]
enum Shape {
    /// Matches anything: a wildcard or a binding.
    Any,
    Constructor(Symbol, Vec<Self>),
    /// A record, by the fields it names; the others it takes whatever of.
    Record(Vec<(Symbol, Self)>),
    Tuple(Vec<Self>),
    /// Matches some values of its type, which only running it says: a
    /// number, a range, a string, or a list's end that is itself tested.
    Tested,
}

impl Facts<'_> {
    /// Whether some value of `ty` that `pattern` matches holds a resource.
    pub(super) fn matched_carries(&self, pattern: &Pattern, ty: &Type) -> bool {
        self.shape_carries(&self.shape(pattern), ty)
    }

    /// Whether some value of `ty` that none of `rows` matches holds a
    /// resource.
    pub(super) fn unmatched_carries<'p>(
        &self,
        rows: impl IntoIterator<Item = &'p Pattern>,
        ty: &Type,
    ) -> bool {
        let rows = rows
            .into_iter()
            .map(|pattern| vec![self.shape(pattern)])
            .collect();
        self.escapes(rows, std::slice::from_ref(ty), Some(0))
    }

    fn shape(&self, pattern: &Pattern) -> Shape {
        match pattern {
            Pattern::Wild | Pattern::Bind(_) => Shape::Any,
            Pattern::As(_, pattern) => self.shape(pattern),
            Pattern::Constructor(name, fields) => Shape::Constructor(
                *name,
                fields.iter().map(|field| self.shape(field)).collect(),
            ),
            Pattern::Number { .. } | Pattern::Range | Pattern::String | Pattern::Ending => {
                Shape::Tested
            }
            Pattern::List(elements, rest) => self.listed(elements, rest.as_deref()),
            Pattern::Split(split) => self.ending(split),
            Pattern::Record(fields) => Shape::Record(
                fields
                    .iter()
                    .map(|(name, field)| (*name, self.shape(field)))
                    .collect(),
            ),
            Pattern::Product(members) => {
                Shape::Tuple(members.iter().map(|member| self.shape(member)).collect())
            }
        }
    }

    /// A list's elements and the rest of it, as the constructors it is.
    fn listed(&self, elements: &[Pattern], rest: Option<&Pattern>) -> Shape {
        let tail = rest.map_or_else(
            || Shape::Constructor(self.list_nil, Vec::new()),
            |rest| self.shape(rest),
        );
        elements.iter().rev().fold(tail, |tail, element| {
            Shape::Constructor(self.list_cons, vec![self.shape(element), tail])
        })
    }

    /// A list's end: where nothing in it is tested, a list ending in `m`
    /// elements is any list of `m` or more.
    fn ending(&self, split: &Split) -> Shape {
        let front = self.shape(&split.front);
        let last: Vec<Shape> = split.last.iter().map(|each| self.shape(each)).collect();
        if !matches!(front, Shape::Any) || !last.iter().all(|each| matches!(each, Shape::Any)) {
            return Shape::Tested;
        }
        last.iter().fold(Shape::Any, |tail, _| {
            Shape::Constructor(self.list_cons, vec![Shape::Any, tail])
        })
    }

    /// Whether some value of `ty` that `shape` matches holds a resource.
    fn shape_carries(&self, shape: &Shape, ty: &Type) -> bool {
        match (shape, ty) {
            (Shape::Constructor(name, shapes), _) if !self.is_resource(ty) => {
                self.fields(*name, ty).map_or_else(
                    || self.carries(ty),
                    |fields| {
                        shapes
                            .iter()
                            .zip(&fields)
                            .any(|(shape, field)| self.shape_carries(shape, field))
                    },
                )
            }
            (Shape::Tuple(shapes), Type::Tuple(members)) => shapes
                .iter()
                .zip(members)
                .any(|(shape, member)| self.shape_carries(shape, member)),
            (Shape::Record(named), Type::Record(fields)) => fields.iter().any(|(name, field)| {
                named.iter().find(|(each, _)| each == name).map_or_else(
                    || self.carries(field),
                    |(_, shape)| self.shape_carries(shape, field),
                )
            }),
            _ => self.carries(ty),
        }
    }

    /// Whether some values of `columns`, one each, are matched by none of
    /// `rows` while the one at `need`, where there is one, holds a
    /// resource.
    fn escapes(&self, rows: Vec<Vec<Shape>>, columns: &[Type], need: Option<usize>) -> bool {
        let Some((ty, _)) = columns.split_first() else {
            return rows.is_empty();
        };
        if need == Some(0) && !self.carries(ty) {
            return false;
        }
        let parts = self.forms(ty, &rows);
        let Some(parts) = parts else {
            return self.escapes_whole(rows, columns, need);
        };
        parts.into_iter().any(|(constructor, fields)| {
            let rows = rows
                .iter()
                .filter_map(|row| {
                    Some(
                        [
                            opened(&row[0], constructor, ty, fields.len())?,
                            row[1..].to_vec(),
                        ]
                        .concat(),
                    )
                })
                .collect::<Vec<_>>();
            let columns = [fields.as_slice(), &columns[1..]].concat();
            match need {
                Some(0) => {
                    (0..fields.len()).any(|at| self.escapes(rows.clone(), &columns, Some(at)))
                }
                need => self.escapes(rows, &columns, need.map(|at| at - 1 + fields.len())),
            }
        })
    }

    /// How a value of `ty` is built, where `rows` tell its ways apart: a
    /// tuple's or a record's one way, by its fields, or each constructor
    /// by its own. `None` where nothing in the rows takes it apart.
    fn forms(&self, ty: &Type, rows: &[Vec<Shape>]) -> Option<Vec<(Option<Symbol>, Vec<Type>)>> {
        match ty {
            Type::Tuple(members) => Some(vec![(None, members.clone())]),
            Type::Record(fields) => Some(vec![(
                None,
                fields.iter().map(|(_, field)| field.clone()).collect(),
            )]),
            _ if rows
                .iter()
                .any(|row| matches!(row[0], Shape::Constructor(..))) =>
            {
                self.constructors_of(ty).and_then(|constructors| {
                    constructors
                        .into_iter()
                        .map(|each| Some((Some(each), self.fields(each, ty)?)))
                        .collect()
                })
            }
            _ => None,
        }
    }

    /// The first column passed over, as nothing in it is taken apart: the
    /// rows taking anything there go on, and a value holding a resource is
    /// there for the taking where one is needed.
    fn escapes_whole(&self, rows: Vec<Vec<Shape>>, columns: &[Type], need: Option<usize>) -> bool {
        let rows = rows
            .into_iter()
            .filter(|row| matches!(row[0], Shape::Any))
            .map(|row| row[1..].to_vec())
            .collect();
        self.escapes(rows, &columns[1..], need.and_then(|at| at.checked_sub(1)))
    }
}

/// The fields `head` matches of a value of `ty` built by `constructor`,
/// or by its one shape where it is `None`; `None` where `head` may not
/// match it.
fn opened(
    head: &Shape,
    constructor: Option<Symbol>,
    ty: &Type,
    arity: usize,
) -> Option<Vec<Shape>> {
    match (head, constructor, ty) {
        (Shape::Any, _, _) => Some(vec![Shape::Any; arity]),
        (Shape::Constructor(name, fields), Some(each), _) => {
            (*name == each).then(|| fields.clone())
        }
        (Shape::Tuple(members), None, _) => Some(members.clone()),
        (Shape::Record(named), None, Type::Record(fields)) => Some(
            fields
                .iter()
                .map(|(name, _)| {
                    named
                        .iter()
                        .find(|(each, _)| each == name)
                        .map_or(Shape::Any, |(_, shape)| shape.clone())
                })
                .collect(),
        ),
        _ => None,
    }
}
