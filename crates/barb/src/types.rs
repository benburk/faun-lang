//! Borrowed declaration metadata, without functions, expressions, or constants.
//! Program supplies this view from its own pools; IDs remain program-local.

use super::{Ctor, CtorId, Type, TypeId};
use crate::index::Pool;

/// Structural behavior relevant to runtime representation selection.
///
/// Names and constructor order do not affect this classification. A spine has
/// exactly one empty constructor and one constructor with exactly one recursive
/// field. `Sequence` is the one-payload case; a wider spine preserves the
/// general constructor shape rather than pretending its payload is one value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TypeShape {
    Uninhabited,
    Unit {
        constructor: CtorId,
    },
    Wrapper {
        constructor: CtorId,
        field: TypeId,
    },
    Product {
        constructor: CtorId,
    },
    Natural {
        empty: CtorId,
        push: CtorId,
        recursive: usize,
    },
    Sequence {
        empty: CtorId,
        push: CtorId,
        recursive: usize,
        element: TypeId,
    },
    Spine {
        empty: CtorId,
        push: CtorId,
        recursive: usize,
    },
    Enumeration,
    Sum,
}

#[derive(Clone, Copy, Debug)]
pub(super) struct TypeInfo<'a> {
    types: &'a Pool<TypeId, Type>,
    ctors: &'a Pool<CtorId, Ctor>,
    fields: &'a [TypeId],
}

impl<'a> TypeInfo<'a> {
    pub(super) const fn new(
        types: &'a Pool<TypeId, Type>,
        ctors: &'a Pool<CtorId, Ctor>,
        fields: &'a [TypeId],
    ) -> Self {
        Self {
            types,
            ctors,
            fields,
        }
    }

    /// How many types are declared, which bounds any walk through them.
    pub(super) const fn count(self) -> usize {
        self.types.len()
    }

    pub(super) fn get_type(self, id: TypeId) -> Option<&'a Type> {
        self.types.get(id)
    }
    pub(super) fn get_ctor(self, id: CtorId) -> Option<&'a Ctor> {
        self.ctors.get(id)
    }
    pub(super) fn type_(self, id: TypeId) -> &'a Type {
        &self.types[id]
    }
    pub(super) fn ctor(self, id: CtorId) -> &'a Ctor {
        &self.ctors[id]
    }

    pub(super) fn ctors(self, id: TypeId) -> &'a [Ctor] {
        &self.ctors.as_slice()[self.type_(id).constructors().range()]
    }

    pub(super) fn fields(self, id: CtorId) -> &'a [TypeId] {
        &self.fields[self.ctor(id).fields.range()]
    }

    pub(super) fn tag(self, id: CtorId) -> u32 {
        id.0 - self.type_(self.ctor(id).owner).constructors().start()
    }

    pub(super) fn ctor_at(self, owner: TypeId, tag: u32) -> CtorId {
        CtorId(self.type_(owner).constructors().start() + tag)
    }

    pub(super) fn shape(self, id: TypeId) -> TypeShape {
        let count = self.ctors(id).len();
        if count == 0 {
            return TypeShape::Uninhabited;
        }
        if count == 1 {
            let constructor = self.ctor_at(id, 0);
            return match self.fields(constructor) {
                [] => TypeShape::Unit { constructor },
                [field] => TypeShape::Wrapper {
                    constructor,
                    field: *field,
                },
                _ => TypeShape::Product { constructor },
            };
        }
        if count == 2
            && let Some(spine) = self.spine(id)
        {
            return spine;
        }
        if self.all_nullary(id, count) {
            TypeShape::Enumeration
        } else {
            TypeShape::Sum
        }
    }

    fn spine(self, id: TypeId) -> Option<TypeShape> {
        let (first, second) = (self.ctor_at(id, 0), self.ctor_at(id, 1));
        for (empty, push) in [(first, second), (second, first)] {
            if !self.fields(empty).is_empty() {
                continue;
            }
            let mut recursive = self
                .fields(push)
                .iter()
                .enumerate()
                .filter(|(_, field)| **field == id);
            let (Some((recursive, _)), None) = (recursive.next(), recursive.next()) else {
                continue;
            };
            let mut payload = self
                .fields(push)
                .iter()
                .enumerate()
                .filter(|(at, _)| *at != recursive)
                .map(|(_, field)| *field);
            return Some(match (payload.next(), payload.next()) {
                (None, None) => TypeShape::Natural {
                    empty,
                    push,
                    recursive,
                },
                (Some(element), None) => TypeShape::Sequence {
                    empty,
                    push,
                    recursive,
                    element,
                },
                _ => TypeShape::Spine {
                    empty,
                    push,
                    recursive,
                },
            });
        }
        None
    }

    fn all_nullary(self, id: TypeId, count: usize) -> bool {
        (0..count).all(|tag| {
            let tag = u32::try_from(tag).expect("a constructor count fits its encoded range");
            self.fields(self.ctor_at(id, tag)).is_empty()
        })
    }
}
