//! Borrowed declaration metadata, without functions, expressions, or constants.
//! Program supplies this view from its own pools; IDs remain program-local.

use super::{Ctor, CtorId, Type, TypeId};
use crate::index::Pool;

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
}
