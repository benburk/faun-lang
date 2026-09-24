//! The constant module owns storage and every insertion path. Only Program
//! pairs these operations with its declaration metadata; the pool is not public.

use num_bigint::BigUint;

use super::{
    Constant, ConstructionError, Held, Value, checked, encode, write_natural, write_number,
};
use crate::barb::budget::LimitExceeded;
use crate::barb::types::TypeInfo;
use crate::barb::{ConstId, Range, TypeId};
use crate::index::Pool;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Entry {
    owner: TypeId,
    bytes: Range,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(in crate::barb) struct ConstantPool {
    entries: Pool<ConstId, Entry>,
    bytes: Vec<u8>,
}

impl ConstantPool {
    pub(in crate::barb) fn bytes(&self, id: ConstId) -> &[u8] {
        &self.bytes[self.entries[id].bytes.range()]
    }

    pub(in crate::barb) fn get<'a>(&'a self, types: TypeInfo<'a>, id: ConstId) -> Constant<'a> {
        Constant::new(types, self.entries[id].owner, self.bytes(id))
    }

    pub(in crate::barb) fn intern(
        &mut self,
        types: TypeInfo<'_>,
        owner: TypeId,
        value: &Value,
    ) -> Result<ConstId, ConstructionError> {
        checked::tree(types, owner, value)?;
        Ok(self.hold(owner, |out| encode(types, owner, value, out)))
    }

    pub(in crate::barb) fn number(
        &mut self,
        types: TypeInfo<'_>,
        owner: TypeId,
        value: u64,
    ) -> Result<ConstId, ConstructionError> {
        checked::natural(types, owner)?;
        Ok(self.hold(owner, |out| write_number(value, out)))
    }

    pub(in crate::barb) fn natural(
        &mut self,
        types: TypeInfo<'_>,
        owner: TypeId,
        value: &BigUint,
    ) -> Result<ConstId, ConstructionError> {
        checked::natural(types, owner)?;
        Ok(self.hold(owner, |out| write_natural(value, out)))
    }

    pub(in crate::barb) fn byte_spine(
        &mut self,
        types: TypeInfo<'_>,
        owner: TypeId,
        bytes: &[u8],
    ) -> Result<ConstId, ConstructionError> {
        checked::byte_spine(types, owner)?;
        let count = u64::try_from(bytes.len()).map_err(|_| LimitExceeded::ValueSize)?;
        Ok(self.hold(owner, |out| {
            write_number(count, out);
            for &byte in bytes {
                write_number(u64::from(byte), out);
            }
        }))
    }

    pub(in crate::barb) fn intern_held(&mut self, value: &Held) -> ConstId {
        self.hold(value.owner(), |out| out.extend_from_slice(value.encoded()))
    }

    fn hold(&mut self, owner: TypeId, write: impl FnOnce(&mut Vec<u8>)) -> ConstId {
        let start = self.bytes.len();
        write(&mut self.bytes);
        self.entries.push(Entry {
            owner,
            bytes: Range::of(start, self.bytes.len() - start),
        })
    }

    #[cfg(test)]
    pub(in crate::barb) fn allocations(&self) -> [*const (); 2] {
        [
            self.entries.as_slice().as_ptr().cast(),
            self.bytes.as_ptr().cast(),
        ]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::barb::model::TypeDefinition;
    use crate::barb::{Ctor, CtorId, Symbol, Type};

    #[test]
    fn a_pool_needs_only_declarations_not_a_program_or_name_table() {
        let mut types = Pool::default();
        let nat = types.push(Type {
            name: Symbol::at(0),
            inline: false,
            definition: TypeDefinition::Defined(Range::of(0, 2)),
        });
        let mut ctors = Pool::default();
        // Successor first, empty constructor last. Names are opaque to the codec.
        for fields in [Range::of(0, 1), Range::EMPTY] {
            ctors.push(Ctor {
                name: Symbol::at(0),
                owner: nat,
                fields,
            });
        }
        let fields = [nat];
        let types = TypeInfo::new(&types, &ctors, &fields);
        let mut pool = ConstantPool::default();
        let zero = pool.number(types, nat, 0).unwrap();
        assert_eq!(pool.get(types, zero).constructor(), CtorId::at(1));
        let one = pool.number(types, nat, 1).unwrap();
        assert_eq!(pool.bytes(one), &[1]);
        assert_eq!(pool.get(types, one).constructor(), CtorId::at(0));
    }
}
