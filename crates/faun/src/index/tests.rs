use super::{Id, Pool};
use crate::ir::{FunctionId, ValueId};

#[test]
fn insertion_returns_the_inserted_typed_slot() {
    let mut pool = Pool::<FunctionId, &str>::default();
    let first: FunctionId = pool.push("first");
    let second = pool.push("second");
    assert_eq!(first, FunctionId(0));
    assert_eq!(second, FunctionId(1));
    assert_eq!(pool[first], "first");
    assert_eq!(pool.get(second), Some(&"second"));
    assert_eq!(pool.get(FunctionId(2)), None);
    assert_eq!(pool.get(FunctionId(u32::MAX)), None);
    assert_eq!(pool.position(|value| *value == "second"), Some(second));
    assert_eq!(pool.position(|value| *value == "absent"), None);
    pool[second] = "changed";
    assert_eq!(pool.as_slice(), &["first", "changed"]);
}

#[test]
fn growth_and_cloning_preserve_slot_numbers() {
    let mut pool = Pool::<ValueId, usize>::default();
    for value in 0..1024 {
        assert_eq!(pool.push(value), ValueId::at(value));
    }
    for (id, &value) in pool.iter_enumerated() {
        assert_eq!(pool[id], value);
        assert_eq!(id.index(), value);
    }
    let mut copy = pool.clone();
    copy[ValueId(0)] = 77;
    assert_eq!(pool[ValueId(0)], 0);
    assert_eq!(copy.push(1024), ValueId(1024));
    assert_eq!(pool.len(), 1024);
}

#[test]
fn id_iteration_is_an_owned_snapshot_not_a_borrow_or_live_cursor() {
    let mut pool = Pool::<ValueId, u32>::default();
    let first = pool.push(10);
    let second = pool.push(20);
    let ids = pool.ids();
    assert_eq!(ids.len(), 2);
    let later = pool.push(30);
    for id in ids {
        pool[id] += 1;
    }
    assert_eq!(pool[first], 11);
    assert_eq!(pool[second], 21);
    assert_eq!(pool[later], 30);
    assert_eq!(pool.ids().rev().collect::<Vec<_>>(), [later, second, first]);
}

#[test]
fn borrowed_iteration_keeps_values_in_slot_order() {
    let mut pool = Pool::<ValueId, u32>::default();
    pool.push(10);
    pool.push(20);
    for value in &mut pool {
        *value *= 2;
    }
    assert_eq!(pool.iter().copied().collect::<Vec<_>>(), [20, 40]);
    let mut entries = pool.iter_enumerated();
    assert_eq!(entries.len(), 2);
    assert_eq!(entries.next_back(), Some((ValueId(1), &40)));
    assert_eq!(entries.next(), Some((ValueId(0), &20)));
    assert_eq!(entries.next(), None);
    assert_eq!((&pool).into_iter().count(), 2);
}

#[test]
fn empty_storage_does_not_require_default_ids_or_elements() {
    struct Entity(u32);
    let mut pool = Pool::<ValueId, Entity>::default();
    assert_eq!(pool.len(), 0);
    assert_eq!(pool.get(ValueId(0)).map(|e| e.0), None);
    assert_eq!(pool.position(|_| true), None);
    assert_eq!(pool.ids().len(), 0);
    assert_eq!(pool.iter_enumerated().len(), 0);
    let id = pool.push(Entity(7));
    assert_eq!(pool[id].0, 7);
}

#[derive(Clone, Copy)]
struct ByteId(u8);
impl Id for ByteId {
    fn at(index: usize) -> Self {
        Self(u8::try_from(index).expect("a byte index"))
    }
    fn index(self) -> usize {
        usize::from(self.0)
    }
}

#[test]
fn an_unrepresentable_id_is_rejected_before_insertion() {
    let mut pool = Pool::<ByteId, usize>::default();
    for value in 0..=usize::from(u8::MAX) {
        let id = pool.push(value);
        assert_eq!(pool[id], value);
    }
    let before = pool.as_slice().to_vec();
    let error = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| pool.push(999)));
    assert!(error.is_err());
    assert_eq!(pool.as_slice(), before);
    assert_eq!(pool.get(ByteId(u8::MAX)), Some(&255));
}

#[test]
fn typed_storage_keeps_vec_size_and_compact_ids() {
    assert_eq!(size_of::<Pool<ValueId, u8>>(), size_of::<Vec<u8>>());
    assert_eq!(size_of::<ValueId>(), size_of::<u32>());
}
