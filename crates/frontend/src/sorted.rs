//! Hash tables written in the order of their keys, so a snapshot of the
//! same state is the same bytes however the tables were built: they are
//! read back as hash tables, as any map is.

use serde::{Serialize, Serializer};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

/// `map`, written in the order of its keys.
pub(crate) fn map<K: Ord + Serialize, V: Serialize, H, S: Serializer>(
    map: &HashMap<K, V, H>,
    serializer: S,
) -> Result<S::Ok, S::Error> {
    map.iter().collect::<BTreeMap<_, _>>().serialize(serializer)
}

/// A map of maps, each written in the order of its keys.
pub(crate) fn maps<K: Ord + Serialize, J: Ord + Serialize, V: Serialize, H, I, S: Serializer>(
    maps: &HashMap<K, HashMap<J, V, I>, H>,
    serializer: S,
) -> Result<S::Ok, S::Error> {
    maps.iter()
        .map(|(key, map)| (key, map.iter().collect::<BTreeMap<_, _>>()))
        .collect::<BTreeMap<_, _>>()
        .serialize(serializer)
}

/// `set`, written in order.
pub(crate) fn set<K: Ord + Serialize, H, S: Serializer>(
    set: &HashSet<K, H>,
    serializer: S,
) -> Result<S::Ok, S::Error> {
    set.iter().collect::<BTreeSet<_>>().serialize(serializer)
}
