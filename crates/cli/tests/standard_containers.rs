//! The standard containers and the hashing that keys them answer what
//! Ori's do. Each package is lowered for x86-64 and run on the reference
//! interpreter. Their larger cases outrun what folding may spend, and what
//! is left unfolded outgrows the 6502's 64 KiB, so the standard library's
//! own expectations, which every target runs, leave them here.

mod support;

use support::Package;

/// Each value feeds a hasher its parts, a record's and a tuple's members
/// in order, as the words and byte strings a tracing hasher records.
#[test]
fn each_value_feeds_a_hasher_its_parts() {
    let package = Package::new(
        "each-value-feeds-a-hasher-its-parts",
        r#"# What each value feeds a hasher, as the words and byte strings it wrote.
         Trace : List(Nat).(
           write_u64 : (Trace, U64) -> Trace
           write_u64(Trace(seen), word) -> Trace(seen.append(word.to_nat()))

           write_bytes : (Trace, List(U8)) -> Trace
           write_bytes(Trace(seen), bytes) ->
             Trace(seen.append(bytes.len()).concat(bytes.map(|byte| byte.to_nat())))
         )

         traced : Trace -> List(Nat)
         traced(Trace(seen)) -> seen

         fed(value) -> traced(value.hash_into(Trace([])))

         expect fed(7) == [7]
         expect fed(-3) == [1, 3]
         expect fed(True) == [1]
         expect fed("hi") == [2, 104, 105]
         expect fed([4, 5]) == [2, 4, 5]
         expect fed((1, "a")) == [1, 1, 97]
         expect fed({x: 2, y: [3]}) == fed({y: [3], x: 2}) & fed({x: 2, y: [3]}).len() == 3
         expect fed(((1, 2), [(3, True)])) == [1, 2, 1, 3, 1]"#,
    );
    assert_eq!(support::test_file(&package.entry()), (Vec::new(), 8));
}

/// A sorted map and set answer in key order, whatever order they were
/// built in.
#[test]
fn sorted_containers_keep_their_keys_in_order() {
    let package = Package::new(
        "sorted-containers-keep-their-keys-in-order",
        r#"built : SortedMap(Nat, Str)
         built = SortedMap.of_list([(5, "five"), (1, "one"), (9, "nine"), (3, "three"), (7, "seven"), (1, "uno")])

         expect built.len() == 5
         expect built.keys() == [1, 3, 5, 7, 9]
         expect built.get(1) == Ok("uno")
         expect built.get(4).is_err()
         expect built.remove(5).keys() == [1, 3, 7, 9]
         expect built.remove(4).len() == 5
         expect built.fold(0, |total, key, _| total + key) == 25
         expect List.range(200).fold(SortedMap.empty, |map, n| map.insert(n * 7 % 200, n)).len() == 200
         expect List.range(100).fold(SortedMap.empty, |map, n| map.insert(n, n)).remove(50).remove(3).keys().len() == 98
         expect SortedMap.of_list([((1, 2), "a"), ((0, 5), "b")]).keys() == [(0, 5), (1, 2)]
         expect SortedSet.of_list([1, 2, 3]).intersection(SortedSet.of_list([2, 3, 4])).to_list() == [2, 3]
         expect SortedSet.of_list([1, 2, 3]).difference(SortedSet.of_list([2])).to_list() == [1, 3]
         expect SortedSet.of_list(["b", "a", "c"]).contains("a")
         expect SortedSet.of_list([3, 1, 2, 3, 1]).to_list() == [1, 2, 3]
         expect SortedSet.of_list([1, 2, 3]).union(SortedSet.of_list([3, 4])).to_list() == [1, 2, 3, 4]"#,
    );
    assert_eq!(support::test_file(&package.entry()), (Vec::new(), 15));
}

/// A map and a set keyed by hash answer in insertion order, a key of any
/// shape that feeds a hasher, and `Map.grouped` gathers into one.
#[test]
fn hashed_containers_keep_insertion_order() {
    let package = Package::new(
        "hashed-containers-keep-insertion-order",
        r#"counts : Map(Str, Nat)
         counts = Map.of_list([("b", 2), ("a", 1), ("c", 3)])

         expect counts.get("a") == Ok(1)
         expect counts.get("z") == Err(Missing)
         expect counts.get_or("z", 0) == 0
         expect counts.len() == 3 & !counts.is_empty() & Map.empty.is_empty()
         expect counts.keys() == ["b", "a", "c"]
         expect counts.insert("a", 10).to_list() == [("b", 2), ("a", 10), ("c", 3)]
         expect counts.remove("a").keys() == ["b", "c"] & counts.remove("a").len() == 2
         expect counts.remove("q") == counts
         expect counts.update("c", |n| n * 2).get("c") == Ok(6)
         expect counts.map_values(|n| n + 1).values() == [3, 2, 4]
         expect counts.fold(0, |total, _, n| total + n) == 6
         expect counts == Map.of_list([("c", 3), ("a", 1), ("b", 2)])
         expect counts != counts.insert("a", 5)
         expect Map.of_list(List.range(100).map(|n| (n, n * n))).get(77) == Ok(5929)
         expect Map.of_list(List.range(100).map(|n| (n, n))).len() == 100
         expect Map.of_list([((1, "x"), True)]).contains((1, "x"))
         expect Map.of_list([({a: 1, b: [2]}, 7)]).get({b: [2], a: 1}) == Ok(7)
         expect Map.of_list(List.range(40).map(|n| (n, n))).remove(3).remove(20).insert(3, 9).keys().len() == 39

         expect Map.grouped([1, 2, 3, 4, 5, 6], |n| n % 3).to_list() == [(1, [1, 4]), (2, [2, 5]), (0, [3, 6])]
         expect Map.grouped(["ab", "c", "de", "f"], |word| word.len()).values() == [["ab", "de"], ["c", "f"]]
         expect Map.counted(["b", "a", "b"]).to_list() == [("b", 2), ("a", 1)]

         letters : Set(Str)
         letters = Set.of_list(["x", "y", "x", "z"])

         expect letters.to_list() == ["x", "y", "z"]
         expect letters.contains("y") & !letters.contains("w")
         expect letters.union(Set.of_list(["w"])).len() == 4
         expect letters.intersection(Set.of_list(["z", "x", "q"])).to_list() == ["x", "z"]
         expect letters.difference(Set.of_list(["x"])).to_list() == ["y", "z"]
         expect letters == Set.of_list(["z", "y", "x"])"#,
    );
    assert_eq!(support::test_file(&package.entry()), (Vec::new(), 27));
}
