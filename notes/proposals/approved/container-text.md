# Proposal: A container is written as the call building it

- **Status:** Approved
- **Created:** 2026-11-05
- **Approved:** 2026-11-05
- **Affects:** the standard library's `Map`, `Set`, `SortedMap` and
  `SortedSet`, `notes/values/collections.md`, the standard library's README

---

## Summary

`Map`, `Set`, `SortedMap` and `SortedSet` each have a `to_str`, writing
the container as its `of_list` call, its entries in the order `to_list`
answers them.

| Written                              | Before  | After                       |
| ------------------------------------ | ------- | --------------------------- |
| `"${Map.of_list([("b", 2)])}"`       | refused | `Map.of_list([("b", 2)])`   |
| `Set.of_list([3, 1, 3]).to_str()`    | refused | `Set.of_list([3, 1])`       |
| `SortedSet.of_list([3, 1]).to_str()` | refused | `SortedSet.of_list([1, 3])` |
| An empty map                         | refused | `Map.of_list([])`           |

## Motivation

No container had a `to_str`, so one could not be spliced, printed by a
runner, or shown inside another value, and a program wanting to see one
wrote `"${m.to_list()}"`, which loses which container it was. Since
[quoted strings](quoted-strings.md), every other `to_str` writes a value
as source writes it.

## Design

Each container's `to_str` is `"Name.of_list(${to_list(container)})"`,
asking `to_str` of its keys and values through `where` bounds and nothing
else. `Map` and `Set` are written in insertion order, the sorted ones in
ascending key order. A seeded map's seed is not written.

## Costs

Two equal `Map`s built in different orders are written differently. The
text is longer than Python's.

## Alternatives considered

- **Braces, `{"a": 1}` and `{1, 2}`.** Braces are records in Faun, an
  empty map would be `{}` as an empty record is, and the text would not
  read back as a map.
- **Keys written in order.** It would ask `cmp` of a `Map`'s keys, which
  nothing else a `Map` asks, and `SortedMap` already gives it.
