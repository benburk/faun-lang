---
name: rust-module-design
description: Use when designing, extracting, or reviewing Rust modules and APIs for total contracts, ownership, coupling, and allocation costs.
---

# Rust module design

Remove caller obligations and representation knowledge; preserve the compiler's data-oriented layout.

**Design:** sketch the contract and an ordinary caller before implementing.
**Lint:** inspect definitions, mutation paths, and callers. Report at most five supported
findings with `path:line` evidence, the smallest change, and a validation case.
Do not edit in lint mode unless asked. Treat search hits and Clippy warnings as leads.

## Contracts

- Make operations total over their inputs. Prefer ordinary Rust types (`Result`,
  enums, references, tuples, arrays) and private validated handles over frameworks.
  Return the inserted ID, range, or scalar rather than making callers reconstruct it.
- Validate at construction boundaries and preserve those facts through mutation.
  Remove repeated `unwrap`/`expect` obligations through better contracts. Keep justified
  invariant assertions; never replace them with plausible defaults.
- Match exhaustive views instead of repeatedly probing kinds. Distinguish wrong kind,
  overflow, malformed input, and resource refusal. Give `None` one meaning.
- Name different operations instead of adding boolean modes. Keep genuine predicates
  and independent switches. Distinguish pending, empty, and unreachable states.
- State what rejection leaves changed. Validate before writing when possible;
  a precheck is not rollback. Test the promised failure postcondition.

## Boundaries

- Put storage and coordinated updates under one owner. Moving functions while callers
  still manipulate the buffers is not encapsulation. Store each authoritative fact once;
  give caches an invalidation rule.
- Accept the concrete component or borrowed metadata needed, not all of `Program`.
  Apply Demeter to representation knowledge, not dot counts. Avoid forwarding layers
  that hide no invariant or useful operation.
- Keep functions focused, but keep tightly coupled code and cohesive exhaustive matches
  together. Extract for a named responsibility, not a line limit. Share invariants;
  leave independently changing passes and backend policies independent.
- Justify traits and abstractions with actual callers. Prefer small duplication to a
  shared framework with mode flags and escape hatches.
- Typed IDs and ordinary lifetimes do not prove arena provenance. Document same-owner
  requirements and which IDs or analyses rebuilding invalidates.

## Work and layout

- Preserve compact IDs, contiguous pools, ranges, explicit ownership, and separate passes.
  Do not add per-node boxes, `Rc<RefCell<_>>`, virtual hierarchies, or cloned arenas for style.
- Trace copies, allocations, and repeated scans through callers. Borrow or iterate when
  possible; retain copies that provide necessary snapshots or failure atomicity.
- Check limits before expensive work. Preserve exact work/size/depth charges and refusal
  thresholds unless changing policy deliberately; even zero-byte fields can cost work.
- Report obligations removed and introduced, layout/allocation tradeoffs, and validation.
  Allocation removal is not a measured speedup. Preserve evaluation order and effects.

Design references: [small-method rules](https://thoughtbot.com/blog/sandi-metz-rules-for-developers)
and [the wrong abstraction](https://sandimetz.com/blog/2016/1/20/the-wrong-abstraction).
