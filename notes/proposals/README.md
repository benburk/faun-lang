# Proposals

A change to what Faun programs mean or how they are written starts here: new
syntax, a new rule in the checker, a change to what the standard library
promises. The format follows Ori's (`docs/ori_lang/proposals/` in
[ori-lang](https://github.com/upstat-io/ori-lang)).

## Where a proposal lives

The folder a proposal is in is its status:

- `drafts/`: being written or argued. Nothing in it is built.
- `approved/`: decided. It may be built already, or not yet.
- `rejected/`: decided against. The reasons stay for the next person to ask.
- `superseded/`: replaced by a later proposal, which it names.

A proposal moves between folders when its status changes, and its `Status`
line changes with it. `just check` fails where the two disagree.

A file is named for its subject, in lowercase words joined by hyphens:
`blocks.md`, not `block-proposal.md`.

## Changing a decided proposal

An approved proposal is not rewritten. A correction or a detail settled while
building it goes in an `Errata` section at the end, dated. A proposal that
replaces another names it under `Supersedes`, and the old one moves to
`superseded/` with a notice at its top naming its replacement.

## Template

```markdown
# Proposal: Title

- **Status:** Draft
- **Author:** name
- **Created:** 2026-01-31
- **Affects:** what changes: the lexer, the checker, every program, ...

---

## Summary

What changes, in a paragraph, and a table of before and after where the
change is to syntax.

## Motivation

Why, with evidence from real programs: counts, excerpts, the code that is
hard to write today.

## Design

What the change is, precisely enough to build from. Each decision the
change forces, and what was decided.

## Costs

What it takes away or makes worse, measured where it can be.

## Alternatives considered

Each other way, and why not.

## Implementation impact

What changes in the compiler, the grammar files, the tools and the
programs, and in what order.

## Testing

What shows it is built as decided.

## Open questions

What must be settled before it is approved. None, once it is.

## Origin

What prompted it.
```

A decided proposal adds its date under its status, `**Approved:**`,
`**Rejected:**` or `**Superseded:**`, and a superseded one names its
replacement: `**Superseded by:** blocks.md`. Optional lines are
`**Depends on:**` and `**Supersedes:**`. A section with nothing to say is
left out.
