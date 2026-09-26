# AGENTS.md

This crate is a chess engine whose rules are formally specified and verified with
[Verus](https://github.com/verus-lang/verus). The specification is fixed; your job is
to implement it. These rules are mandatory for any agent working in this repository.

## Protected files: never modify

- `src/spec.rs` — the specification (the rules of chess as Verus `spec` functions).
- `src/types.rs` — the data types the specification is stated over.
- `AGENTS.md`, `CLAUDE.md`, `.claude/settings.json` — these guardrails.

Do not edit, move, rename, delete, reformat or regenerate these files, by any means
(editor tools, shell commands, scripts, `git checkout`/`git apply`, …). If you believe
the specification is wrong or incomplete, stop and report it to a human with a concrete
example. Do not work around it.

## Implementation rules

1. **Implement the spec.** Every executable function in the public API must be proven
   against the spec. Keep its `ensures` clauses: you may strengthen them but not weaken
   them. Keep its `requires` clauses: you may weaken them but not strengthen them.
   For example, `legal_moves_exec` must still be proven sound, complete and duplicate-free
   with respect to `spec::is_legal`.
2. **No trusted escape hatches.** Do not use `assume`, `admit`, `assume_specification`,
   `#[verifier::external_body]`, `#[verifier::external]`, `#[verifier::external_fn_specification]`,
   `#[verifier::exec_allows_no_decreases_clause]`, or `verify = false`. Do not move rules logic outside `verus!` to avoid verification. The only
   unverified code allowed is I/O glue (`src/fen.rs`), and it must not decide any chess rule.
3. **Definition of done.** Both of these must pass:
   ```sh
   cargo verus verify       # must report 0 errors
   cargo test --release     # perft + game tests
   ```
   Do not weaken, skip or delete existing tests (for example the perft reference counts in
   `tests/perft.rs`) to make them pass.
