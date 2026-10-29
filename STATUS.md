# Implementation status

This file records where the implementation stands, so that the work can be restarted from it.
The plan is Part G of DESIGN.md, in the spec repository (`../zed`). The repository layout is
in docs/layout.md.

## Current position

- Done: **M0.1** (repository scaffolding), **M0.9** (kernel reference evaluator).
- Next: M0.2 and M0.3. Both are spec artifacts. M0.2 is marked done in the spec; its test is
  `tools/grammar/cases.py` in the spec repository. M0.3 still lacks the kernel desugaring
  rules, one per production. After those come M0.4 (the corpus) and the rest of M0.

## Test baseline

Last full run: `CI=true cargo test --workspace` gave 48 passed and 0 failed (18 unit tests of
`zed-kernel`, 2 of `zed-tests`, 28 step tests: 3 in `m0_01_scaffolding`, 25 in
`m0_09_kernel_evaluator`). `cargo fmt --all --check` and
`cargo clippy --workspace --all-targets -- -D warnings` are clean.

## Steps

| Step | State | Notes |
|---|---|---|
| M0.1 | done | workspace (`zedc`, `zed-kernel`, `zed-rt`, `zed-cert`, `zed-tests`), CI workflow, insta snapshots. Both negative controls fail as they should: a corrupted snapshot, and an undeclared step folder |
| M0.9 | done | `zed-kernel`: values, families, terms, exact float sum and canonical tree, big-step evaluator with a world of ports. Done ahead of M0.3–M0.8 because later steps test against it. Its decisions are the "Reference semantics" paragraph of DESIGN.md sec:kernel. Negative controls: disabling the exact sum fails 2 step tests; changing the tree split fails 2 unit tests |

## Decisions made

- Toolchain: Fedora's rustc and cargo 1.99.1, edition 2024. CI uses the stable toolchain.
- Cargo's target directory is `build/cargo`, set in `.cargo/config.toml`.
- Language tests: `tests/steps/<step>/`, all in one test binary. Unit tests of internal
  functions: `#[cfg(test)]` beside the code.
- Fences: CI must not read the spec repository (the author's instruction, 2026-10-29). Step
  L1.7 copies the fences into fixture files in this repository, with a drift check that runs
  where `../zed` exists.
- The reference evaluator uses `i64` with checked arithmetic (overflow is an error), a fuel
  of 10^8 calls, at most 20 000 nested calls, and runs on its own thread with a 1 GiB stack.
- Coverage runs in CI (`cargo llvm-cov`, job `coverage`), not locally: this machine has no
  LLVM tools, and installing them is a system package change.
- Workspace lints: `missing_docs` warns, `unsafe_code` is forbidden. `zed-rt` will need
  `unsafe` when native code arrives (L1.34 and L1.36), so it will relax that lint for itself.

- No step waits for a person (the author's instruction, 2026-10-29; spec commit 827385b).
  M0(d) is now a prediction suite kept as tests, the M0(e) postmortems run alongside and gate
  nothing, and the corpus programs are corrected to fit the language rather than the reverse.
  When the spec is unclear, I choose, record the choice in DESIGN.md and here, and continue.

## In progress

- A full read of DESIGN.md by six agents, one line range each, listing what would otherwise need
  the author's input. Each item is to be resolved in the spec before the step it affects.
- Postmortems of related languages, written to the session scratchpad. Their lessons may amend
  the spec.

## Open points

- Apply the batch of resolutions from the six-part read of DESIGN.md (scan files in the
  session scratchpad), prose and grammar together, before the steps they affect.
