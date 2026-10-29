# Implementation status

This file records where the implementation stands, so that the work can be restarted from it.
The plan is Part G of DESIGN.md, in the spec repository (`../zed`). The repository layout is
in docs/layout.md.

## Current position

- Done: **M0.1** (repository scaffolding).
- Next: M0.2 and M0.3. Both are spec artifacts. M0.2 is marked done in the spec; its test is
  `tools/grammar/cases.py` in the spec repository. M0.3 still lacks the kernel desugaring
  rules, one per production. After those come M0.4 (the corpus) and the rest of M0.

## Test baseline

Last full run: `CI=true cargo test --workspace` gave 5 passed and 0 failed (2 unit tests of
`zed-tests`, 3 step tests in `m0_01_scaffolding`). `cargo fmt --all --check` and
`cargo clippy --workspace --all-targets -- -D warnings` are clean.

## Steps

| Step | State | Notes |
|---|---|---|
| M0.1 | done | workspace (`zedc`, `zed-kernel`, `zed-rt`, `zed-cert`, `zed-tests`), CI workflow, insta snapshots. Both negative controls fail as they should: a corrupted snapshot, and an undeclared step folder |

## Decisions made

- Toolchain: Fedora's rustc and cargo 1.99.1, edition 2024. CI uses the stable toolchain.
- Cargo's target directory is `build/cargo`, set in `.cargo/config.toml`.
- Language tests: `tests/steps/<step>/`, all in one test binary. Unit tests of internal
  functions: `#[cfg(test)]` beside the code.
- Fences: CI must not read the spec repository (the author's instruction, 2026-10-29). Step
  L1.7 copies the fences into fixture files in this repository, with a drift check that runs
  where `../zed` exists.
- Workspace lints: `missing_docs` warns, `unsafe_code` is forbidden. `zed-rt` will need
  `unsafe` when native code arrives (L1.34 and L1.36), so it will relax that lint for itself.

## Open points

- No coverage tool is installed yet. `cargo-llvm-cov` would need the author's approval to
  install, since it goes into `~/.cargo/bin`.
