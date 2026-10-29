# Implementation status

This file records where the implementation stands, so that the work can be restarted from it.
The plan is Part G of DESIGN.md, in the spec repository (`../zed`). The repository layout is
in docs/layout.md.

## Current position

- Done: **M0.1** (repository scaffolding), **M0.4** (the corpus, in `zed/corpus/`), **M0.9**
  (kernel reference evaluator), and in the spec, M0.2 and M0.3 (the desugaring rules, spec
  commit e3b217f).
- Done: **M0.10**, the finite-model harness (`tests/steps/m0_10_finite_model_harness/`): laws
  1–28, witness bijectivity, the recursion checks, the metatheory smoke cases; budget values
  in DESIGN.md M0.10 (spec commit fc58a1f).
- Next: M0.5–M0.8, M0.11, then L1.

## Test baseline

Last full run: `cargo test --workspace` gave 149 passed and 0 failed (21 unit tests of
`zed-kernel`, 10 of `zed-tests`, 118 step tests: 3 in `m0_01_scaffolding`, 32 in
`m0_09_kernel_evaluator`, 83 in `m0_10_finite_model_harness`). `cargo fmt --all --check` and
`cargo clippy --workspace --all-targets -- -D warnings` are clean. The steps binary takes
about 30 s in a debug build.

## Steps

| Step | State | Notes |
|---|---|---|
| M0.1 | done | workspace (`zedc`, `zed-kernel`, `zed-rt`, `zed-cert`, `zed-tests`), CI workflow, insta snapshots. Both negative controls fail as they should: a corrupted snapshot, and an undeclared step folder |
| M0.10 | done | `zed_kernel::budgets` holds the ladder budgets and the rung 6 instance. `zed_tests::{instances, check, kernel}` hold the enumerators, the equation checker, and the derived forms. Laws 1–28 with a counterexample per side condition; the eight layer-free witness entries with their side-condition counterexamples (truncated division fails the packing inverse on row -1); every schedule agrees on all 512 three-node graphs and 512 random ones, stalls included; smoke cases. Negative control: making an undefined read ignore which `fix` it belongs to fails both nested-fix tests. 11 s in a release build |
| M0.4 | done | `zed/corpus/`: 31 programs with inputs, outputs and Python reference scripts (`refcheck.sh`, run in CI). The layer checker is the spec's `tools/grammar/layer.py`; every label equals its enabled layer, and the four negative controls fail. Four ledger descriptions corrected in the spec (programs 6, 8, 13, 19) |
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

- Budgets (M0.10, in `zed_kernel::budgets`): enumeration of at most 4,096 bindings per
  obligation; rung 6 cuts integers to `-8..=8`, sequences to length 4, loops to 16
  generations, floats to 0.0, -0.0, 1.0, 0.1, 0.2, 0.3, ±inf and NaN, and runs at most 65,536
  bindings in shortlex order; rung 3 saturates for at most 8 iterations or 10,000 e-nodes.
- The kernel `fold` term carries the depth of the folded family (M0.10). The evaluator cannot
  read the depth off a family with no leaves, so without it `fold` of an empty two-level
  family gave `#empty` where its type gives the empty family, and laws 4 and 8 failed on the
  empty input. Typing supplies the depth; a leaf at another depth is the mixed-depth error.
- Kernel values are normalized: a key over an empty level is dropped, so the nonempty-level
  conditions of laws 1, 2 and 7 have no counterexample among values. They constrain the
  guaranteed domains, and are checked where `card` facts are (L1.24, L3.6).
- Integer overflow, like fuel and nesting depth, is a limit of the reference evaluator and not
  a meaning (spec reference semantics (i), commit after a1ed53b). Law 11 deletes a dead binding
  whose computation would overflow; that is not a counterexample, and the laws are checked on
  instances the evaluator can run.
- The harness compares outcomes as values (floats bitwise after NaN canonicalization) or as
  errors of one kind, since two sides that both collide may name different keypaths.

## In progress

- A full read of DESIGN.md by six agents, one line range each, listing what would otherwise need
  the author's input. Each item is to be resolved in the spec before the step it affects.
- Postmortems of related languages, written to the session scratchpad. Their lessons may amend
  the spec.

## Open points

- Corpus outputs that rest on rules the spec has not fixed yet; each is a choice stated in
  the program's `ref/NN.py`, to be revisited at the step that fixes the rule: the `.window`
  signature and late-drop rule (programs 17, 18, 29; step L7.5), where a parse error is
  reported (7, 30), `serialize` writing no whitespace, `++` on int-keyed sets reading in key
  order, `zip` keeping the overlap of two rank ranges (25), stdin keyed by rank from 0.
  The programs are only parsed and layer-checked so far, not type-checked or run.
- Programs 14 and 15 are labeled L7 for incremental reuse (L7.6), though their syntax only
  reaches L6.

- Apply the batch of resolutions from the six-part read of DESIGN.md (scan files in the
  session scratchpad), prose and grammar together, before the steps they affect.

## Postmortem amendments (spec commit after 678e2d1)

The postmortem of related languages (array, dataflow, Datalog and incremental languages; report kept outside the repo) proposed nine amendments. Applied to DESIGN.md:
- A3: `@export("c", "symbol")` lets C call pure Zed functions (sec:ffi; tested in L7.4).
- A1: `zed build --explain-plan` (L5.10).
- A2: a lowering stays within a constant factor of `f::cost`; `@cost(depth: …)`.
- A6: recompute or incremental is chosen per wave by cost; the L7 gate adds a 50%-dirty check.
- A7: the L5 ratios are one core against one core, and efficiency is measured against the Rust baseline. L5.14 now agrees with the gate table.

Not applied:
- A4 (name a first domain): a product decision with no effect on what is built.
- A5 (license): the repo already has LICENSE; the choice belongs to the owner.
- A8 (two-process test at L7): distribution is post-v1 in sec:targets.
- A9 (count programs needing generations): no decision depends on the count.

## M0.3 — desugaring rules (done, in the spec)

The spec's sec:grammar now has a `desugar` fence with one rule per syntactic production (107), and the spec repo's `tools/grammar/check.py` checks that rules and productions match one to one. A negative control (an extra rule and a duplicate) is caught. Nothing in this repo changes until the L1 elaborator, which implements these rules. Decisions:
- `&&` and `||` desugar to `if`, not to the strict primitives; the spec calls them selection nodes that short-circuit observationally.
- Recursion enters at L6. A recursive function is the definedness fix over its parameter domain, evaluated on demand. The M0.9 evaluator computes that fix over a finite domain only; the L1/L6 interpreter evaluates on demand.
- Kernel primitives the rules name that the M0.9 kernel lacks: `pow` (L1), `range` (L3), and the type test `is` (L1). They are added at those steps.
- `break e`: the step's guard returns `#break(e)` and the loop's result is `e`.
