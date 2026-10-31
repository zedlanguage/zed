# Rust and Dart implementations compared

On 2026-10-31 the author stopped the Rust implementation and ordered a port of all of it, tests
included, to Dart, step by step in the plan's order. This file records the Rust baseline and
will hold the Dart numbers for the same steps once the port reaches the same point. PROGRESS.md
marks each step `[d]` once its Dart port passes.

## Where the Rust work stopped

The Rust tree stopped at commit `55f537a` ("Z7: captures merged through a map"), in the
performance pass over earlier steps (COMPLEXITY.md). Two rows were open, both in the native
backend of L1.36:

| Row | Problem | Cost |
|---|---|---|
| Z8 | `tables.rs` finds constants and call targets by linear search | O(C²), O(applies·lambdas) |
| Z9 | `tables.rs` `visit` clones each node with its regions | O(N·depth) |

The unfinished work is saved, uncommitted to the source, as `docs/wip/z8-z9-stopped.patch`
(4 files, 82 lines added, 12 removed: `codegen.rs`, `tables.rs` and an L1.36 scaling test).
It was stuck here: Z9's clones exist because `visit` holds a borrow of the term tree while it
builds the tables, so it copied each node to release the borrow. An attempt to release the
borrow of an `if` condition early did not make the compile linear, and the scaling test in the
patch still failed. The last full Rust test run before the stop passed 930 tests.

## Build and test baseline (Rust)

Measured on 2026-10-31 at `55f537a`, in a scope capped at 64 GB, with a separate target
directory so that the first build is cold.

| Measurement | Time |
|---|---:|
| Clean debug build, all targets | 56.6 s |
| Rebuild after touching `zedc/src/lib.rs` | 10.8 s |
| Rebuild after touching the step-test crate | 8.6 s |
| `cargo clippy` after the build | 28.2 s |
| Clean release build, libraries and binaries | 67.8 s |
| Full test run, parallel, already built | 99.7 s |
| Full test run, one thread, with per-test times | 402.2 s |

Per-test times, from the single-threaded run (930 tests, 0 failed, 384.8 s of test time). The
time per step, summed over its tests, for every step above one second:

| Step | Tests | Time |
|---|---:|---:|
| L1.25 | 42 | 71.4 s |
| L1.26 | 42 | 51.8 s |
| M0.10 | 90 | 41.0 s |
| M0.11 | 13 | 37.4 s |
| L1.14 | 22 | 28.9 s |
| L1.16 | 35 | 20.8 s |
| L1.28 | 18 | 20.1 s |
| L1.38 | 16 | 16.4 s |
| store unit tests | 20 | 13.0 s |
| L1.39 | 28 | 12.1 s |
| L1.24 | 26 | 10.5 s |
| L1.29 | 19 | 10.0 s |
| L1.23 | 29 | 9.8 s |
| M0.5 | 34 | 9.5 s |
| L1.37 | 7 | 5.9 s |
| L1.13 | 14 | 3.5 s |
| M0.9 | 41 | 3.0 s |
| L1.33 | 29 | 2.9 s |
| scaling unit tests | 2 | 2.9 s |
| L1.21 | 22 | 2.3 s |
| types unit tests | 1 | 2.0 s |
| L1.36 | 18 | 2.0 s |
| L1.18 | 22 | 1.4 s |
| L1.15 | 20 | 1.2 s |

Every other step takes under one second in all. The slowest single tests are M0.11's ten
million steps (19.5 s) and its axioms on the harness instances (16.0 s), and L1.25's random
preimage tests (16.4 s and 14.6 s). Most of the time in the slow steps is in scaling tests,
which run each pass at two sizes, five times each.

## Compile errors in the Rust work

Counted from the session transcripts: every tool result between 2026-10-29 and the stop order
(2026-10-31 08:47 UTC), including subagents. An error is one `error[Exxxx]` or syntax error from
rustc, counted once per run per error code and source location, so an error printed twice by
one run (a build and a clippy pass) counts once. Clippy lints and rustfmt diffs are counted
apart, as they are not compile errors. A run that fails with any error counts once in the
"runs" column.

- **Borrow-checker errors: 12, in 10 compiler runs.** The codes counted as the borrow checker
  are the ownership and lifetime errors (E0499, E0502, E0382, E0594, E0373, E0505, E0507,
  E0597, E0716, E0106 and the like) and the uncoded "lifetime may not live long enough".
  Each of the 12 was read by hand: E0502 ×2, E0499 ×4, E0382 ×2, E0594 ×2, E0373 ×2.
- **Other compile errors: 217, in 84 compiler runs.** Type errors (E0308 ×44, E0599 ×38,
  E0277 ×19, E0061 ×17, E0283 ×8, E0063 ×8, …), unresolved names and imports (E0425 ×22,
  E0433 ×12, E0432 ×7, …), and syntax errors.
- Clippy failures: 27 runs; rustfmt failures: 8 runs; failing test runs: 399.

These counts understate what the borrow checker cost. Most of its cost never reached the
compiler as an error: the code was written from the start to avoid one, with `Arc`, `Rc`,
`clone()` and index-based graphs, and several performance-pass rows (K6, K7, K13, F17, Z9)
existed to undo copies that were made only to satisfy ownership.

## Time per step

Model time is time spent writing and reasoning; tool time is time waiting for tools, mostly for
builds and test runs. Both come from the gaps between transcript events, each attributed to the
next commit. The initial build ran from 2026-10-29 04:31 to 2026-10-30 03:35 MDT; the
performance pass from then to the stop at 2026-10-31 02:15 MDT. Rows marked `pass` are
performance-pass rows of COMPLEXITY.md, each of which revisited one or more earlier steps.
Hand-off waits between sessions (21.0 h in all) are excluded.

The Dart columns are filled as the port reaches each step.

| Step | Rust model time | Rust tool time | Rust borrow-checker errors (runs) | Rust other compile errors (runs) | Dart model time | Dart tool time | Dart compile errors (runs) |
|---|---:|---:|---:|---:|---:|---:|---:|
| M0.1 | 1:52 | 0:37 | 0 (0) | 1 (1) | 0:11 | 0:01 | 0 (0) |
| other (CI) | 0:01 | 0:02 | 0 (0) | 0 (0) | | | |
| other (STATUS) | 0:08 | 0:06 | 0 (0) | 0 (0) | | | |
| M0.9 | 0:15 | 0:01 | 1 (1) | 2 (1) | 0:28 | 0:00 | 0 (0) |
| M0.10 | 0:49 | 0:10 | 4 (3) | 20 (9) | | | |
| M0.4 | 0:01 | 0:00 | 0 (0) | 0 (0) | | | |
| M0.5 | 0:54 | 0:59 | 0 (0) | 7 (3) | | | |
| M0.6 | 0:03 | 0:01 | 0 (0) | 0 (0) | | | |
| other (Corpus 24) | 0:05 | 0:00 | 0 (0) | 0 (0) | | | |
| M0.7 | 0:04 | 0:12 | 1 (1) | 5 (2) | | | |
| M0.8 | 0:03 | 0:01 | 0 (0) | 0 (0) | | | |
| M0.11 | 0:07 | 0:02 | 0 (0) | 1 (1) | | | |
| L1.1 | 0:03 | 0:01 | 0 (0) | 0 (0) | | | |
| L1.2 | 0:03 | 0:01 | 0 (0) | 0 (0) | | | |
| L1.3 | 0:01 | 0:01 | 0 (0) | 0 (0) | | | |
| L1.4 | 0:01 | 0:00 | 0 (0) | 0 (0) | | | |
| L1.5 | 0:05 | 0:01 | 0 (0) | 0 (0) | | | |
| L1.6 | 0:02 | 0:01 | 0 (0) | 0 (0) | | | |
| L1.7 | 0:06 | 0:01 | 0 (0) | 0 (0) | | | |
| L1.8 | 0:06 | 0:01 | 0 (0) | 0 (0) | | | |
| L1.9 | 0:04 | 0:01 | 0 (0) | 0 (0) | | | |
| L1.10 | 0:04 | 0:01 | 0 (0) | 0 (0) | | | |
| L1.11 | 0:04 | 0:01 | 0 (0) | 0 (0) | | | |
| L1.12 | 0:03 | 0:01 | 0 (0) | 2 (1) | | | |
| L1.13 | 0:09 | 0:03 | 0 (0) | 0 (0) | | | |
| L1.14 | 0:07 | 0:02 | 0 (0) | 0 (0) | | | |
| L1.15 | 0:08 | 0:03 | 1 (1) | 16 (3) | | | |
| L1.16 | 0:15 | 0:01 | 0 (0) | 1 (1) | | | |
| L1.17 | 0:13 | 0:04 | 0 (0) | 5 (2) | | | |
| L1.18 | 0:08 | 0:04 | 0 (0) | 2 (1) | | | |
| L1.19 | 0:12 | 0:03 | 0 (0) | 1 (1) | | | |
| L1.20 | 0:13 | 0:04 | 0 (0) | 3 (2) | | | |
| L1.21 | 0:09 | 0:02 | 0 (0) | 0 (0) | | | |
| L1.22 | 0:14 | 0:04 | 0 (0) | 1 (1) | | | |
| L1.23 | 0:15 | 0:08 | 0 (0) | 3 (2) | | | |
| L1.24 | 0:12 | 0:05 | 0 (0) | 1 (1) | | | |
| L1.25 | 0:36 | 0:16 | 1 (1) | 7 (2) | | | |
| L1.26 | 1:01 | 0:12 | 0 (0) | 6 (2) | | | |
| L1.27 | 0:07 | 0:03 | 0 (0) | 2 (2) | | | |
| L1.28 | 0:15 | 0:07 | 0 (0) | 0 (0) | | | |
| L1.29 | 0:17 | 0:07 | 0 (0) | 4 (2) | | | |
| L1.30 | 0:06 | 0:04 | 0 (0) | 3 (1) | | | |
| L1.31 | 0:20 | 0:04 | 0 (0) | 1 (1) | | | |
| L1.32 | 0:06 | 0:04 | 0 (0) | 0 (0) | | | |
| other (Signed zeros) | 0:04 | 0:01 | 0 (0) | 0 (0) | | | |
| L1.33 | 0:13 | 0:06 | 2 (1) | 0 (0) | | | |
| L1.34 | 0:22 | 0:05 | 0 (0) | 0 (0) | | | |
| L1.35 | 0:03 | 0:03 | 0 (0) | 0 (0) | | | |
| L1.36 | 0:26 | 0:04 | 0 (0) | 12 (2) | | | |
| L1.37 | 0:07 | 0:04 | 0 (0) | 0 (0) | | | |
| L1.38 | 0:17 | 0:09 | 0 (0) | 6 (2) | | | |
| L1.39 | 0:36 | 0:20 | 0 (0) | 6 (3) | | | |
| pass S2,S4 | 0:07 | 0:17 | 1 (1) | 0 (0) | | | |
| pass S5 | 0:04 | 0:04 | 0 (0) | 0 (0) | | | |
| pass S3 | 0:07 | 0:12 | 0 (0) | 0 (0) | | | |
| pass S8,S11,S12 | 0:12 | 0:18 | 0 (0) | 16 (4) | | | |
| pass S9 | 0:05 | 0:04 | 0 (0) | 0 (0) | | | |
| pass S10 | 0:01 | 0:02 | 0 (0) | 0 (0) | | | |
| pass Z1 | 0:08 | 0:15 | 0 (0) | 0 (0) | | | |
| pass Z2,Z3 | 0:04 | 0:07 | 0 (0) | 0 (0) | | | |
| pass K1,K3 | 0:20 | 0:20 | 0 (0) | 7 (2) | | | |
| pass K2 | 0:07 | 0:13 | 0 (0) | 0 (0) | | | |
| pass F1 | 0:02 | 0:01 | 0 (0) | 0 (0) | | | |
| pass F2 | 0:04 | 0:06 | 0 (0) | 0 (0) | | | |
| pass F3 | 0:01 | 0:03 | 0 (0) | 0 (0) | | | |
| pass K4 | 0:04 | 0:03 | 0 (0) | 0 (0) | | | |
| pass K5 | 0:03 | 0:04 | 0 (0) | 1 (1) | | | |
| pass K6 | 0:01 | 0:05 | 0 (0) | 1 (1) | | | |
| pass K7 | 0:09 | 0:24 | 0 (0) | 2 (1) | | | |
| pass K8 | 0:03 | 0:06 | 0 (0) | 0 (0) | | | |
| pass K9 | 0:02 | 0:04 | 0 (0) | 9 (3) | | | |
| pass K10 | 0:01 | 0:11 | 0 (0) | 0 (0) | | | |
| pass K11 | 0:03 | 0:06 | 0 (0) | 2 (1) | | | |
| pass K12 | 0:05 | 0:07 | 0 (0) | 0 (0) | | | |
| pass K13 | 0:02 | 0:03 | 0 (0) | 2 (1) | | | |
| pass K14 | 0:06 | 0:07 | 0 (0) | 4 (2) | | | |
| pass K15 | 0:03 | 0:05 | 0 (0) | 0 (0) | | | |
| pass K16 | 0:03 | 0:02 | 0 (0) | 9 (3) | | | |
| pass K17 | 0:09 | 0:06 | 0 (0) | 5 (2) | | | |
| pass F4,F13 | 0:08 | 0:24 | 0 (0) | 0 (0) | | | |
| pass F5 | 0:04 | 0:07 | 0 (0) | 0 (0) | | | |
| pass F8 | 0:03 | 0:06 | 0 (0) | 2 (1) | | | |
| pass F9 | 0:06 | 0:12 | 0 (0) | 0 (0) | | | |
| pass F6 | 0:05 | 0:13 | 0 (0) | 0 (0) | | | |
| pass F18 | 0:55 | 2:10 | 0 (0) | 0 (0) | | | |
| pass F16 | 0:02 | 0:12 | 0 (0) | 0 (0) | | | |
| pass replacement 1 | 2:11 | 0:08 | 1 (1) | 0 (0) | | | |
| pass replacement 2 | 0:02 | 0:07 | 0 (0) | 2 (2) | | | |
| pass replacement 3a | 0:08 | 0:01 | 0 (0) | 2 (1) | | | |
| pass replacement 3b | 0:11 | 0:09 | 0 (0) | 11 (1) | | | |
| pass replacement 8a | 0:18 | 0:12 | 0 (0) | 3 (2) | | | |
| pass replacement 9 | 0:09 | 0:15 | 0 (0) | 12 (1) | | | |
| pass S13 | 0:06 | 0:02 | 0 (0) | 2 (1) | | | |
| pass S15 | 0:13 | 0:58 | 0 (0) | 6 (4) | | | |
| pass F10,F11 | 0:03 | 0:08 | 0 (0) | 0 (0) | | | |
| pass F12 | 0:01 | 0:07 | 0 (0) | 0 (0) | | | |
| pass F14 | 0:01 | 0:03 | 0 (0) | 0 (0) | | | |
| pass F15 | 0:01 | 0:04 | 0 (0) | 0 (0) | | | |
| pass F17 | 0:03 | 0:03 | 0 (0) | 1 (1) | | | |
| pass Z6 | 0:01 | 0:03 | 0 (0) | 0 (0) | | | |
| pass Z7 | 0:00 | 0:03 | 0 (0) | 0 (0) | | | |
| pass Z8, Z9 (stopped) | 0:00 | 0:00 | 0 (0) | 0 (0) | | | |
| **Total** | **20:10** | **15:04** | **12 (10)** | **217 (84)** | | | |

## Changes per file

How many times each file was written or edited: before the performance pass, and during it.
A file's creation counts as one change. 437 files: 1,165 changes before the performance pass,
986 during it. DESIGN.md lives in the spec repository but is counted, since steps edited it.
The Dart port records the same two numbers for its own files in the Dart section below.

| file | changes before the performance pass | changes during the performance pass |
|---|---:|---:|
| `STATUS.md` | 70 | 51 |
| `crates/zed-kernel/src/eval.rs` | 39 | 17 |
| `DESIGN.md` | 39 | 16 |
| `crates/zedc/src/check/mod.rs` | 21 | 32 |
| `tests/steps/l01_23_subtyping/scaling.rs` | 0 | 50 |
| `COMPLEXITY.md` | 1 | 47 |
| `tests/steps/main.rs` | 47 | 0 |
| `crates/zedc/src/store/product.rs` | 12 | 31 |
| `tests/steps/l01_25_preimage_catalog/scaling.rs` | 2 | 34 |
| `crates/zedc/src/store/preimage.rs` | 9 | 24 |
| `crates/zed-kernel/src/types/empty.rs` | 1 | 29 |
| `crates/zedc/src/store/presburger.rs` | 5 | 25 |
| `crates/zedc/src/elab.rs` | 14 | 15 |
| `tests/src/scaling.rs` | 1 | 27 |
| `tests/steps/l01_16_elaboration/scaling.rs` | 0 | 27 |
| `crates/zed-kernel/src/types.rs` | 4 | 21 |
| `crates/zed-kernel/src/types/bdd.rs` | 0 | 22 |
| `tests/steps/l01_26_type_resolution/scaling.rs` | 0 | 21 |
| `tests/steps/m0_05_widening_and_iteration/scaling.rs` | 0 | 20 |
| `crates/zedc/src/lib.rs` | 19 | 0 |
| `tests/steps/l01_39_reduced_product/scaling.rs` | 0 | 19 |
| `docs/thresholds.md` | 0 | 18 |
| `crates/zedc/src/zir/lower.rs` | 6 | 9 |
| `tests/steps/m0_09_kernel_evaluator/scaling.rs` | 0 | 15 |
| `crates/zed-kernel/src/family.rs` | 3 | 11 |
| `crates/zed-kernel/src/print.rs` | 9 | 5 |
| `tests/steps/l01_39_reduced_product/random.rs` | 14 | 0 |
| `tests/steps/m0_09_kernel_evaluator/mod.rs` | 13 | 1 |
| `crates/zedc/src/stage.rs` | 4 | 9 |
| `tests/steps/l01_25_preimage_catalog/random.rs` | 3 | 10 |
| `tests/steps/m0_10_finite_model_harness/scaling.rs` | 0 | 13 |
| `crates/zedc/src/store/interval.rs` | 3 | 9 |
| `mod.rs` | 10 | 2 |
| `tests/steps/l01_28_staging/trick.rs` | 3 | 9 |
| `crates/zed-kernel/src/lib.rs` | 10 | 1 |
| `crates/zed-kernel/src/value.rs` | 8 | 3 |
| `crates/zedc/src/check/ty.rs` | 6 | 5 |
| `crates/zedc/src/lex/mod.rs` | 9 | 2 |
| `crates/zedc/src/lex/string.rs` | 8 | 3 |
| `crates/zedc/src/store/revision.rs` | 4 | 7 |
| `tests/steps/l01_13_formatter/scaling.rs` | 0 | 11 |
| `tests/steps/l01_25_preimage_catalog/entries.rs` | 4 | 7 |
| `crates/zedc/src/store/iterate.rs` | 1 | 9 |
| `tests/steps/l01_38_presburger/mod.rs` | 8 | 2 |
| `tests/steps/l01_39_reduced_product/controls.rs` | 2 | 8 |
| `crates/zed-kernel/src/term.rs` | 9 | 0 |
| `crates/zed-native/src/codegen.rs` | 4 | 5 |
| `crates/zedc/src/ast/mod.rs` | 6 | 3 |
| `crates/zedc/src/ast/stmts.rs` | 9 | 0 |
| `crates/zedc/src/resolve.rs` | 6 | 3 |
| `crates/zedc/src/run.rs` | 7 | 2 |
| `crates/zedc/src/testing.rs` | 4 | 5 |
| `tests/steps/l01_15_kernel_terms/scaling.rs` | 0 | 9 |
| `tests/steps/l01_20_provenance/kernel.rs` | 8 | 1 |
| `tests/steps/l01_25_preimage_catalog/mod.rs` | 9 | 0 |
| `tests/steps/l01_33_lowering/scaling.rs` | 0 | 9 |
| `tests/steps/m0_10_finite_model_harness/mod.rs` | 8 | 1 |
| `crates/zed-kernel/src/types/rec.rs` | 2 | 6 |
| `crates/zedc/src/canon/binders.rs` | 6 | 2 |
| `crates/zedc/src/lex/number.rs` | 8 | 0 |
| `crates/zedc/src/store/lattice.rs` | 3 | 5 |
| `tests/steps/l01_23_subtyping/oracle.rs` | 1 | 7 |
| `tests/steps/l01_25_preimage_catalog/stops.rs` | 6 | 2 |
| `tests/steps/l01_26_type_resolution/probe.rs` | 8 | 0 |
| `tests/steps/l01_31_zir/rejections.rs` | 8 | 0 |
| `tests/steps/l01_36_cranelift/scaling.rs` | 0 | 8 |
| `tests/steps/l01_38_presburger/scaling.rs` | 0 | 8 |
| `tests/steps/m0_05_widening_and_iteration/iteration.rs` | 1 | 7 |
| `tests/steps/m0_10_finite_model_harness/laws_11_20.rs` | 8 | 0 |
| `zed/prelude/iteration.zed` | 3 | 5 |
| `crates/zedc/src/canon/serial.rs` | 7 | 0 |
| `crates/zedc/src/format.rs` | 2 | 5 |
| `crates/zedc/src/store/wto.rs` | 2 | 5 |
| `tests/src/lib.rs` | 7 | 0 |
| `tests/steps/l01_05_lexer_strings/scaling.rs` | 0 | 7 |
| `tests/steps/l01_14_name_resolution/scaling.rs` | 0 | 7 |
| `tests/steps/l01_25_preimage_catalog/exact.rs` | 0 | 7 |
| `crates/zed-kernel/src/provenance.rs` | 3 | 3 |
| `crates/zedc/src/canon/mod.rs` | 4 | 2 |
| `crates/zedc/src/source.rs` | 4 | 2 |
| `crates/zedc/src/zir/mod.rs` | 5 | 1 |
| `tests/steps/l01_20_provenance/scaling.rs` | 0 | 6 |
| `tests/steps/l01_23_subtyping/rec.rs` | 2 | 4 |
| `tests/steps/l01_24_refinement_lattices/cell.rs` | 2 | 4 |
| `tests/steps/l01_28_staging/mix.rs` | 3 | 3 |
| `tests/steps/l01_29_diagnostics/derivations.rs` | 2 | 4 |
| `tests/steps/l01_32_canonical_zir/stability.rs` | 6 | 0 |
| `tests/steps/l01_33_lowering/corpus.rs` | 6 | 0 |
| `tests/steps/l01_37_oracle/oracle.rs` | 6 | 0 |
| `tests/steps/m0_07_canonicalization/rules.rs` | 5 | 1 |
| `$D/mod.rs` | 5 | 0 |
| `.github/workflows/ci.yml` | 5 | 0 |
| `crates/zed-kernel/src/error.rs` | 5 | 0 |
| `crates/zed-native/src/lib.rs` | 1 | 4 |
| `crates/zedc/src/query.rs` | 2 | 3 |
| `crates/zedc/src/store/mod.rs` | 5 | 0 |
| `crates/zedc/src/zir/binary.rs` | 5 | 0 |
| `crates/zedc/src/zir/memory.rs` | 4 | 1 |
| `docs/layout.md` | 5 | 0 |
| `tests/steps/l01_15_kernel_terms/evidence.rs` | 5 | 0 |
| `tests/steps/l01_20_provenance/mod.rs` | 3 | 2 |
| `tests/steps/l01_22_type_representation/forms.rs` | 4 | 1 |
| `tests/steps/l01_24_refinement_lattices/scaling.rs` | 0 | 5 |
| `tests/steps/l01_26_type_resolution/random.rs` | 3 | 2 |
| `tests/steps/l01_28_staging/scaling.rs` | 0 | 5 |
| `tests/steps/l01_29_diagnostics/scaling.rs` | 0 | 5 |
| `tests/steps/l01_32_canonical_zir/fuzz.rs` | 2 | 3 |
| `tests/steps/l01_34_memory/corpus.rs` | 3 | 2 |
| `tests/steps/m0_01_scaffolding/snapshots/steps__m0_01_scaffolding__step_index.snap` | 5 | 0 |
| `tests/steps/m0_05_widening_and_iteration/widening.rs` | 2 | 3 |
| `tests/steps/m0_07_canonicalization/alpha.rs` | 3 | 2 |
| `tests/steps/m0_10_finite_model_harness/laws_01_10.rs` | 5 | 0 |
| `tests/steps/m0_10_finite_model_harness/smoke.rs` | 5 | 0 |
| `zed/prelude/lattice.zed` | 3 | 2 |
| `$D/fences.rs` | 4 | 0 |
| `Cargo.toml` | 4 | 0 |
| `crates/zed-kernel/src/num.rs` | 4 | 0 |
| `crates/zedc/Cargo.toml` | 4 | 0 |
| `crates/zedc/src/cost.rs` | 3 | 1 |
| `crates/zedc/src/lex/name.rs` | 4 | 0 |
| `crates/zedc/src/main.rs` | 4 | 0 |
| `crates/zedc/src/zir/canon.rs` | 1 | 3 |
| `eval.rs` | 4 | 0 |
| `tests/src/kernel.rs` | 4 | 0 |
| `tests/src/oracle.rs` | 4 | 0 |
| `tests/steps/l01_02_lexer_names/names.rs` | 4 | 0 |
| `tests/steps/l01_09_postfix_chains/fences.rs` | 4 | 0 |
| `tests/steps/l01_13_formatter/layout.rs` | 4 | 0 |
| `tests/steps/l01_15_kernel_terms/layout.rs` | 3 | 1 |
| `tests/steps/l01_16_elaboration/errors.rs` | 4 | 0 |
| `tests/steps/l01_16_elaboration/mod.rs` | 3 | 1 |
| `tests/steps/l01_17_value_representation/atoms.rs` | 4 | 0 |
| `tests/steps/l01_19_whole_file_ports/lines.rs` | 4 | 0 |
| `tests/steps/l01_24_refinement_lattices/mod.rs` | 2 | 2 |
| `tests/steps/l01_26_type_resolution/mod.rs` | 3 | 1 |
| `tests/steps/l01_27_absences/mod.rs` | 4 | 0 |
| `tests/steps/l01_29_diagnostics/mod.rs` | 1 | 3 |
| `tests/steps/l01_30_queries/reuse.rs` | 4 | 0 |
| `tests/steps/l01_39_reduced_product/exact.rs` | 0 | 4 |
| `tests/steps/l01_39_reduced_product/spec.rs` | 3 | 1 |
| `tests/steps/m0_10_finite_model_harness/laws_21_28.rs` | 4 | 0 |
| `zed/compiler/MLIR.md` | 4 | 0 |
| `zed/prelude/revision.zed` | 3 | 1 |
| `$d/units.rs` | 3 | 0 |
| `crates/zed-kernel/src/exact.rs` | 3 | 0 |
| `crates/zed-native/src/hooks.rs` | 2 | 1 |
| `crates/zed-native/src/tables.rs` | 2 | 1 |
| `crates/zedc/src/axioms.rs` | 3 | 0 |
| `crates/zedc/src/parse/mod.rs` | 3 | 0 |
| `crates/zedc/src/store/affine.rs` | 1 | 2 |
| `lower.rs` | 3 | 0 |
| `ports.rs` | 3 | 0 |
| `random.rs` | 2 | 1 |
| `run.rs` | 3 | 0 |
| `tests/Cargo.toml` | 3 | 0 |
| `tests/src/check.rs` | 3 | 0 |
| `tests/src/instances.rs` | 1 | 2 |
| `tests/src/trees.rs` | 3 | 0 |
| `tests/steps/l01_01_source_loading/rejected.rs` | 3 | 0 |
| `tests/steps/l01_05_lexer_strings/strings.rs` | 3 | 0 |
| `tests/steps/l01_06_lexer_tokens/program.rs` | 3 | 0 |
| `tests/steps/l01_06_lexer_tokens/words.rs` | 3 | 0 |
| `tests/steps/l01_08_parser/errors.rs` | 3 | 0 |
| `tests/steps/l01_08_parser/mod.rs` | 3 | 0 |
| `tests/steps/l01_09_postfix_chains/calls.rs` | 3 | 0 |
| `tests/steps/l01_11_statements/blocks.rs` | 3 | 0 |
| `tests/steps/l01_16_elaboration/programs.rs` | 3 | 0 |
| `tests/steps/l01_17_value_representation/order.rs` | 3 | 0 |
| `tests/steps/l01_19_whole_file_ports/files.rs` | 3 | 0 |
| `tests/steps/l01_19_whole_file_ports/replay.rs` | 3 | 0 |
| `tests/steps/l01_20_provenance/programs.rs` | 2 | 1 |
| `tests/steps/l01_21_test_runner/marks.rs` | 0 | 3 |
| `tests/steps/l01_21_test_runner/mod.rs` | 0 | 3 |
| `tests/steps/l01_26_type_resolution/signatures.rs` | 1 | 2 |
| `tests/steps/l01_31_zir/items.rs` | 3 | 0 |
| `tests/steps/l01_34_memory/mod.rs` | 3 | 0 |
| `tests/steps/l01_36_cranelift/checks.rs` | 3 | 0 |
| `tests/steps/l01_37_oracle/controls.rs` | 3 | 0 |
| `tests/steps/l01_38_presburger/entailment.rs` | 3 | 0 |
| `tests/steps/m0_05_widening_and_iteration/mod.rs` | 2 | 1 |
| `tests/steps/m0_05_widening_and_iteration/revision.rs` | 3 | 0 |
| `tests/steps/m0_05_widening_and_iteration/wto.rs` | 1 | 2 |
| `tests/steps/m0_10_finite_model_harness/derived.rs` | 3 | 0 |
| `tests/steps/m0_10_finite_model_harness/recursion.rs` | 3 | 0 |
| `tests/steps/m0_10_finite_model_harness/witnesses.rs` | 3 | 0 |
| `zed/fences/sync.py` | 3 | 0 |
| `$D/laws.rs` | 2 | 0 |
| `$D/retry.zed` | 2 | 0 |
| `$D/tables.rs` | 2 | 0 |
| `$S/a.zed` | 2 | 0 |
| `$S/b.zed` | 2 | 0 |
| `$S/count.zed` | 2 | 0 |
| `$S/f12.py` | 0 | 2 |
| `$S/head/tests/steps/l01_39_reduced_product/scaling.rs` | 0 | 2 |
| `$S/k1.py` | 0 | 2 |
| `$S/mut21.py` | 2 | 0 |
| `(insta snapshots accepted)` | 2 | 0 |
| `adoption.rs` | 2 | 0 |
| `audit.py` | 2 | 0 |
| `crates/zed-kernel/src/budgets.rs` | 2 | 0 |
| `crates/zed-kernel/src/text.rs` | 0 | 2 |
| `crates/zed-kernel/src/words.rs` | 2 | 0 |
| `crates/zed-rt/src/heap.rs` | 2 | 0 |
| `crates/zedc/src/ast.rs` | 2 | 0 |
| `crates/zedc/src/interp.rs` | 2 | 0 |
| `crates/zedc/src/parse/grammar.rs` | 2 | 0 |
| `crates/zedc/src/store/cell.rs` | 1 | 1 |
| `crates/zedc/src/store/float.rs` | 1 | 1 |
| `crates/zedc/src/zir/text.rs` | 2 | 0 |
| `cse.rs` | 2 | 0 |
| `elab.rs` | 0 | 2 |
| `exact.rs` | 0 | 2 |
| `forms.rs` | 2 | 0 |
| `functions.rs` | 2 | 0 |
| `preimage.rs` | 0 | 2 |
| `src/lib.rs` | 2 | 0 |
| `src/rope.rs` | 2 | 0 |
| `testing.rs` | 2 | 0 |
| `tests/src/fences.rs` | 2 | 0 |
| `tests/steps/l01_01_source_loading/mod.rs` | 1 | 1 |
| `tests/steps/l01_01_source_loading/places.rs` | 0 | 2 |
| `tests/steps/l01_02_lexer_names/scripts.rs` | 2 | 0 |
| `tests/steps/l01_04_lexer_floats_and_rationals/mod.rs` | 2 | 0 |
| `tests/steps/l01_05_lexer_strings/holes.rs` | 2 | 0 |
| `tests/steps/l01_05_lexer_strings/mod.rs` | 1 | 1 |
| `tests/steps/l01_06_lexer_tokens/mod.rs` | 2 | 0 |
| `tests/steps/l01_08_parser/cases.rs` | 2 | 0 |
| `tests/steps/l01_08_parser/rings.rs` | 2 | 0 |
| `tests/steps/l01_09_postfix_chains/chains.rs` | 2 | 0 |
| `tests/steps/l01_13_formatter/fences.rs` | 2 | 0 |
| `tests/steps/l01_13_formatter/mod.rs` | 1 | 1 |
| `tests/steps/l01_14_name_resolution/mod.rs` | 1 | 1 |
| `tests/steps/l01_14_name_resolution/scopes.rs` | 2 | 0 |
| `tests/steps/l01_15_kernel_terms/mod.rs` | 1 | 1 |
| `tests/steps/l01_17_value_representation/numbers.rs` | 2 | 0 |
| `tests/steps/l01_18_scalar_interpreter/mod.rs` | 2 | 0 |
| `tests/steps/l01_19_whole_file_ports/writes.rs` | 2 | 0 |
| `tests/steps/l01_21_test_runner/scaling.rs` | 0 | 2 |
| `tests/steps/l01_22_type_representation/laws.rs` | 2 | 0 |
| `tests/steps/l01_24_refinement_lattices/float.rs` | 1 | 1 |
| `tests/steps/l01_24_refinement_lattices/loops.rs` | 1 | 1 |
| `tests/steps/l01_24_refinement_lattices/xp.rs` | 0 | 2 |
| `tests/steps/l01_25_preimage_catalog/tonicity.rs` | 2 | 0 |
| `tests/steps/l01_27_absences/families.rs` | 2 | 0 |
| `tests/steps/l01_27_absences/loose.rs` | 2 | 0 |
| `tests/steps/l01_28_staging/mod.rs` | 1 | 1 |
| `tests/steps/l01_29_diagnostics/layout.rs` | 2 | 0 |
| `tests/steps/l01_29_diagnostics/variants.rs` | 2 | 0 |
| `tests/steps/l01_30_queries/keys.rs` | 2 | 0 |
| `tests/steps/l01_30_queries/mod.rs` | 2 | 0 |
| `tests/steps/l01_33_lowering/errors.rs` | 1 | 1 |
| `tests/steps/l01_33_lowering/forms.rs` | 2 | 0 |
| `tests/steps/l01_33_lowering/mod.rs` | 1 | 1 |
| `tests/steps/l01_33_lowering/ports.rs` | 0 | 2 |
| `tests/steps/l01_34_memory/cells.rs` | 2 | 0 |
| `tests/steps/l01_36_cranelift/corpus.rs` | 2 | 0 |
| `tests/steps/l01_36_cranelift/mod.rs` | 1 | 1 |
| `tests/steps/l01_37_oracle/mod.rs` | 2 | 0 |
| `tests/steps/l01_38_presburger/controls.rs` | 1 | 1 |
| `tests/steps/l01_38_presburger/preimage.rs` | 2 | 0 |
| `tests/steps/l01_38_presburger/random.rs` | 2 | 0 |
| `tests/steps/l01_39_reduced_product/mod.rs` | 1 | 1 |
| `tests/steps/m0_06_cost_scalarization/mod.rs` | 2 | 0 |
| `tests/steps/m0_07_canonicalization/domains.rs` | 2 | 0 |
| `tests/steps/m0_07_canonicalization/mod.rs` | 1 | 1 |
| `tests/steps/m0_11_prelude_axioms_and_limits/axioms.rs` | 2 | 0 |
| `tests/steps/m0_11_prelude_axioms_and_limits/limits.rs` | 2 | 0 |
| `tests/steps/m0_11_prelude_axioms_and_limits/units.rs` | 2 | 0 |
| `text.rs` | 2 | 0 |
| `tools/progress.py` | 2 | 0 |
| `value.rs` | 2 | 0 |
| `zed/compiler/ZED0.md` | 2 | 0 |
| `zed/prelude/axioms.zed` | 2 | 0 |
| `$D/blocks.rs` | 1 | 0 |
| `$D/casts.rs` | 1 | 0 |
| `$D/command.rs` | 1 | 0 |
| `$D/config.zed` | 1 | 0 |
| `$D/elses.rs` | 1 | 0 |
| `$D/fahrenheit.zed` | 1 | 0 |
| `$D/failures.rs` | 1 | 0 |
| `$D/floats.rs` | 1 | 0 |
| `$D/forms.rs` | 1 | 0 |
| `$D/greeting.zed` | 1 | 0 |
| `$D/is.rs` | 1 | 0 |
| `$D/lambdas.rs` | 1 | 0 |
| `$D/marks.rs` | 1 | 0 |
| `$D/returns.rs` | 1 | 0 |
| `$D/shape.zed` | 1 | 0 |
| `$D/tests_of_types.rs` | 1 | 0 |
| `$D/tuples.rs` | 1 | 0 |
| `$D/untestable.zed` | 1 | 0 |
| `$D/username.zed` | 1 | 0 |
| `$D/words.rs` | 1 | 0 |
| `$D/zed.rs` | 1 | 0 |
| `$S/c.zed` | 1 | 0 |
| `$S/cx18.py` | 0 | 1 |
| `$S/d.zed` | 1 | 0 |
| `$S/f10.py` | 0 | 1 |
| `$S/f14.py` | 0 | 1 |
| `$S/f16.py` | 0 | 1 |
| `$S/f6.py` | 0 | 1 |
| `$S/frontier.py` | 0 | 1 |
| `$S/mut31.py` | 1 | 0 |
| `$S/mut32.py` | 1 | 0 |
| `$S/mut34.py` | 1 | 0 |
| `$S/mutant.py` | 0 | 1 |
| `$S/mutants.py` | 0 | 1 |
| `$S/mutate.py` | 1 | 0 |
| `$S/open/*.zed` | 0 | 1 |
| `$S/p30.zed` | 1 | 0 |
| `$S/probe.rs` | 0 | 1 |
| `$S/probe/Cargo.toml` | 1 | 0 |
| `$S/probe/d.zed` | 0 | 1 |
| `$S/probe/src/main.rs` | 1 | 0 |
| `$S/r4b.py` | 0 | 1 |
| `$S/r4c.py` | 0 | 1 |
| `$S/r4d.py` | 0 | 1 |
| `$S/revisions.py` | 0 | 1 |
| `$S/t/dead.zed` | 1 | 0 |
| `$S/t/e.zed` | 1 | 0 |
| `$S/t/f.zed` | 1 | 0 |
| `$S/t/g.zed` | 1 | 0 |
| `$S/t/h.zed` | 1 | 0 |
| `$S/t/outer.zed` | 1 | 0 |
| `$S/t/stale.zed` | 1 | 0 |
| `$S/t/two.zed` | 1 | 0 |
| `$S/t/x1.zed` | 1 | 0 |
| `$S/t/x2.zed` | 1 | 0 |
| `$S/t1.zed` | 1 | 0 |
| `$S/twice/t$n.zed` | 0 | 1 |
| `$S/w30.zed` | 1 | 0 |
| `$SP/mut18.py` | 1 | 0 |
| `$SP/mutate.py` | 1 | 0 |
| `$SP/mutate6.py` | 1 | 0 |
| `$cd_dir/axioms.rs` | 1 | 0 |
| `$cd_dir/mod.rs` | 1 | 0 |
| `$d/limits.rs` | 1 | 0 |
| `$t/graphs.rs` | 1 | 0 |
| `$t/items.rs` | 1 | 0 |
| `.cargo/config.toml` | 1 | 0 |
| `EXAMPLES.md` | 1 | 0 |
| `ZED0.md` | 1 | 0 |
| `aot.rs` | 1 | 0 |
| `binders.rs` | 1 | 0 |
| `calls.rs` | 1 | 0 |
| `checks.rs` | 1 | 0 |
| `clippy.toml` | 0 | 1 |
| `codegen.rs` | 1 | 0 |
| `corpus/LEDGER.md` | 1 | 0 |
| `crates/$c/Cargo.toml` | 1 | 0 |
| `crates/zed-cert/src/lib.rs` | 1 | 0 |
| `crates/zed-kernel/Cargo.toml` | 0 | 1 |
| `crates/zed-native/Cargo.toml` | 1 | 0 |
| `crates/zed-native/src/gen.rs` | 1 | 0 |
| `crates/zed-rt/src/lib.rs` | 1 | 0 |
| `crates/zed-rt/src/ports.rs` | 1 | 0 |
| `crates/zedc/src/address.rs` | 1 | 0 |
| `crates/zedc/src/ast/types.rs` | 1 | 0 |
| `crates/zedc/src/canon/domain.rs` | 1 | 0 |
| `crates/zedc/src/fence.rs` | 1 | 0 |
| `crates/zedc/src/lex/comment.rs` | 1 | 0 |
| `crates/zedc/src/lex/punct.rs` | 1 | 0 |
| `errors.rs` | 1 | 0 |
| `family.rs` | 1 | 0 |
| `fences.rs` | 1 | 0 |
| `fits.rs` | 1 | 0 |
| `ifs.rs` | 1 | 0 |
| `l01_31_zir/graphs.rs` | 1 | 0 |
| `lib.rs` | 1 | 0 |
| `m0_11_prelude_axioms_and_limits/mod.rs` | 1 | 0 |
| `m0_11_prelude_axioms_and_limits/signed_zero.rs` | 1 | 0 |
| `main.rs` | 1 | 0 |
| `narrowing.rs` | 1 | 0 |
| `product.rs` | 0 | 1 |
| `pushes.rs` | 1 | 0 |
| `scalars.rs` | 1 | 0 |
| `signatures.rs` | 1 | 0 |
| `src/zir/text.rs` | 1 | 0 |
| `steps/main.rs` | 1 | 0 |
| `strings.rs` | 1 | 0 |
| `term.rs` | 1 | 0 |
| `tests/src/tokens.rs` | 1 | 0 |
| `tests/steps/l01_01_source_loading/accepted.rs` | 1 | 0 |
| `tests/steps/l01_02_lexer_names/mod.rs` | 1 | 0 |
| `tests/steps/l01_03_lexer_integers/mod.rs` | 1 | 0 |
| `tests/steps/l01_07_fences/copies.rs` | 1 | 0 |
| `tests/steps/l01_07_fences/extractor.rs` | 1 | 0 |
| `tests/steps/l01_07_fences/mod.rs` | 1 | 0 |
| `tests/steps/l01_08_parser/probe.rs` | 1 | 0 |
| `tests/steps/l01_09_postfix_chains/mod.rs` | 1 | 0 |
| `tests/steps/l01_10_lambdas_types_else_tuples/fences.rs` | 1 | 0 |
| `tests/steps/l01_11_statements/fences.rs` | 1 | 0 |
| `tests/steps/l01_12_declarations/functions.rs` | 1 | 0 |
| `tests/steps/l01_12_declarations/mod.rs` | 1 | 0 |
| `tests/steps/l01_14_name_resolution/fences.rs` | 1 | 0 |
| `tests/steps/l01_14_name_resolution/order.rs` | 1 | 0 |
| `tests/steps/l01_14_name_resolution/survey.rs` | 1 | 0 |
| `tests/steps/l01_15_kernel_terms/notation.rs` | 1 | 0 |
| `tests/steps/l01_16_elaboration/calls.rs` | 1 | 0 |
| `tests/steps/l01_17_value_representation/equality.rs` | 1 | 0 |
| `tests/steps/l01_17_value_representation/mod.rs` | 1 | 0 |
| `tests/steps/l01_18_scalar_interpreter/casts.rs` | 1 | 0 |
| `tests/steps/l01_18_scalar_interpreter/{casts,failures,words}.rs` | 1 | 0 |
| `tests/steps/l01_19_whole_file_ports/mod.rs` | 1 | 0 |
| `tests/steps/l01_21_test_runner/cones.rs` | 0 | 1 |
| `tests/steps/l01_23_subtyping/cases.rs` | 1 | 0 |
| `tests/steps/l01_23_subtyping/mod.rs` | 1 | 0 |
| `tests/steps/l01_24_refinement_lattices/bounds.rs` | 1 | 0 |
| `tests/steps/l01_25_preimage_catalog/probe_scale.rs` | 1 | 0 |
| `tests/steps/l01_26_type_resolution/adoption.rs` | 1 | 0 |
| `tests/steps/l01_26_type_resolution/narrowing.rs` | 1 | 0 |
| `tests/steps/l01_29_diagnostics/probe_tmp.rs` | 0 | 1 |
| `tests/steps/l01_29_diagnostics/repairs.rs` | 1 | 0 |
| `tests/steps/l01_31_zir/graphs.rs` | 1 | 0 |
| `tests/steps/l01_31_zir/mod.rs` | 1 | 0 |
| `tests/steps/l01_32_canonical_zir/mod.rs` | 1 | 0 |
| `tests/steps/l01_34_memory/borrow.rs` | 1 | 0 |
| `tests/steps/l01_34_memory/checks.rs` | 1 | 0 |
| `tests/steps/l01_34_memory/explore.rs` | 1 | 0 |
| `tests/steps/l01_34_memory/fusion.rs` | 1 | 0 |
| `tests/steps/l01_35_mlir_study/mod.rs` | 1 | 0 |
| `tests/steps/l01_36_cranelift/ports.rs` | 1 | 0 |
| `tests/steps/l01_36_cranelift/scalars.rs` | 0 | 1 |
| `tests/steps/l01_36_cranelift/strings.rs` | 1 | 0 |
| `tests/steps/m0_01_scaffolding/mod.rs` | 1 | 0 |
| `tests/steps/m0_01_scaffolding/snapshots/*.snap` | 1 | 0 |
| `tests/steps/m0_07_canonicalization/scaling.rs` | 0 | 1 |
| `tests/steps/m0_08_zed0_checklist/mod.rs` | 1 | 0 |
| `tests/steps/m0_11_prelude_axioms_and_limits/signed_zero.rs` | 0 | 1 |
| `ty.rs` | 0 | 1 |
| `zed/compiler/audit.py` | 1 | 0 |
| `zed/corpus/24-weighted-pick.zed` | 1 | 0 |
| `zed/corpus/ref/24.py` | 1 | 0 |
| `zed/prelude/cost.zed` | 1 | 0 |
| `zed/prelude/limits.zed` | 1 | 0 |
| `zed/prelude/unit.zed` | 1 | 0 |
| `zedc/src/zir/lower.rs` | 1 | 0 |
| **total (437 files)** | **1165** | **986** |

## Code size per file

The bytes of each Rust source and test file, and of the Dart files that port it once they pass.
`tools/sizes.py` writes this table from `tools/dart_map.txt`, which pairs each Dart file with
the Rust file it ports; a Rust file only partly ported so far shows the Dart written so far.

<!-- sizes -->
| Rust file | bytes | Dart files | bytes | Dart / Rust |
|---|---:|---|---:|---:|
| `crates/zed-cert/src/lib.rs` | 371 | | | |
| `crates/zed-kernel/src/error.rs` | 4,895 | `lib/src/kernel/error.dart`<br>`test/kernel/error_test.dart` | 4,993 | 1.02 |
| `crates/zed-kernel/src/eval.rs` | 60,185 | `lib/src/kernel/eval.dart` | 33,816 | 0.56 |
| `crates/zed-kernel/src/exact.rs` | 9,165 | `lib/src/kernel/exact.dart`<br>`test/kernel/exact_test.dart` | 6,847 | 0.75 |
| `crates/zed-kernel/src/family.rs` | 13,904 | `lib/src/kernel/family.dart`<br>`lib/src/kernel/pmap.dart`<br>`test/kernel/family_test.dart` | 16,256 | 1.17 |
| `crates/zed-kernel/src/lib.rs` | 1,148 | `lib/kernel.dart` | 299 | 0.26 |
| `crates/zed-kernel/src/num.rs` | 7,397 | `lib/src/kernel/num.dart` | 5,848 | 0.79 |
| `crates/zed-kernel/src/print.rs` | 16,237 | | | |
| `crates/zed-kernel/src/provenance.rs` | 10,812 | | | |
| `crates/zed-kernel/src/term.rs` | 13,219 | `lib/src/kernel/term.dart` | 6,217 | 0.47 |
| `crates/zed-kernel/src/text.rs` | 5,582 | `lib/src/kernel/text.dart`<br>`test/kernel/text_test.dart` | 4,320 | 0.77 |
| `crates/zed-kernel/src/types.rs` | 37,473 | | | |
| `crates/zed-kernel/src/types/bdd.rs` | 27,452 | | | |
| `crates/zed-kernel/src/types/empty.rs` | 7,024 | | | |
| `crates/zed-kernel/src/types/rec.rs` | 18,327 | | | |
| `crates/zed-kernel/src/value.rs` | 16,674 | `lib/src/kernel/value.dart`<br>`test/kernel/value_test.dart` | 14,226 | 0.85 |
| `crates/zed-kernel/src/words.rs` | 5,277 | `lib/src/kernel/words.dart` | 4,024 | 0.76 |
| `crates/zed-native/src/codegen.rs` | 27,147 | | | |
| `crates/zed-native/src/hooks.rs` | 18,557 | | | |
| `crates/zed-native/src/lib.rs` | 3,845 | | | |
| `crates/zed-native/src/tables.rs` | 7,653 | | | |
| `crates/zed-rt/src/heap.rs` | 18,978 | | | |
| `crates/zed-rt/src/lib.rs` | 764 | | | |
| `crates/zed-rt/src/ports.rs` | 2,581 | | | |
| `crates/zed-rt/src/rope.rs` | 4,631 | | | |
| `crates/zedc/src/address.rs` | 2,176 | | | |
| `crates/zedc/src/ast/mod.rs` | 21,974 | | | |
| `crates/zedc/src/ast/stmts.rs` | 9,682 | | | |
| `crates/zedc/src/ast/types.rs` | 11,772 | | | |
| `crates/zedc/src/axioms.rs` | 7,016 | | | |
| `crates/zedc/src/canon/binders.rs` | 20,447 | | | |
| `crates/zedc/src/canon/domain.rs` | 4,086 | | | |
| `crates/zedc/src/canon/mod.rs` | 8,601 | | | |
| `crates/zedc/src/canon/serial.rs` | 10,637 | | | |
| `crates/zedc/src/check/mod.rs` | 109,155 | | | |
| `crates/zedc/src/check/ty.rs` | 26,843 | | | |
| `crates/zedc/src/cost.rs` | 8,807 | | | |
| `crates/zedc/src/elab.rs` | 56,580 | | | |
| `crates/zedc/src/fence.rs` | 2,991 | | | |
| `crates/zedc/src/format.rs` | 23,772 | | | |
| `crates/zedc/src/interp.rs` | 1,137 | | | |
| `crates/zedc/src/lex/comment.rs` | 1,304 | | | |
| `crates/zedc/src/lex/mod.rs` | 8,813 | | | |
| `crates/zedc/src/lex/name.rs` | 3,147 | | | |
| `crates/zedc/src/lex/number.rs` | 4,413 | | | |
| `crates/zedc/src/lex/punct.rs` | 1,719 | | | |
| `crates/zedc/src/lex/string.rs` | 11,031 | | | |
| `crates/zedc/src/lib.rs` | 835 | | | |
| `crates/zedc/src/main.rs` | 1,770 | | | |
| `crates/zedc/src/parse/grammar.rs` | 10,399 | | | |
| `crates/zedc/src/parse/mod.rs` | 10,459 | | | |
| `crates/zedc/src/query.rs` | 4,746 | | | |
| `crates/zedc/src/resolve.rs` | 15,634 | | | |
| `crates/zedc/src/run.rs` | 24,727 | | | |
| `crates/zedc/src/source.rs` | 7,459 | | | |
| `crates/zedc/src/stage.rs` | 31,611 | | | |
| `crates/zedc/src/store/affine.rs` | 19,512 | | | |
| `crates/zedc/src/store/cell.rs` | 13,091 | | | |
| `crates/zedc/src/store/float.rs` | 5,956 | | | |
| `crates/zedc/src/store/interval.rs` | 21,092 | | | |
| `crates/zedc/src/store/iterate.rs` | 9,869 | | | |
| `crates/zedc/src/store/lattice.rs` | 16,014 | | | |
| `crates/zedc/src/store/mod.rs` | 690 | | | |
| `crates/zedc/src/store/preimage.rs` | 100,503 | | | |
| `crates/zedc/src/store/presburger.rs` | 56,642 | | | |
| `crates/zedc/src/store/product.rs` | 51,610 | | | |
| `crates/zedc/src/store/revision.rs` | 25,960 | | | |
| `crates/zedc/src/store/wto.rs` | 10,717 | | | |
| `crates/zedc/src/testing.rs` | 10,643 | | | |
| `crates/zedc/src/zir/binary.rs` | 16,518 | | | |
| `crates/zedc/src/zir/canon.rs` | 10,571 | | | |
| `crates/zedc/src/zir/lower.rs` | 40,730 | | | |
| `crates/zedc/src/zir/memory.rs` | 45,377 | | | |
| `crates/zedc/src/zir/mod.rs` | 24,971 | | | |
| `crates/zedc/src/zir/text.rs` | 36,164 | | | |
| `tests/src/check.rs` | 5,056 | | | |
| `tests/src/fences.rs` | 3,325 | | | |
| `tests/src/instances.rs` | 5,466 | `test/support/instances.dart` | 1,064 | 0.19 |
| `tests/src/kernel.rs` | 10,041 | `test/support/kernel.dart` | 7,960 | 0.79 |
| `tests/src/lib.rs` | 2,590 | `test/support/support.dart`<br>`test/support/support_test.dart` | 3,467 | 1.34 |
| `tests/src/oracle.rs` | 7,128 | | | |
| `tests/src/scaling.rs` | 3,377 | `test/support/scaling.dart` | 2,230 | 0.66 |
| `tests/src/tokens.rs` | 1,819 | | | |
| `tests/src/trees.rs` | 1,371 | | | |
| `tests/steps/l01_01_source_loading/accepted.rs` | 1,455 | | | |
| `tests/steps/l01_01_source_loading/mod.rs` | 163 | | | |
| `tests/steps/l01_01_source_loading/places.rs` | 1,478 | | | |
| `tests/steps/l01_01_source_loading/rejected.rs` | 5,272 | | | |
| `tests/steps/l01_02_lexer_names/mod.rs` | 126 | | | |
| `tests/steps/l01_02_lexer_names/names.rs` | 2,106 | | | |
| `tests/steps/l01_02_lexer_names/scripts.rs` | 2,205 | | | |
| `tests/steps/l01_03_lexer_integers/mod.rs` | 2,418 | | | |
| `tests/steps/l01_04_lexer_floats_and_rationals/mod.rs` | 2,411 | | | |
| `tests/steps/l01_05_lexer_strings/holes.rs` | 2,265 | | | |
| `tests/steps/l01_05_lexer_strings/mod.rs` | 1,138 | | | |
| `tests/steps/l01_05_lexer_strings/scaling.rs` | 1,663 | | | |
| `tests/steps/l01_05_lexer_strings/strings.rs` | 3,036 | | | |
| `tests/steps/l01_06_lexer_tokens/mod.rs` | 198 | | | |
| `tests/steps/l01_06_lexer_tokens/program.rs` | 2,380 | | | |
| `tests/steps/l01_06_lexer_tokens/words.rs` | 3,054 | | | |
| `tests/steps/l01_07_fences/copies.rs` | 4,073 | | | |
| `tests/steps/l01_07_fences/extractor.rs` | 1,624 | | | |
| `tests/steps/l01_07_fences/mod.rs` | 275 | | | |
| `tests/steps/l01_08_parser/cases.rs` | 4,059 | | | |
| `tests/steps/l01_08_parser/errors.rs` | 969 | | | |
| `tests/steps/l01_08_parser/mod.rs` | 214 | | | |
| `tests/steps/l01_08_parser/rings.rs` | 1,697 | | | |
| `tests/steps/l01_09_postfix_chains/calls.rs` | 2,767 | | | |
| `tests/steps/l01_09_postfix_chains/chains.rs` | 2,422 | | | |
| `tests/steps/l01_09_postfix_chains/fences.rs` | 1,560 | | | |
| `tests/steps/l01_09_postfix_chains/mod.rs` | 609 | | | |
| `tests/steps/l01_10_lambdas_types_else_tuples/elses.rs` | 1,137 | | | |
| `tests/steps/l01_10_lambdas_types_else_tuples/fences.rs` | 1,170 | | | |
| `tests/steps/l01_10_lambdas_types_else_tuples/lambdas.rs` | 1,491 | | | |
| `tests/steps/l01_10_lambdas_types_else_tuples/mod.rs` | 1,042 | | | |
| `tests/steps/l01_10_lambdas_types_else_tuples/tests_of_types.rs` | 2,064 | | | |
| `tests/steps/l01_10_lambdas_types_else_tuples/tuples.rs` | 402 | | | |
| `tests/steps/l01_11_statements/blocks.rs` | 3,631 | | | |
| `tests/steps/l01_11_statements/fences.rs` | 1,382 | | | |
| `tests/steps/l01_11_statements/mod.rs` | 1,308 | | | |
| `tests/steps/l01_11_statements/returns.rs` | 675 | | | |
| `tests/steps/l01_12_declarations/fences.rs` | 945 | | | |
| `tests/steps/l01_12_declarations/functions.rs` | 2,328 | | | |
| `tests/steps/l01_12_declarations/ifs.rs` | 703 | | | |
| `tests/steps/l01_12_declarations/mod.rs` | 1,390 | | | |
| `tests/steps/l01_12_declarations/pushes.rs` | 304 | | | |
| `tests/steps/l01_13_formatter/fences.rs` | 1,584 | | | |
| `tests/steps/l01_13_formatter/layout.rs` | 3,440 | | | |
| `tests/steps/l01_13_formatter/mod.rs` | 1,943 | | | |
| `tests/steps/l01_13_formatter/scaling.rs` | 1,811 | | | |
| `tests/steps/l01_14_name_resolution/fences.rs` | 1,432 | | | |
| `tests/steps/l01_14_name_resolution/mod.rs` | 2,673 | | | |
| `tests/steps/l01_14_name_resolution/order.rs` | 2,255 | | | |
| `tests/steps/l01_14_name_resolution/scaling.rs` | 2,201 | | | |
| `tests/steps/l01_14_name_resolution/scopes.rs` | 3,843 | | | |
| `tests/steps/l01_15_kernel_terms/evidence.rs` | 3,397 | | | |
| `tests/steps/l01_15_kernel_terms/layout.rs` | 4,320 | | | |
| `tests/steps/l01_15_kernel_terms/mod.rs` | 288 | | | |
| `tests/steps/l01_15_kernel_terms/notation.rs` | 5,524 | | | |
| `tests/steps/l01_15_kernel_terms/scaling.rs` | 2,895 | | | |
| `tests/steps/l01_16_elaboration/calls.rs` | 2,863 | | | |
| `tests/steps/l01_16_elaboration/errors.rs` | 4,274 | | | |
| `tests/steps/l01_16_elaboration/mod.rs` | 2,130 | | | |
| `tests/steps/l01_16_elaboration/programs.rs` | 6,170 | | | |
| `tests/steps/l01_16_elaboration/scaling.rs` | 8,985 | | | |
| `tests/steps/l01_17_value_representation/atoms.rs` | 3,143 | | | |
| `tests/steps/l01_17_value_representation/equality.rs` | 1,900 | | | |
| `tests/steps/l01_17_value_representation/mod.rs` | 439 | | | |
| `tests/steps/l01_17_value_representation/numbers.rs` | 3,876 | | | |
| `tests/steps/l01_17_value_representation/order.rs` | 2,591 | | | |
| `tests/steps/l01_18_scalar_interpreter/casts.rs` | 3,013 | | | |
| `tests/steps/l01_18_scalar_interpreter/failures.rs` | 2,066 | | | |
| `tests/steps/l01_18_scalar_interpreter/floats.rs` | 2,591 | | | |
| `tests/steps/l01_18_scalar_interpreter/mod.rs` | 472 | | | |
| `tests/steps/l01_18_scalar_interpreter/words.rs` | 1,770 | | | |
| `tests/steps/l01_19_whole_file_ports/files.rs` | 3,361 | | | |
| `tests/steps/l01_19_whole_file_ports/lines.rs` | 2,653 | | | |
| `tests/steps/l01_19_whole_file_ports/mod.rs` | 1,734 | | | |
| `tests/steps/l01_19_whole_file_ports/replay.rs` | 2,909 | | | |
| `tests/steps/l01_19_whole_file_ports/writes.rs` | 5,039 | | | |
| `tests/steps/l01_20_provenance/kernel.rs` | 11,110 | | | |
| `tests/steps/l01_20_provenance/mod.rs` | 1,709 | | | |
| `tests/steps/l01_20_provenance/programs.rs` | 2,221 | | | |
| `tests/steps/l01_20_provenance/scaling.rs` | 3,753 | | | |
| `tests/steps/l01_21_test_runner/command.rs` | 1,961 | | | |
| `tests/steps/l01_21_test_runner/cones.rs` | 2,773 | | | |
| `tests/steps/l01_21_test_runner/fences.rs` | 1,302 | | | |
| `tests/steps/l01_21_test_runner/marks.rs` | 1,835 | | | |
| `tests/steps/l01_21_test_runner/mod.rs` | 672 | | | |
| `tests/steps/l01_21_test_runner/scaling.rs` | 1,563 | | | |
| `tests/steps/l01_21_test_runner/tables.rs` | 3,635 | | | |
| `tests/steps/l01_21_test_runner/zed.rs` | 1,016 | | | |
| `tests/steps/l01_22_type_representation/forms.rs` | 5,811 | | | |
| `tests/steps/l01_22_type_representation/is.rs` | 1,718 | | | |
| `tests/steps/l01_22_type_representation/laws.rs` | 7,730 | | | |
| `tests/steps/l01_22_type_representation/mod.rs` | 387 | | | |
| `tests/steps/l01_23_subtyping/cases.rs` | 6,177 | | | |
| `tests/steps/l01_23_subtyping/mod.rs` | 549 | | | |
| `tests/steps/l01_23_subtyping/oracle.rs` | 8,422 | | | |
| `tests/steps/l01_23_subtyping/rec.rs` | 12,986 | | | |
| `tests/steps/l01_23_subtyping/scaling.rs` | 14,517 | | | |
| `tests/steps/l01_24_refinement_lattices/bounds.rs` | 6,164 | | | |
| `tests/steps/l01_24_refinement_lattices/cell.rs` | 6,341 | | | |
| `tests/steps/l01_24_refinement_lattices/float.rs` | 3,442 | | | |
| `tests/steps/l01_24_refinement_lattices/loops.rs` | 6,177 | | | |
| `tests/steps/l01_24_refinement_lattices/mod.rs` | 3,301 | | | |
| `tests/steps/l01_24_refinement_lattices/scaling.rs` | 9,294 | | | |
| `tests/steps/l01_25_preimage_catalog/entries.rs` | 10,757 | | | |
| `tests/steps/l01_25_preimage_catalog/exact.rs` | 4,245 | | | |
| `tests/steps/l01_25_preimage_catalog/mod.rs` | 5,544 | | | |
| `tests/steps/l01_25_preimage_catalog/random.rs` | 15,145 | | | |
| `tests/steps/l01_25_preimage_catalog/scaling.rs` | 8,378 | | | |
| `tests/steps/l01_25_preimage_catalog/stops.rs` | 4,452 | | | |
| `tests/steps/l01_25_preimage_catalog/tonicity.rs` | 6,655 | | | |
| `tests/steps/l01_26_type_resolution/adoption.rs` | 2,963 | | | |
| `tests/steps/l01_26_type_resolution/calls.rs` | 1,711 | | | |
| `tests/steps/l01_26_type_resolution/fits.rs` | 2,412 | | | |
| `tests/steps/l01_26_type_resolution/mod.rs` | 1,634 | | | |
| `tests/steps/l01_26_type_resolution/narrowing.rs` | 2,113 | | | |
| `tests/steps/l01_26_type_resolution/random.rs` | 4,051 | | | |
| `tests/steps/l01_26_type_resolution/scaling.rs` | 3,444 | | | |
| `tests/steps/l01_26_type_resolution/signatures.rs` | 4,237 | | | |
| `tests/steps/l01_27_absences/families.rs` | 3,030 | | | |
| `tests/steps/l01_27_absences/loose.rs` | 2,981 | | | |
| `tests/steps/l01_27_absences/mod.rs` | 565 | | | |
| `tests/steps/l01_28_staging/mix.rs` | 7,525 | | | |
| `tests/steps/l01_28_staging/mod.rs` | 1,692 | | | |
| `tests/steps/l01_28_staging/scaling.rs` | 1,987 | | | |
| `tests/steps/l01_28_staging/trick.rs` | 5,160 | | | |
| `tests/steps/l01_29_diagnostics/derivations.rs` | 7,910 | | | |
| `tests/steps/l01_29_diagnostics/layout.rs` | 1,974 | | | |
| `tests/steps/l01_29_diagnostics/mod.rs` | 975 | | | |
| `tests/steps/l01_29_diagnostics/repairs.rs` | 1,845 | | | |
| `tests/steps/l01_29_diagnostics/scaling.rs` | 1,691 | | | |
| `tests/steps/l01_29_diagnostics/variants.rs` | 3,220 | | | |
| `tests/steps/l01_30_queries/keys.rs` | 690 | | | |
| `tests/steps/l01_30_queries/mod.rs` | 1,120 | | | |
| `tests/steps/l01_30_queries/reuse.rs` | 4,327 | | | |
| `tests/steps/l01_31_zir/graphs.rs` | 6,502 | | | |
| `tests/steps/l01_31_zir/items.rs` | 3,698 | | | |
| `tests/steps/l01_31_zir/mod.rs` | 1,199 | | | |
| `tests/steps/l01_31_zir/rejections.rs` | 9,252 | | | |
| `tests/steps/l01_32_canonical_zir/fuzz.rs` | 7,874 | | | |
| `tests/steps/l01_32_canonical_zir/mod.rs` | 557 | | | |
| `tests/steps/l01_32_canonical_zir/stability.rs` | 6,674 | | | |
| `tests/steps/l01_33_lowering/corpus.rs` | 1,687 | | | |
| `tests/steps/l01_33_lowering/cse.rs` | 2,578 | | | |
| `tests/steps/l01_33_lowering/errors.rs` | 2,795 | | | |
| `tests/steps/l01_33_lowering/forms.rs` | 8,027 | | | |
| `tests/steps/l01_33_lowering/mod.rs` | 2,007 | | | |
| `tests/steps/l01_33_lowering/ports.rs` | 4,565 | | | |
| `tests/steps/l01_33_lowering/scaling.rs` | 4,443 | | | |
| `tests/steps/l01_34_memory/borrow.rs` | 4,405 | | | |
| `tests/steps/l01_34_memory/cells.rs` | 4,070 | | | |
| `tests/steps/l01_34_memory/checks.rs` | 2,185 | | | |
| `tests/steps/l01_34_memory/corpus.rs` | 3,156 | | | |
| `tests/steps/l01_34_memory/fusion.rs` | 2,960 | | | |
| `tests/steps/l01_34_memory/mod.rs` | 1,432 | | | |
| `tests/steps/l01_35_mlir_study/mod.rs` | 4,008 | | | |
| `tests/steps/l01_36_cranelift/aot.rs` | 1,041 | | | |
| `tests/steps/l01_36_cranelift/checks.rs` | 3,759 | | | |
| `tests/steps/l01_36_cranelift/corpus.rs` | 2,456 | | | |
| `tests/steps/l01_36_cranelift/mod.rs` | 1,225 | | | |
| `tests/steps/l01_36_cranelift/ports.rs` | 1,802 | | | |
| `tests/steps/l01_36_cranelift/scalars.rs` | 5,467 | | | |
| `tests/steps/l01_36_cranelift/strings.rs` | 2,004 | | | |
| `tests/steps/l01_37_oracle/controls.rs` | 2,243 | | | |
| `tests/steps/l01_37_oracle/mod.rs` | 461 | | | |
| `tests/steps/l01_37_oracle/oracle.rs` | 2,818 | | | |
| `tests/steps/l01_38_presburger/controls.rs` | 4,924 | | | |
| `tests/steps/l01_38_presburger/entailment.rs` | 4,804 | | | |
| `tests/steps/l01_38_presburger/mod.rs` | 3,246 | | | |
| `tests/steps/l01_38_presburger/preimage.rs` | 3,156 | | | |
| `tests/steps/l01_38_presburger/random.rs` | 9,176 | | | |
| `tests/steps/l01_38_presburger/scaling.rs` | 3,967 | | | |
| `tests/steps/l01_39_reduced_product/controls.rs` | 9,351 | | | |
| `tests/steps/l01_39_reduced_product/exact.rs` | 5,167 | | | |
| `tests/steps/l01_39_reduced_product/mod.rs` | 2,191 | | | |
| `tests/steps/l01_39_reduced_product/random.rs` | 5,421 | | | |
| `tests/steps/l01_39_reduced_product/scaling.rs` | 4,279 | | | |
| `tests/steps/l01_39_reduced_product/spec.rs` | 3,919 | | | |
| `tests/steps/m0_01_scaffolding/mod.rs` | 1,529 | `test/steps/m0_01_scaffolding/scaffolding_test.dart` | 1,174 | 0.77 |
| `tests/steps/m0_05_widening_and_iteration/iteration.rs` | 11,596 | | | |
| `tests/steps/m0_05_widening_and_iteration/mod.rs` | 6,193 | | | |
| `tests/steps/m0_05_widening_and_iteration/revision.rs` | 8,571 | | | |
| `tests/steps/m0_05_widening_and_iteration/scaling.rs` | 7,201 | | | |
| `tests/steps/m0_05_widening_and_iteration/widening.rs` | 10,766 | | | |
| `tests/steps/m0_05_widening_and_iteration/wto.rs` | 7,970 | | | |
| `tests/steps/m0_06_cost_scalarization/mod.rs` | 9,704 | | | |
| `tests/steps/m0_07_canonicalization/alpha.rs` | 14,310 | | | |
| `tests/steps/m0_07_canonicalization/domains.rs` | 4,497 | | | |
| `tests/steps/m0_07_canonicalization/mod.rs` | 1,083 | | | |
| `tests/steps/m0_07_canonicalization/rules.rs` | 6,095 | | | |
| `tests/steps/m0_07_canonicalization/scaling.rs` | 1,973 | | | |
| `tests/steps/m0_08_zed0_checklist/mod.rs` | 2,069 | | | |
| `tests/steps/m0_09_kernel_evaluator/mod.rs` | 26,083 | `test/steps/m0_09_kernel_evaluator/kernel_evaluator_test.dart` | 20,101 | 0.77 |
| `tests/steps/m0_09_kernel_evaluator/scaling.rs` | 11,009 | `test/steps/m0_09_kernel_evaluator/scaling_test.dart` | 9,446 | 0.86 |
| `tests/steps/m0_10_finite_model_harness/derived.rs` | 3,184 | | | |
| `tests/steps/m0_10_finite_model_harness/laws_01_10.rs` | 24,999 | | | |
| `tests/steps/m0_10_finite_model_harness/laws_11_20.rs` | 29,305 | | | |
| `tests/steps/m0_10_finite_model_harness/laws_21_28.rs` | 26,308 | | | |
| `tests/steps/m0_10_finite_model_harness/mod.rs` | 2,211 | | | |
| `tests/steps/m0_10_finite_model_harness/recursion.rs` | 12,275 | | | |
| `tests/steps/m0_10_finite_model_harness/scaling.rs` | 9,925 | | | |
| `tests/steps/m0_10_finite_model_harness/smoke.rs` | 7,212 | | | |
| `tests/steps/m0_10_finite_model_harness/witnesses.rs` | 11,966 | | | |
| `tests/steps/m0_11_prelude_axioms_and_limits/axioms.rs` | 11,459 | | | |
| `tests/steps/m0_11_prelude_axioms_and_limits/limits.rs` | 3,277 | | | |
| `tests/steps/m0_11_prelude_axioms_and_limits/mod.rs` | 453 | | | |
| `tests/steps/m0_11_prelude_axioms_and_limits/signed_zero.rs` | 1,622 | | | |
| `tests/steps/m0_11_prelude_axioms_and_limits/units.rs` | 3,566 | | | |
| `tests/steps/main.rs` | 1,298 | | | |
| **all 292 Rust files** | **2,228,697** | | | |
| **the Rust files ported so far** | **197,541** | | **142,288** | **0.72** |
<!-- /sizes -->

## Ease of each step in each language

Rust, from the record above:

- **M0.9, kernel evaluator.** The evaluator first copied families and environments on every
  read to keep ownership simple; K6 (share families), K7 (persistent family), K8 (persistent
  scope) and K15 (equality by shared maps) later replaced those copies. One E0502 while the
  evaluator held a borrow of its trace.
- **M0.10, finite-model harness.** The most borrow errors of any step (4): mutable borrows of
  the model while iterating it, and a value moved into a closure.
- **L1.15, kernel printer.** An E0499 in the layout test; 16 other compile errors from the
  printer's document type.
- **L1.33.** Two E0373: closures that borrowed locals and had to own them.
- **L1.36, native backend.** Z9 is the clearest case: each node cloned so that a table builder
  could hold the tree. Unfinished at the stop.
- Most other steps had no borrow errors; their compile errors were type and name errors.

Dart:

- **M0.1, scaffolding.** No compile errors. The test harness and the scaling helper were
  small; Dart has no stack-size or thread setup to port.
- **M0.9, kernel evaluator.** No compile errors and no failing test on the first run. The
  evaluator was written in its final shape from the start, the one the Rust version reached
  only after the performance pass: families on a persistent ordered map (`pmap.dart`, in place
  of the `imbl` crate), names in a persistent scope, a family shared rather than copied when a
  variable, literal or lookup yields it. The evaluator runs on an explicit stack, so deep
  recursion needs no large thread stack; the Rust tests started threads with large stacks for
  it. The Dart port leaves out the provenance trace (step L1.20) and the `is` pattern
  (step L1.22), which the Rust `eval.rs` already holds, so its size ratio of 0.56 is low for
  that reason. One mistake caught before the analyzer ran: `lib/kernel.dart` exported
  `family.dart` and `num.dart`, which are `part` files of `value.dart`.

## Dart

*In progress.* Steps ported: M0.1, M0.9. The port lives in `dart/` (Dart 3.13, `dart format -l 100`, `dart analyze`,
`dart test`). It carries its own expected-output files under `dart/test/steps/<step>/expected/` and does
not read the Rust tree.

### Changes per Dart file

Counted as for the Rust files: a file's creation is one change. No step has had a
performance pass yet, so the second number is 0 throughout.

| file | changes before the performance pass | changes during the performance pass |
|---|---:|---:|
| `lib/kernel.dart` | 2 | 0 |
| `lib/src/kernel/error.dart` | 1 | 0 |
| `lib/src/kernel/eval.dart` | 1 | 0 |
| `lib/src/kernel/exact.dart` | 1 | 0 |
| `lib/src/kernel/family.dart` | 1 | 0 |
| `lib/src/kernel/num.dart` | 1 | 0 |
| `lib/src/kernel/pmap.dart` | 1 | 0 |
| `lib/src/kernel/term.dart` | 1 | 0 |
| `lib/src/kernel/text.dart` | 1 | 0 |
| `lib/src/kernel/value.dart` | 1 | 0 |
| `lib/src/kernel/words.dart` | 1 | 0 |
| `test/kernel/error_test.dart` | 1 | 0 |
| `test/kernel/exact_test.dart` | 1 | 0 |
| `test/kernel/family_test.dart` | 1 | 0 |
| `test/kernel/text_test.dart` | 1 | 0 |
| `test/kernel/value_test.dart` | 1 | 0 |
| `test/support/kernel.dart` | 1 | 0 |
| `test/support/instances.dart` | 1 | 0 |
| `test/steps/m0_09_kernel_evaluator/kernel_evaluator_test.dart` | 1 | 0 |
| `test/steps/m0_09_kernel_evaluator/scaling_test.dart` | 1 | 0 |

`dart format` rewrote 8 files at the end of M0.9; reformatting is not counted as a change.
