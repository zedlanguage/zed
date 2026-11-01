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

### Rust changes after the stop

The Dart port found two faults of order n² that the Rust shared, and the Rust was fixed to
match, each with the Dart's scaling test (COMPLEXITY.md K18, F20). With the old code put back,
each test ran past 500 s and was stopped. The port also found a third fault, in the Rust type
checker only (F21), which is left open until the port reaches L1.27. The full Rust test run
now passes 932 tests (930 plus the two new ones), and clippy is clean.

| file | edit calls | lines added | lines removed |
|---|---:|---:|---:|
| `crates/zed-kernel/src/family.rs` | 1 | 6 | 0 |
| `crates/zed-kernel/src/value.rs` | 2 | 13 | 9 |
| `crates/zedc/src/cost.rs` | 2 | 15 | 6 |
| `tests/steps/m0_06_cost_scalarization/mod.rs` | 4 | 29 | 0 |
| `tests/steps/l01_18_scalar_interpreter/mod.rs` | 5 | 1 | 0 |
| `tests/steps/l01_18_scalar_interpreter/scaling.rs` (new) | 7 | 32 | 0 |
| `COMPLEXITY.md` | 1 | 3 | 1 |

The edit calls include the round trips for the negative controls and a probe test that was
added and then removed. Time: 0:05 model, 0:24 tool, most of the tool time spent on the
negative controls and the full test run. No compile errors.

At L1.22 the Dart port found a third shared fault (COMPLEXITY.md F22): a union of n tuple
types in an `is` test took O(n²) to elaborate, in two places. The elaborator joined the types
one at a time, each tuple type to the decision diagram of those before it; and the Rust type
checker, which the Dart does not have yet, copied the union so far at each member. Both now
build the union in one pass. Debug build, n = 250 to 2000: elaboration took 50, 180, 720 and
2,860 ms before and 4, 7, 15 and 34 ms after. The new scaling test fails on the old checker
(45 times as long for 8 times the size, against the limit of 24), and its negative control,
the one-at-a-time union, fails as it should. The full Rust test run now passes 934 tests (932
plus the two new ones), and clippy is clean. L1.22's tests now take 12.0 s on one thread, most
of it in the negative control.

| file | edit calls | lines added | lines removed |
|---|---:|---:|---:|
| `crates/zedc/src/elab.rs` | 1 | 2 | 4 |
| `crates/zedc/src/check/ty.rs` | 1 | 17 | 2 |
| `tests/steps/l01_22_type_representation/mod.rs` | 1 | 1 | 0 |
| `tests/steps/l01_22_type_representation/scaling.rs` (new) | 3 | 67 | 0 |
| `COMPLEXITY.md` | 1 | 1 | 0 |

The edit calls include two probe tests, added and then removed, and two timing probes in the
elaborator, put back from a saved copy. No compile errors. The time is counted in the Dart
port's L1.22 row.

At L1.23 a negative control in the Dart port showed a gap in the shared scaling test for
recursive definitions: running the search for cycles once per definition, which makes the
definition-time checks O(d²), was not caught, because unfolding the chain dominates its time.
Both test sets now also time the definition-time checks alone, on a chain of 1,000 to 8,000
definitions; with the search run once per definition the check fails in Rust and in Dart, and
without it it passes. No Rust library code changed. The full Rust test run passes (868 step
tests), clippy is clean, and L1.23's tests still take 9.8 s on one thread.

| file | edit calls | lines added | lines removed |
|---|---:|---:|---:|
| `tests/steps/l01_23_subtyping/rec.rs` | 1 | 18 | 12 |

The negative control was one edit to `crates/zed-kernel/src/types/rec.rs`, put back from a
saved copy. No compile errors. The time is counted in the Dart port's L1.23 row.

An audit of both implementations for work of order n² (2026-10-31) found three faults shared
by the Rust and the Dart, now fixed in both (COMPLEXITY.md K19, F23, F24): the text of a type,
and of a lambda nested in a parameter's default, copied the texts of the parts inside it; and
each named argument, and each parameter a default reads, was looked for among all the
parameters. Rust elaboration of a call naming n arguments, debug build: 567 ms at n = 4,000
and 23.7 s at 32,000 before, 115 ms and 978 ms after. Every new test fails with the old code
put back, in both languages, except the Rust test of F24: the Rust builder recurses once per
level of nesting and overflows before the copying can be measured, which is left open. The
F23 tests run at n = 8,000, so that each of the four searches fails alone; they take about 33 s
each, and L1.16's tests now take 71.3 s on one thread (20.8 s before). L1.22's take 13.6 s
(12.0 s before), L1.10's 0.6 s and L1.12's 0.2 s. The full Rust test run passes (873 step
tests), and clippy is clean.

| file | lines added | lines removed |
|---|---:|---:|
| `crates/zed-kernel/src/types.rs` | 183 | 71 |
| `crates/zedc/src/ast/mod.rs` | 13 | 2 |
| `crates/zedc/src/ast/stmts.rs` | 8 | 7 |
| `crates/zedc/src/ast/types.rs` | 14 | 9 |
| `crates/zedc/src/check/mod.rs` | 9 | 1 |
| `crates/zedc/src/elab.rs` | 28 | 11 |
| `tests/steps/l01_10_lambdas_types_else_tuples/scaling.rs` (new) | 54 | 0 |
| `tests/steps/l01_16_elaboration/scaling.rs` | 74 | 0 |
| `tests/steps/l01_22_type_representation/scaling.rs` | 40 | 1 |

The negative controls put the old code back from saved copies, in a separate target directory
where a test binary was running. Edit calls and compile errors for this work were not counted.

The rest of the audit's list, in the parts of the Rust not yet ported (COMPLEXITY.md F25 to F27,
Z10 to Z12), is fixed in the Rust alone, so that the Dart port of L1.28 and L1.33 starts from
code of low complexity. Staging looked for each name among the roots and among the names bound
around it; lowering read the whole body of each `let`-bound lambda for its ports, the lambdas
nested in it included, kept a copy of the scope for each function called in place, and its
graph check counted each state edge's uses by search. One fault is shared with the Dart and
fixed in both: the test runner looked for each output port among all the writes. Each new test
fails with the old code put back, at 29 to 74 times as long for 8 times the size; the test of
functions called in place, which passes in 9 s, does not finish in 30 min. The lowering's scope
is now a persistent map (`imbl`, already used by the kernel).
One change of meaning comes with Z11: a name bound
inside a lambda's body is no longer taken for a function of the same name outside it, and a new
test checks this. On one thread L1.28's tests take 30.6 s and L1.33's 22.3 s. The full Rust test
run passes (879 step tests), clippy is clean, and the Dart tests pass (659).

| file | lines added | lines removed |
|---|---:|---:|
| `crates/zedc/Cargo.toml` | 1 | 0 |
| `crates/zedc/src/stage.rs` | 50 | 20 |
| `crates/zedc/src/testing.rs` | 7 | 6 |
| `crates/zedc/src/zir/lower.rs` | 194 | 50 |
| `crates/zedc/src/zir/mod.rs` | 10 | 7 |
| `dart/lib/testing.dart` | 6 | 1 |
| `tests/steps/l01_28_staging/scaling.rs` | 57 | 1 |
| `tests/steps/l01_33_lowering/errors.rs` | 25 | 0 |
| `tests/steps/l01_33_lowering/scaling.rs` | 98 | 0 |

Lowering also found the current state of each port by searching the ports its region had used
(COMPLEXITY.md Z13). Each frame now keeps them in a map; the new test of pushes to many ports
passes in 3.7 s and, with the old code put back, fails at 42 to 44 times as long for 8 times
the size. The Rust change is 11 lines added and 19 removed in `crates/zedc/src/zir/lower.rs`,
with 23 lines of test in `tests/steps/l01_33_lowering/scaling.rs`. On one thread L1.33's tests now take 25.7 s.

The checker collected a signature's type variables by searching those found before, and named
them by searching lists (COMPLEXITY.md F28): a new set beside the ordered list fixes it, and a
test of a signature of many type variables, which passes in 4.2 s, fails with the old code at 29
times as long for 8 times the size. The reasons shown with a type error were found the same way
(F29); the fix is a set, but the old code also passes its test (18 s against 19 s), since its
cost is small beside the rest of the check. A first version of that test put every note on one
line, and took more than 15 min with either code: each step of a diagnostic prints its whole
line, so the output was `O(n²)` characters (F30, not a fault). The Rust changes are 31 lines
added and 22 removed in `crates/zedc/src/check/mod.rs` and `ty.rs`, with 54 lines of test.
The rest of the audit's list in the native code and the counting machine is fixed in the Rust
alone, since the port has not reached L1.34 (COMPLEXITY.md Z5, Z8, Z14, Z15, F33). Each word of
the native code is kept in a stack slot and loaded just before each use, so that no value lives
across many calls; field, port, constant and lambda indices are maps; the counting machine's
memory check looks only at the cells touched since the last check; and Cranelift runs with its
e-graph optimizer and backtracking register allocator off. With the old code put back, many
named fields and many ports do not finish in 10 times the fixed time (671 s and 1411 s), and
many lambdas take 0.53, 1.6, 5.0 and 17.8 s at n = 60 to 500, against 2.9 s for the fixed code
at 500. Many constants and one value used many times are linear on the old code at the sizes
the tests run, so those two tests show no old cost.

| file | lines added | lines removed |
|---|---:|---:|
| `crates/zed-native/src/codegen.rs` | 94 | 44 |
| `crates/zed-native/src/hooks.rs` | 21 | 14 |
| `crates/zed-native/src/lib.rs` | 5 | 1 |
| `crates/zed-native/src/tables.rs` | 21 | 10 |
| `crates/zedc/src/store/product.rs` | 3 | 2 |
| `crates/zedc/src/zir/memory.rs` | 112 | 29 |
| `tests/steps/l01_36_cranelift/mod.rs` | 1 | 0 |
| `tests/steps/l01_36_cranelift/scaling.rs` (new) | 169 | 0 |

At L1.27 the port fixed F21 in both languages, and found and fixed a second shared fault
(F32): the kernel kept its emptiness results from one unit to the next, and a unit checked
after an equal one compared each of its types in full with the equal kept one. `dart test`
runs a file's tests in one isolate, so the Dart showed it first; the Rust showed it in a
probe on one thread (second check 0.55, 2.0 and 7.8 s at n = 2000 to 8000, against 0.26,
0.43 and 0.85 s). The new test checks a chain of failure atoms twice at each size. With the
old `without_loose` it does not finish in 10 times the fixed time in either language; with
the old memo it fails in Dart and passes in Rust, where the fastest of five runs at the larger
size is the first, made before an equal unit is kept. The test needs a 512 MB stack in Rust,
since the Rust parser and checker recurse once per operator.

| file | lines added | lines removed |
|---|---:|---:|
| `crates/zed-kernel/src/types/empty.rs` | 9 | 1 |
| `crates/zedc/src/check/mod.rs` | 1 | 0 |
| `crates/zedc/src/check/ty.rs` | 5 | 2 |
| `tests/steps/l01_27_absences/mod.rs` | 1 | 0 |
| `tests/steps/l01_27_absences/scaling.rs` (new) | 37 | 0 |

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
| L1.22 | 14 | 12.0 s |
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
| L1.18 | 23 | 1.7 s |
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
| M0.10 | 0:49 | 0:10 | 4 (3) | 20 (9) | 0:09 | 0:01 | 3 (2) |
| M0.4 | 0:01 | 0:00 | 0 (0) | 0 (0) | — | — | — |
| M0.5 | 0:54 | 0:59 | 0 (0) | 7 (3) | 0:14 | 0:21 | 6 (3) |
| M0.6 | 0:03 | 0:01 | 0 (0) | 0 (0) | 0:02 | 0:00 | 1 (1) |
| other (Corpus 24) | 0:05 | 0:00 | 0 (0) | 0 (0) | | | |
| M0.7 | 0:04 | 0:12 | 1 (1) | 5 (2) | 0:07 | 0:00 | 1 (1) |
| M0.8 | 0:03 | 0:01 | 0 (0) | 0 (0) | 0:00 | 0:00 | 0 (0) |
| M0.11 | 0:07 | 0:02 | 0 (0) | 1 (1) | 0:02 | 0:00 | 0 (0) |
| L1.1 | 0:03 | 0:01 | 0 (0) | 0 (0) | 0:04 | 0:00 | 1 (1) |
| L1.2 | 0:03 | 0:01 | 0 (0) | 0 (0) | 0:06 | 0:01 | 4 (1) |
| L1.3 | 0:01 | 0:01 | 0 (0) | 0 (0) | 0:00 | 0:00 | 0 (0) |
| L1.4 | 0:01 | 0:00 | 0 (0) | 0 (0) | 0:00 | 0:00 | 0 (0) |
| L1.5 | 0:05 | 0:01 | 0 (0) | 0 (0) | 0:06 | 0:06 | 3 (1) |
| L1.6 | 0:02 | 0:01 | 0 (0) | 0 (0) | 0:01 | 0:00 | 0 (0) |
| L1.7 | 0:06 | 0:01 | 0 (0) | 0 (0) | 0:01 | 0:00 | 0 (0) |
| L1.8 | 0:06 | 0:01 | 0 (0) | 0 (0) | 0:04 | 0:05 | 3 (1) |
| L1.9 | 0:04 | 0:01 | 0 (0) | 0 (0) | 0:03 | 0:01 | 2 (2) |
| L1.10 | 0:04 | 0:01 | 0 (0) | 0 (0) | 0:05 | 0:01 | 0 (0) |
| L1.11 | 0:04 | 0:01 | 0 (0) | 0 (0) | 0:01 | 0:00 | 2 (2) |
| L1.12 | 0:03 | 0:01 | 0 (0) | 2 (1) | 0:01 | 0:08 | 2 (1) |
| L1.13 | 0:09 | 0:03 | 0 (0) | 0 (0) | 0:06 | 0:01 | 1 (1) |
| L1.14 | 0:07 | 0:02 | 0 (0) | 0 (0) | 0:04 | 0:01 | 0 (0) |
| L1.15 | 0:08 | 0:03 | 1 (1) | 16 (3) | 0:04 | 0:03 | 2 (2) |
| L1.16 | 0:15 | 0:01 | 0 (0) | 1 (1) | 0:12 | 0:10 | 0 (0) |
| L1.17 | 0:13 | 0:04 | 0 (0) | 5 (2) | 0:04 | 0:01 | 0 (0) |
| L1.18 | 0:08 | 0:04 | 0 (0) | 2 (1) | 0:03 | 0:14 | 0 (0) |
| L1.19 | 0:12 | 0:03 | 0 (0) | 1 (1) | 0:06 | 0:08 | 8 (1) |
| L1.20 | 0:13 | 0:04 | 0 (0) | 3 (2) | 0:12 | 0:01 | 3 (2) |
| L1.21 | 0:09 | 0:02 | 0 (0) | 0 (0) | 0:05 | 0:02 | 5 (1) |
| L1.22 | 0:14 | 0:04 | 0 (0) | 1 (1) | 0:16 | 0:04 | 19 (5) |
| L1.23 | 0:15 | 0:08 | 0 (0) | 3 (2) | 0:18 | 0:07 | 6 (3) |
| L1.24 | 0:12 | 0:05 | 0 (0) | 1 (1) | 0:05 | 0:04 | 0 (0) |
| L1.25 | 0:36 | 0:16 | 1 (1) | 7 (2) | 0:19 | 0:05 | 9 (3) |
| L1.26 | 1:01 | 0:12 | 0 (0) | 6 (2) | 0:27 | 0:28 | 119 (9) |
| L1.27 | 0:07 | 0:03 | 0 (0) | 2 (2) | 0:42 | 0:35 | 1 (1) |
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
A file's creation counts as one change. 438 files: 1,165 changes before the performance pass,
1,000 during it. DESIGN.md lives in the spec repository but is counted, since steps edited it.
The Dart port records the same two numbers for its own files in the Dart section below.

| file | changes before the performance pass | changes during the performance pass |
|---|---:|---:|
| `STATUS.md` | 70 | 51 |
| `crates/zed-kernel/src/eval.rs` | 39 | 17 |
| `DESIGN.md` | 39 | 16 |
| `crates/zedc/src/check/mod.rs` | 21 | 33 |
| `tests/steps/l01_23_subtyping/scaling.rs` | 0 | 50 |
| `COMPLEXITY.md` | 1 | 48 |
| `tests/steps/main.rs` | 47 | 0 |
| `crates/zedc/src/store/product.rs` | 12 | 32 |
| `tests/steps/l01_25_preimage_catalog/scaling.rs` | 2 | 34 |
| `crates/zedc/src/store/preimage.rs` | 9 | 24 |
| `crates/zed-kernel/src/types/empty.rs` | 1 | 30 |
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
| `crates/zedc/src/check/ty.rs` | 6 | 6 |
| `tests/steps/l01_27_absences/scaling.rs` | 0 | 1 |
| `crates/zedc/src/lex/mod.rs` | 9 | 2 |
| `crates/zedc/src/lex/string.rs` | 8 | 3 |
| `crates/zedc/src/store/revision.rs` | 4 | 7 |
| `tests/steps/l01_13_formatter/scaling.rs` | 0 | 11 |
| `tests/steps/l01_25_preimage_catalog/entries.rs` | 4 | 7 |
| `crates/zedc/src/store/iterate.rs` | 1 | 9 |
| `tests/steps/l01_38_presburger/mod.rs` | 8 | 2 |
| `tests/steps/l01_39_reduced_product/controls.rs` | 2 | 8 |
| `crates/zed-kernel/src/term.rs` | 9 | 0 |
| `crates/zed-native/src/codegen.rs` | 4 | 6 |
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
| `tests/steps/l01_36_cranelift/scaling.rs` | 0 | 9 |
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
| `crates/zed-native/src/lib.rs` | 1 | 5 |
| `crates/zedc/src/query.rs` | 2 | 3 |
| `crates/zedc/src/store/mod.rs` | 5 | 0 |
| `crates/zedc/src/zir/binary.rs` | 5 | 0 |
| `crates/zedc/src/zir/memory.rs` | 4 | 2 |
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
| `tests/steps/l01_27_absences/mod.rs` | 4 | 1 |
| `tests/steps/l01_29_diagnostics/mod.rs` | 1 | 3 |
| `tests/steps/l01_30_queries/reuse.rs` | 4 | 0 |
| `tests/steps/l01_39_reduced_product/exact.rs` | 0 | 4 |
| `tests/steps/l01_39_reduced_product/spec.rs` | 3 | 1 |
| `tests/steps/m0_10_finite_model_harness/laws_21_28.rs` | 4 | 0 |
| `zed/compiler/MLIR.md` | 4 | 0 |
| `zed/prelude/revision.zed` | 3 | 1 |
| `$d/units.rs` | 3 | 0 |
| `crates/zed-kernel/src/exact.rs` | 3 | 0 |
| `crates/zed-native/src/hooks.rs` | 2 | 2 |
| `crates/zed-native/src/tables.rs` | 2 | 2 |
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
| `tests/steps/l01_36_cranelift/mod.rs` | 1 | 2 |
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
`tools/bin/sizes.dart` writes this table from `tools/dart_map.txt`, which pairs each Dart file with
the Rust file it ports; a Rust file only partly ported so far shows the Dart written so far.

<!-- sizes -->
| Rust file | bytes | Dart files | bytes | Dart / Rust |
|---|---:|---|---:|---:|
| `crates/zed-cert/src/lib.rs` | 371 | | | |
| `crates/zed-kernel/src/error.rs` | 4,895 | `lib/src/kernel/error.dart`<br>`test/kernel/error_test.dart` | 4,993 | 1.02 |
| `crates/zed-kernel/src/eval.rs` | 60,185 | `lib/src/kernel/eval.dart` | 42,495 | 0.71 |
| `crates/zed-kernel/src/exact.rs` | 9,165 | `lib/src/kernel/exact.dart`<br>`test/kernel/exact_test.dart` | 6,847 | 0.75 |
| `crates/zed-kernel/src/family.rs` | 14,132 | `lib/src/kernel/family.dart`<br>`lib/src/kernel/pmap.dart`<br>`test/kernel/family_test.dart` | 18,349 | 1.30 |
| `crates/zed-kernel/src/lib.rs` | 1,148 | `lib/kernel.dart` | 362 | 0.32 |
| `crates/zed-kernel/src/num.rs` | 7,397 | `lib/src/kernel/num.dart` | 5,993 | 0.81 |
| `crates/zed-kernel/src/print.rs` | 16,237 | `lib/src/kernel/print.dart` | 12,393 | 0.76 |
| `crates/zed-kernel/src/provenance.rs` | 10,812 | `lib/src/kernel/provenance.dart` | 10,825 | 1.00 |
| `crates/zed-kernel/src/term.rs` | 13,219 | `lib/src/kernel/term.dart` | 6,776 | 0.51 |
| `crates/zed-kernel/src/text.rs` | 5,582 | `lib/src/kernel/text.dart`<br>`test/kernel/text_test.dart` | 4,417 | 0.79 |
| `crates/zed-kernel/src/types.rs` | 40,294 | `lib/src/kernel/types.dart` | 31,339 | 0.78 |
| `crates/zed-kernel/src/types/bdd.rs` | 27,452 | `lib/src/kernel/bdd.dart`<br>`test/steps/l01_22_type_representation/bdd_test.dart` | 20,688 | 0.75 |
| `crates/zed-kernel/src/types/empty.rs` | 7,395 | `lib/src/kernel/empty.dart` | 7,079 | 0.96 |
| `crates/zed-kernel/src/types/rec.rs` | 18,327 | `lib/src/kernel/rec.dart` | 13,763 | 0.75 |
| `crates/zed-kernel/src/value.rs` | 16,934 | `lib/src/kernel/value.dart`<br>`test/kernel/value_test.dart` | 15,465 | 0.91 |
| `crates/zed-kernel/src/words.rs` | 5,277 | `lib/src/kernel/words.dart` | 4,040 | 0.77 |
| `crates/zed-native/src/codegen.rs` | 29,032 | | | |
| `crates/zed-native/src/hooks.rs` | 18,705 | | | |
| `crates/zed-native/src/lib.rs` | 4,130 | | | |
| `crates/zed-native/src/tables.rs` | 8,237 | | | |
| `crates/zed-rt/src/heap.rs` | 18,978 | | | |
| `crates/zed-rt/src/lib.rs` | 764 | | | |
| `crates/zed-rt/src/ports.rs` | 2,581 | | | |
| `crates/zed-rt/src/rope.rs` | 4,631 | | | |
| `crates/zedc/src/address.rs` | 2,176 | `lib/address.dart`<br>`test/address_test.dart` | 2,125 | 0.98 |
| `crates/zedc/src/ast/mod.rs` | 22,450 | `lib/ast.dart` | 16,672 | 0.74 |
| `crates/zedc/src/ast/stmts.rs` | 9,619 | `lib/src/ast/stmts.dart` | 6,861 | 0.71 |
| `crates/zedc/src/ast/types.rs` | 11,820 | `lib/src/ast/types.dart` | 8,520 | 0.72 |
| `crates/zedc/src/axioms.rs` | 7,016 | `lib/axioms.dart` | 7,266 | 1.04 |
| `crates/zedc/src/canon/binders.rs` | 20,447 | `lib/src/canon/binders.dart` | 14,538 | 0.71 |
| `crates/zedc/src/canon/domain.rs` | 4,086 | `lib/src/canon/domain.dart` | 3,436 | 0.84 |
| `crates/zedc/src/canon/mod.rs` | 8,601 | `lib/src/canon/canon.dart`<br>`lib/canon.dart`<br>`lib/src/canon/blake3.dart`<br>`test/canon/blake3_test.dart` | 18,499 | 2.15 |
| `crates/zedc/src/canon/serial.rs` | 10,637 | `lib/src/canon/serial.dart` | 7,244 | 0.68 |
| `crates/zedc/src/check/mod.rs` | 109,499 | `lib/check.dart` | 80,096 | 0.73 |
| `crates/zedc/src/check/ty.rs` | 28,025 | `lib/src/check/ty.dart` | 23,711 | 0.85 |
| `crates/zedc/src/cost.rs` | 9,373 | `lib/cost.dart`<br>`test/cost_test.dart` | 10,032 | 1.07 |
| `crates/zedc/src/elab.rs` | 57,082 | `lib/elab.dart`<br>`lib/src/tables.dart` | 43,882 | 0.77 |
| `crates/zedc/src/fence.rs` | 2,991 | `lib/fence.dart` | 2,352 | 0.79 |
| `crates/zedc/src/format.rs` | 23,772 | `lib/format.dart` | 20,819 | 0.88 |
| `crates/zedc/src/interp.rs` | 1,137 | `lib/interp.dart` | 906 | 0.80 |
| `crates/zedc/src/lex/comment.rs` | 1,304 | `lib/src/lex/comment.dart` | 1,138 | 0.87 |
| `crates/zedc/src/lex/mod.rs` | 8,813 | `lib/lex.dart` | 12,990 | 1.47 |
| `crates/zedc/src/lex/name.rs` | 3,147 | `lib/src/lex/name.dart` | 2,770 | 0.88 |
| `crates/zedc/src/lex/number.rs` | 4,413 | `lib/src/lex/number.dart` | 4,074 | 0.92 |
| `crates/zedc/src/lex/punct.rs` | 1,719 | `lib/src/lex/punct.dart` | 1,544 | 0.90 |
| `crates/zedc/src/lex/string.rs` | 11,031 | `lib/src/lex/string.dart` | 12,231 | 1.11 |
| `crates/zedc/src/lib.rs` | 835 | | | |
| `crates/zedc/src/main.rs` | 1,770 | `bin/zedc.dart` | 1,329 | 0.75 |
| `crates/zedc/src/parse/grammar.rs` | 10,399 | `lib/src/parse/grammar.dart` | 8,017 | 0.77 |
| `crates/zedc/src/parse/mod.rs` | 10,467 | `lib/parse.dart` | 11,116 | 1.06 |
| `crates/zedc/src/query.rs` | 4,746 | | | |
| `crates/zedc/src/resolve.rs` | 15,634 | `lib/resolve.dart` | 13,317 | 0.85 |
| `crates/zedc/src/run.rs` | 24,727 | `lib/run.dart` | 18,133 | 0.73 |
| `crates/zedc/src/source.rs` | 7,459 | `lib/source.dart` | 7,286 | 0.98 |
| `crates/zedc/src/stage.rs` | 32,641 | `lib/stage.dart` | 3,781 | 0.12 |
| `crates/zedc/src/store/affine.rs` | 19,512 | `lib/src/store/affine.dart` | 18,616 | 0.95 |
| `crates/zedc/src/store/cell.rs` | 13,091 | `lib/src/store/cell.dart` | 11,450 | 0.87 |
| `crates/zedc/src/store/float.rs` | 5,956 | `lib/src/store/float.dart` | 4,576 | 0.77 |
| `crates/zedc/src/store/interval.rs` | 21,092 | `lib/src/store/interval.dart`<br>`test/store/interval_test.dart` | 21,857 | 1.04 |
| `crates/zedc/src/store/iterate.rs` | 9,869 | `lib/src/store/iterate.dart` | 8,271 | 0.84 |
| `crates/zedc/src/store/lattice.rs` | 16,014 | `lib/src/store/lattice.dart`<br>`test/store/lattice_test.dart` | 12,885 | 0.80 |
| `crates/zedc/src/store/mod.rs` | 690 | `lib/store.dart` | 477 | 0.69 |
| `crates/zedc/src/store/preimage.rs` | 100,503 | `lib/src/store/preimage.dart` | 67,858 | 0.68 |
| `crates/zedc/src/store/presburger.rs` | 56,642 | | | |
| `crates/zedc/src/store/product.rs` | 51,680 | | | |
| `crates/zedc/src/store/revision.rs` | 25,960 | `lib/src/store/revision.dart`<br>`test/store/revision_test.dart` | 23,082 | 0.89 |
| `crates/zedc/src/store/wto.rs` | 10,717 | `lib/src/store/wto.dart`<br>`test/store/wto_test.dart` | 8,951 | 0.84 |
| `crates/zedc/src/testing.rs` | 10,756 | `lib/testing.dart` | 7,092 | 0.66 |
| `crates/zedc/src/zir/binary.rs` | 16,518 | | | |
| `crates/zedc/src/zir/canon.rs` | 10,571 | | | |
| `crates/zedc/src/zir/lower.rs` | 45,130 | | | |
| `crates/zedc/src/zir/memory.rs` | 48,172 | | | |
| `crates/zedc/src/zir/mod.rs` | 25,095 | | | |
| `crates/zedc/src/zir/text.rs` | 36,164 | | | |
| `tests/src/check.rs` | 5,056 | `test/support/check.dart`<br>`test/support/check_test.dart` | 4,359 | 0.86 |
| `tests/src/fences.rs` | 3,349 | `test/support/fences.dart` | 2,468 | 0.74 |
| `tests/src/instances.rs` | 5,466 | `test/support/instances.dart`<br>`test/support/instances_test.dart` | 4,397 | 0.80 |
| `tests/src/kernel.rs` | 10,041 | `test/support/kernel.dart` | 7,960 | 0.79 |
| `tests/src/lib.rs` | 2,590 | `test/support/support.dart`<br>`test/support/support_test.dart` | 3,467 | 1.34 |
| `tests/src/oracle.rs` | 7,128 | | | |
| `tests/src/scaling.rs` | 3,377 | `test/support/scaling.dart` | 2,230 | 0.66 |
| `tests/src/tokens.rs` | 1,819 | `test/support/tokens.dart` | 1,557 | 0.86 |
| `tests/src/trees.rs` | 1,371 | `test/support/trees.dart` | 1,121 | 0.82 |
| `tests/steps/l01_01_source_loading/accepted.rs` | 1,455 | `test/steps/l01_01_source_loading/accepted_test.dart` | 1,467 | 1.01 |
| `tests/steps/l01_01_source_loading/mod.rs` | 163 | | | |
| `tests/steps/l01_01_source_loading/places.rs` | 1,478 | `test/steps/l01_01_source_loading/places_test.dart` | 1,560 | 1.06 |
| `tests/steps/l01_01_source_loading/rejected.rs` | 5,272 | `test/steps/l01_01_source_loading/rejected_test.dart` | 5,100 | 0.97 |
| `tests/steps/l01_02_lexer_names/mod.rs` | 126 | | | |
| `tests/steps/l01_02_lexer_names/names.rs` | 2,106 | `test/steps/l01_02_lexer_names/names_test.dart` | 1,857 | 0.88 |
| `tests/steps/l01_02_lexer_names/scripts.rs` | 2,205 | `test/steps/l01_02_lexer_names/scripts_test.dart` | 2,478 | 1.12 |
| `tests/steps/l01_03_lexer_integers/mod.rs` | 2,418 | `test/steps/l01_03_lexer_integers/integers_test.dart` | 2,159 | 0.89 |
| `tests/steps/l01_04_lexer_floats_and_rationals/mod.rs` | 2,411 | `test/steps/l01_04_lexer_floats_and_rationals/floats_test.dart` | 2,241 | 0.93 |
| `tests/steps/l01_05_lexer_strings/holes.rs` | 2,265 | `test/steps/l01_05_lexer_strings/holes_test.dart` | 2,332 | 1.03 |
| `tests/steps/l01_05_lexer_strings/mod.rs` | 1,138 | `test/steps/l01_05_lexer_strings/parts.dart` | 1,449 | 1.27 |
| `tests/steps/l01_05_lexer_strings/scaling.rs` | 1,663 | `test/steps/l01_05_lexer_strings/scaling_test.dart` | 1,567 | 0.94 |
| `tests/steps/l01_05_lexer_strings/strings.rs` | 3,036 | `test/steps/l01_05_lexer_strings/strings_test.dart` | 2,798 | 0.92 |
| `tests/steps/l01_06_lexer_tokens/mod.rs` | 198 | | | |
| `tests/steps/l01_06_lexer_tokens/program.rs` | 2,380 | `test/steps/l01_06_lexer_tokens/program_test.dart` | 2,424 | 1.02 |
| `tests/steps/l01_06_lexer_tokens/words.rs` | 3,054 | `test/steps/l01_06_lexer_tokens/words_test.dart` | 2,910 | 0.95 |
| `tests/steps/l01_07_fences/copies.rs` | 4,090 | `test/steps/l01_07_fences/copies_test.dart` | 3,458 | 0.85 |
| `tests/steps/l01_07_fences/extractor.rs` | 1,624 | `test/steps/l01_07_fences/extractor_test.dart` | 1,776 | 1.09 |
| `tests/steps/l01_07_fences/mod.rs` | 287 | | | |
| `tests/steps/l01_08_parser/cases.rs` | 4,060 | `test/steps/l01_08_parser/cases_test.dart` | 4,101 | 1.01 |
| `tests/steps/l01_08_parser/errors.rs` | 969 | `test/steps/l01_08_parser/errors_test.dart` | 1,242 | 1.28 |
| `tests/steps/l01_08_parser/mod.rs` | 214 | | | |
| `tests/steps/l01_08_parser/rings.rs` | 1,713 | `test/steps/l01_08_parser/rings_test.dart` | 1,785 | 1.04 |
| `tests/steps/l01_09_postfix_chains/calls.rs` | 2,767 | `test/steps/l01_09_postfix_chains/calls_test.dart` | 2,796 | 1.01 |
| `tests/steps/l01_09_postfix_chains/chains.rs` | 2,422 | `test/steps/l01_09_postfix_chains/chains_test.dart` | 2,325 | 0.96 |
| `tests/steps/l01_09_postfix_chains/fences.rs` | 1,560 | `test/steps/l01_09_postfix_chains/fences_test.dart` | 1,380 | 0.88 |
| `tests/steps/l01_09_postfix_chains/mod.rs` | 609 | `test/steps/l01_09_postfix_chains/ast.dart` | 548 | 0.90 |
| `tests/steps/l01_10_lambdas_types_else_tuples/elses.rs` | 1,137 | `test/steps/l01_10_lambdas_types_else_tuples/elses_test.dart` | 1,029 | 0.91 |
| `tests/steps/l01_10_lambdas_types_else_tuples/fences.rs` | 1,170 | `test/steps/l01_10_lambdas_types_else_tuples/fences_test.dart` | 1,710 | 1.46 |
| `tests/steps/l01_10_lambdas_types_else_tuples/lambdas.rs` | 1,491 | `test/steps/l01_10_lambdas_types_else_tuples/lambdas_test.dart` | 1,420 | 0.95 |
| `tests/steps/l01_10_lambdas_types_else_tuples/mod.rs` | 1,055 | `test/steps/l01_10_lambdas_types_else_tuples/sx.dart` | 929 | 0.88 |
| `tests/steps/l01_10_lambdas_types_else_tuples/scaling.rs` | 1,884 | | | |
| `tests/steps/l01_10_lambdas_types_else_tuples/tests_of_types.rs` | 2,064 | `test/steps/l01_10_lambdas_types_else_tuples/types_test.dart` | 1,967 | 0.95 |
| `tests/steps/l01_10_lambdas_types_else_tuples/tuples.rs` | 402 | `test/steps/l01_10_lambdas_types_else_tuples/tuples_test.dart` | 448 | 1.11 |
| `tests/steps/l01_11_statements/blocks.rs` | 3,631 | `test/steps/l01_11_statements/blocks_test.dart` | 3,075 | 0.85 |
| `tests/steps/l01_11_statements/fences.rs` | 1,382 | `test/steps/l01_11_statements/fences_test.dart` | 1,310 | 0.95 |
| `tests/steps/l01_11_statements/mod.rs` | 1,308 | `test/steps/l01_11_statements/sx.dart` | 1,065 | 0.81 |
| `tests/steps/l01_11_statements/returns.rs` | 675 | `test/steps/l01_11_statements/returns_test.dart` | 647 | 0.96 |
| `tests/steps/l01_12_declarations/fences.rs` | 945 | `test/steps/l01_12_declarations/fences_test.dart` | 1,010 | 1.07 |
| `tests/steps/l01_12_declarations/functions.rs` | 2,328 | `test/steps/l01_12_declarations/functions_test.dart` | 2,306 | 0.99 |
| `tests/steps/l01_12_declarations/ifs.rs` | 703 | `test/steps/l01_12_declarations/ifs_test.dart` | 824 | 1.17 |
| `tests/steps/l01_12_declarations/mod.rs` | 1,390 | `test/steps/l01_12_declarations/sx.dart` | 1,170 | 0.84 |
| `tests/steps/l01_12_declarations/pushes.rs` | 304 | `test/steps/l01_12_declarations/pushes_test.dart` | 432 | 1.42 |
| `tests/steps/l01_13_formatter/fences.rs` | 1,584 | `test/steps/l01_13_formatter/fences_test.dart` | 1,646 | 1.04 |
| `tests/steps/l01_13_formatter/layout.rs` | 3,440 | `test/steps/l01_13_formatter/layout_test.dart` | 3,688 | 1.07 |
| `tests/steps/l01_13_formatter/mod.rs` | 1,943 | `test/steps/l01_13_formatter/fmt.dart` | 1,389 | 0.71 |
| `tests/steps/l01_13_formatter/scaling.rs` | 1,811 | `test/steps/l01_13_formatter/scaling_test.dart` | 2,022 | 1.12 |
| `tests/steps/l01_14_name_resolution/fences.rs` | 1,432 | `test/steps/l01_14_name_resolution/fences_test.dart` | 1,777 | 1.24 |
| `tests/steps/l01_14_name_resolution/mod.rs` | 2,673 | `test/steps/l01_14_name_resolution/res.dart` | 2,212 | 0.83 |
| `tests/steps/l01_14_name_resolution/order.rs` | 2,255 | `test/steps/l01_14_name_resolution/order_test.dart` | 2,203 | 0.98 |
| `tests/steps/l01_14_name_resolution/scaling.rs` | 2,201 | `test/steps/l01_14_name_resolution/scaling_test.dart` | 2,271 | 1.03 |
| `tests/steps/l01_14_name_resolution/scopes.rs` | 3,843 | `test/steps/l01_14_name_resolution/scopes_test.dart` | 3,515 | 0.91 |
| `tests/steps/l01_15_kernel_terms/evidence.rs` | 3,397 | `test/steps/l01_15_kernel_terms/evidence_test.dart` | 2,381 | 0.70 |
| `tests/steps/l01_15_kernel_terms/layout.rs` | 4,320 | `test/steps/l01_15_kernel_terms/layout_test.dart` | 3,770 | 0.87 |
| `tests/steps/l01_15_kernel_terms/mod.rs` | 288 | | | |
| `tests/steps/l01_15_kernel_terms/notation.rs` | 5,524 | `test/steps/l01_15_kernel_terms/notation_test.dart` | 4,233 | 0.77 |
| `tests/steps/l01_15_kernel_terms/scaling.rs` | 2,895 | `test/steps/l01_15_kernel_terms/scaling_test.dart` | 2,032 | 0.70 |
| `tests/steps/l01_16_elaboration/calls.rs` | 2,863 | `test/steps/l01_16_elaboration/calls_test.dart` | 2,782 | 0.97 |
| `tests/steps/l01_16_elaboration/errors.rs` | 4,274 | `test/steps/l01_16_elaboration/errors_test.dart` | 4,350 | 1.02 |
| `tests/steps/l01_16_elaboration/mod.rs` | 2,130 | `test/steps/l01_16_elaboration/elab.dart` | 1,967 | 0.92 |
| `tests/steps/l01_16_elaboration/programs.rs` | 6,170 | `test/steps/l01_16_elaboration/programs_test.dart` | 5,480 | 0.89 |
| `tests/steps/l01_16_elaboration/scaling.rs` | 11,696 | `test/steps/l01_16_elaboration/scaling_test.dart` | 4,078 | 0.35 |
| `tests/steps/l01_17_value_representation/atoms.rs` | 3,143 | `test/steps/l01_17_value_representation/atoms_test.dart` | 3,072 | 0.98 |
| `tests/steps/l01_17_value_representation/equality.rs` | 1,900 | `test/steps/l01_17_value_representation/equality_test.dart` | 1,983 | 1.04 |
| `tests/steps/l01_17_value_representation/mod.rs` | 439 | `test/steps/l01_17_value_representation/scaling_test.dart` | 1,580 | 3.60 |
| `tests/steps/l01_17_value_representation/numbers.rs` | 3,876 | `test/steps/l01_17_value_representation/numbers_test.dart` | 3,709 | 0.96 |
| `tests/steps/l01_17_value_representation/order.rs` | 2,591 | `test/steps/l01_17_value_representation/order_test.dart` | 2,227 | 0.86 |
| `tests/steps/l01_18_scalar_interpreter/casts.rs` | 3,013 | `test/steps/l01_18_scalar_interpreter/casts_test.dart` | 2,844 | 0.94 |
| `tests/steps/l01_18_scalar_interpreter/failures.rs` | 2,066 | `test/steps/l01_18_scalar_interpreter/failures_test.dart` | 1,960 | 0.95 |
| `tests/steps/l01_18_scalar_interpreter/floats.rs` | 2,591 | `test/steps/l01_18_scalar_interpreter/floats_test.dart` | 2,647 | 1.02 |
| `tests/steps/l01_18_scalar_interpreter/mod.rs` | 485 | `test/steps/l01_18_scalar_interpreter/scalar.dart` | 416 | 0.86 |
| `tests/steps/l01_18_scalar_interpreter/scaling.rs` | 1,076 | `test/steps/l01_18_scalar_interpreter/scaling_test.dart` | 1,811 | 1.68 |
| `tests/steps/l01_18_scalar_interpreter/words.rs` | 1,770 | `test/steps/l01_18_scalar_interpreter/words_test.dart` | 1,695 | 0.96 |
| `tests/steps/l01_19_whole_file_ports/files.rs` | 3,361 | `test/steps/l01_19_whole_file_ports/files_test.dart` | 2,887 | 0.86 |
| `tests/steps/l01_19_whole_file_ports/lines.rs` | 2,653 | `test/steps/l01_19_whole_file_ports/lines_test.dart` | 2,678 | 1.01 |
| `tests/steps/l01_19_whole_file_ports/mod.rs` | 1,734 | `test/steps/l01_19_whole_file_ports/ports.dart`<br>`test/steps/l01_19_whole_file_ports/scaling_test.dart` | 3,425 | 1.98 |
| `tests/steps/l01_19_whole_file_ports/replay.rs` | 2,909 | `test/steps/l01_19_whole_file_ports/replay_test.dart` | 2,894 | 0.99 |
| `tests/steps/l01_19_whole_file_ports/writes.rs` | 5,039 | `test/steps/l01_19_whole_file_ports/writes_test.dart` | 4,418 | 0.88 |
| `tests/steps/l01_20_provenance/kernel.rs` | 11,110 | `test/steps/l01_20_provenance/kernel_test.dart` | 9,215 | 0.83 |
| `tests/steps/l01_20_provenance/mod.rs` | 1,709 | `test/steps/l01_20_provenance/provenance.dart` | 1,367 | 0.80 |
| `tests/steps/l01_20_provenance/programs.rs` | 2,221 | `test/steps/l01_20_provenance/programs_test.dart` | 1,754 | 0.79 |
| `tests/steps/l01_20_provenance/scaling.rs` | 3,753 | `test/steps/l01_20_provenance/scaling_test.dart` | 3,251 | 0.87 |
| `tests/steps/l01_21_test_runner/command.rs` | 1,961 | `test/steps/l01_21_test_runner/command_test.dart` | 1,645 | 0.84 |
| `tests/steps/l01_21_test_runner/cones.rs` | 2,773 | `test/steps/l01_21_test_runner/cones_test.dart` | 2,093 | 0.75 |
| `tests/steps/l01_21_test_runner/fences.rs` | 1,302 | `test/steps/l01_21_test_runner/fences_test.dart` | 1,242 | 0.95 |
| `tests/steps/l01_21_test_runner/marks.rs` | 1,835 | `test/steps/l01_21_test_runner/marks_test.dart` | 1,776 | 0.97 |
| `tests/steps/l01_21_test_runner/mod.rs` | 672 | `test/steps/l01_21_test_runner/runner.dart` | 476 | 0.71 |
| `tests/steps/l01_21_test_runner/scaling.rs` | 1,563 | `test/steps/l01_21_test_runner/scaling_test.dart` | 984 | 0.63 |
| `tests/steps/l01_21_test_runner/tables.rs` | 3,635 | `test/steps/l01_21_test_runner/tables_test.dart` | 3,363 | 0.93 |
| `tests/steps/l01_21_test_runner/zed.rs` | 1,016 | `test/steps/l01_21_test_runner/zed_test.dart` | 937 | 0.92 |
| `tests/steps/l01_22_type_representation/forms.rs` | 5,811 | `test/steps/l01_22_type_representation/forms_test.dart` | 5,110 | 0.88 |
| `tests/steps/l01_22_type_representation/is.rs` | 1,718 | `test/steps/l01_22_type_representation/is_test.dart` | 1,487 | 0.87 |
| `tests/steps/l01_22_type_representation/laws.rs` | 7,730 | `test/steps/l01_22_type_representation/laws_test.dart` | 6,677 | 0.86 |
| `tests/steps/l01_22_type_representation/mod.rs` | 400 | | | |
| `tests/steps/l01_22_type_representation/scaling.rs` | 3,721 | `test/steps/l01_22_type_representation/scaling_test.dart` | 3,151 | 0.85 |
| `tests/steps/l01_23_subtyping/cases.rs` | 6,177 | `test/steps/l01_23_subtyping/cases_test.dart` | 6,341 | 1.03 |
| `tests/steps/l01_23_subtyping/mod.rs` | 549 | | | |
| `tests/steps/l01_23_subtyping/oracle.rs` | 8,422 | `test/steps/l01_23_subtyping/oracle_test.dart` | 7,814 | 0.93 |
| `tests/steps/l01_23_subtyping/rec.rs` | 13,224 | `test/steps/l01_23_subtyping/rec_test.dart` | 11,891 | 0.90 |
| `tests/steps/l01_23_subtyping/scaling.rs` | 14,517 | `test/steps/l01_23_subtyping/scaling_test.dart` | 10,834 | 0.75 |
| `tests/steps/l01_24_refinement_lattices/bounds.rs` | 6,164 | `test/steps/l01_24_refinement_lattices/bounds_test.dart` | 5,020 | 0.81 |
| `tests/steps/l01_24_refinement_lattices/cell.rs` | 6,341 | `test/steps/l01_24_refinement_lattices/cell_test.dart` | 5,524 | 0.87 |
| `tests/steps/l01_24_refinement_lattices/float.rs` | 3,442 | `test/steps/l01_24_refinement_lattices/float_test.dart` | 2,934 | 0.85 |
| `tests/steps/l01_24_refinement_lattices/loops.rs` | 6,177 | `test/steps/l01_24_refinement_lattices/loops_test.dart` | 4,593 | 0.74 |
| `tests/steps/l01_24_refinement_lattices/mod.rs` | 3,301 | `test/steps/l01_24_refinement_lattices/support.dart` | 2,732 | 0.83 |
| `tests/steps/l01_24_refinement_lattices/scaling.rs` | 9,294 | `test/steps/l01_24_refinement_lattices/scaling_test.dart` | 8,219 | 0.88 |
| `tests/steps/l01_25_preimage_catalog/entries.rs` | 10,757 | `test/steps/l01_25_preimage_catalog/entries_test.dart` | 9,633 | 0.90 |
| `tests/steps/l01_25_preimage_catalog/exact.rs` | 4,245 | `test/steps/l01_25_preimage_catalog/exact_test.dart` | 3,649 | 0.86 |
| `tests/steps/l01_25_preimage_catalog/mod.rs` | 5,544 | `test/steps/l01_25_preimage_catalog/support.dart` | 4,485 | 0.81 |
| `tests/steps/l01_25_preimage_catalog/random.rs` | 15,145 | `test/steps/l01_25_preimage_catalog/random_test.dart` | 13,296 | 0.88 |
| `tests/steps/l01_25_preimage_catalog/scaling.rs` | 8,378 | `test/steps/l01_25_preimage_catalog/scaling_test.dart` | 5,792 | 0.69 |
| `tests/steps/l01_25_preimage_catalog/stops.rs` | 4,452 | `test/steps/l01_25_preimage_catalog/stops_test.dart` | 3,946 | 0.89 |
| `tests/steps/l01_25_preimage_catalog/tonicity.rs` | 6,655 | `test/steps/l01_25_preimage_catalog/tonicity_test.dart` | 5,580 | 0.84 |
| `tests/steps/l01_26_type_resolution/adoption.rs` | 2,963 | `test/steps/l01_26_type_resolution/adoption_test.dart` | 2,828 | 0.95 |
| `tests/steps/l01_26_type_resolution/calls.rs` | 1,711 | `test/steps/l01_26_type_resolution/calls_test.dart` | 1,632 | 0.95 |
| `tests/steps/l01_26_type_resolution/fits.rs` | 2,412 | `test/steps/l01_26_type_resolution/fits_test.dart` | 2,289 | 0.95 |
| `tests/steps/l01_26_type_resolution/mod.rs` | 1,634 | `test/steps/l01_26_type_resolution/support.dart` | 1,145 | 0.70 |
| `tests/steps/l01_26_type_resolution/narrowing.rs` | 2,113 | `test/steps/l01_26_type_resolution/narrowing_test.dart` | 2,037 | 0.96 |
| `tests/steps/l01_26_type_resolution/random.rs` | 4,051 | `test/steps/l01_26_type_resolution/random_test.dart` | 3,388 | 0.84 |
| `tests/steps/l01_26_type_resolution/scaling.rs` | 4,188 | `test/steps/l01_26_type_resolution/scaling_test.dart` | 3,632 | 0.87 |
| `tests/steps/l01_26_type_resolution/signatures.rs` | 4,237 | `test/steps/l01_26_type_resolution/signatures_test.dart` | 3,895 | 0.92 |
| `tests/steps/l01_27_absences/families.rs` | 3,030 | `test/steps/l01_27_absences/families_test.dart` | 2,844 | 0.94 |
| `tests/steps/l01_27_absences/loose.rs` | 2,981 | `test/steps/l01_27_absences/loose_test.dart` | 2,848 | 0.96 |
| `tests/steps/l01_27_absences/mod.rs` | 578 | | | |
| `tests/steps/l01_28_staging/mix.rs` | 7,525 | | | |
| `tests/steps/l01_28_staging/mod.rs` | 1,692 | | | |
| `tests/steps/l01_28_staging/scaling.rs` | 4,036 | | | |
| `tests/steps/l01_28_staging/trick.rs` | 5,160 | | | |
| `tests/steps/l01_29_diagnostics/derivations.rs` | 7,910 | | | |
| `tests/steps/l01_29_diagnostics/layout.rs` | 1,974 | | | |
| `tests/steps/l01_29_diagnostics/mod.rs` | 975 | | | |
| `tests/steps/l01_29_diagnostics/repairs.rs` | 1,845 | | | |
| `tests/steps/l01_29_diagnostics/scaling.rs` | 3,066 | | | |
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
| `tests/steps/l01_33_lowering/errors.rs` | 3,655 | | | |
| `tests/steps/l01_33_lowering/forms.rs` | 8,027 | | | |
| `tests/steps/l01_33_lowering/mod.rs` | 2,007 | | | |
| `tests/steps/l01_33_lowering/ports.rs` | 4,565 | | | |
| `tests/steps/l01_33_lowering/scaling.rs` | 8,494 | | | |
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
| `tests/steps/l01_36_cranelift/mod.rs` | 1,238 | | | |
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
| `tests/steps/m0_05_widening_and_iteration/iteration.rs` | 11,596 | `test/steps/m0_05_widening_and_iteration/iteration_test.dart` | 9,671 | 0.83 |
| `tests/steps/m0_05_widening_and_iteration/mod.rs` | 6,193 | `test/steps/m0_05_widening_and_iteration/harness.dart` | 5,175 | 0.84 |
| `tests/steps/m0_05_widening_and_iteration/revision.rs` | 8,571 | `test/steps/m0_05_widening_and_iteration/revision_test.dart` | 7,157 | 0.84 |
| `tests/steps/m0_05_widening_and_iteration/scaling.rs` | 7,201 | `test/steps/m0_05_widening_and_iteration/scaling_test.dart` | 5,931 | 0.82 |
| `tests/steps/m0_05_widening_and_iteration/widening.rs` | 10,766 | `test/steps/m0_05_widening_and_iteration/widening_test.dart` | 9,570 | 0.89 |
| `tests/steps/m0_05_widening_and_iteration/wto.rs` | 7,970 | `test/steps/m0_05_widening_and_iteration/wto_test.dart` | 6,409 | 0.80 |
| `tests/steps/m0_06_cost_scalarization/mod.rs` | 10,778 | `test/steps/m0_06_cost_scalarization/cost_scalarization_test.dart` | 9,422 | 0.87 |
| `tests/steps/m0_07_canonicalization/alpha.rs` | 14,310 | `test/steps/m0_07_canonicalization/alpha_test.dart` | 10,487 | 0.73 |
| `tests/steps/m0_07_canonicalization/domains.rs` | 4,497 | `test/steps/m0_07_canonicalization/domains_test.dart` | 3,799 | 0.84 |
| `tests/steps/m0_07_canonicalization/mod.rs` | 1,083 | `test/steps/m0_07_canonicalization/harness.dart` | 793 | 0.73 |
| `tests/steps/m0_07_canonicalization/rules.rs` | 6,095 | `test/steps/m0_07_canonicalization/rules_test.dart` | 5,713 | 0.94 |
| `tests/steps/m0_07_canonicalization/scaling.rs` | 1,973 | `test/steps/m0_07_canonicalization/scaling_test.dart` | 1,525 | 0.77 |
| `tests/steps/m0_08_zed0_checklist/mod.rs` | 2,068 | `test/steps/m0_08_zed0_checklist/checklist_test.dart` | 1,785 | 0.86 |
| `tests/steps/m0_09_kernel_evaluator/mod.rs` | 26,083 | `test/steps/m0_09_kernel_evaluator/kernel_evaluator_test.dart` | 20,101 | 0.77 |
| `tests/steps/m0_09_kernel_evaluator/scaling.rs` | 11,009 | `test/steps/m0_09_kernel_evaluator/scaling_test.dart` | 9,446 | 0.86 |
| `tests/steps/m0_10_finite_model_harness/derived.rs` | 3,184 | `test/steps/m0_10_finite_model_harness/derived_test.dart` | 2,836 | 0.89 |
| `tests/steps/m0_10_finite_model_harness/laws_01_10.rs` | 24,999 | `test/steps/m0_10_finite_model_harness/laws_01_10_test.dart` | 20,586 | 0.82 |
| `tests/steps/m0_10_finite_model_harness/laws_11_20.rs` | 29,305 | `test/steps/m0_10_finite_model_harness/laws_11_20_test.dart` | 23,078 | 0.79 |
| `tests/steps/m0_10_finite_model_harness/laws_21_28.rs` | 26,308 | `test/steps/m0_10_finite_model_harness/laws_21_28_test.dart` | 21,866 | 0.83 |
| `tests/steps/m0_10_finite_model_harness/mod.rs` | 2,211 | `test/steps/m0_10_finite_model_harness/harness.dart` | 3,543 | 1.60 |
| `tests/steps/m0_10_finite_model_harness/recursion.rs` | 12,275 | `test/steps/m0_10_finite_model_harness/recursion_test.dart` | 10,312 | 0.84 |
| `tests/steps/m0_10_finite_model_harness/scaling.rs` | 9,925 | `test/steps/m0_10_finite_model_harness/scaling_test.dart` | 7,264 | 0.73 |
| `tests/steps/m0_10_finite_model_harness/smoke.rs` | 7,212 | `test/steps/m0_10_finite_model_harness/smoke_test.dart` | 5,993 | 0.83 |
| `tests/steps/m0_10_finite_model_harness/witnesses.rs` | 11,966 | `test/steps/m0_10_finite_model_harness/witnesses_test.dart` | 10,392 | 0.87 |
| `tests/steps/m0_11_prelude_axioms_and_limits/axioms.rs` | 11,459 | `test/steps/m0_11_prelude_axioms_and_limits/axioms_test.dart` | 8,469 | 0.74 |
| `tests/steps/m0_11_prelude_axioms_and_limits/limits.rs` | 3,277 | `test/steps/m0_11_prelude_axioms_and_limits/limits_test.dart` | 2,947 | 0.90 |
| `tests/steps/m0_11_prelude_axioms_and_limits/mod.rs` | 453 | | | |
| `tests/steps/m0_11_prelude_axioms_and_limits/signed_zero.rs` | 1,622 | `test/steps/m0_11_prelude_axioms_and_limits/signed_zero_test.dart` | 892 | 0.55 |
| `tests/steps/m0_11_prelude_axioms_and_limits/units.rs` | 3,566 | `test/steps/m0_11_prelude_axioms_and_limits/units_test.dart` | 2,803 | 0.79 |
| `tests/steps/main.rs` | 1,298 | | | |
| **all 295 Rust files** | **2,266,791** | | | |
| **the Rust files ported so far** | **1,654,828** | | **1,356,808** | **0.82** |
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
- **M0.2, M0.3 and M0.4.** M0.2 (operator precedence) and M0.3 (the normative grammar) are
  written in DESIGN.md alone, and M0.4 (the corpus) is Zed programs with their inputs and
  expected outputs; none of the three has Rust code to port. M0.4's reference programs, which
  compute each expected output, were written in Python and rewritten in Dart
  (`zed/corpus/ref/*.dart`) by the separate task that removed all Python, after M0.10 was
  ported, not as a step of this port, so no time or errors are recorded for them here. All
  31 match their expected outputs (`refcheck.sh`, exit 0).
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
- **M0.10, finite-model harness.** 90 step tests and 13 support tests, all passing. Three
  compile errors in two runs, all from Dart's rules on constants and patterns: a record
  pattern cannot assign to list elements (a swap), a `const` record cannot be destructured,
  and `Float` has no `const` constructor. One test needed a fix to its matcher (`contains` on
  a list of records) and one an explicit `<int>[]`. The Rust step's 4 borrow errors, from
  mutating the model while iterating it and moving values into closures, have no counterpart.
  The relation helpers that laws 21–28 share with law 15 sit in `harness.dart` rather than in
  the law-15 file, which is why `harness.dart` is 1.6 times its Rust file and
  `laws_11_20_test.dart` 0.79. The Rust scaling file compares the provenance facts of a
  demanded entry with those of rounds; the Dart test compares values only until provenance is
  ported with step L1.20, so its size ratio of 0.67 is low for that reason. No test needed a
  thread with a large stack.
- **M0.5, widening and iteration.** 34 step tests and 18 unit tests for the store's
  interval, lattice, order and revision modules, all passing. Six compile errors in three
  runs: three from using a `case` pattern as a boolean expression, which Dart allows only in
  `if` and `switch`; a type bound (`Comparable`) that `FiniteSet` could not meet; an
  `Equations<Object?>` that broke the bound of `Equations`; and a nullable `fold`. The code
  was written in the shape the Rust version reached after its performance pass (S3, S9,
  S13): phase 1 skips a component none of whose inputs changed, the weak topological order
  comes from one traversal, and each cell takes the landmarks of its loop. Two Rust flaws
  were fixed rather than copied: a congruence join whose modulus passes 63 bits now gives
  every integer instead of overflowing, and `pow` rounds its roots in the right direction.
  One mistake was mine and not the language's: the test helper that measures the nesting
  depth recursed twice per level, 2^48 calls at depth 48, and the test hung until it was
  rewritten as a loop. The tool time includes the two hung runs.
- **M0.6, cost scalarization.** 8 step tests and 4 unit tests, all passing. One compile
  error: the same list swap through a record pattern as in M0.10. Dart's `int` is signed, so
  the costs saturate at 2^63 - 1 where Rust's `u64` saturated at 2^64 - 1; no test reaches
  either. A region is a record, which gives its equality with no code. The Rust frontier
  compared every pair of plans, O(P²), which COMPLEXITY.md kept "for a handful of plans".
  The Dart frontier sorts the vectors lexicographically, where every dominator comes before
  what it dominates, and compares each plan only with the frontier found so far:
  O(P log P + P·F) for F plans on the frontier. It is still quadratic when every plan is on
  the frontier; no known algorithm finds a Pareto frontier of more than three quantities in
  O(P log P), and the vector has 3·devices + 2. A new scaling test checks the case of a small
  frontier, and fails on the Rust algorithm (checked by putting it back). The Rust now uses
  the same algorithm, with the same test (COMPLEXITY.md F20).
- **M0.7, canonicalization.** 18 step tests and a BLAKE3 test, all passing, and the pinned
  address of `balance` matched on the first run. One compile error: `Float` has no const
  constructor. The Rust took BLAKE3 from a crate; the Dart package has no dependencies, so
  BLAKE3 is written out (about 120 lines) and checked against 26 hashes from the crate, at
  lengths that cross every block, chunk and subtree boundary. Dart's term classes have no
  structural equality, which Rust derived, so the definition's `==` needed a hand-written
  term comparison. The rename step's search was simpler in Dart: it renames in the first
  child that holds a written binder, where the Rust counted the written binders of each
  child first. Breaking the shadowing lookup of the one-pass normal form makes 5 of the 18
  tests fail.
- **M0.8, the Zed₀ checklist.** One test, which reads the checklist and corpus program 31
  from the spec copy in `zed/` and passed on its first run, in under a minute against the
  Rust's four. Dart's `split` and a regular expression stand in for Rust's iterator chain.
- **M0.11, prelude axioms and limits.** 11 tests, all passing on the first run, with no
  compile error; the pinned unit address matched. A law is a sealed class whose ten laws
  without an argument are one enum implementing it, so a switch over laws is checked
  exhaustive, and an axiom is a record. The constants of a law are kernel values, where the
  Rust needed a separate `Const` type because its values cannot be built in a constant; the
  table is a `final` list, since a `Float` cannot be `const`. Dart's `++` keeps a join of two
  strings unwritten, so the memory test also reads the text, which writes all 2^29
  characters out. Two of the three signed-zero tests read a program's values through the
  elaboration of step L1.16, and are ported with that step.
- **L1.1, source loading.** Dart has no Unicode normalization in its SDK, and the port adds
  no package, so the Dart code implements NFC itself (`lib/src/unicode.dart`, 150 lines) from
  tables that `tools/unicode_tables.py` writes from the Unicode 18.0.0 character database,
  the version of the Rust crate. It is checked against the whole of that version's
  `NormalizationTest.txt`, kept compressed with the tests, and on every code point. These
  three files have no Rust file to set beside them in the size table, since the Rust takes
  normalization from a crate. Dart's UTF-8 decoder reports no length for an invalid
  sequence, so `load` decodes the bytes itself, following the Unicode rule for the longest
  invalid prefix that Rust's `Utf8Error` follows. One compile error, a misnamed helper. The
  four tests, with a scaling test added, pass, and two negative controls (composing across
  a blocking mark; accepting an encoded surrogate) each fail one test.
- **L1.2, names.** The whole lexer is ported at once, since the name tests already need
  numbers, keywords and operators. The Rust lexer reads a `&str` by byte offset; Dart strings
  are UTF-16, so the Dart lexer reads the UTF-8 bytes (`lib/src/lex/text.dart`, which has no
  Rust file beside it) and every span stays a byte offset. Dart has no XID or script data, so
  `tools/unicode_tables.py` now also writes XID_Start, XID_Continue, Script and
  Script_Extensions, and the characters a quoted character shows as an escape, which Rust's
  `{:?}` takes from its standard library. The first tables were wrong: one map per file kept
  only the last property of a code point, so most letters lost XID_Start, and the script
  tests failed until each property was read on its own. Checked once against the Rust crates
  on all 1,112,064 code points: XID_Start and XID_Continue agree everywhere, and Script,
  Script_Extensions and the escapes differ only on the 13,007 code points new in Unicode 18.0
  and three Script_Extensions values 18.0 revised, since `unicode-script` 0.5.8 and Rust's
  standard library are at Unicode 17.0. Four compile errors in one run, all from one
  misescaped record field in a test. The two tests, with a scaling test added, pass; two
  negative controls (not reading the trailing `'`; refusing Latin with Han) each fail tests.
- **L1.3, integers.** The lexer of step L1.2 already reads integers, so only the tests are
  ported, with the malformed-number messages kept as expected output and a scaling test
  added. No compile errors. Two negative controls (taking every base of 10 or more as hex
  digits; keeping the `_` in the digits) each fail one test.
- **L1.4, floats and rationals.** Also tests only: the number lexer of step L1.2 reads both.
  No compile errors; one wrong token count in the new scaling test (`1..10` is three tokens).
  Two negative controls (reading `.` without a following digit; accepting `r` after any base)
  each fail tests.
- **L1.5, strings.** The string lexer of step L1.2 read holes by recursion: the scan for a
  hole's end called the string scan, and lexing a hole's tokens called the lexer, so a string
  nested in holes 2048 deep overflowed the Dart stack, which no flag can enlarge. The Rust test
  ran at 4000 on a 1 GiB thread. Both scans now keep the strings and holes they are in on a
  stack: 128,000 levels lex in 0.2 s. Three compile errors in one run, from a destructuring
  declaration in a test, rewritten as an `if case`. Two negative controls (stripping no
  indentation; never recording a hole's end) each fail tests.
- **L1.6, the other tokens.** Tests only, with the token renderer of the tests ported; its
  per-line rendering, which compared every token with every line, now walks the tokens once.
  A scaling test is added. No compile errors. Two negative controls (trying the shortest
  operator first; block comments that do not nest) each fail tests.
- **L1.7, fences.** The extractor, the fence helpers of the tests, and the tests. A fence and
  its marks are records; record equality compares lists by identity, so one test compares the
  mark lists themselves (a failed test, not a compile error). A label is read by one regular
  expression with a look-ahead. No compile errors. Two negative controls (missing an indented
  fence; reading `// layer L1x` as a label) each fail tests.
- **L1.8, parser.** The grammar reader, the packrat parser that runs the grammar, the tree
  printer, and the tests. The grammar is a Dart constant that `tools/bin/sync.dart` writes, as
  the Rust parser includes the copied file at compile time. Rules refer to each other as
  objects, and nodes hold their children, so there are no rule or node indices. Three compile
  errors in one run (a record typedef that names itself; two pattern assignments to fields).
  The recursive matcher overflowed the stack at 200 nested parentheses, so the matcher became
  an explicit stack of frames; 100,000 nested parentheses then parse in about 2 s. The memo is
  kept per token. Three negative controls (no memo, which ran past 240 s; no restore of the
  expected set after `!`; ignoring the ring) each fail tests.
- **L1.9, postfix chains.** The syntax tree of expressions, and the tests. Each node is built
  by a generator that yields the child nodes it needs, which an explicit stack runs, so the
  builder has the shape of the recursive one without its depth limit; 4,000 nested calls
  build. A string hole is built from its own tokens and tree by the same stack. A grouping
  widens its expression's span in place rather than copying it. The fences give 512 chains
  built and 170 of later forms, as in Rust. Two compile errors in two runs (a local `span`
  hiding the method; a `while` with a `case` pattern, which Dart allows only in `if`). Three
  negative controls (a duplicate name not caught; `?.` read as `.`; a grouping's span not
  widened) each fail tests.
- **L1.10** (lambdas, types, `else`, tuples): easy. The type, parameter and pattern builders
  are a mixin in `lib/src/ast/types.dart`, a part of `ast.dart`. To share one explicit stack
  with the expression builder, each generator now yields the generators of the parts it
  needs, and each result is left in one variable of the library; type nesting, lambda nesting
  and tuple nesting are each bounded by memory alone. All the Rust cases pass but two, which
  name a block: Rust at L1.10 named it with the step that builds it ("step L1.11"), and the
  Dart port names every form not built yet by its layer, as Rust does from L1.29 on, so both
  say "this form (Block) is built from layer L1" until L1.11 builds blocks. The fence count
  differs from Rust, and Rust's count is wrong: the Rust test counts every `Expr` node in the
  parser's node arena, which keeps 7 nodes of alternatives that later backtracked and holds
  none of the 14 `Expr` nodes inside string holes (1814 = 1807 + 7, measured with a temporary
  Rust test). The Dart test counts the expressions in the trees, holes included: 1512 built
  and 309 of later forms, 1821 in all. No compile errors. Four negative controls (an `else`
  pattern dropped; `is not` read as `is`; `->?` read as `->`; a tuple parameter built) each
  fail tests.
- **L1.11** (statements and blocks): easy. The block and statement builders are a second
  mixin, in `lib/src/ast/stmts.dart`; a target `_` is a null name rather than a separate
  class. The port follows the block rules Rust has from L1.29 on, not those of Rust at L1.11:
  statements may come in any order, so the export need not be last, and a second export is
  reported with a note at the first ("a block exports once; the block's first export at byte
  7"). The cases differ from Rust at L1.11 accordingly (one case reordered, the message
  text), and the function and push statements, which Rust at L1.11 named with "step L1.12",
  name their layer. The fence count is 1 block built and none of later forms, as in Rust. Two
  compile errors in two runs, both in one test pattern (`final` inside a declaration pattern;
  a list pattern of `Bind` matched against a `List<Stmt>`, which an irrefutable pattern
  cannot narrow). Three negative controls (a second export accepted; `_` bound as a name;
  `return a, b` keeping only `a`) each fail tests.
- **L1.12** (functions, test tables, ports, pushes, `if`/`else`, units): easy. A function
  is the class `FunctionDef`, since `Function` is a type name Dart reserves; an output port
  keeps its span, as in Rust from L1.29 on. The parameter list a lambda and a function share
  is one generator. All the Rust cases pass, the block message in the form Rust has from L1.29
  on (see L1.11). The fences give 23 units built and 113 of later forms, as in Rust. Two
  compile errors in one run (the reserved name `Function`; a `void` result used inside a
  record). The first scaling test of a table of n cases in each of n functions grew as n²
  in the size of its own text and was killed at the time limit; it now builds n functions
  and one table of n cases. Four negative controls (an equation read as a block; a second
  `test` table dropped; an `if`'s branches swapped; a top-level `return` accepted) each fail
  tests.
- **L1.13** (the source formatter and `zedc fmt`): easy. The formatter is ported from the
  Rust at its final shape, in which comments sit in an ordered map and text is a tree of
  parts, so both of the Rust's later scaling fixes are in from the start; the map is Dart's
  `SplayTreeMap`. It runs on one explicit stack of generators, as the builder does, so it
  needs no large thread stack, where the Rust scaling test raises the stack to 256 MiB. A
  source that fails to load is reported at its line and column, as for the other errors;
  the Rust prints the load error without a position, though its documentation promises one.
  The block's export is stored last, and the L1.11 case that expected written order changed
  with it, as in Rust. One compile error in one run (a pattern after `&&` in an `if`, which
  Dart parses as a boolean). All the Rust cases pass on the first run. Four negative
  controls (the export left in place; a comment on the next line taken as trailing; one
  newline counted as a blank line; equality made left-associative) fail tests, but the
  fourth only after adding the case `(a == b) == c`, which neither port tested. The step's
  time includes checking M0.2 to M0.4, about a minute.
- **L1.14** (name resolution): easy. Ported from the Rust at its final shape, in which a name
  is found in `O(1)` however deep the scopes nest and an overload's parameter types sit in a
  set. A use holds the binders themselves, not their indices into the unit's list, and an
  `else` pattern's binders are a list, not a range of indices; the binder list a use holds
  is shared, since a scope binds all its names before any is read. The prelude's words are a
  map, where the Rust searches a list. The walk runs on one explicit stack of generators, so
  the scaling test needs no large thread stack (the Rust raises it to 4 GiB). Errors are
  thrown as one exception holding the list. No compile errors; all the Rust cases pass on
  the first run. Five negative controls (every function of a name taken as an overload; a
  closed scope's names left visible; a `test` case read in its function's scope; a later
  layer's word accepted; the overload signatures kept in a list) fail tests, but the last,
  which makes declaring k overloads cost k², passed at first: the scaling test timed the
  lexer and parser too, which hid the resolver's growth. Both scaling tests now build each
  size's statements once and time the resolver alone, and the list version then runs 39 to
  49 times as long at eight times the size, over the limit of 24.
- **L1.15** (printer of kernel terms). Easy. The evidence record was already on `fold` and
  `fix`, and the canonical serializer already wrote it in name order, so the step was the
  printer and its tests. The printer is a part of the term library, so `Term.toString` can
  use it; each subterm's layout is built the first time a walk reaches it, and every walk
  (one-line text, the fit test, the broken layout) runs on an explicit stack, so the
  16,000-deep scaling test needs no large thread stack (the Rust raises it to 512 MiB). Two
  compile errors, both syntax the formatter rejected: `x case P ? a : b` is not an
  expression in Dart, and there is no `while`-`case` loop. All 20 tests pass on the first
  run. Five negative controls (evidence written in build order; a fit test that always
  fits; a call's head copied as text into each enclosing call; a fit test that reads the
  whole text; no space inside one-line braces) each fail tests; the head copy and the
  whole-text fit test fail the scaling test, the second at 65 to 74 times as long at eight
  times the size, over the limit of 24.
- **L1.16** (elaboration to kernel terms). Moderate. The first version recursed, and blocks
  nested more than about 1,000 deep overflowed the stack; it was rewritten as generators on
  an explicit stack, like the resolver. The Rust stops a term with `?` on an `Option`; the
  Dart stops one by throwing, and the stack driver catches the throw and leaves it as the
  stopped step's result. A function's uses are found by binary search among its scope's
  statements, so a use is read once per scope it belongs to, not once per scope around it.
  The L1.16 Rust elaborated a default again at each call that left its parameter out, so a
  chain of defaults that call functions with defaults took time doubling with each function
  (440 ms at 16); each default's term is now made once and shared, which keeps every printed
  term as the Rust prints it (the Rust fixed this later, in F2, by making each default a
  definition). No compile errors. Six negative controls each fail tests: a scan for the
  next ready statement (31 to 37 times as long at eight times the size, over the limit of
  24, once the test's size was raised from 1,000 to 4,000, where the scan's cost shows), a
  scan of every use at each scope (47 to 54 times), a scan of the defaults' uses from the
  start of the unit (47 to 55 times), each default elaborated again (up to 9,805 times),
  ties broken by the greatest index, and errors of one span sorted in reverse order or not
  sorted by start. The last two needed a new test, of two errors on one span.
- **L1.17** (value representation). Easy. The kernel's unbounded integers, rationals, natural
  order and IEEE `==` were already in the Dart kernel, ported from the later Rust; the step
  added about 40 lines to the elaborator, for big integer and rational literals, atoms with
  payloads and patterns that match fields by name. The step's tests found three faults in
  the earlier kernel port that no test had reached: a rational had no `toString`, so it
  printed as `Instance of 'Rat'`; it had no `hashCode`, so two equal rationals fell in
  different buckets of a hash set; and a pattern looked up each named field with a linear
  scan, so matching n fields took time of order n² (54 to 57 times as long at eight times
  the size), where the Rust binary-searches the sorted fields. The L1.17 Rust test expects
  a NaN to print as `NaN`; the Rust changed this to `nan` at L1.18, and the Dart test takes
  the later form, since the Dart kernel prints that way. The error-order test of L1.16 used
  rational literals, which stop being errors here, and now uses `is` tests. No compile
  errors. Three negative controls each fail tests: a linear scan for each field of a
  pattern (57 times), a linear check of a pattern's fields for repeats (45 to 49 times),
  and a rational without `hashCode`.
- **L1.18** (scalar interpreter). Easy. The words, casts, float printing and per-region
  arrows were already in the Dart kernel; the step added a 30-line `prelude` that binds ten
  words to their primitives, and the L1.16 tests now run under it in place of a stand-in
  `String`. All 25 new tests passed on their first run. The scaling test found one fault:
  merging failures built a new set from every member at each `+`, so a chain of n failing
  operands took time of order n² (79 times as long at eight times the size). The Rust
  merge now extends the largest `#errs` set among its operands, a persistent map that shares
  all but O(log n) nodes per insert. One analyzer warning (an unused import), no compile
  errors. The negative control is the earlier merge, caught at 79 times as long. The Rust
  `merge_failures` made the same copy and had no test that reached it; it now extends the
  largest set too, with a scaling test (COMPLEXITY.md K18). In the Rust the same chain
  written as source is still of order n², in the type checker, which the Dart has not yet
  reached (F21).
- **L1.19** (whole-file ports). Easy. `zedc run` and `zedc replay`, the line and file ports,
  the write commit and the record format went into one 500-line `run.dart`; all 19 tests
  passed on their first run. The 8 compile errors, in one run, were name clashes: the
  lexer's `Atom` and `Str` against the kernel's, and a local `load` that hid the library
  function. `show` clauses and a prefixed import fixed them. Reading stdin is asynchronous
  in Dart, so `command` returns a `Future<int>`; the Rust reads it with one blocking call.
  A new scaling test covers `cat` of n lines, a record of n reads, and a wave reading n
  paths. The negative control, a line splitter that copies the rest of the input at each
  line, did not finish within 400 s.
- **L1.20** (provenance). Moderate. The trace is a `part` of `eval.dart`, so its stacks and
  constructors stay private to the evaluator. The call sites and keypath are immutable linked
  lists that every fact address shares, in place of the Rust persistent vectors. Each region
  form names the call site and argument facts before it calls an operand, and a stopped
  attempt at a definedness entry truncates the facts and restores the trace from marks taken
  when the attempt began. All 20 tests passed on their first full run after one matcher fix
  (`contains` on a list of lists compares by identity). The 3 compile errors, in 2 runs: a
  keypath comparison used for a list of positions, and a misnamed `Str` field. The M0.10
  scaling test now also compares the facts of a demanded entry with those of rounds, as the
  Rust test does. Two negative controls fail as they should: keeping the reader's keypath in
  a demanded entry makes the Pull and Rounds facts differ, and keeping the facts of a stopped
  attempt repeats fact addresses.
- **L1.21** (the test runner). Easy. The port includes the later fix that runs each row under
  only the definitions it reaches (`Cones`), so `Unit.close` closes over a term's cone and a
  `Program` closes `main` once, in a `late final` field. A rejected unit is a `Diagnostics`
  exception from `compile`, and a failing row a private exception caught where the row's
  outcome is made. The 5 compile errors, in 1 run, all came from one cause: the runner's
  function `test` clashed with `test` of package:test in every test file that imports both,
  so it is `testUnit`. The first full run overflowed the stack in two earlier scaling tests:
  the free-name walk recursed once per nested term, and the L1.18 and L1.19 terms nest
  thousands deep. The walk now keeps its own stack. Two negative controls fail as they should:
  closing a row over every definition fails the cone test, and makes 800 functions take 38 to
  41 times as long as 100 against the limit of 24.
- **L1.22** (types as sets of values, and `is`). Hard: the largest kernel step so far. A type
  is a record of parts, one per universe; the tuple and morphism parts are reduced ordered
  decision diagrams, hash-consed in one static table, with a part kept as an expression when
  the diagram would grow past the sizes of its operands. The digests copy the Rust's exactly,
  with unsigned 64-bit arithmetic done by hand, so the atom order and every printed form
  matched on the first run. Emptiness (`empty.rs`, labeled L1.23 in the Rust) came with it,
  since the forms test asks for `equiv` and `isEmpty`. The 19 compile errors, in 5 runs, were
  of three kinds: a node table typed too narrowly for its casts, private types in a public
  signature (`_Lits` and its kin are now public, and not exported), and folds whose type
  Dart could not infer from a nullable seed. The step's scaling test found that a union of n
  tuple types in `is` took O(n²) to elaborate, in the Dart and in the Rust, which also had
  a quadratic union in its type checker; all three are fixed (COMPLEXITY.md F22). Two negative
  controls fail as they should: the one-at-a-time union, and the elaborator with its old fold
  put back (29 to 48 times as long for 8 times the size, against 24).
- **L1.23** (subtyping and recursive types). Medium. A recursive type is a `Type` whose parts
  are a `late final` field, filled from a closure the first time they are read, so a group of
  definitions ties its knot with no table of indices. The three definition-time checks
  (regular, contractive, monotone) give the Rust's rejection messages exactly. The step's
  scaling tests overflowed the Dart stack, which is fixed at about 45,500 frames: no VM flag
  changes it, `ulimit -s` does not, and `Isolate.run` has the same limit, where the Rust runs
  its deep cases on threads with 256 to 512 MB of stack. The diagram union, complement, atom
  visit and path walk are now loops over their own stacks, and the emptiness search is a set of
  `sync*` generators calling each other with `yield*`, which the VM keeps on the heap (measured:
  depth 1,000,000 in 245 ms, and the cost per value yielded does not grow with depth); the
  tests then pass at the Rust's sizes. The scaling test that lists the values of a type past a
  cap waits for L1.28, which the listing belongs to. The 6 compile errors, in 3 runs, were 2 in
  `rec.dart` as it was written, 2 from a null-aware element in a cascade, and 2 from a test
  still calling the old `paths`. Four negative controls fail as they should: a type named when
  made (ratios 32 to 77), the cycle search run once per definition (61 to 65), a deep walk of
  each tuple made (the nested-tuple test fails), and the search for cycles in Rust.
- **L1.24** (refinement lattices). Easy. Symbolic affine bounds, float classes and cells
  with their premises; no compile errors, and the 26 tests passed on the first run. The
  bounds of an element are grouped by their terms in a `SplayTreeMap`, so the bounds sharing
  a bound's terms are one lookup, where the Rust reads a range of a `BTreeSet`. A premise set
  is a sealed tree of unions shared by reference, which the Rust holds in `Arc` nodes compared
  with `ptr_eq`. Fact addresses gained public constructors and an order, which the Rust
  derives. An affine bound is evaluated exactly, in `BigInt` past 64 bits, where the Rust
  gives up past `i128`. The step's interval tests (cap, join, the forward images and their
  scaling) were not in the Dart M0.5 tests, and are ported here with the step.
- **L1.25** (scalar preimage catalog). Medium. The catalog, the `@exact` search and the
  witness search are ported whole; the linear-relation stage that the Rust `preimage.rs` also
  holds waits for L1.38, so the size ratio of that file (0.68) compares the catalog with the
  catalog and the stage together. Of `stage.rs` only the test of whether a term ends is
  ported; the rest is L1.28. The 41 tests pass, with four expected results that differ from
  the Rust's, each a case the Rust makes exact or narrower in its linear stage: a sum of two
  calls (`x [0..=50]; necessary` for the Rust's `x [50..=50]; exact`), a sum past `2^63`
  (exact only after enumeration), `x * 7 mod 10 == 3` (`[2..=29]` for the hull `[9..=29]`) and
  the chain `x1 = i + i; …` (`i [-50..=50]; necessary` for `i [0..=50]; exact`). Each holds
  every point that meets the demand, which the tests check against every point of a window,
  and each changes back when the Dart port reaches L1.38. The Rust step L1.38 is complete;
  the port of its test of the linear translation's scaling comes with the Dart L1.38 too. Terms are keyed by identity (`Map.identity()`) where the Rust
  keys them by address; `i128` end arithmetic is `BigInt`, and a 64-bit congruence modulus
  is checked against `int` overflow by hand. The 9 compile errors, in 3 runs, were 2 from a
  `while (t case Var(...))` loop, which Dart does not have, 1 from a test-local name clashing
  with an exported one, and 6 from a `case` pattern used as a lambda's body. The formatter
  crashed with an internal error on a `switch` expression followed by `+` in an
  expression-bodied `toString`; assigning the switch to a local first works around it.
- **L1.26** (type resolution). Hard: the largest step so far, 109 KB of Rust checker. The
  checker, its types (`check/ty.rs`) and the binder tables it shares with elaboration are
  ported whole, and with them the parts of later steps the Rust checker already holds: the
  call checks and arrows of L1.27, the error derivations of L1.29, the fits of L1.37, the
  linear facts the L1.38 checker reads, and the F-item and replacement changes made in the
  performance pass. Elaboration was changed to take the checker's adoptions and fits, and
  eight test files of L1.16 to L1.19 were updated, each to the result the Rust test now
  expects (a bare literal adopts the other side's kind; a curried call names its argument).
  The 43 tests pass, and the random test gives the Rust's counts exactly: 366 functions,
  760 values, 0 failed. The Rust checker recurses on the native stack and keeps its undo log
  as an enum replayed in reverse; the Dart checker's passes are `sync*` generators stepped
  by one loop, so nesting depth costs heap and not stack, and the undo log is a list of
  closures. Of the 119
  compile errors, in 9 runs, 54 came from one record pattern written as an assignment
  target, which Dart does not allow outside a declaration (each later use of its five
  names was an error too), and most of the rest were cascades of the same kind: a
  `case` pattern used in a condition, `final` variables assigned on some paths only, and
  bodies that the analyzer could not prove return. One bug passed the analyzer: Rust's
  `of_mask(m).next().is_some_and(...)` is false when the mask holds only the bit for
  non-carrier values, and its port as `.first` threw on that case; a tuple compared with a
  parameter found it. The L1.18 test of a chain of `+` failures elaborated source text,
  where the Rust test builds the kernel term, and so timed the checker as well as the
  evaluator: 137 s of the Dart suite's 220 s. It now builds the term, and the suite takes
  129 s. The checker on that chain is O(n²) in both languages, COMPLEXITY.md F21, which is
  to be fixed at L1.27: 3.3 s at n = 1000 and 9.1 s at 2000 in Dart, 1.09 s and 4.30 s in
  the Rust release CLI.
- **L1.27** (absences). Easy: the checker ported at L1.26 already holds the step's logic, and
  the 11 tests passed on their first run, after one compile error (`Carrier.int` for
  `Carrier.integer`). With `withoutLoose` returning its operand unchanged, 8 of the 11 fail.
  Most of the time went to the two shared faults F21 and F32 and their controls. The fix of
  F21 is one line in each language, an identity of sets: `set − loose` is
  `(set − atoms) ∪ (set ∩ family)`, and only the right side avoids complementing every atom.
  A first fix of F32 keyed the Dart memo by identity, which broke the reuse of results
  within one unit that L1.23's tuple-difference test needs; the memo is now cleared at the
  start of each unit's check, in both languages.

## Dart

*In progress.* Steps ported: M0.1, M0.2, M0.3, M0.4, M0.9, M0.10, M0.5, M0.6, M0.7, M0.8, M0.11, L1.1, L1.2, L1.3, L1.4, L1.5, L1.6, L1.7, L1.8, L1.9, L1.10, L1.11, L1.12, L1.13, L1.14, L1.15, L1.16, L1.17, L1.18, L1.19, L1.20, L1.21, L1.22, L1.23, L1.24, L1.25, L1.26, L1.27. The port lives in `dart/` (Dart 3.13, `dart format -l 100`, `dart analyze`,
`dart test`). It carries its own expected-output files under `dart/test/steps/<step>/expected/` and does
not read the Rust tree.
The Unicode data, which the port first took from tables it generated from the Unicode 18.0.0
character database (`lib/src/unicode_tables.dart`, 156 KB, and its generator), now comes from
ICU4X 2.4.0 (package `icu4x`, which links a prebuilt ICU4X library through a build hook and is
also at Unicode 18). Before the change, a script compared the two on every one of the
1,114,112 code points, for the combining class, XID_Start, XID_Continue, Script,
Script_Extensions, the escapes of a quoted character, the NFC of each code point, and the NFC
and the NFC test of 200,000 random strings of letters, marks and Hangul jamo: they agree
everywhere. The case mappings agree except that the binding drops a leading U+FEFF, which
`lib/src/unicode.dart` restores (a new test; with the restoring loop removed it fails).
`unicode.dart` falls from 253 lines to 118, and the 662 Dart tests pass, the conformance test
of `NormalizationTest.txt` among them.

### What each language expresses more naturally

Notes made during the port, one row per case met. "Rust" or "Dart" names the language in
which the case was shorter, clearer or cheaper to run.

| case | better in | why |
|---|---|---|
| Shared subterms and graphs with back references | Dart | The garbage collector lets any number of owners hold the same object. The Rust needs `Arc` or `Rc` for sharing, clones to satisfy the borrow checker, and graphs stored as vectors addressed by index. |
| Deep recursion (16,000-deep terms, deeply nested blocks) | Rust | A Rust thread can be given a larger stack (`stack_size(1 << 29)` for the L1.15 printer, 4 GiB for the L1.14 resolver), so plain recursion works. A Dart isolate's stack cannot be raised, so each deep walk is rewritten on an explicit stack; `sync*` generators keep that rewrite short (L1.14, L1.15, L1.16). |
| A map whose keys must be read in order | equal | `BTreeMap` keeps the evidence record sorted. The first port used a Dart `Map`, which keeps insertion order, so the printer and the serializer each sorted the keys (L1.15); the evidence is now a `SplayTreeMap` of `dart:collection`, read in key order like the `BTreeMap`. |
| Looping while a value matches a pattern | Rust | `while let Term::Let(x, e, body) = t` walks a chain of `let`s. Dart has `if`-`case` but no `while`-`case`, so the loop becomes `for (; t is Let; t = t.body)` (L1.15). |
| Adding a behavior to a type from another file | Rust | `impl fmt::Display for Term` can live in the printer's module. In Dart `toString` must be declared in the class, so the printer is a `part` of the term library and the base class's `toString` calls it (L1.15). |
| Early exit from a fold | Rust | `try_fold` with `Option` and `?` stops as soon as the room runs out. Dart has no `?` for null; the printer reads its text as a lazy stream and returns from a `for` loop instead, which is as short but less direct (L1.15). |
| Building a value lazily, once | Dart | A `late final` field computes on first read. The Rust needs `OnceCell` or builds everything ahead (L1.15). |
| Lists built with conditions and loops | Dart | Collection `for` and `if` elements (`[a, if (c) b, for (x in xs) f(x)]`) replace Rust's `iter().map().collect()` chains and `push` sequences (L1.15 `fold` and `fix` arguments). |
| Matching on a closed set of variants | equal | Dart's sealed classes with object patterns in `switch` expressions are as short as Rust's `match` and are also checked for exhaustiveness. |
| Stopping a computation that met an error | Rust | `?` on an `Option` returns `None` from the function at once, and the caller's `?` passes it on. Dart's `?` exists only for null-aware access, so the elaborator stops by throwing, and each generator step that may stop is caught by the stack driver (L1.16). |
| Reading the keys of a sorted map in a range | Rust | `BTreeMap::range(a..)` reads the keys from a bound. A Dart `SplayTreeMap` has only `firstKeyAfter`, so a range is a loop calling it once per key, each call a new search from the root (L1.16). The port's own balanced tree, `PMap` in `lib/src/kernel/pmap.dart`, now has `from(key)`, which finds the first key in O(log n) and steps in order from there, and the uses of names are kept in it; that took 25 lines the Rust did not need. |
| Maps keyed by object identity | Dart | Any object is a map key, compared by identity unless it defines `==`, so the elaborator's tables are keyed by the binder or the parameter itself. The Rust keys them by index or by span, because its objects are borrowed or cloned and have no identity of their own (L1.16). |
| Sharing one computed value among many users | Dart | A default's term is made once and the same object placed in every call that leaves its parameter out. The Rust would need `Rc<Term>` throughout the term type to do the same; the L1.16 Rust copied the term instead (L1.16). |
| A list with an optional first element | Dart | `[?receiver, ...args]` adds the receiver only when it is not null. The Rust writes `receiver.into_iter().chain(args).collect()` (L1.16). |
| Keeping equality and hashing consistent | Rust | A Rust type used as a `HashMap` key must implement `Hash`, and `#[derive(PartialEq, Eq, Hash)]` writes both from one list of fields. A Dart class that overrides `==` and not `hashCode` compiles, and equal values land in different buckets of a hash set; the ported `Rat` did this until a test put two equal rationals in a set (L1.17). |
| Printing a value of a new type | Rust | `{}` on a type without `Display` is a compile error. Dart's `toString` falls back to `Instance of 'Rat'` without a warning, and the fault shows only when a test prints the value (L1.17). |
| Binary search of a sorted list | Rust | `slice::binary_search` is in the standard library. Dart's core `List` has none (`package:collection`, a package of the Dart team, has `binarySearch` and `lowerBound`), so `Atom.field` writes the loop out; the earlier port used `indexOf` instead, a linear scan (L1.17). |
| Unbounded integers | Dart | `BigInt` is in the core library, with `parse(radix:)`, `pow` and `isValidInt`. The Rust adds the `num-bigint` and `num-rational` crates and their dependencies (L1.17). |
| Extending a set that other values still hold | Dart | The Dart family is a persistent map, so adding one failure to an `#errs` set makes a new set that shares the old one's nodes, and the old value is unchanged. The Rust `BTreeSet` is mutable and owned, so the merge clones it whole; sharing would need a persistent-collection crate or `Rc` nodes. |
| Reading float bits | Rust | `f64::to_bits` and `from_bits` are methods on the type. Dart writes the float into a `ByteData` and reads it back as an integer. |
| Unicode case mapping | Rust | `str::to_uppercase` and `to_lowercase` are in the standard library, with the full Unicode mappings (`straße` to `STRASSE`) and the final-sigma rule. Dart's `toUpperCase` and `toLowerCase` use simple one-character mappings (`straße` gives `STRAßE`, and a final capital sigma becomes `σ`), and differ from the Unicode 18 mappings on 597 code points uppercase and 486 lowercase, so the Dart port takes case mapping, like normalization, identifiers and scripts, from ICU4X (package `icu4x`). Its Dart binding decodes the mapped text with `utf8.decode`, which drops a leading U+FEFF, so `lib/src/unicode.dart` maps the text after any leading U+FEFF characters and puts them back. |
| Reading all of stdin | Rust | `io::stdin().read_to_end` blocks and returns the bytes. Dart's `stdin` is a stream, so the command that reads it is `async` and returns a `Future`, and every caller awaits it (L1.19). |
| Telling apart the ways a file read fails | Rust | `io::Error::kind()` gives an enum, matched as `ErrorKind::NotFound`. Dart throws `PathNotFoundException` for a missing file and the general `FileSystemException` for the rest, so the cases are told apart by exception class and a `catch` order (L1.19). |
| Name clashes between imports | Rust | Rust names nothing it is not asked for (`use lex::Atom` is explicit). A Dart import brings in every public name of the library, so two libraries that both define `Atom` clash until one is narrowed with `show` or prefixed (L1.19). |
| A stack shared by many records | Dart | A persistent stack is a three-field class with a `final` tail, freed by the collector; each fact address holds a reference to it. The Rust uses a persistent vector from a crate (`imbl::Vector`) for the same sharing (L1.20). |
| Keying a node of a tree by identity | Rust | `node as *const Term as usize` keys a map by the node's address, and Rust never merges two equal values into one object. Dart has `Map.identity()`, but `const` makes equal constant terms one object, so a term is copied into fresh nodes before its nodes are numbered (L1.20). |
| A tree walk deeper than the call stack | Rust | The recursive free-name walk handles the terms of the L1.18 and L1.19 scaling tests, thousands of lets deep, on Rust's stack; the same recursion overflowed the Dart stack, so the Dart walk pushes terms and bind and release markers on a list (L1.21). |
| Naming a library function after its job | Rust | A Rust function `testing::test` sits beside the `#[test]` attribute without a clash. A Dart top-level `test` clashes with package:test's `test` in every test file that imports both, so the runner's function is `testUnit` (L1.21). |
| A value computed on its first use | Dart | `late final Term _main = …;` in the class body, or `cache[i] ??= f(i)`. The Rust needs a `OnceLock` or `OnceCell` field, its initialization in each constructor, and `get_or_init` at each use (L1.21). |
| Operator overloading on a type | Dart | One `operator |`, `&`, `-` and `~` per class. The Rust implements `BitOr`, `BitAnd`, `Sub` and `Not` for both `Type` and `&Type`, so that neither side must be cloned. Dart has no overloadable `!`, so the complement is `~` (L1.22). |
| A hash-consing table | Dart | One `static final` map on the class. The Rust keeps each table in a `thread_local!` `RefCell`, borrowed at every node made (L1.22). |
| Unsigned 64-bit arithmetic | Rust | `u64` wraps and compares unsigned by itself. Dart's `int` is signed: a digest shifts with `>>>`, and two digests compare by flipping the sign bit first (L1.22). |
| A closed hierarchy of node kinds | Dart | `sealed class Part`, with `Bdd` (`Leaf`, `Node`) and `Expr` under it, matched exhaustively. The Rust nests enums, `Part::Bdd(Bdd::Leaf(…))`, and each level is matched apart (L1.22). |
| A memo keyed by object identity | Dart | `Map.identity()`. The Rust keys its maps by `*const` raw pointers, which are valid keys only while the terms they point to are held elsewhere (L1.22). |
| Stopping at the first missing result | Rust | `?` on an `Option` returns early from the diagram's apply. Dart tests for null and returns at each call (L1.22). |
| A value defined in terms of itself | Dart | A `late final` field set from a closure on first read ties a recursive type's knot. The Rust holds the body in a cell filled after the node is shared (L1.23). |
| Deep recursion | Rust | A thread with a chosen stack size runs any recursion as written. A Dart isolate's stack is fixed at about 45,500 frames, so each recursion that a test drives deep is rewritten as a loop over its own stack (L1.23). |
| A recursive search that can be suspended | Dart | `sync*` generators calling each other with `yield*` keep the suspended calls on the heap, at a cost per step that does not grow with depth, so a mutual recursion keeps its shape. Stable Rust has no generators (L1.23). |
| A walk that asks its caller at each step | Dart | The walk is a generator of questions, and the caller answers in a field before reading the next; the same walk serves a plain callback and a suspended search. In Rust this is a hand-written iterator with its state in a struct (L1.23). |
| Deriving an order for a key | Rust | `#[derive(PartialOrd, Ord)]` orders a premise or a fact address by its fields. Dart writes `compareTo` by hand, with a helper comparing two lists in lexicographic order (L1.24). |
| Arithmetic that must not overflow | Dart | An affine bound evaluated at large symbol values falls back from `int` to `BigInt` and stays exact. The Rust evaluates in `i128` with checked operations and gives no answer when they overflow (L1.24). |
| Arithmetic just past 64 bits | Rust | `i128` holds every sum or product of two `i64` ends at machine speed. Dart has no 128-bit integer, so an interval end computed past `int` goes through `BigInt`, which allocates (L1.25). |
| Looping while a pattern matches | Rust | `while let Term::Var(x) = t { … }` binds and loops in one line. Dart has `if (t case …)` but no `while (t case …)`, so the loop tests `t is Var` and reads the field after (L1.25). |
| A boolean test written as a pattern | Rust | `matches!(s.bounds(), Some((a, b)) if a != b)` is one expression. In Dart `x case P when g` is allowed only in an `if`, so a lambda that returns it needs a `switch` expression with a second arm (L1.25). |
| An undo log | Dart | Each change to the checker's state pushes a closure that undoes it, and backtracking runs them in reverse. The Rust log is an enum with one variant per kind of change and a `match` that undoes each, which must be kept in step with every new kind of change (L1.26). |
| Deep recursion over a program | Dart | The checker's passes are `sync*` generators stepped by one loop, so a deeply nested body uses heap, not stack. The Rust checker recurses on the native stack, which bounds the nesting it can take (L1.26). |
| Mapping over an optional value | Rust | `iter.next().is_some_and(\|c\| …)` tests the first item, if any, in one expression. Dart has no `map` on a nullable value; `.first` throws on an empty iterable, and the port needs an `if (… case final c?)` statement (L1.26). |
| State kept between tests | Rust | The Rust test harness runs each test on its own thread, so a thread-local memo starts empty in each test. `dart test` runs all the tests of a file in one isolate, so a top-level memo carries over from test to test; this exposed F32, which a long-running Rust process would also have (L1.27). |
| Deep recursion in a test | Dart | A chain of 8,000 operators parses and checks with no setting. The Rust test runs on a thread with a 512 MB stack, since the parser and checker recurse once per operator (L1.27). |
| Quoting a string for display | Rust | `{name:?}` writes a quoted, escaped string at no cost. Dart needs a quoting function (the kernel's `quote`). |

### Changes per Dart file

Counted as for the Rust files: a file's creation is one change. The second number counts the
changes that fix a fault of COMPLEXITY.md; the first were at L1.27 (F21, F32).

| file | changes before the performance pass | changes during the performance pass |
|---|---:|---:|
| `lib/kernel.dart` | 3 | 0 |
| `lib/src/kernel/error.dart` | 1 | 0 |
| `lib/src/kernel/eval.dart` | 5 | 0 |
| `lib/src/kernel/exact.dart` | 1 | 0 |
| `lib/src/kernel/family.dart` | 1 | 0 |
| `lib/src/kernel/num.dart` | 2 | 0 |
| `lib/src/kernel/pmap.dart` | 3 | 0 |
| `lib/src/kernel/provenance.dart` | 2 | 0 |
| `lib/src/kernel/term.dart` | 3 | 0 |
| `lib/src/kernel/print.dart` | 4 | 0 |
| `lib/src/kernel/types.dart` | 4 | 0 |
| `lib/src/kernel/bdd.dart` | 4 | 0 |
| `lib/src/kernel/empty.dart` | 3 | 1 |
| `lib/src/kernel/rec.dart` | 1 | 0 |
| `lib/src/kernel/text.dart` | 1 | 0 |
| `lib/src/kernel/value.dart` | 3 | 0 |
| `lib/src/kernel/words.dart` | 1 | 0 |
| `test/kernel/error_test.dart` | 1 | 0 |
| `test/kernel/exact_test.dart` | 1 | 0 |
| `test/kernel/family_test.dart` | 1 | 0 |
| `test/kernel/text_test.dart` | 1 | 0 |
| `test/kernel/value_test.dart` | 1 | 0 |
| `test/support/kernel.dart` | 1 | 0 |
| `test/support/instances.dart` | 2 | 0 |
| `test/support/instances_test.dart` | 3 | 0 |
| `test/support/check.dart` | 1 | 0 |
| `test/support/check_test.dart` | 1 | 0 |
| `test/steps/m0_09_kernel_evaluator/kernel_evaluator_test.dart` | 1 | 0 |
| `test/steps/m0_09_kernel_evaluator/scaling_test.dart` | 1 | 0 |
| `test/steps/m0_10_finite_model_harness/harness.dart` | 2 | 0 |
| `test/steps/m0_10_finite_model_harness/derived_test.dart` | 1 | 0 |
| `test/steps/m0_10_finite_model_harness/smoke_test.dart` | 1 | 0 |
| `test/steps/m0_10_finite_model_harness/witnesses_test.dart` | 1 | 0 |
| `test/steps/m0_10_finite_model_harness/recursion_test.dart` | 2 | 0 |
| `test/steps/m0_10_finite_model_harness/laws_01_10_test.dart` | 2 | 0 |
| `test/steps/m0_10_finite_model_harness/laws_11_20_test.dart` | 1 | 0 |
| `test/steps/m0_10_finite_model_harness/laws_21_28_test.dart` | 1 | 0 |
| `test/steps/m0_10_finite_model_harness/scaling_test.dart` | 2 | 0 |
| `lib/store.dart` | 3 | 0 |
| `lib/src/store/interval.dart` | 2 | 0 |
| `lib/src/store/affine.dart` | 1 | 0 |
| `lib/src/store/cell.dart` | 1 | 0 |
| `lib/src/store/float.dart` | 1 | 0 |
| `lib/src/store/lattice.dart` | 2 | 0 |
| `lib/src/store/wto.dart` | 1 | 0 |
| `lib/src/store/iterate.dart` | 3 | 0 |
| `lib/src/store/revision.dart` | 2 | 0 |
| `lib/src/store/preimage.dart` | 1 | 0 |
| `lib/stage.dart` | 1 | 0 |
| `test/store/interval_test.dart` | 1 | 0 |
| `test/store/lattice_test.dart` | 1 | 0 |
| `test/store/wto_test.dart` | 1 | 0 |
| `test/store/revision_test.dart` | 2 | 0 |
| `test/steps/m0_05_widening_and_iteration/harness.dart` | 1 | 0 |
| `test/steps/m0_05_widening_and_iteration/widening_test.dart` | 1 | 0 |
| `test/steps/m0_05_widening_and_iteration/wto_test.dart` | 1 | 0 |
| `test/steps/m0_05_widening_and_iteration/iteration_test.dart` | 1 | 0 |
| `test/steps/m0_05_widening_and_iteration/revision_test.dart` | 2 | 0 |
| `test/steps/m0_05_widening_and_iteration/scaling_test.dart` | 2 | 0 |
| `lib/address.dart` | 1 | 0 |
| `lib/cost.dart` | 1 | 0 |
| `test/address_test.dart` | 1 | 0 |
| `test/cost_test.dart` | 1 | 0 |
| `test/steps/m0_06_cost_scalarization/cost_scalarization_test.dart` | 3 | 0 |
| `lib/src/canon/blake3.dart` | 1 | 0 |
| `lib/src/canon/binders.dart` | 2 | 0 |
| `lib/src/canon/domain.dart` | 1 | 0 |
| `lib/src/canon/serial.dart` | 2 | 0 |
| `lib/src/canon/canon.dart` | 2 | 0 |
| `lib/canon.dart` | 1 | 0 |
| `test/canon/blake3_test.dart` | 1 | 0 |
| `test/steps/m0_07_canonicalization/harness.dart` | 1 | 0 |
| `test/steps/m0_07_canonicalization/alpha_test.dart` | 2 | 0 |
| `test/steps/m0_07_canonicalization/domains_test.dart` | 1 | 0 |
| `test/steps/m0_07_canonicalization/rules_test.dart` | 1 | 0 |
| `test/steps/m0_07_canonicalization/scaling_test.dart` | 1 | 0 |
| `test/steps/m0_08_zed0_checklist/checklist_test.dart` | 1 | 0 |
| `lib/axioms.dart` | 1 | 0 |
| `test/steps/m0_11_prelude_axioms_and_limits/axioms_test.dart` | 1 | 0 |
| `test/steps/m0_11_prelude_axioms_and_limits/limits_test.dart` | 1 | 0 |
| `test/steps/m0_11_prelude_axioms_and_limits/signed_zero_test.dart` | 1 | 0 |
| `test/steps/m0_11_prelude_axioms_and_limits/units_test.dart` | 1 | 0 |
| `lib/source.dart` | 1 | 0 |
| `lib/src/unicode.dart` | 2 | 0 |
| `lib/src/unicode_tables.dart` | 2 | 0 |
| `test/unicode/unicode_test.dart` | 1 | 0 |
| `test/steps/l01_01_source_loading/accepted_test.dart` | 1 | 0 |
| `test/steps/l01_01_source_loading/places_test.dart` | 1 | 0 |
| `test/steps/l01_01_source_loading/rejected_test.dart` | 1 | 0 |
| `test/steps/l01_01_source_loading/scaling_test.dart` | 1 | 0 |
| `lib/lex.dart` | 4 | 0 |
| `lib/fence.dart` | 1 | 0 |
| `lib/parse.dart` | 6 | 3 |
| `lib/src/parse/grammar.dart` | 1 | 0 |
| `lib/src/parse/peg.dart` | 1 | 0 |
| `lib/ast.dart` | 7 | 0 |
| `lib/src/ast/types.dart` | 2 | 0 |
| `lib/src/ast/stmts.dart` | 3 | 0 |
| `lib/format.dart` | 2 | 0 |
| `bin/zedc.dart` | 4 | 0 |
| `lib/run.dart` | 5 | 0 |
| `lib/resolve.dart` | 3 | 0 |
| `lib/elab.dart` | 13 | 0 |
| `lib/interp.dart` | 1 | 0 |
| `lib/testing.dart` | 3 | 0 |
| `lib/src/lex/text.dart` | 1 | 0 |
| `lib/src/lex/comment.dart` | 1 | 0 |
| `lib/src/lex/name.dart` | 1 | 0 |
| `lib/src/lex/number.dart` | 1 | 0 |
| `lib/src/lex/punct.dart` | 1 | 0 |
| `lib/src/lex/string.dart` | 5 | 0 |
| `test/steps/l01_02_lexer_names/names_test.dart` | 1 | 0 |
| `test/steps/l01_02_lexer_names/scripts_test.dart` | 1 | 0 |
| `test/steps/l01_02_lexer_names/scaling_test.dart` | 1 | 0 |
| `test/steps/l01_03_lexer_integers/integers_test.dart` | 1 | 0 |
| `test/steps/l01_03_lexer_integers/scaling_test.dart` | 1 | 0 |
| `test/steps/l01_04_lexer_floats_and_rationals/floats_test.dart` | 1 | 0 |
| `test/steps/l01_04_lexer_floats_and_rationals/scaling_test.dart` | 2 | 0 |
| `test/steps/l01_05_lexer_strings/parts.dart` | 1 | 0 |
| `test/steps/l01_05_lexer_strings/strings_test.dart` | 1 | 0 |
| `test/steps/l01_05_lexer_strings/holes_test.dart` | 2 | 0 |
| `test/steps/l01_05_lexer_strings/scaling_test.dart` | 2 | 0 |
| `test/support/tokens.dart` | 3 | 0 |
| `test/steps/l01_06_lexer_tokens/program_test.dart` | 1 | 0 |
| `test/steps/l01_06_lexer_tokens/words_test.dart` | 1 | 0 |
| `test/steps/l01_06_lexer_tokens/scaling_test.dart` | 1 | 0 |
| `test/support/fences.dart` | 2 | 0 |
| `test/steps/l01_07_fences/extractor_test.dart` | 3 | 0 |
| `test/steps/l01_07_fences/copies_test.dart` | 1 | 0 |
| `test/steps/l01_07_fences/scaling_test.dart` | 1 | 0 |
| `test/support/trees.dart` | 1 | 0 |
| `test/steps/l01_08_parser/cases_test.dart` | 2 | 0 |
| `test/steps/l01_08_parser/errors_test.dart` | 1 | 0 |
| `test/steps/l01_08_parser/rings_test.dart` | 1 | 0 |
| `test/steps/l01_08_parser/scaling_test.dart` | 2 | 0 |
| `test/steps/l01_09_postfix_chains/ast.dart` | 1 | 0 |
| `test/steps/l01_09_postfix_chains/calls_test.dart` | 1 | 0 |
| `test/steps/l01_09_postfix_chains/chains_test.dart` | 1 | 0 |
| `test/steps/l01_09_postfix_chains/fences_test.dart` | 1 | 0 |
| `test/steps/l01_09_postfix_chains/scaling_test.dart` | 3 | 0 |
| `test/steps/l01_10_lambdas_types_else_tuples/elses_test.dart` | 2 | 0 |
| `test/steps/l01_10_lambdas_types_else_tuples/fences_test.dart` | 3 | 0 |
| `test/steps/l01_10_lambdas_types_else_tuples/lambdas_test.dart` | 2 | 0 |
| `test/steps/l01_10_lambdas_types_else_tuples/scaling_test.dart` | 2 | 0 |
| `test/steps/l01_10_lambdas_types_else_tuples/sx.dart` | 1 | 0 |
| `test/steps/l01_10_lambdas_types_else_tuples/tuples_test.dart` | 1 | 0 |
| `test/steps/l01_10_lambdas_types_else_tuples/types_test.dart` | 1 | 0 |
| `test/steps/l01_11_statements/blocks_test.dart` | 5 | 0 |
| `test/steps/l01_11_statements/fences_test.dart` | 1 | 0 |
| `test/steps/l01_11_statements/returns_test.dart` | 1 | 0 |
| `test/steps/l01_11_statements/scaling_test.dart` | 1 | 0 |
| `test/steps/l01_11_statements/sx.dart` | 1 | 0 |
| `test/steps/l01_12_declarations/fences_test.dart` | 1 | 0 |
| `test/steps/l01_12_declarations/functions_test.dart` | 1 | 0 |
| `test/steps/l01_12_declarations/ifs_test.dart` | 1 | 0 |
| `test/steps/l01_12_declarations/pushes_test.dart` | 1 | 0 |
| `test/steps/l01_12_declarations/scaling_test.dart` | 2 | 0 |
| `test/steps/l01_12_declarations/sx.dart` | 1 | 0 |
| `test/steps/l01_13_formatter/fmt.dart` | 1 | 0 |
| `test/steps/l01_13_formatter/layout_test.dart` | 2 | 0 |
| `test/steps/l01_13_formatter/fences_test.dart` | 1 | 0 |
| `test/steps/l01_13_formatter/scaling_test.dart` | 1 | 0 |
| `test/steps/l01_14_name_resolution/res.dart` | 2 | 0 |
| `test/steps/l01_14_name_resolution/order_test.dart` | 1 | 0 |
| `test/steps/l01_14_name_resolution/scopes_test.dart` | 1 | 0 |
| `test/steps/l01_14_name_resolution/fences_test.dart` | 2 | 0 |
| `test/steps/l01_14_name_resolution/scaling_test.dart` | 4 | 0 |
| `test/steps/l01_15_kernel_terms/notation_test.dart` | 2 | 0 |
| `test/steps/l01_15_kernel_terms/layout_test.dart` | 1 | 0 |
| `test/steps/l01_15_kernel_terms/evidence_test.dart` | 2 | 0 |
| `test/steps/l01_15_kernel_terms/scaling_test.dart` | 1 | 0 |
| `test/steps/l01_16_elaboration/elab.dart` | 2 | 0 |
| `test/steps/l01_16_elaboration/calls_test.dart` | 1 | 0 |
| `test/steps/l01_16_elaboration/errors_test.dart` | 5 | 0 |
| `test/steps/l01_16_elaboration/programs_test.dart` | 1 | 0 |
| `test/steps/l01_16_elaboration/scaling_test.dart` | 6 | 0 |
| `test/steps/l01_17_value_representation/atoms_test.dart` | 1 | 0 |
| `test/steps/l01_17_value_representation/equality_test.dart` | 1 | 0 |
| `test/steps/l01_17_value_representation/numbers_test.dart` | 1 | 0 |
| `test/steps/l01_17_value_representation/order_test.dart` | 3 | 0 |
| `test/steps/l01_17_value_representation/scaling_test.dart` | 1 | 0 |
| `test/steps/l01_18_scalar_interpreter/scalar.dart` | 1 | 0 |
| `test/steps/l01_18_scalar_interpreter/words_test.dart` | 1 | 0 |
| `test/steps/l01_18_scalar_interpreter/casts_test.dart` | 1 | 0 |
| `test/steps/l01_18_scalar_interpreter/failures_test.dart` | 1 | 0 |
| `test/steps/l01_18_scalar_interpreter/floats_test.dart` | 2 | 0 |
| `test/steps/l01_18_scalar_interpreter/scaling_test.dart` | 2 | 0 |
| `test/steps/l01_19_whole_file_ports/ports.dart` | 1 | 0 |
| `test/steps/l01_19_whole_file_ports/lines_test.dart` | 1 | 0 |
| `test/steps/l01_19_whole_file_ports/files_test.dart` | 1 | 0 |
| `test/steps/l01_19_whole_file_ports/replay_test.dart` | 1 | 0 |
| `test/steps/l01_19_whole_file_ports/writes_test.dart` | 1 | 0 |
| `test/steps/l01_19_whole_file_ports/scaling_test.dart` | 1 | 0 |
| `test/steps/l01_20_provenance/provenance.dart` | 1 | 0 |
| `test/steps/l01_20_provenance/kernel_test.dart` | 1 | 0 |
| `test/steps/l01_20_provenance/programs_test.dart` | 1 | 0 |
| `test/steps/l01_20_provenance/scaling_test.dart` | 1 | 0 |
| `test/steps/l01_21_test_runner/runner.dart` | 2 | 0 |
| `test/steps/l01_21_test_runner/command_test.dart` | 1 | 0 |
| `test/steps/l01_21_test_runner/cones_test.dart` | 1 | 0 |
| `test/steps/l01_21_test_runner/fences_test.dart` | 2 | 0 |
| `test/steps/l01_21_test_runner/marks_test.dart` | 1 | 0 |
| `test/steps/l01_21_test_runner/scaling_test.dart` | 2 | 0 |
| `test/steps/l01_21_test_runner/tables_test.dart` | 1 | 0 |
| `test/steps/l01_21_test_runner/zed_test.dart` | 2 | 0 |
| `test/steps/l01_22_type_representation/forms_test.dart` | 1 | 0 |
| `test/steps/l01_22_type_representation/laws_test.dart` | 2 | 0 |
| `test/steps/l01_22_type_representation/bdd_test.dart` | 2 | 0 |
| `test/steps/l01_22_type_representation/is_test.dart` | 1 | 0 |
| `test/steps/l01_22_type_representation/scaling_test.dart` | 1 | 0 |
| `test/steps/l01_23_subtyping/cases_test.dart` | 1 | 0 |
| `test/steps/l01_23_subtyping/oracle_test.dart` | 1 | 0 |
| `test/steps/l01_23_subtyping/rec_test.dart` | 1 | 0 |
| `test/steps/l01_23_subtyping/scaling_test.dart` | 1 | 0 |
| `test/steps/l01_24_refinement_lattices/support.dart` | 1 | 0 |
| `test/steps/l01_24_refinement_lattices/bounds_test.dart` | 1 | 0 |
| `test/steps/l01_24_refinement_lattices/cell_test.dart` | 1 | 0 |
| `test/steps/l01_24_refinement_lattices/float_test.dart` | 1 | 0 |
| `test/steps/l01_24_refinement_lattices/loops_test.dart` | 1 | 0 |
| `test/steps/l01_24_refinement_lattices/scaling_test.dart` | 1 | 0 |
| `lib/check.dart` | 2 | 1 |
| `lib/src/check/ty.dart` | 1 | 1 |
| `lib/src/tables.dart` | 1 | 0 |
| `test/steps/l01_26_type_resolution/support.dart` | 1 | 0 |
| `test/steps/l01_26_type_resolution/adoption_test.dart` | 1 | 0 |
| `test/steps/l01_26_type_resolution/calls_test.dart` | 1 | 0 |
| `test/steps/l01_26_type_resolution/fits_test.dart` | 1 | 0 |
| `test/steps/l01_26_type_resolution/narrowing_test.dart` | 1 | 0 |
| `test/steps/l01_26_type_resolution/random_test.dart` | 1 | 0 |
| `test/steps/l01_26_type_resolution/scaling_test.dart` | 1 | 0 |
| `test/steps/l01_26_type_resolution/signatures_test.dart` | 1 | 0 |
| `test/steps/l01_27_absences/families_test.dart` | 1 | 0 |
| `test/steps/l01_27_absences/loose_test.dart` | 1 | 0 |
| `test/steps/l01_27_absences/scaling_test.dart` | 0 | 1 |

`dart format` rewrote 8 files at the end of M0.9; reformatting is not counted as a change.
