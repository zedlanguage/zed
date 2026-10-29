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
- Done: **M0.5**, widening and iteration (`zedc::store`, `tests/steps/m0_05_widening_and_iteration/`,
  prelude units in `zed/prelude/`); values in DESIGN.md M0.5.
- Done: **M0.6**, the cost scalarization (`zedc::cost`, `zedc::address`, prelude unit `cost`).
- Done: **M0.7**, the canonicalizer (`zedc::canon`); values in DESIGN.md M0.7.
- Done: **M0.8**, the Zed₀ checklist (`zed/compiler/ZED0.md`): L6 completes Zed₀, so row S
  follows L6.
- Done: **M0.11**, the built-in operator axioms (`zedc::axioms`, prelude unit `axioms`), unit
  addresses (`zedc::canon::unit_address`, prelude unit `unit`), and the minimum resource
  limits (`zed_kernel::eval::MIN_*`, prelude unit `limits`). M0 is complete.
- Done: **L1.1**, source loading (`zedc::source`): UTF-8 and NFC checked, rejected with a
  span, line endings normalized.
- Done: **L1.2**, names and the wildcard (`zedc::lex`), with the one-script rule.
- Next: L1.3.

## Test baseline

Last full run: `cargo test --workspace` gave 241 passed and 0 failed (21 unit tests of
`zed-kernel`, 10 of `zed-tests`, 22 of `zedc`, 188 step tests: 6 in `l01_01_source_loading`, 8 in `l01_02_lexer_names`, 3 in `m0_01_scaffolding`, 23 in
`m0_05_widening_and_iteration`, 8 in `m0_06_cost_scalarization`, 14 in
`m0_07_canonicalization`, 1 in `m0_08_zed0_checklist`, 32 in
`m0_09_kernel_evaluator`, 83 in `m0_10_finite_model_harness`, 10 in
`m0_11_prelude_axioms_and_limits`). `cargo fmt --all --check` and
`cargo clippy --workspace --all-targets -- -D warnings` are clean. The steps binary takes
about 27 s in a debug build, with `zed-kernel` built at opt-level 2.

## Steps

| Step | State | Notes |
|---|---|---|
| M0.1 | done | workspace (`zedc`, `zed-kernel`, `zed-rt`, `zed-cert`, `zed-tests`), CI workflow, insta snapshots. Both negative controls fail as they should: a corrupted snapshot, and an undeclared step folder |
| M0.10 | done | `zed_kernel::budgets` holds the ladder budgets and the rung 6 instance. `zed_tests::{instances, check, kernel}` hold the enumerators, the equation checker, and the derived forms. Laws 1–28 with a counterexample per side condition; the eight layer-free witness entries with their side-condition counterexamples (truncated division fails the packing inverse on row -1); every schedule agrees on all 512 three-node graphs and 512 random ones, stalls included; smoke cases. Negative control: making an undefined read ignore which `fix` it belongs to fails both nested-fix tests. 11 s in a release build |
| M0.5 | done | `zedc::store::{interval, lattice, wto, iterate, revision}`: interval unions with the piece limit and widening, congruences, finite sets, cardinalities; Bourdoncle's order and recursive strategy (phase 1) and Jacobi narrowing rounds (phase 2); the tonicity and HC4 tables and the reductions. Oracles: a declarative weak topological order (2,048 graphs), a stack machine for phase 1 (512 systems × 5 delays × 2 bounds), the concrete least fixpoint in a window, and brute-force soundness of one revision round (over 10^6 solutions). The prelude units `lattice`, `iteration`, `revision` parse (`ring.py`) and check at L6 together (`layer.py`). Negative controls: widening at `changes >= delay` fails 2 tests; dropping the zero guard of backward `*` fails 2; reversed successor order fails the order oracle; Gauss-Seidel narrowing fails 2 |
| M0.6 | done | `zedc::cost`: target profiles (default: one 8-core CPU, 16 GiB), per-device Brent bounds plus one transfer per cut edge, the per-device Pareto frontier, the pick with content-address tie-break. `zedc::address::ContentAddress` (bytes, hex, byte order; hashing comes at M0.7). Negative controls: reversing the tie-break, dropping the transfer latency, a frontier over totals, ignoring capacity, and flooring the Brent bound each fail a test |
| M0.7 | done | `zedc::canon`: four rules (binders to de Bruijn levels with the written name kept as a hint, hints dropped, facets sorted and deduplicated, domain normal form), each with a rank; the tagged serialization; BLAKE3 address over a domain tag, `VERSION` = 1 and the serialization, with resolved free names hashed as their definitions' addresses. Over kernel terms until ZIR exists (L1.32). Oracles: de Bruijn-index α-equivalence on 2,048 random term pairs; domain normal forms against membership in -60..=60 on 4,096 random domains; rank decrease and rule-order independence on 512 random definitions. Negative controls: ignoring shadowing (two places), dropping a lambda's arity, ignoring resolution, hashing `abs` of floats, skipping the run merge, skipping the point-class join, keeping the first duplicate facet, and dropping the version each fail a test |
| M0.8 | done | `zed/compiler/ZED0.md` and `audit.py`: program 31 needs 91 grammar alternatives (L1, L2, L3, L6) and 13 words (up to L5), each found by deleting the alternative and reparsing; Part B adds the compiler's needs beyond program 31, all at L1–L6 but the built-in Cranelift ports (step S.4). The audit needs the spec's grammar tools, so it runs by hand; the step test keeps the stated layer equal to the highest item and to program 31's label. Negative controls: one entry deleted from the checklist makes the audit exit 1 naming it; program 17 audits to `window` at L7; stating L5 fails the step test |
| M0.11 | done | `zedc::axioms`: 86 axioms, one per operator, carrier and law, over the kernel's carriers `int`, `f64`, `bool`, `String`; each holds on the M0.10 instances (rung 6 ints and floats, both bools, strings over `a`, `b` up to length 3), run on the reference evaluator, and `zed/prelude/axioms.zed` is checked equal to the table. `zedc::canon::unit_address` hashes the exports by name and address. `MIN_STEPS` 10^7, `MIN_MEMORY` 1 GiB, `MIN_NESTED_CALLS` 20,000, with a compile-time assertion that the evaluator's fuel and depth meet them; tests run a 9,999,999-step program, a 20,000-deep chain and a 2^30 - 1 byte live string, and one step or call more is shown to cross the step and depth limits. Negative controls: a false claim of each kind of law is refuted (16 claims); claiming `+` associative at `f64` fails on 1.0, 0.1, 0.1; dropping the name length from the unit hash breaks the pinned address; `MAX_DEPTH` 19,999 does not compile |
| L1.1 | done | `zedc::source::load`: UTF-8 (the first invalid sequence's bytes are the span), no leading byte order mark, NFC (the span is the first piece cut before a character of combining class 0, or pair of such pieces, that NFC changes, and the message gives its NFC spelling); `\r\n` and `\r` become `\n`. Golden rejections of ten files as tools write them (ISO-8859-1, a macOS decomposed name, Notepad's mark, a truncated download, CESU-8, an overlong `/`, U+212B, marks out of order, Hangul jamo, a CRLF file), each repaired by its NFC spelling; a 20,000-string fuzz checks the span against `is_nfc`. Negative controls: checking the pair before the single piece widens the span and fails the fuzz; dropping the lone-`\r` rule fails the line-ending test |
| L1.2 | done | `zedc::lex`: the lexer, whose token kinds grow through L1.6 (a character no rule reads yet is an `Unexpected` error); `lex::name` reads `Name` and `Wildcard` by the lexical grammar, and `is_single_script` is UTS #39 Highly Restrictive. Tests: names in eleven scripts and three Latin-with-East-Asian mixes lex; Cyrillic and Greek lookalikes, `ΔT` and Hangul with kana are rejected with the span and the scripts named; `_`, `_x`, `__init__`, one trailing `'`. Negative controls: without the East Asian sets `user名` is rejected; reading a bare `_` as a name fails the wildcard test (the test's helper first printed both as `_` and missed it; fixed) |
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
- M0.5 values (DESIGN.md M0.5): piece limit 8; widening delay 3; 64 head updates per
  stabilization, then the component goes to ⊤; 64 narrowing rounds; finite sets widen to ⊤
  past 64 members; Presburger relations of at most 16 variables and 64 atoms, eliminations of at
  most 4,096 atoms. Rule 1 of sec:constraints now says phase 1 is Bourdoncle's recursive
  strategy and only phase 2 runs in rounds; the sec:domains example is the tested three-cell
  loop. `flat(elems, top:)` is defined there (bottom `#empty`).
- M0.6 (DESIGN.md M0.6): the scalar sums devices as if run in sequence, an upper bound on
  the running time; L24 may refine the estimate but must keep it monotone in the frontier's
  quantities. The frontier is per device, because the scalar is not monotone in plan totals
  (work moved to a slower device costs more).
- M0.7 (DESIGN.md M0.7): the canonicalizer runs over kernel terms now and moves onto ZIR at
  L1.32. A canonical binder name is NUL then its level, which no source name can contain. The
  definition's own name, port names, atom names and catalog witnesses are part of the
  interface and so of the address. Renaming one binder per pass is O(n²) in the binders;
  L1.32 may do it in one pass if it gives the same normal form.
- M0.11 (DESIGN.md M0.11): an axiom is per arrow; a law every arrow of a name must have is
  listed at each kernel carrier. `+` at `f64` has identity -0.0, not 0.0. `min` and `max`
  have no identity. A unit has no version number: its address covers its exported
  declarations only, so its path and unused local declarations do not change it. The
  reference evaluator sets no memory limit; a step is a call, a `fix` round or a `gen` step.
  The old comment on `DEFAULT_FUEL` cited a 10^8-step budget in sec:verification that the spec
  does not state; it now says the fuel is ten times `MIN_STEPS`.
- L1.1 (DESIGN.md sec:lexical): a leading byte order mark is rejected, like a file not in NFC;
  a lone `\r` is a line break. A U+FEFF after the start is the lexer's to reject. Dependency:
  `unicode-normalization`.
- L1.2 (DESIGN.md sec:lexical): mixed script is the complement of UTS #39 Highly Restrictive,
  so Greek with Latin (`ΔT`) is rejected. Dependencies: `unicode-ident`, `unicode-script`.
- Known limits of the M0.5 store: the order and the stabilization recurse as deep as the graph
  (revisit at L1.24, where real programs give large graphs); `End::from_i128` saturates at the
  64-bit limits, which lie within the evaluator's own range limit.
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
