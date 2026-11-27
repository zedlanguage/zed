# Repository layout

The implementation follows the plan in Part G of the Zed design document (DESIGN.md): stage
M0, then layers L1 to L29, with row S, the self-hosted compiler, after L6. The layout is meant
to stay the same through all of them. A later stage adds files in the places below, not new
kinds of places.

```
Cargo.toml            the Rust workspace
crates/               the Rust-hosted toolchain, kept permanently as the bootstrap root
  zed-collections/    sorted-list operations and small data structures every crate shares
  zed-graph/          graph algorithms every crate shares: strongly connected components,
                      over nodes numbered before the search or as the walk meets them
  zed-numtheory/      number theory on words and big integers that every crate shares: gcds,
                      products and powers modulo a word and modulo 2^61 - 1, primality,
                      factoring, sieves, the floor sum; below zed-kernel, depending only on num-bigint,
                      num-integer and num-traits
  zed-kernel/         kernel terms, the ZIR node inventory, the M0.9 reference evaluator
  zedc/               the compiler's top crate: the incremental queries, the run of a program,
                      the `zedc` command's code, and each zedc-* crate's modules re-exported at
                      their old paths (`zedc::check`, `zedc::store::presburger`, ...)
  zedc-base/          source text, addresses, rejections, costs, the definitional interpreter
  zedc-syntax/        lexer, parser, syntax tree, formatter
  zedc-int/           the unbounded integers of the constraint store and their rationals `Q`
  zedc-lattice/       the store's lattices: intervals, affine, floats, cells, iteration orders
  zedc-solvers/       linear programs, two-variable and UTVPI systems, shortest paths
  zedc-presburger/    the Presburger decision procedure, conjuncts, hulls
  zedc-types/         checker types and their kernel types
  zedc-resolve/       name resolution and its tables, doc comments
  zedc-stage/         staging, definitions, cones
  zedc-preimage/      preimages and the reduced product
  zedc-check/         the checker
  zedc-zir/           ZIR and canonical forms
  zedc-elab/          elaboration to kernel terms
  zed-rt/             the runtime that native code links against
  zed-native/         native code by Cranelift (step L1.36), `zedc build` (L1.36a), and the
                      runtime library `libzed_native.a` an executable links; the `zedc` binary,
                      whose source is in zedc/src/main.rs, is a target of this crate
  zed-cert/           the independent certificate checker; depends on zed-kernel only
  zed-alloc-count/    the counting allocator the test binaries use to measure bytes allocated
  zed-meter-settings/ the C library settings the scaling tests count under; a test binary
                      started without them starts itself again with them
  zed-testkit/        the seed of a random test and the scaling test (n/8n ratios), a
                      dev-dependency of every crate's tests; zed-tests re-exports both
  zed-tools/          the commands: sync, check, cases, fences, fuzz, layer, ring, audit,
                      progress, catalog; each takes the spec directory, and shares `zedc::parse`;
                      conflicts writes the conflict lists of docs/plan_dag.md
zed/                  Zed source code
  prelude/            the normative prelude (from step M0.5)
  corpus/             the 31 corpus programs (step M0.4): NN-name.zed with its .in and .out,
                      a folder NN-name/ for the other units of a multi-unit program,
                      ref/, the crate zed-corpus-ref computing each .out, variants/, controls/,
                      LEDGER.md
  compiler/           the compiler written in Zed (row S); for now CATALOG.md, the routines
                      the Rust calls (row PORT-catalog)
  grammar/            the grammars the parser reads, lexical.peg, syntax.peg and notation.peg
                      (DESIGN.md sec:grammar points here; this is their one copy), and the
                      bracketing and left-recursion cases (step L1.8)
  fences/             variants/, one fixture per commented ✗ variant of the spec's fences
                      (step L1.7), and predictions/
tests/                the step tests (the `zed-tests` crate)
  Cargo.toml          one test target per step folder, written by the step_targets tool
  src/                helpers shared by every step; step_helpers/, those that the tests of
                      more than one step folder use
  steps/<step>/       one folder per step of Part G, each its own test binary; the local
                      suite, which needs only the Rust toolchain
  full/<step>/        tests of a step that need outside tools, listed in the folder's file
                      `needs`; run by tools/run_tests.sh --full
benches/              the crossover benchmarks (the `zed-benches` crate): each times the two
                      methods either side of a threshold where the code changes method at a
                      size and sets the threshold; run by hand on each target platform, not tests
docs/                 documentation of the implementation
tools/                scripts that build, test and merge: run_tests.sh, fetch_test_deps.sh,
                      merge_check.sh, plan_merge.sh (the git merge driver of plan_dag.md),
                      bench_limit.sh and others, each with its test_*.sh; dagview/, the viewer of the plan's graph
build/                every generated file; ignored by git
STATUS.md             progress and handoff notes
ZED_PORT_GAPS.md      what the Rust relies on that Zed lacks; each step adds to it
```

## Crates

The four crates are the ones step M0.1 names. The certificate checker is independent of the
optimizer it checks (sec:optimizer), and the runtime is not used by the interpreter, so that the
differential oracle (step L1.37) compares two independent implementations.

The compiler is split into the crates `zedc-*` (item ZEDC-split) so that an edit recompiles only
its own crate and the crates above it, not the whole compiler. Each is built as an rlib and a
dylib, and takes its lints from the workspace. The incremental database of step L1.30 stays in
`zedc`, which is the top crate; it re-exports each moved module at its old path, so callers
still write `zedc::check` or `zedc::store::presburger`. From the bottom up, each crate depends
only on crates above it in this list:

| Crate | The zedc crates it depends on |
|---|---|
| zedc-base | |
| zedc-syntax | base |
| zedc-int | |
| zedc-affine | int |
| zedc-lattice | affine, base, int |
| zedc-solvers | affine, int |
| zedc-presburger | affine, int, lattice, solvers |
| zedc-types | base, syntax |
| zedc-resolve | base, syntax |
| zedc-stage | base, syntax |
| zedc-preimage | affine, int, lattice, presburger, stage |
| zedc-check | base, int, lattice, preimage, resolve, syntax, types |
| zedc-zir | base, int, lattice, syntax |
| zedc-elab | base, check, resolve, stage, syntax, types |
| zedc | all of them |

An item a crate above uses is `pub`, with a doc comment; anything else stays private to its
crate. A feature that changes a crate's code for tests (`printed-types`, `counts`,
`two-at-a-time`) is also named in that crate's own dev-dependencies, and in those of each crate
above it whose tests need it. A dylib's file name does not change with its features, so without
this `cargo test -p <crate>` would build the crate with fewer features over the workspace build's
copy, and the next workspace build would build it again. Add a new module to the lowest crate
whose dependencies it needs, and re-export it from `zedc` if callers outside the compiler use it.

Code generation through MLIR and LLVM (L28) and the GPU, distributed and hardware targets
(L27) go into new modules of `zedc`, or into a new crate only where they bring a heavy native
dependency that a build should be able to leave out.

### Library DAG

Generic algorithms and data structures live in library crates, which know nothing of Zed's terms,
types or ZIR. The libraries form a DAG; each sits as low as its dependencies allow (author,
2026-11-26). Crates marked *new* are being made by the DRY-2026-11-26 rows of
`docs/plan_dag.md`.

| Library | Depends on | Holds |
|---|---|---|
| zed-hash (new) | | splitmix64, FNV-1a, seeded test generators (xorshift, the two LCGs kept bit-exact) |
| zed-numtheory | | word arithmetic: gcd, inverses (also mod 2^64), `add_mod`/`mul_mod`, CRT, primes, factoring, sieves, bit width (`BitLen`), mod 2^61-1 and 2^64-59 hashing; the floor sum `floor_sum` (on `BigInt`) and `floor_sum_i128` |
| zed-graph | | reach, SCC, Kahn, worklists (plain, priority, keyed), union-find, BFS paths, Knuth's least derivation, functional-graph cycles |
| zed-alloc-count | | the counting allocator |
| zed-collections | numtheory, hash | sorted lists (merge, merge with values, subset, disjoint, `sort_dedup`), intervals, interval ends with the infinities (`ext::Ext`), gallop search, interners, min-add segment tree, persistent treap with a lazy tag, join-based AVL, Patricia trie, priority search tree |
| zed-bignum (new) | numtheory, collections, num-bigint | big-integer algorithms: product and remainder trees, fast division, gcd and printing, power by squaring, least and nth roots, coprime bases, CRT trees (the `m * 2^e` bound type is DRY-bignum-bound-type) |
| zed-bignum-small (dev only) | as zed-bignum | zed-bignum's source built again with its unit tests' small leaves, for zed-kernel's unit tests alone (zed-bignum `fast::SMALL_LEAVES`) |
| zed-testkit (dev only) | hash, alloc-count, meter-settings | `seed` and `scaling` (timers, n/8n ratios, inputs, load), a dev-dependency of 15 crates and zed-tests (until DRY-testkit-2026-11-26 included by `#[path]` in 24 places) |

Above the libraries, two compiler crates are shared by the rest and hold the generic parts that
need the compiler's integer `Int`: `zedc-int` (`Int`, `Int::inverse_mod`, `Int::crt_pair`, the
rational `Q`) and `zedc-affine` (new; depends on zedc-int: affine forms over `BTreeMap<K, V>` with the
merge that drops zero coefficients (`add_term`, `add_scaled`, `scaled`), gcd-normalized rows
(`content`, `row_divisor`, `divide_row`), primitive-form keys (`primitive_form`), and in
`shadow` rows in one variable read as bounds (`i128_row_bound`, `i128_meet`), Fourier-Motzkin
pairs and the dark shadow (`i128_pair`, `dark_gap`, `dark_exact`), and in `plane` the 2D
geometry (`cross`, `dot`, `angle_cmp`, `angle_cmp_from`, `cramer`) and unimodular bases from
Bezout (`Basis`), over `i128` and `Int` (depends also on zed-numtheory), and in `lines` the
upper envelope of lines (`upper_envelope`, `upper_envelope_by`, `not_above`) and `floor_sum` on `Int` (zed-numtheory's),
in `space` lattice reduction (`lll`), Babai's nearest plane (`nearest_plane`), unimodular
completion (`complete`) and 3D vectors over `Q`, and in `equalities` the elimination of unit
equalities (`eliminate_units`, over zed-graph's work list; zed-graph depends on no crate);
still to come: Karr's affine hull, after its row trait). Text helpers stay in
`zed_kernel::text::prose` and `zedc_base` (`source`, `terminal`, `address`).

Before writing an algorithm that is likely generic or reusable, search these crates and call what
is there. If nothing fits, put the reusable part in the lowest library that can hold it, with its
tests, and call it. If the library version is too narrow, make it more general there (a type
parameter, a closure, a trait, an option), with tests for its old and new uses, rather than
writing a variant beside it.

## Tests

There are two kinds of test.

- **Unit tests of the compiler's own code** sit beside that code, in `#[cfg(test)]` modules.
  They test internal functions that no Zed program can reach directly.
- **Step tests** sit in `tests/steps/<step>/`, one folder per step of Part G (two for a few
  large steps, below). They test the language: each one gives Zed source to the compiler and
  checks what comes out. Their purpose
  goes beyond checking. The user documentation is to be built from them, so that a reader can
  learn the language from the inside out, one layer at a time. So a step test is written as a
  small real-world example, simplified until it tests just the thing it is about.

A step folder is named `<stage>_<step>_<description>`:

| Stage | Meaning | Example |
|---|---|---|
| `m0` | stage M0 | `m0_09_kernel_evaluator` |
| `l01` … `l29` | layers L1 to L29 | `l01_07_fences` |
| `s` | row S, self-hosting | `s_01_stage1` |

The step is the two-digit step number within its stage, and the description is a few
lowercase words. Where a layer's work runs in vertical slices (Part G), a slice's tests go into
the folder of each step it takes from. The structure check in `m0_01_scaffolding` rejects a
folder whose name is malformed, a folder without a test target and a target without a folder,
and the same file holds the index of all steps as an expected-output snapshot.

A step folder holds:

- `mod.rs`, plus further `.rs` files for its topics;
- `*.zed` fixture files where the source is longer than a few lines;
- `snapshots/`, the expected outputs, kept by [insta](https://insta.rs). A changed output fails
  the test; review it with `cargo insta review` and accept it there.

Each step folder is a test binary of its own, named after the folder, with the folder's
`mod.rs` as its crate root, so a change to one folder's tests recompiles and links that binary
alone. To run one step: `cargo test -p zed-tests --test l01_07_fences`. Within the binary a
test's name is its path below the folder: `copies::every_design_fence_lexes`, not
`l01_07_fences::copies::every_design_fence_lexes`. The targets are listed in
`tests/Cargo.toml` between the lines `# BEGIN step targets` and `# END step targets`, which
`cargo run -p zed-tools --bin step_targets` writes from the folders; run it after adding,
renaming or removing a folder, and after a rebase that does. Code that the tests of more than
one folder use lives in the `zed-tests` library, under `tests/src/step_helpers/`, in a module
named after the folder it came from. The exceptions are the files `binary.rs` that run the zedc
executable (in m0_09, l01_19a and l01_36a): they are not modules of their folder's binary but
tests of zed-native, named in `crates/zed-native/Cargo.toml`, since only a test of that package
can name the executable.

**When a step's tests are split into two binaries** (TESTS-split, author A30: the size that
suits both test edits and compiler edits). A large binary is slow to rebuild after an edit to
one of its tests; every binary adds a fixed cost to each build of all tests, which an edit to a
compiler crate or to `tests/src` causes. Measured on 2026-11-14 through zcargo with 4 jobs at
load 40 to 56, three runs each: a one-line edit to a test rebuilds its binary in 0.6 s plus
0.1 s per 1,000 lines of the folder (0.6 to 1.0 s for l01_09, 400 lines; 3.7 to 4.5 s for
l01_23, 32,900 lines). After an edit to zedc-check each test binary takes 0.58 s of CPU plus
0.16 s per 1,000 lines (all 81 binaries: 60 to 77 s, 86 to 97 s of CPU); after an edit to
`tests/src`, 0.43 s plus 0.11 s per 1,000 lines. The agent transcripts of 2026-11-13 and 14
show 5.1 builds of one test binary and 1.27 builds of all of them per commit. Halving a folder
of L thousand lines that a share c of all commits edit saves 5.1 × c × 0.1 × L / 2 s per
commit and costs 1.27 × 0.58 / 4 = 0.18 s per commit, so a folder is split in two when
c × L > 0.73, and in three when c × L > 2.2. By the 2,690 commits of 2026-11-07 to 14 this
splits l01_38 (1.96), l01_39 (1.57), l01_23 (1.49) and l01_29 (1.32) in two; the next is
l01_26 at 0.61. The second folder keeps the step number with a description of its own
(`l01_29_diagnostics` and `l01_29_repairs_and_printing`), modules that refer to each other stay
in one folder, the edits fall about evenly between the two, and helpers both use move to
`tests/src/step_helpers/`. Compute c × L again when a folder grows or its edits move.

Measured again after the four splits, on 2026-11-14 at load 19 to 24 (the first measurement
ran at 40 to 56, so the times are compared through ratios measured in the same run): a
one-line edit to a test rebuilds l01_09 in 0.3 s, l01_23_groups_and_refusals (20,100 lines) in
1.3 to 1.5 s and l01_23_subtyping (13,100 lines) in 1.4 s, so an l01_23 edit went from 6.2 to
7.5 times the small folder's build to 4.3 to 5. Building all 85 test binaries after an edit to
zedc-check took 28 to 37 s (wall), after an edit to `tests/src` 9 s; the eight binaries of
the split steps cost 0.31 to 0.46 of the 77 binaries no split touched (0.21 to 0.32 for their
four binaries before) after the zedc-check edit, and 0.32 to 0.33 after the `tests/src` edit
(0.24 to 0.29 before). So each new binary adds 0.7 % to 2 % of the other binaries' build (by
the means of the runs: 2 % and 1.5 %), 0.5 to 1.5 s of CPU at the first measurement's load
against the 0.58 s the rule assumes. The noise is as large as the effect: at 0.9 s the
thresholds would be 1.1 and 3.4 and the four splits stand; at 1.5 s they would be 1.9 and 5.7,
and only l01_38 (1.96) would be split. Measure again, at a steady load, before splitting more.

Notes and plan rows written before the split name the old folder. The module names did not
change; these moved:

| Old folder | New folder | Its modules |
|---|---|---|
| l01_23_subtyping | l01_23_groups_and_refusals | bes, bes_families, cases, complete, cycle_dup, group_oracle, judgments, r6_reduction, refusals, sweep_agreement |
| l01_29_diagnostics | l01_29_repairs_and_printing | casts, domain_repairs, kernel_names, menu_order, offered_repairs, order, parens, power_repairs, printed, rare, refused_in_rejection, refused_warning, rejection_addresses, repairs, scaling, stable, suppress, too_large, type_size, widen_test |
| l01_38_presburger | l01_38_omega_test | completeness, decide_sat, disj_groups, extend, front_cost, live3, model, model_keys, names, omega, one_scope, preimage, probe, projection_oracle, q1_local, repair, scaling, stages, tight |
| l01_39_reduced_product | l01_39_scope_relations | deep_condition, disjoint, families, holes, lazy, linked, nests, path_check, seed_edges, two_disjunctions, xst |

**The design document's fences.** From step L1.7 on, every `zed` fence of DESIGN.md and
EXAMPLES.md is a test. The spec repository is private and this one is public, so no text of
the spec is kept here: the tests that need it read DESIGN.md and EXAMPLES.md in place, under
the cargo feature `spec` of `zed-tests` (`tests/src/spec.rs`). `$ZED_SPEC_DIR` names the spec
directory; without it, the first ancestor directory holding `zed/DESIGN.md` is used, which for
a checkout beside the spec repository is `../zed`. `tools/run_tests.sh` always enables the
feature, and a test run with the feature on and no spec fails, naming the paths it tried. A
build without the feature compiles and runs every test that does not read the spec. The
fences are laid out by `zed_tests::fences` with the spec's own parsers (`zed_tools::spec`),
and the variant fixtures of commented ✗ lines stay in `zed/fences/variants/`.

The three grammars, `lexical.peg`, `syntax.peg` and `notation.peg`, live only in
`zed/grammar/` (`zedc-syntax` embeds `syntax.peg` with `include_str!`); DESIGN.md sec:grammar
points to them. A change to the syntax edits DESIGN.md's prose and these files together. The
desugaring rules and the table of words are read from DESIGN.md in place. The hand-run command
`cargo run -p zed-tools --bin sync -- <spec dir>` writes nothing: it runs the checks that need
the spec's prose (the kernel grammar's rule names, the prelude laws and the build-mode table)
and `cite`'s check that each `sec:` this repository cites exists, and exits nonzero when one
fails.

**Tests written in Zed.** Until the `test { }` runner lands (step L1.21), every step test is
written in Rust, with the Zed source given as strings or fixture files. From then on, tests of
what a Zed program computes are to be written in Zed itself, in a form the design document
specifies, and run by the Rust harness.

## build/

`.cargo/config.toml` sets Cargo's target directory to `build/cargo`. Every other generated
file goes under `build/` too, each tool in its own subdirectory, such as compiler caches,
native objects and coverage reports. Deleting `build/` loses nothing that a build cannot make
again. Test builds carry no debug info, which keeps them about a third of the size. For perf or
gdb use `cargo test --profile profiling`, then delete `build/cargo/profiling`.
