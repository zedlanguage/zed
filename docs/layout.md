# Repository layout

The implementation follows the plan in Part G of the Zed design document (DESIGN.md): stage
M0, then layers L1 to L29, with row S, the self-hosted compiler, after L6. The layout is meant
to stay the same through all of them. A later stage adds files in the places below, not new
kinds of places.

```
Cargo.toml            the Rust workspace
crates/               the Rust-hosted toolchain, kept permanently as the bootstrap root
  zed-kernel/         kernel terms, the ZIR node inventory, the M0.9 reference evaluator
  zedc/               the compiler's top crate: the incremental queries, the run of a program,
                      the `zedc` command's code, and each zedc-* crate's modules re-exported at
                      their old paths (`zedc::check`, `zedc::store::presburger`, ...)
  zedc-base/          source text, addresses, rejections, costs, the definitional interpreter
  zedc-syntax/        lexer, parser, syntax tree, formatter
  zedc-int/           the unbounded integers of the constraint store
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
  zed-tools/          the commands: check, cases, fences, fuzz, layer, ring, audit, sync,
                      progress, catalog; each takes the spec directory, and shares `zedc::parse`;
                      conflicts writes the conflict lists of docs/plan_dag.md
zed/                  Zed source code
  prelude/            the normative prelude (from step M0.5)
  corpus/             the 31 corpus programs (step M0.4): NN-name.zed with its .in and .out,
                      a folder NN-name/ for the other units of a multi-unit program,
                      ref/, the crate zed-corpus-ref computing each .out, variants/, controls/,
                      LEDGER.md
  compiler/           the compiler written in Zed (row S); for now ZED0.md and CATALOG.md, the
                      routines the Rust calls (row PORT-catalog)
  grammar/            the syntactic grammar of sec:grammar and its bracketing cases (step
                      L1.8), written by the sync tool
  fences/             the spec's `zed` fences (step L1.7): design.md and examples.md, written
                      by the sync tool, and variants/, one fixture per commented ✗ variant
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
tools/                run_tests.sh and fetch_test_deps.sh
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
| zedc-lattice | base, int |
| zedc-solvers | int |
| zedc-presburger | int, lattice, solvers |
| zedc-types | syntax |
| zedc-resolve | base, syntax |
| zedc-stage | base, syntax |
| zedc-preimage | int, lattice, presburger, stage |
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

## Tests

There are two kinds of test.

- **Unit tests of the compiler's own code** sit beside that code, in `#[cfg(test)]` modules.
  They test internal functions that no Zed program can reach directly.
- **Step tests** sit in `tests/steps/<step>/`, one folder per step of Part G. They test the
  language: each one gives Zed source to the compiler and checks what comes out. Their purpose
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
test's name is its path below the folder: `copies::the_copies_match_the_spec`, not
`l01_07_fences::copies::the_copies_match_the_spec`. The targets are listed in
`tests/Cargo.toml` between the lines `# BEGIN step targets` and `# END step targets`, which
`cargo run -p zed-tools --bin step_targets` writes from the folders; run it after adding,
renaming or removing a folder, and after a rebase that does. Code that the tests of more than
one folder use lives in the `zed-tests` library, under `tests/src/step_helpers/`, in a module
named after the folder it came from. The exceptions are the files `binary.rs` that run the zedc
executable (in m0_09, l01_19a and l01_36a): they are not modules of their folder's binary but
tests of zed-native, named in `crates/zed-native/Cargo.toml`, since only a test of that package
can name the executable.

**The design document's fences.** From step L1.7 on, every `zed` fence of DESIGN.md and
EXAMPLES.md is a test. The extractor copies them into checked-in fixture files under
`tests/steps/l01_07_fences/`, so that CI needs only this repository. A separate check fails
when the copies no longer match the spec. It finds the spec repository through `$ZED_SPEC_DIR` or as the `zed` checkout
beside an ancestor of this one (`tests/src/spec.rs`), fails where it finds none, and is
skipped only under `ZED_SPEC_DIR=none`, which CI sets.

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
