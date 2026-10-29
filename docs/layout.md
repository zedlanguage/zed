# Repository layout

The implementation follows the plan in Part G of the Zed design document (DESIGN.md): stage
M0, then layers L1 to L29, with row S, the self-hosted compiler, after L6. The layout is meant
to stay the same through all of them. A later stage adds files in the places below, not new
kinds of places.

```
Cargo.toml            the Rust workspace
crates/               the Rust-hosted toolchain, kept permanently as the bootstrap root
  zed-kernel/         kernel terms, the ZIR node inventory, the M0.9 reference evaluator
  zedc/               the compiler: loading, lexer, parser, elaboration, checker,
                      interpreter, ZIR, code generation, and the `zedc` command
  zed-rt/             the runtime that native code links against
  zed-cert/           the independent certificate checker; depends on zed-kernel only
zed/                  Zed source code
  prelude/            the normative prelude (from step M0.5)
  corpus/             the 31 corpus programs (step M0.4): NN-name.zed with its .in and .out,
                      a folder NN-name/ for the other units of a multi-unit program,
                      ref/NN.py computing each .out, variants/, controls/, LEDGER.md
  compiler/           the compiler written in Zed (row S); empty until then
tests/                the step tests (the `zed-tests` crate)
  src/                helpers shared by every step
  steps/main.rs       declares one module per step, in plan order
  steps/<step>/       one folder per step of Part G
docs/                 documentation of the implementation
build/                every generated file; ignored by git
STATUS.md             progress and handoff notes
```

## Crates

The four crates are the ones step M0.1 names. A crate is split out only where the design asks
for a separate artifact. The certificate checker is independent of the optimizer it checks
(sec:optimizer), and the runtime is not used by the interpreter, so that the differential
oracle (step L1.37) compares two independent implementations. The compiler's stages are
modules of `zedc`, not crates, because from step L1.30 on they are queries over one shared
incremental database.

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
folder whose name is malformed and a folder not declared in `main.rs`, and the same file holds
the index of all steps as a golden snapshot.

A step folder holds:

- `mod.rs`, plus further `.rs` files for its topics;
- `*.zed` fixture files where the source is longer than a few lines;
- `snapshots/`, the golden outputs, kept by [insta](https://insta.rs). A changed output fails
  the test; review it with `cargo insta review` and accept it there.

All step folders compile into one test binary, `steps`, so adding a step adds a module, not a
link step. To run one step: `cargo test -p zed-tests --test steps l01_07`.

**The design document's fences.** From step L1.7 on, every `zed` fence of DESIGN.md and
EXAMPLES.md is a test. The extractor copies them into checked-in fixture files under
`tests/steps/l01_07_fences/`, so that CI needs only this repository. A separate check, run
where the spec repository is present, fails when the copies no longer match the spec.

**Tests written in Zed.** Until the `test { }` runner lands (step L1.21), every step test is
written in Rust, with the Zed source given as strings or fixture files. From then on, tests of
what a Zed program computes are to be written in Zed itself, in a form the design document
specifies, and run by the Rust harness.

## build/

`.cargo/config.toml` sets Cargo's target directory to `build/cargo`. Every other generated
file goes under `build/` too, each tool in its own subdirectory, such as compiler caches,
native objects and coverage reports. Deleting `build/` loses nothing that a build cannot make
again.
