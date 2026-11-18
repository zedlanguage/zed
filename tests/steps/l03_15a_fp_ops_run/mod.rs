//! The standard operations on lists and maps, compiled and run (plan row FP-ops-run, author
//! P229; docs/fp-ops-inventory.md). Each case is the example or test DESIGN.md gives for the
//! word: steps L3.2 (`split`, `lines`, `concat`, folds), L3.15a (`.any`, `.all`, `.find`),
//! L5.1 (`sort`, `.orderedValues`, positional selection), L5.1c (the reverse of an order),
//! L5.2 (`++`, `zip`) and L5.3 (`scan`, `.chunkBy`), and the laws the row names: `zip` then the
//! two projections gives back both operands, and the last entry of a scan equals the fold.
//!
//! Every case runs a whole program through `zedc run` and compares what it prints, so a case
//! passes only when the word parses, resolves, elaborates, checks and runs. `kernel` tests the
//! kernel primitives the row adds on their own; `runs` checks the words built so far three
//! ways (the M0 model, `zedc run`, an executable); `bench` measures them at n and 8n.
//! COMPLETENESS.md lists each case and the test that covers it.
// Proving the bench closures `Sync` (zed_tests::scaling::check) walks the kernel's nested types
// deeper than rustc's default limit of 128; since nightly-2026-11-18 that is the lint
// `recursion_depth_exceeding_limit` (rust-lang/rust#159228), an error under clippy -D warnings.
#![recursion_limit = "256"]

mod bench;
mod cases;
mod kernel;
#[cfg(target_os = "linux")]
mod runs;

use std::path::PathBuf;

use zed_tests::step_helpers::l01_36a_executables::{Ran, dir, interpreter};

/// The program whose `main` writes `body` to standard output, saved under the test's own
/// directory as `name.zed`.
pub(crate) fn program(name: &str, body: &str) -> PathBuf {
    let src = dir(&format!("l03_15a_fp_ops_run/{name}")).join(format!("{name}.zed"));
    let text = format!("main(m: MainArgs) {{\n    m.stdout <- \"{body}\";\n}}\n");
    std::fs::write(&src, text).unwrap();
    src
}

/// `body` run by `zedc run` as the output of a program.
pub(crate) fn run(name: &str, body: &str) -> Ran {
    interpreter(&program(name, body), &[], &[])
}
