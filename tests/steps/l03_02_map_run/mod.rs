//! Step L3.2, plan row MAP-run (author P221): displays, `map`, `where`, lookups that miss,
//! `in` and `not in`, and `><` with a built-in operator, run end to end.
//!
//! `map` and `where` are built into zedc for now: the prelude definition
//! `map(positional m, positional f) = reindex(m, k -> k, f)` of DESIGN.md sec:keypaths needs
//! what plan row MAP-pure-zed records. Each case of `runs` is checked against the M0 model,
//! the reference evaluator of zed-kernel run on the kernel terms the spec defines the form by
//! (`map` as `reindex` with the identity key map, `where` as `discard`, `><` as `fold`), and run
//! by `zedc run` and by an executable `zedc build` makes. `types` holds the refusals.
//! COMPLETENESS.md lists each case and the test that covers it.

#![cfg(target_os = "linux")]

mod bench;
mod folds;
mod functions;
mod pushes;
mod runs;
mod types;

use std::path::PathBuf;

use zed_tests::step_helpers::l01_36a_executables::{Ran, dir, interpreter};

/// The program whose `main` writes `body` to standard output, saved under the test's own
/// directory as `name.zed`.
pub(crate) fn program(name: &str, body: &str) -> PathBuf {
    let src = dir(&format!("l03_02_map_run/{name}")).join(format!("{name}.zed"));
    let text = format!("main(m: MainArgs) {{\n    m.stdout <- \"{body}\";\n}}\n");
    std::fs::write(&src, text).unwrap();
    src
}

/// `body` run by `zedc run` as the output of a program.
pub(crate) fn run(name: &str, body: &str) -> Ran {
    interpreter(&program(name, body), &[], &[])
}

/// The headlines of the warnings that a stopping read of a range with no upper end is not
/// proved to end (plan row RANGE-open-ending-warn), as `zedc run` writes them to standard
/// error, `file:line:col: message`: each from the message on, in the order written. A program
/// meant to run may be warned so; the warning's notes are tested in `types`.
pub(crate) fn not_proved(stderr: &str) -> Vec<&str> {
    (stderr.lines())
        .filter(|l| l.contains(" is not proved to end: "))
        .map(|l| l.find(": `").map_or(l, |i| &l[i + 2..]))
        .collect()
}
