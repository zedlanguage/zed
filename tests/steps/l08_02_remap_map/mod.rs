//! `map` composed with remaps (DESIGN.md sec:remap_law, sec:keypaths; plan row
//! REMAP-map-tests, author P221: "run tests combining map with remapping").
//!
//! `forms` writes each composition in source form, a `map` before a remap and after one, on
//! each side of a reducer `><` at each level, with each legal move (repack, widen, truncate)
//! and inside the value expression of a remap, and checks each result against a display
//! written by hand and, where the composition is a kernel term, against the M0 model (`map`
//! is `reindex(F, (p, v) -> p, (p, v) -> f(v))`, sec:keypaths). `rank` composes `map` with
//! rank insertion on the kernel, whose source form waits for step L8.2. `law` checks on
//! random families that a `map` commutes with a remap that moves only keys. `bench` holds
//! the scaling benchmark (run with `--bench`). COMPLETENESS.md lists each case and its test.
mod bench;
mod forms;
mod law;
mod rank;

use zed_kernel::{Term, eval};
use zed_tests::step_helpers::l01_16_elaboration::value;

/// `m`, two levels: `{ "a" -> { 1 -> 10, 2 -> 20 }, "b" -> { 1 -> 30 } }`.
pub const M: &str = "m = { \"a\" -> { 1 -> 10, 2 -> 20 }, \"b\" -> { 1 -> 30 } };\n";

/// The value of `got` in `src` is the display `want`, and is not an evaluation error.
pub fn prints(src: &str, got: &str, want: &str) {
    let g = value(src, got);
    assert!(!g.starts_with("error"), "{src}\n{got} = {g}");
    assert_eq!(g, want, "{src}\n{got}");
}

/// The value of `got` in `src` is the value the M0 reference evaluator gives `model`.
pub fn models(src: &str, got: &str, model: &Term) {
    let want = eval(model).unwrap_or_else(|e| panic!("model of {got}: {e:?}"));
    prints(src, got, &want.to_string());
}
