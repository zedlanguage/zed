//! Benchmarks of `xst::holes`: each times the work at a size and at 8 times it, run apart from
//! the correctness tests (`tools/run_tests.sh --bench`).

use super::*;

/// Claude round 3 and 4 (`family4`, `probe_r4_holes_laps`), Codex round 3 and 4, Gemini
/// round 4: laps with `r = 6n`, measured there at 64 and 512 names, here at 96 and 768. Every
/// name's ends are 0, found by composing the cycle once. Main takes about 8.8 times the work
/// for 8 times the size; with the `Vec` interval sets before INTERVAL-persistent it took 17.4
/// times.
#[test]
fn laps_have_exact_ends_in_near_linear_time() {
    family("laps, r = 6n", 96, |n| laps(n, 6 * n as i64));
}

/// The staircase at 256 and 2,048 names (16 and 128 before): every name in `0..=n`. Main takes
/// about 8.9 times the work for 8 times the size.
#[test]
fn the_staircase_has_exact_ends_in_near_linear_time() {
    family("staircase", 256, staircase);
}

/// The mixed family, `r = 3n`, at 128 and 1,024 names (16 and 128 before). Main takes about
/// 8.7 times the work for 8 times the size.
#[test]
fn the_mixed_family_has_exact_ends_in_near_linear_time() {
    family("mixed, r = 3n", 128, |n| mixed(n, 3 * n as i64));
}

/// CONTROL (Claude round 4): laps without the closing edge, the same tests otherwise. With
/// no cycle the holes cost one pass, so what is left is the cost of the tests themselves:
/// each `x != v` makes a preimage over the domain of `x`, whose holes grow with the number of
/// tests. When the preimage built its landmarks from the ends of every input domain at each
/// test (before LAPS-preimage-cost), that cost was `O(p log p)` per test for `p` holes, and
/// this control took 17.8 times the work for 8 times the size, as the laps with the cycle
/// did (16.3): the cycle was never the cause. It now takes about 8.8 times.
#[test]
fn laps_without_the_closing_edge_take_near_linear_time() {
    family("laps without the closing edge", 128, |n| {
        let mut inst = laps(n, 6 * n as i64);
        inst.edges.pop();
        inst
    });
}
