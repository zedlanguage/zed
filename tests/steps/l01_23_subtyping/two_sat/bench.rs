//! The benchmarks of `two_sat.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `two_sat.rs`.

use super::*;

/// The cost of deciding a shape at the variable counts `(a, b)`, the types built before the
/// runs, under the scaling limit. The input's size is that of the type: about one clause per
/// variable, each a union of tuple types of one component per variable, so of order `vars^2`,
/// and `b` about `2.83 a` gives it 8 times over, which the assert of the size ratio checks.
/// This was `scales` in `two_sat.rs`, at 45 and 128 variables (`VARS`) for every shape; each
/// benchmark below names its own counts, chosen for about 0.5 s at the smaller
/// (TEST-bench-move-l0123, author P169).
fn scales_at(name: &str, (a, b): (usize, usize)) {
    let (small, large) = (instance(name, a), instance(name, b));
    let ratio = large.2 as f64 / small.2 as f64;
    assert!((7.9..8.2).contains(&ratio), "{name}: size ratio {ratio}");
    scaling::compare(
        &format!(
            "2-CNF {name}: {a} and {b} variables, sizes {} and {}, {ratio:.2} times",
            small.2, large.2
        ),
        1,
        || decide(name, a, &small),
        || decide(name, b, &large),
    );
}

#[test]
fn a_chain_is_decided_in_the_size_of_its_type() {
    // TEST-bench-move-l0123, author P169: 45 and 128 variables before, now 500 and 1414; 1x 0.59 s
    // by `ns`, load 56.
    scales_at("chain", (500, 1414));
}

#[test]
fn an_open_chain_is_decided_in_the_size_of_its_type() {
    // TEST-bench-move-l0123, author P169: 45 and 128 variables before, now 256 and 724; 1x 0.41 s
    // by `ns`, load 56.
    scales_at("chainsat", (256, 724));
}

#[test]
fn a_parity_cycle_is_decided_in_the_size_of_its_type() {
    // TEST-bench-move-l0123, author P169: 45 and 128 variables before, now 1000 and 2828; 1x
    // 0.26 s by `ns`, load 33.
    scales_at("xorcycle", (1000, 2828));
}

/// The parity cycle at 11 and 88 variables, within 24 times: linear in the clauses, a smaller
/// measure than the type, whose size grows 64 times. The search before item T6-2sat costs about
/// `vars^3` here, which is `n^1.5` in the type's size: 22 times at 8 times the size, inside the
/// limit of [`scales_at`], so only this test tells it from the 2-CNF reading (it allocated 446
/// times the bytes from 11 to 88 variables).
#[test]
fn a_parity_cycle_is_decided_in_time_linear_in_its_clauses() {
    // Left at its old size, 11 variables, as a finding (TEST-bench-move-l0123, author P169):
    // it fails the limit 10.5 at that size too. Instructions at n and 8n, load 27 to 57: n 11,
    // 2518740 and 27181124, 10.792 (bytes 9.16), the same in two runs (the baseline of
    // 2026-11-13 had 3009355 and 30413409, 10.106); n 22, 4985098 and 71559247, 14.355 (bytes
    // 11.11); n 32, 7867806 and 126869932, 16.125 (bytes 11.21); n 64, 18234809 and
    // 390442319, 21.412 (bytes 13.97). By variables the ratio grows toward 8^1.5 = 22.6:
    // more than linear in the clauses, far less than `vars^3` (512). The 1x at 11 took
    // 0.53 ms by `ns`. Not profiled: perf cannot open events here.
    let n = 11;
    let types = scaling::inputs(n, |m| instance("xorcycle", m));
    scaling::check("2-CNF xorcycle, by variables", n, |m| {
        decide("xorcycle", m, &types[&m]);
    });
}
