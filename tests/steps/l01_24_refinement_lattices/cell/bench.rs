//! The benchmarks of `cell.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `cell.rs`.

use super::*;

/// Reading the premises of a loop's summary costs the parts of the set, not its paths: the
/// summary after `n` iterations has about `3n` parts and `n²/2` paths.
/// TEST-bench-move-l0123, author P169: n was 2000, now 250_000; 1x 0.22 s at load 32.
#[test]
fn reading_a_shared_premise_set_scales() {
    let n = 250_000;
    // The sets, built before the timing; reading them is timed.
    let sets = zed_tests::scaling::inputs(n, |m| {
        let addrs: Vec<FactAddress> = (0..m as u32).map(addr).collect();
        loop_summary(&addrs, &mut || {})
    });
    zed_tests::scaling::check(
        "the premises of a loop summary after n iterations",
        n,
        |m| assert_eq!(sets[&m].set().len(), m),
    );
}
