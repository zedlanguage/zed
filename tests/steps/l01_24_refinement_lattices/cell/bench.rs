//! The benchmarks of `cell.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `cell.rs`.

use super::*;

/// Reading the premises of a loop's summary costs the parts of the set, not its paths: the
/// summary after `n` iterations has about `3n` parts and `n²/2` paths.
#[test]
fn reading_a_shared_premise_set_scales() {
    // The sets, built before the timing; reading them is timed.
    let sets: std::collections::BTreeMap<usize, Premises> = [2000, 16000]
        .into_iter()
        .map(|n| {
            let addrs: Vec<FactAddress> = (0..n as u32).map(addr).collect();
            (n, loop_summary(&addrs, &mut || {}))
        })
        .collect();
    zed_tests::scaling::check(
        "the premises of a loop summary after n iterations",
        2000,
        |n| assert_eq!(sets[&n].set().len(), n),
    );
}
