//! The benchmarks of `oracle.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169, P178). Each check has a drawn sample among
//! the correctness tests of `oracle.rs`.

use super::*;

/// Every system of seeds 1 and 2 the cross-review measured (wt/xv/Q1Q7/REPORT.md, check 4),
/// with the check the correctness test made on all 8000 before TEST-bench-move-l0123;
/// `the_two_routes_agree_on_recursive_systems` asks 1500 of them each run.
#[test]
fn every_recursive_system() {
    let (routes, accepted) = recursive_routes(
        (1..=2).flat_map(|seed| (0..SYSTEMS_PER_SEED as usize).map(move |idx| (seed, idx))),
        "every system",
    );
    assert!(
        routes.same > 3900 && routes.refused < 100,
        "{routes:?} of {accepted}"
    );
}
