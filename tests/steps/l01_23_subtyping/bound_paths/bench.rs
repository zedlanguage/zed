//! The benchmarks of `bound_paths.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `bound_paths.rs`.

/// The walk is linear in the written types: checking a program of `n` and of `8n` parameters,
/// each with a nested bounded type, does work of order n, counted in instructions. The
/// checker is timed alone, on statements parsed and resolved before the timing (COMPLEXITY.md
/// F85).
/// TEST-bench-move-l0123, author P169: n was 250, now 10_000; 1x 0.40 s at load 27.
#[test]
fn the_bound_walk_scales_linearly() {
    let units: std::collections::HashMap<usize, _> = [10_000, 80_000]
        .into_iter()
        .map(|n| (n, zed_tests::deep::resolved(&super::nested_bounds(n))))
        .collect();
    zed_tests::scaling::check_order("bound walk", 10_000, 1, |n| {
        let (stmts, res) = &units[&n];
        let info = zedc::check::walk::check(stmts, res);
        assert!(info.errors.is_empty(), "{:?}", info.errors);
    });
}
