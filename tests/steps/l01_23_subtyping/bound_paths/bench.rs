//! The benchmarks of `bound_paths.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `bound_paths.rs`.

/// The walk is linear in the written types: checking a program of `n` and of `8n` parameters,
/// each with a nested bounded type, does work of order n, counted in instructions. The
/// checker is timed alone, on statements parsed and resolved before the timing (COMPLEXITY.md
/// F85).
#[test]
fn the_bound_walk_scales_linearly() {
    let program = |n: usize| {
        let params: Vec<String> = (0..n)
            .map(|i| format!("x{i}: (int, #a .. #a | #b -> int) | int"))
            .collect();
        format!("f({}) = 0;\nmain() = 0;\n", params.join(", "))
    };
    let units: std::collections::HashMap<usize, _> = [250, 2000]
        .into_iter()
        .map(|n| (n, zed_tests::deep::resolved(&program(n))))
        .collect();
    zed_tests::scaling::check_order("bound walk", 250, 1, |n| {
        let (stmts, res) = &units[&n];
        let info = zedc::check::walk::check(stmts, res);
        assert!(info.errors.is_empty(), "{:?}", info.errors);
    });
}
