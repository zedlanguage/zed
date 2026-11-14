//! The benchmark of `utvpi::tests`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-crates, author P178: a test of many cases is a benchmark). The
//! correctness test `small_graphs_get_the_answers_of_bellman_ford_moore` runs the same battery
//! on 10,000 graphs, from a new seed each run.

use super::tests::small_graphs_agree;

// The battery item UTVPI-GOR's verifier ran, 300,000 random graphs of 1 to 12 nodes, in six
// pieces of 50,000, each from a new seed each run, so that each runs well within the time
// limit: as one piece it took 17.4 s at load 28 and 34.6 s at load 60, against a limit of 38 s.

#[test]
fn many_small_graphs_1() {
    small_graphs_agree(crate::seed::seed("many_small_graphs_1"), 50_000);
}

#[test]
fn many_small_graphs_2() {
    small_graphs_agree(crate::seed::seed("many_small_graphs_2"), 50_000);
}

#[test]
fn many_small_graphs_3() {
    small_graphs_agree(crate::seed::seed("many_small_graphs_3"), 50_000);
}

#[test]
fn many_small_graphs_4() {
    small_graphs_agree(crate::seed::seed("many_small_graphs_4"), 50_000);
}

#[test]
fn many_small_graphs_5() {
    small_graphs_agree(crate::seed::seed("many_small_graphs_5"), 50_000);
}

#[test]
fn many_small_graphs_6() {
    small_graphs_agree(crate::seed::seed("many_small_graphs_6"), 50_000);
}
