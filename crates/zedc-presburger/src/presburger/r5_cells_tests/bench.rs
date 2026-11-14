//! The benchmarks of `r5_cells_tests`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-crates). The correctness test that keeps a small instance of
//! what each checks besides the ratio is `the_benchmark_inputs_have_their_answers_at_small_sizes`.
//! Sizes are set (2026-11-14) so the 1x case takes about 0.3 to 1 s and a piece stays under
//! 20 s.

use super::*;

#[test]
fn distinct_pairs_with_one_common_main_and_different_extras_scale() {
    scaling::check_order("different extras of one shared main", 10_000, 1, |n| {
        assert_eq!(has_point(distinct_extras(n)), Ok(true));
    });
}

#[test]
fn different_windows_of_disjoint_bases_scale() {
    scaling::check_order("skew windows of disjoint bases", 10_000, 1, |n| {
        assert_eq!(has_point(skew(n, true)), Ok(false));
    });
}

#[test]
fn different_windows_with_a_point_scale() {
    scaling::check_order("skew windows with a point", 10_000, 1, |n| {
        assert_eq!(has_point(skew(n, false)), Ok(true));
    });
}

#[test]
fn distinct_window_pairs_of_two_bases_scale() {
    scaling::check_order("distinct pairs of windowed bases", 10_000, 1, |n| {
        assert_eq!(has_point(distinct_meets(n)), Ok(true));
    });
}

#[test]
fn independent_components_of_a_cell_core_scale() {
    scaling::check_order("independent components of a cell core", 3000, 1, |n| {
        assert_eq!(has_point(point_rows(n, false)), Ok(false));
    });
}
