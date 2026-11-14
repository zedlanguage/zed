//! The benchmarks of `r4_cells_tests`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-crates). The correctness test that keeps a small instance of
//! what each checks besides the ratio is `the_benchmark_inputs_have_their_answers_at_small_sizes`.
//! Sizes are set (2026-11-14) so the 1x case takes about 0.3 to 1 s and a piece stays under
//! 20 s.

use super::*;

#[test]
fn a_shared_guard_chain_without_a_point_scales_linearly() {
    scaling::check_order("shared guard chain, no point", 8000, 1, |n| {
        assert_eq!(has_point(holders(n, 1)), Ok(false));
    });
}

#[test]
fn a_shared_guard_chain_with_a_point_scales_linearly() {
    scaling::check_order("shared guard chain, point", 10_000, 1, |n| {
        assert_eq!(has_point(holders(n, 0)), Ok(true));
    });
}

#[test]
fn two_shared_bases_with_different_windows_join_before_the_window() {
    scaling::check_order("two bases under different windows", 8000, 1, |n| {
        assert_eq!(has_point(window_parts(n, false)), Ok(false));
    });
}

#[test]
fn an_independent_choice_does_not_hide_inconsistent_forced_rows() {
    scaling::check_order("forced rows beside a choice", 8000, 1, |n| {
        assert_eq!(has_point(window_parts(n, true)), Ok(false));
    });
}

#[test]
fn repeated_neighbor_set_meets_scale_in_the_number_of_edges() {
    scaling::check_order("bipartite graph, edge count", 125_000, 1, |edges| {
        let side = (edges as f64).sqrt() as usize;
        assert_eq!(has_point(bipartite(side)), Ok(false));
    });
}

#[test]
fn shared_conjunctions_preserve_their_disjunctions_under_different_windows() {
    let fs = scaling::inputs(20_000, |n| window_formula(n, false));
    scaling::check_order("shared formula, different windows", 20_000, 1, |n| {
        assert_eq!(decide(&fs[&n]), Ok(false));
    });
}

#[test]
fn shared_conjunctions_preserve_their_disjunctions_under_equal_windows() {
    let fs = scaling::inputs(9000, |n| window_formula(n, true));
    scaling::check_order("shared formula, equal windows", 9000, 1, |n| {
        assert_eq!(decide(&fs[&n]), Ok(false));
    });
}

#[test]
fn a_shared_guard_chain_with_an_odd_input_scales_linearly() {
    scaling::check_order("a shared guard with an odd input", 8000, 1, |n| {
        let mut p = holders(n, 0);
        p.cons.pop();
        p.cons.push(Con::eq(
            &var("i"),
            &var("t").times(2).plus(&Lin::constant(1)),
        ));
        assert_eq!(has_point(p), Ok(false));
    });
}

#[test]
fn rows_read_by_one_disjunct_each_scale_linearly() {
    scaling::check_order("rows read by one disjunct each", 3000, 1, |n| {
        assert_eq!(has_point(point_rows(n)), Ok(false));
    });
}
