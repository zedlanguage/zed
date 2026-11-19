//! The benchmark of `r6_shared_window_tests`, run by `tools/run_tests.sh --bench` and left out
//! of its default run (TEST-bench-split). Its small instances are checked by
//! `views_of_one_set_through_different_windows_have_a_point_at_small_sizes`.

use super::*;
use crate::scaling;

// Two views of one set through different windows were merged whole: R 14.5 at 8n on main
// (distinct_extras_skew, cross-review R5-CX1b).
#[test]
fn views_of_one_set_through_different_windows_meet_in_linear_time() {
    scaling::check_order("views of one set through different windows", 125, 1, |n| {
        assert_eq!(has_point(skew(n)), Ok(true));
    });
}

// Wide extras crossing disjoint windows of one base copied O(n) runs per holder on main:
// R = 11.90 at 250 -> 2000; exact same-base window algebra copies K = 0 runs (R7 Q3).
#[test]
fn cross_window_copy_meets_in_linear_time() {
    scaling::check_order("cross window copy on one base", 250, 1, |n| {
        assert_eq!(has_point(cross_window_copy(n)), Ok(true));
    });
}

// Two disjoint windows of one shared base per holder materialized O(n) runs per holder on main:
// R = 18.01 at 125 -> 1000; multi-window `CellPiece` keeps the base uncopied (R7 Q3).
#[test]
fn two_windows_one_base_joins_in_linear_time() {
    scaling::check_order("two disjoint windows on one base", 125, 1, |n| {
        assert_eq!(has_point(two_windows_one_base(n)), Ok(true));
    });
}

// Distinct shared bases with per-holder extras fell back to O(n) run merges per holder on main;
// caching full-base meets in `CellWalk::base_meets` keeps work linear (R7 Q3).
#[test]
fn distinct_bases_extras_meet_in_linear_time() {
    scaling::check_order("distinct bases with per-holder extras", 125, 1, |n| {
        assert_eq!(has_point(distinct_bases_extras(n)), Ok(false));
    });
}
