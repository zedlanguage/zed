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
