//! The benchmark of `r6_cells_minus_tests`, run by `tools/run_tests.sh --bench` and left out of
//! its default run (TEST-bench-split). Its small instances are checked by
//! `few_runs_taken_from_many_leave_the_rest`.

use super::*;
use crate::scaling;

// Each of n² disjunctions takes its two held runs from n cells: n³ runs read on main
// (shared_guard, cross-review H3-6), 8^1.5 = 22.6 times the work at 8 times the size.
#[test]
fn few_runs_taken_from_many_cost_the_few() {
    scaling::check_order("few runs taken from many", 2000, 1, |n| {
        let a: CellSet = (0..n).map(|j| (2 * j, 2 * j)).collect();
        let mut kept = 0;
        for j in 0..n {
            kept += cells_without(&a, &[(0, 2 * j), (2 * j + 2, 2 * n)]).len();
        }
        assert_eq!(kept, 0);
    });
}
