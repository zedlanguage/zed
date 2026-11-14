//! The benchmarks of the cost scalarization, run by `tools/run_tests.sh --bench` and left out of
//! its default run (TEST-bench-move-rest). Each check they make besides the ratio is made at
//! small sizes by a correctness test of the module whose name each file bears; the one here, of
//! the root module's frontier, by `the_frontier_of_scaled_variants_stays_small_at_small_sizes`.

mod overlap;
mod peak;

use crate::{frontier_plans, workstation};
use zedc::cost::pick;

#[test]
fn the_frontier_takes_time_linear_in_the_plans_when_it_stays_small() {
    // Each plan is a fused or a split variant scaled by its distance from the end of the list,
    // so the frontier holds the last two, and every other plan is compared with those only.
    // The input lists them last, where a scan of the plans in arrival order meets them last.
    zed_tests::scaling::check("the Pareto frontier of plans", 2000, |n| {
        pick(&frontier_plans(n), &workstation());
    });
}
