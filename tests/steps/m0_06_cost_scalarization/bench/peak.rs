//! The peak footprint's time, linear in the regions (checked with order 1 at r and 8r); the
//! input is checked at small sizes by `peak::the_peak_of_alternating_jobs_is_found_at_small_sizes`.

use zed_tests::scaling::check_order;
use zedc::cost::{feasible, vector};

use crate::peak::alternating;
use crate::workstation;

#[test]
fn the_peak_takes_time_linear_in_the_regions() {
    // Jobs alternate between the CPU and the GPU with footprints and retained bytes that
    // repeat, so the peak moves through the whole schedule. Both plans are built before the
    // measurement.
    let n = 20_000;
    let (small, large) = (alternating(n), alternating(8 * n));
    let t = workstation();
    check_order("the peak footprint of a plan's regions", n, 1, |r| {
        let p = if r == n { &small } else { &large };
        std::hint::black_box((feasible(p, &t), vector(p, &t)));
    });
}
