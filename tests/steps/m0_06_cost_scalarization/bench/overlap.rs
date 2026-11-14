//! The footprint's time on a static schedule, a balanced nesting and a deep nesting of r
//! regions, each within r log r (checked with order 1 at r and 8r). Each input is checked at
//! small sizes by `overlap::the_footprint_of_each_benchmark_input_is_found_at_small_sizes`.

use zed_tests::scaling::check_order;
use zedc::cost::{feasible, vector};

use crate::overlap::{balanced_nesting, deep_nesting, static_schedule};
use crate::workstation;

#[test]
fn a_static_schedule_takes_time_within_r_log_r() {
    // Jobs alternate between two devices, each lasting 1 to 8 time units and starting 2 apart,
    // so up to four overlap on each device.
    let n = 20_000;
    let (small, large) = (static_schedule(n), static_schedule(8 * n));
    let t = workstation();
    check_order("the footprint of a static schedule", n, 1, |r| {
        let p = if r == n { &small } else { &large };
        std::hint::black_box((feasible(p, &t), vector(p, &t)));
    });
}

#[test]
fn a_balanced_nesting_takes_time_within_r_log_r() {
    // r/4 devices, region i on device i mod r/4: the parts of each composition share devices,
    // so their loads are joined, not only moved.
    let n = 16_384;
    let (small, large) = (balanced_nesting(n), balanced_nesting(8 * n));
    check_order("the footprint of a balanced nesting", n, 1, |r| {
        let (p, t) = if r == n { &small } else { &large };
        std::hint::black_box((feasible(p, t), vector(p, t)));
    });
}

#[test]
fn a_deep_nesting_takes_time_within_r_log_r() {
    // r regions on r/2 devices in r/2 parallel pairs, each pair on two devices, the pairs nested
    // to the right: each sequence joins one pair to the loads of all the pairs after it. Joining
    // into the larger part keeps this within r log r; joining into the earlier part, the naive
    // way, reads O(r) devices per step.
    let n = 16_384;
    let (small, large) = (deep_nesting(n), deep_nesting(8 * n));
    check_order("the footprint of a deep nesting", n, 1, |r| {
        let (p, t) = if r == n { &small } else { &large };
        std::hint::black_box((feasible(p, t), vector(p, t)));
    });
}
