//! A cycle of `n` functions, reported and checked at `n` and `8n` (`recursion.rs`).

use zed_tests::scaling;

use crate::recursion::{a_long_cycle, a_long_cycle_checked, the_report_of_a_long_cycle};

/// The report of the cycle with its n uses, from a unit already resolved. One search with a
/// visited set, each use placed by binary search, `O(n log n)`.
#[test]
fn the_report_of_a_long_cycle_scales() {
    let n = 6900;
    let units = scaling::inputs(n, a_long_cycle);
    scaling::check_order("the report of a cycle of n functions", n, 1, |k| {
        the_report_of_a_long_cycle(&units[&k], k);
    });
}

/// The same cycle through the whole checker, which reports it with its n uses.
#[test]
fn checking_a_long_cycle_scales() {
    let n = 6200;
    let units = scaling::inputs(n, a_long_cycle);
    scaling::check_order("checking a cycle of n functions", n, 1, |k| {
        a_long_cycle_checked(&units[&k], k);
    });
}
