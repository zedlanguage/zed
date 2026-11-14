//! The time to solve a slowly settling recurrence, the same at every start magnitude, since the
//! widening stops at the solved landmark with no iteration per step. The bound found and the
//! count of evaluations at three magnitudes are checked by the test of the same name in
//! `invariant.rs`.

use zed_tests::scaling;
use zedc::store::interval::IntervalSet;

use crate::invariant::Recurrence;

#[test]
fn a_slowly_settling_coefficient_is_solved_without_a_step_per_iteration() {
    let inputs = scaling::inputs(1_000_000_000, |n| {
        Recurrence::new(1023, 1024, (-100, 100), IntervalSet::single(n as i64))
    });
    scaling::check(
        "solving y' = (1023 * y) div 1024 + x from a start of magnitude n",
        1_000_000_000,
        |n| {
            inputs[&n].solve();
        },
    );
}
