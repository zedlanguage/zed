//! The benchmarks of `model.rs` (TEST-bench-move-l0138), run by `tools/run_tests.sh --bench`.

use crate::model::*;
use zed_tests::scaling;
use zedc::store::presburger::satisfiable;

/// The point of a round trip of 64 and of 512 steps, each up or down, built first.
#[test]
fn the_point_of_a_round_trip_scales() {
    let (small, large) = (round_trip(260), round_trip(scaling::FACTOR * 260));
    steps_down(260, &small);
    steps_down(scaling::FACTOR * 260, &large);
    scaling::check("the point of a round trip of steps up or down", 260, |m| {
        drop(satisfiable(if m == 260 { &small } else { &large }));
    });
}
