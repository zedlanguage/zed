//! The benchmarks of `model.rs` (TEST-bench-move-l0138), run by `tools/run_tests.sh --bench`.

use crate::model::*;
use zed_tests::scaling;
use zedc::store::presburger::satisfiable;

/// The point of a round trip of 64 and of 512 steps, each up or down, built first.
#[test]
fn the_point_of_a_round_trip_scales() {
    let (small, large) = (round_trip(390), round_trip(scaling::FACTOR * 390));
    steps_down(390, &small);
    steps_down(scaling::FACTOR * 390, &large);
    scaling::check("the point of a round trip of steps up or down", 390, |m| {
        drop(satisfiable(if m == 390 { &small } else { &large }));
    });
}
