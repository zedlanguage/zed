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

/// `model::satisfiable_agrees_with_decide_on_disjunctions_of_unit_rows` as first written,
/// 1.46 s (2026-11-14, load 25): 400 formulas of seed 0x9eed1.
#[test]
fn satisfiable_agrees_with_decide_on_the_400_disjunctions_of_unit_rows_of_seed_0x9eed1() {
    let c = unit_row_disjunctions_agree(&mut zed_tests::instances::Rng::new(0x9_eed1), 400);
    // 191 with a point, 209 without and none refused on 2026-11-14: a new refusal fails.
    assert!(c.with > 100 && c.without > 100 && c.refused == 0, "{c:?}");
}
