//! The benchmarks of `probe_order`, run by `tools/run_tests.sh --bench` and left out of its
//! default run. Their small instance is `probe_keeps_the_points_of_random_boxed_formulas`, 300
//! formulas.

use super::*;

/// The LIN-probe battery of plan row TESTS-random-batteries-to-size: 3000 random boxed
/// formulas against every point of their box, in three pieces of `PIECE`, each from a seed of
/// its own.
const PIECE: usize = 1000;

fn piece(k: usize) {
    crate::scaling::timed(&format!("{PIECE} boxed formulas, piece {k}"), || {
        probe_keeps_the_points_of_the_box(
            &format!("probe keeps the points of the box, piece {k}"),
            PIECE,
        )
    });
}

#[test]
fn probe_keeps_the_points_of_3000_random_boxed_formulas_0() {
    piece(0);
}

#[test]
fn probe_keeps_the_points_of_3000_random_boxed_formulas_1() {
    piece(1);
}

#[test]
fn probe_keeps_the_points_of_3000_random_boxed_formulas_2() {
    piece(2);
}
