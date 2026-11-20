//! The benchmarks of `threshold::tests`, run by `tools/run_tests.sh --bench` and left out of its
//! default run. Written by the proofs-in-comments audit (proofdoc4b, entry 37a8466a1).

use super::super::*;

/// `n` base upper bounds on one name whose values are `n` points `0, 2, ..., 2n - 2`, each bound
/// odd and below the last, so each one lowers the name's greatest value to the point below it:
/// [`floor`] is called `n` times on a set of `n` pieces. With `floor` built on
/// `IntervalSet::neg`, O(P) a call, the solve cost O(n^2); with the O(log P) lookups it is
/// O(n log n).
#[test]
fn many_upper_bounds_on_a_name_of_many_pieces_cost_near_linear_time() {
    let make = |n: usize| {
        let n = n as i64;
        System {
            names: vec![IntervalSet::from_pieces(
                (0..n)
                    .map(|i| (End::Fin(Num::from(2 * i)), End::Fin(Num::from(2 * i))))
                    .collect(),
            )],
            hub: IntervalSet::single(0),
            parts: vec![],
            uppers: (0..n)
                .map(|i| Upper {
                    x: 0,
                    k: Int::ZERO,
                    a: Int::from(2 * (n - i) - 1),
                })
                .collect(),
            lowers: vec![],
        }
    };
    // The input is built inside the timed run, O(n log n), as `scaling::inputs` is not used
    // in this crate (the `expect(dead_code)` on `mod scaling` in lib.rs).
    // The size 2,000 (and 16,000): measured 2026-11-20 at load 58, the run with the O(log P)
    // `floor` took 4.6 ms and 27 ms (6.7 and 57.8 million instructions, ratio 8.6); with the
    // old `floor` on `IntervalSet::neg` the same sizes did not finish in 60 s, so the size is
    // small enough for the 1x case to stay well under the piece limit when the cost is
    // quadratic again, and large enough for the O(n log n) ratio to show.
    crate::scaling::check(
        "threshold, n upper bounds on a name of n pieces",
        2_000,
        |m| {
            drop(solve(&make(m)));
        },
    );
}
