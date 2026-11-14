//! The benchmarks of `boundary.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `boundary.rs`.

use super::*;

/// The negation of a kept value of `n` terms, checked against the edge `2^127`, costs the
/// terms, not their product or the digits of the value.
#[test]
fn negating_a_kept_sum_scales_with_its_terms() {
    /// `b ^ 200` over the odd `b` from `3 + 2 * lo` to below `3 + 2 * hi`, added in halves so
    /// that building it costs `n log n` term operations.
    fn sum(lo: usize, hi: usize) -> Num {
        if hi - lo == 1 {
            return Num::from(3 + 2 * lo as i64).pow(200);
        }
        let mid = lo + (hi - lo) / 2;
        &sum(lo, mid) + &sum(mid, hi)
    }
    let sums = [sum(0, 200), sum(0, 1600)];
    scaling::check("negating a kept sum of n powers", 200, |n| {
        let s = &sums[usize::from(n != 200)];
        let neg = -s;
        assert!(neg.signum() < 0);
    });
    // A quotient by a negative divisor negates both first, then takes residues of the terms.
    scaling::check("a kept sum of n powers over a negative divisor", 200, |n| {
        let s = &sums[usize::from(n != 200)];
        let q = s.div_floor(&Num::from(-7));
        assert!(q.signum() < 0);
    });
}
