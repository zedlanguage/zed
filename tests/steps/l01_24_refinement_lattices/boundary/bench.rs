//! The benchmarks of `boundary.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `boundary.rs`.

use super::*;

// The two checks below were one test, `negating_a_kept_sum_scales_with_its_terms`, both at
// n = 200; each is now a test of its own (TEST-bench-move-l0123, author P169).

/// The negation of a kept value of `n` terms, checked against the edge `2^127`, costs the
/// terms, not their product or the digits of the value.
/// TEST-bench-move-l0123, author P169: n was 200, now 6000; 1x 9.3 ms at load 27.
#[test]
fn negating_a_kept_sum_scales_with_its_terms() {
    let n = 6000;
    let sums = scaling::inputs(n, |m| kept_sum(0, m));
    scaling::check("negating a kept sum of n powers", n, |m| {
        let neg = -&sums[&m];
        assert!(neg.signum() < 0);
    });
}

/// A quotient by a negative divisor negates both first, then takes residues of the terms.
/// TEST-bench-move-l0123, author P169: n was 200, now 6000; 1x 58.7 ms at load 60.
#[test]
fn dividing_a_kept_sum_by_a_negative_divisor_scales_with_its_terms() {
    let n = 6000;
    let sums = scaling::inputs(n, |m| kept_sum(0, m));
    scaling::check("a kept sum of n powers over a negative divisor", n, |m| {
        let q = sums[&m].div_floor(&Num::from(-7));
        assert!(q.signum() < 0);
    });
}
