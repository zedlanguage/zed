//! The benchmarks of `r5_hull_tests`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-crates). The correctness test that keeps a small instance of
//! what each checks besides the ratio is `the_benchmark_inputs_have_their_answers_at_small_sizes`;
//! the longer chains of the oracle are covered at small sizes by
//! `overlapping_chains_agree_with_independent_small_domains`.
//! Sizes are set (2026-11-14) so the 1x case takes about 0.3 to 1 s and a piece stays under
//! 20 s.

use super::*;

#[test]
fn different_reflection_centers_are_refuted_in_linear_work() {
    scaling::check_order(
        "overlapping guards and two reflection centers",
        1400,
        1,
        |n| {
            assert_eq!(decide(&formula(n, (n / 2 + 1) as i128, false)), Ok(false));
        },
    );
}

/// The odd lengths of the chain above, where the target is reached and a point is found by the
/// walk back from the target (PRES-hull-odd-refusal): sizes 2m + 1 for m = 700 and 5600.
#[test]
fn different_reflection_centers_with_a_point_are_answered_in_linear_work() {
    scaling::check_order(
        "overlapping guards and two reflection centers, odd lengths",
        700,
        1,
        |m| {
            let n = 2 * m + 1;
            assert_eq!(decide(&formula(n, (n / 2 + 1) as i128, false)), Ok(true));
        },
    );
}

#[test]
fn shifts_with_gaps_are_refuted_in_linear_work() {
    scaling::check_order("even shifts and an odd target", 1600, 1, |n| {
        assert_eq!(decide(&formula(n, 1, true)), Ok(false));
    });
}

/// The oracle of `overlapping_chains_agree_with_independent_small_domains` on the longer
/// chains it leaves out, the sizes it had before (TEST-bench-move-crates): unshifted at 8 steps,
/// shifted at 4, 5 and 8 (author P178: a long run). Measured 2026-11-14 at load 30: 0.76 s at 8
/// steps unshifted, 0.41 s, 1.1 s and 4.7 s shifted; since `chain_witness` (debug build, load
/// 33) 0.08 s, 0.13 s, 0.32 s and 0.80 s. A refusal fails the test, as in the small oracle
/// (PRES-overlap-six-steps).
#[test]
fn overlapping_chains_agree_with_independent_small_domains_on_longer_chains() {
    for (n, shift) in [(8, false), (4, true), (5, true), (8, true)] {
        let refused = overlapping_chain_agrees(n, shift);
        assert_eq!(
            refused, 0,
            "{n} steps, shift {shift}: {refused} targets refused"
        );
    }
}

/// `overlap2c_mid` (target 0, period-70 overlapping reflection guards) scales monotonically at
/// both 40 -> 320 and 80 -> 640 (HAS-point-probe R7 Q1).
#[test]
fn overlap2c_mid_scales_monotonically() {
    scaling::check_order("overlap2c_mid 40 to 320", 40, 1, |n| {
        assert_eq!(decide(&formula(n, 0, false)), Ok(true));
    });
    scaling::check_order("overlap2c_mid 80 to 640", 80, 1, |n| {
        assert_eq!(decide(&formula(n, 0, false)), Ok(true));
    });
}

/// `overlap2c` at target -23: main's single-pass forward `chain_witness` hit an early-prefix hole
/// at `i = 2` and fell back to `probe_to` (112.7 G at n = 160, 257.6 G at n = 320); 3-pass
/// interior-margin greedy walk closes 40 -> 320 in linear work (HAS-point-probe R7 Q1).
#[test]
fn overlap2c_target_neg23_scales_in_linear_work() {
    scaling::check_order("overlap2c target -23 (40 to 320)", 40, 1, |n| {
        assert_eq!(decide(&formula(n, -23, false)), Ok(n >= 80));
    });
}

/// `fork` after `forced`/`reduced` substitutes `q_n` into the final disjunction: main left the
/// redundant hull rows on `q_{n-1}` in `leftover_ineqs`, bailing out of `sweep_disjoint`
/// (163.1 G at n = 1000, R = 59.7); vacuous check 3 drops them in O(N) (HAS-point-probe R7 Q4).
#[test]
fn fork_with_forced_reduction_scales_in_linear_work() {
    scaling::check_order("fork with forced reduction (125 to 1000)", 125, 1, |n| {
        assert_eq!(decide(&fork_formula(n)), Ok(false));
    });
}
