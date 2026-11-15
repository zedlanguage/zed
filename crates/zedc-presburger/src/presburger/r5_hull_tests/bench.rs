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
/// steps unshifted, 0.41 s, 1.1 s and 4.7 s shifted.
#[test]
fn overlapping_chains_agree_with_independent_small_domains_on_longer_chains() {
    let refused: usize = [(8, false), (4, true), (5, true), (8, true)]
        .into_iter()
        .map(|(n, shift)| overlapping_chain_agrees(n, shift))
        .sum();
    eprintln!("overlapping-chain oracle on longer chains: refused={refused}");
}
