//! The benchmarks of `r5_orbit_tests`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-crates). The correctness test that keeps a small instance of
//! what each checks besides the ratio is `the_benchmark_inputs_have_their_answers_at_small_sizes`.
//! Sizes are set (2026-11-14) so the 1x case takes about 0.3 to 1 s and a piece stays under
//! 20 s.

use super::*;

#[test]
fn a_guard_on_two_inputs_and_one_reflection_center_scales() {
    scaling::check_order("a chain guarded by the sum of two inputs", 1200, 1, |n| {
        let target = ((n / 2 + 1) | 1) as i128;
        assert_eq!(decide(&formula(n, target, false, false)), Ok(false));
    });
}

#[test]
fn a_functional_two_input_chain_with_a_point_scales() {
    scaling::check_order("two-input chain with an interior point", 1200, 1, |n| {
        assert_eq!(decide(&formula(n, 0, false, false)), Ok(true));
    });
}
