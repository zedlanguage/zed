//! The benchmarks of `r5_shared_arm_tests`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-crates). The correctness test that keeps a small instance of
//! what each checks besides the ratio is `the_benchmark_inputs_have_their_answers_at_small_sizes`.
//! Sizes are set (2026-11-14) so the 1x case takes about 0.3 to 1 s and a piece stays under
//! 20 s.

use super::*;

#[test]
fn shared_flat_arms_with_many_guard_rows_are_read_once() {
    scaling::check_order(
        "shared flat arms with redundant guard rows",
        125_000,
        1,
        |n| {
            assert!(GuardedChain::of(&parts(n, false)).is_some());
        },
    );
}
