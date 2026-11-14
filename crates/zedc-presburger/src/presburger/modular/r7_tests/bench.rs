//! The benchmarks of `r7_tests`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-crates). The correctness test that keeps a small instance of
//! what each checks besides the ratio is `the_benchmark_inputs_have_their_answers_at_small_sizes`.
//! Sizes are set (2026-11-14) so the 1x case takes about 0.3 to 1 s and a piece stays under
//! 20 s.

use super::*;

#[test]
fn pncx_fixed_chain_scale() {
    let inputs = scaling::inputs(60_000, fixed_chain);
    scaling::check_order("atoms fixed one after another", 60_000, 1, |n| {
        assert!(matches!(solve_modular(&inputs[&n], false), Some(Some(_))));
    });
}
