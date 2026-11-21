//! The benchmarks of `scaled::tests`, run by `tools/run_tests.sh --bench` and left out of its
//! default run. The correctness test that keeps a small instance of each is
//! `the_benchmark_inputs_have_their_answers_at_small_sizes`.

use super::*;

/// [`solve_modular`] on [`bench_modulus`] at modulus `m = n` and `8n`: the costly case of a
/// scaled remainder, whose literals pull back to about `m / 3` runs of residues of `x`, so the
/// work is at least linear in `m`.
#[test]
fn scaled_remainders_scale_in_the_modulus() {
    let inputs = scaling::inputs(N_MODULUS, |n| bench_modulus(n as i64).1);
    scaling::check_order("a scaled remainder of modulus m", N_MODULUS, 1, |n| {
        assert!(matches!(solve_modular(&inputs[&n], false), Some(Some(_))))
    });
}

/// The size of [`scaled_remainders_scale_in_the_modulus`].
const N_MODULUS: usize = 20_000;

/// [`solve_modular`] on [`bench_depth`] at `n` and `8n` levels of quotients, with a literal
/// on each level: each literal pulls back in one step by its flat form (Lemma C), on numbers of
/// about `n log2(3)` bits.
#[test]
fn nested_quotients_scale_in_the_depth() {
    let inputs = scaling::inputs(N_DEPTH, |n| bench_depth(n).1);
    scaling::check_order("n nested quotients", N_DEPTH, 1, |n| {
        assert!(matches!(solve_modular(&inputs[&n], false), Some(Some(_))))
    });
}

/// The size of [`nested_quotients_scale_in_the_depth`].
const N_DEPTH: usize = 200;
