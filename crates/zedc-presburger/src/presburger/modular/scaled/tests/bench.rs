//! The benchmark of `scaled::tests`, run by `tools/run_tests.sh --bench` and left out of its
//! default run. The correctness test that keeps a small instance of it is
//! `the_benchmark_inputs_have_their_answers_at_small_sizes`.

use super::*;

/// [`solve_modular_or_scaled`] on [`bench_modulus`] at modulus `m = n` and `8n`: the costly
/// case of a scaled remainder, whose literals pull back to about `m / 3` runs of residues of
/// `x`, so the work is at least linear in `m`.
#[test]
fn scaled_remainders_scale_in_the_modulus() {
    let inputs = scaling::inputs(N_MODULUS, |n| bench_modulus(n as i64).1);
    scaling::check_order("a scaled remainder of modulus m", N_MODULUS, 1, |n| {
        assert!(matches!(
            solve_modular_or_scaled(&inputs[&n], false),
            Some(Some(_))
        ))
    });
}

/// The size of [`scaled_remainders_scale_in_the_modulus`].
const N_MODULUS: usize = 20_000;
