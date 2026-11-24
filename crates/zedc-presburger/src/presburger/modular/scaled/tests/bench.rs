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

/// [`solve_modular_or_scaled`] on [`bench_sum`] at modulus `m = n` and `8n`: a sum of two
/// quotients whose remainder's literals become residues of `x` modulo `15 m`
/// ([`sum_residues`], O(m) steps), so the work is at least linear in `m`.
#[test]
fn sums_of_quotients_scale() {
    let inputs = scaling::inputs(N_SUM, |n| bench_sum(n as i64).1);
    scaling::check_order("a sum of quotients modulo m", N_SUM, 1, |n| {
        assert!(matches!(
            solve_modular_or_scaled(&inputs[&n], false),
            Some(None)
        ))
    });
}

/// [`four_pairs`] and `n` constraints `(i + 1) x + q0 - q2 + r1 >= -10`, each on its own
/// combination, with `r1 == r3 || r1 == r3 + 2`: `r1 = (x - 2) mod 4` and `r3 = (x - 7) mod 4`
/// differ by 1 modulo 4, so there is no point, and the period sweep (`sweep.rs`) folds every
/// constraint at each of the 20 residues of `lcm(5, 4)`. The disjunction keeps `r1 == r3` off
/// the top level, where it would read as a definition row of modulus 1 ([`read_shape`]).
fn bench_sweep(n: usize) -> Formula {
    let divs = four_pairs();
    let mut lits = Vec::with_capacity(n + 1);
    for i in 0..n {
        let sum = x()
            .times(i as i64 + 1)
            .plus(&q(0))
            .plus(&q(2).times(-1))
            .plus(&r(1));
        lits.push(Formula::Con(Con::ge(&sum, &Lin::constant(-10))));
    }
    lits.push(Formula::or(vec![
        Formula::Con(Con::eq(&r(1), &r(3))),
        Formula::Con(Con::eq(&r(1), &r(3).plus(&Lin::constant(2)))),
    ]));
    formula(&divs, Formula::and(lits), vec![])
}

/// The period sweep on [`bench_sweep`] at `n` and `8n` constraints: O(L n) for the fixed period
/// `L = 20`, so linear in `n`. Negative control: the same runs with the run at `8n` done eight
/// times, as a sweep that read every constraint once per constraint would cost, are over the
/// limit, so the check can fail on this input.
#[test]
fn the_period_sweep_scales_in_the_constraints() {
    let inputs = scaling::inputs(N_SWEEP, bench_sweep);
    let run = |n: usize| {
        assert_eq!(sweep::solve_after_refusal(&inputs[&n], false), Some(None));
    };
    scaling::check("the period sweep over n constraints", N_SWEEP, run);
    let mut meter = scaling::Meter::new();
    let small = meter.work(|| run(N_SWEEP)).units;
    let large = meter
        .work(|| {
            for _ in 0..8 {
                run(8 * N_SWEEP);
            }
        })
        .units;
    let ratio = large as f64 / small as f64;
    assert!(
        ratio >= scaling::limit(1),
        "the negative control passed: {small} and {large} instructions, {ratio:.2} times"
    );
}

/// The runs on [`bench_runs`] at `n` and `8n` constraints: O(P n) for the fixed count `P` of
/// points, so linear in `n`. Negative control: the run at `8n` done eight times, as a method
/// that read every constraint once per constraint would cost, is over the limit.
#[test]
fn the_runs_scale_in_the_constraints() {
    let inputs = scaling::inputs(N_RUNS, bench_runs);
    let run = |n: usize| assert_eq!(sweep::solve_after_refusal(&inputs[&n], false), Some(None));
    scaling::check("the runs over n constraints", N_RUNS, run);
    let mut meter = scaling::Meter::new();
    let small = meter.work(|| run(N_RUNS)).units;
    let large = meter
        .work(|| {
            for _ in 0..8 {
                run(8 * N_RUNS);
            }
        })
        .units;
    let ratio = large as f64 / small as f64;
    assert!(
        ratio >= scaling::limit(1),
        "the negative control passed: {small} and {large} instructions, {ratio:.2} times"
    );
}

/// The size of [`the_runs_scale_in_the_constraints`]: at `8n` the count of units, about
/// `(window + 202) (8n + 13)`, stays under `PERIOD_SWEEP_AFTER_REFUSAL_UNITS`, the bound of
/// `sweep::solve_after_refusal`, which the benchmark calls (past `PERIOD_SWEEP_SWITCHOVER` at
/// `8n`).
const N_RUNS: usize = 50;

/// The size of [`the_period_sweep_scales_in_the_constraints`]: at `8n` the sweep's count of
/// units (about `2 * 20 * 8n`) stays under `PERIOD_SWEEP_AFTER_REFUSAL_UNITS`, the bound of
/// `sweep::solve_after_refusal`, which the benchmark calls.
const N_SWEEP: usize = 1_000;

/// The size of [`sums_of_quotients_scale`].
const N_SUM: usize = 2_000;

/// The size of [`scaled_remainders_scale_in_the_modulus`].
const N_MODULUS: usize = 20_000;
