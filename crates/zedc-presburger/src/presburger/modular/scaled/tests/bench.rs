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

/// [`solve_modular_or_scaled`] on [`bench_coprime_sums`] with `k = n` and `8n` rows over the
/// first odd primes, and two sums of all their quotients modulo 2 with no common point
/// (PRES-sum-of-quotients-period-product, part 1): the residues of `x` the sums' literals
/// become number `2 prod_i p_i`, exponential in `k` ([`sum_residues`], which declines once
/// that passes a word, and then the formula went unanswered); decided over the 4 tuples of
/// the sums' remainders ([`sumset`]), the work is linear in `k`. Under a question's meter with
/// no limit, as [`sumset`] runs only under one.
#[test]
fn sums_over_many_coprime_moduli_scale() {
    let inputs = scaling::inputs(N_COPRIME, |n| bench_coprime_sums(n, false).2);
    scaling::check_order("two sums over k coprime moduli", N_COPRIME, 1, |n| {
        let got = metered(u64::MAX, || solve_modular_or_scaled(&inputs[&n], false));
        assert!(matches!(got, Ok(Some(None))))
    });
}

/// [`solve_modular_or_scaled`] on [`bench_many_sums`] with 21 rows in 20 blocks (the first 20
/// odd primes, and a second row of modulus 3 in the block of 3) and `j = n` and `8n` sums
/// modulo 2 with no common point (META1 A3 of XR-presburger4): the sums' tuples number `2^j`,
/// but [`sumset`] holds only the two reached, so the work is O(j) a block, linear in `j`, where
/// a table of all the tuples would be exponential in `j`. Under a question's meter with no
/// limit.
#[test]
fn sums_over_many_moduli_two_scale() {
    let inputs = scaling::inputs(N_TWO, |n| bench_many_sums(20, n, false).2);
    scaling::check_order("j sums modulo 2 over 21 rows", N_TWO, 1, |n| {
        let got = metered(u64::MAX, || solve_modular_or_scaled(&inputs[&n], false));
        assert!(matches!(got, Ok(Some(None))))
    });
}

/// [`solve_modular_or_scaled`] on [`constant_sums`] with `k = n` and `8n` (XR-presburger4 round
/// 2 P2, Codex): `k` sums that are 0 at every `x` beside one sum over all the rows. Each pair of
/// tuples added all `k + 1` coordinates, Θ(k²) word additions over the `k + 1` blocks; with the
/// constant coordinates read once and left out of the tuples, linear in `k`. With a point, so
/// that [`sumset`] is reached and selected (META4 order 10, Codex: without one the literal on the
/// last fixed sum is read as false before the costs, and the path's work was never timed).
#[test]
fn constant_sums_beside_a_dense_sum_scale() {
    let inputs = scaling::inputs(N_CONSTANT, |n| constant_sums(n, true).2);
    scaling::check_order("k constant sums beside a dense sum", N_CONSTANT, 1, |n| {
        by_sumset(&inputs[&n], |got| matches!(got, Some(Some(_))))
    });
}

// Gemini's P-A ([`rows_of_one_remainder`]) and Codex's unread remainders
// ([`unread_remainders`]) have no wall-time benchmark here (META4 order 2 of b22-presburger6):
// timed at `k = 15` and 120 both passed with the fixes off (job j1 of b22-presburger5's lists),
// as the Θ(k²) or Θ(k m) term is a few thousand steps beside the build of the formula. The unit
// counts of `rows_of_one_remainder_leave_the_coordinates` and
// `remainders_no_literal_reads_are_not_filled` read the path's own charges, a word per
// coordinate copied and per place filled, at the same sizes with limit 9, and fail with the
// fixes off (jobs j5c and j6c of b22-presburger6: the first, with rows of one allowed value
// not folded into `B_j`, 38,912 -> 1,922,192 units, 49.4 times; the second, with the
// constant literals not folded, 15,456 -> 726,096 units, 47 times, as on 42ec4cc36, where the
// bounds `0 <= r_j <= m - 1` still made every remainder read).

/// [`solve_modular_or_scaled`] on [`bench_many_sums`] with 3 rows in 2 blocks and `j = n` and
/// `8n` sums modulo 2 (XR-presburger4 round 2 P3, Codex and Gemini): the size of the group of
/// tuples, `2^j`, built one radix at a time, was Θ(j²) bit work (62.25 times from 2,000 to
/// 16,000 on Gemini's extraction), above the path's own linear work with so few rows; the estimate
/// of the costs now holds it in a saturating machine word, O(j) (round 3 P3).
#[test]
fn many_sums_over_few_rows_scale() {
    let inputs = scaling::inputs(N_FEW_ROWS, |n| bench_many_sums(2, n, false).2);
    scaling::check_order("j sums modulo 2 over 3 rows", N_FEW_ROWS, 1, |n| {
        let got = metered(u64::MAX, || solve_modular_or_scaled(&inputs[&n], false));
        assert!(matches!(got, Ok(Some(None))))
    });
}

/// The size of [`many_sums_over_few_rows_scale`].
const N_FEW_ROWS: usize = 2_000;

/// The size of [`constant_sums_beside_a_dense_sum_scale`].
const N_CONSTANT: usize = 400;

/// The size of [`sums_over_many_moduli_two_scale`].
const N_TWO: usize = 100;

/// The size of [`sums_over_many_coprime_moduli_scale`].
const N_COPRIME: usize = 200;

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

/// Runs `solve_modular_or_scaled` on `f` under a question's meter with no limit, asserts its
/// answer with `ok`, and that [`sumset`] was selected, so that no other path that answers first
/// can hide the path's work (XR-presburger4 round 3, Codex).
fn by_sumset(f: &Formula, ok: impl Fn(&Option<Option<Model>>) -> bool) {
    let before = sumset::SELECTED.with(std::cell::Cell::get);
    let got = metered(u64::MAX, || solve_modular_or_scaled(f, false)).expect("no limit");
    assert!(ok(&got), "{got:?}");
    assert!(sumset::SELECTED.with(std::cell::Cell::get) > before);
}

/// The rows of [`missing_residue`] in the benchmarks: primes above `8 N_MISSING`, so each row's
/// remainder takes every residue modulo `M` at both sizes.
const MISSING_ROWS: [i64; 3] = [3_203, 3_209, 3_217];

/// [`missing_residue`] with every row capped, at `M = n` and `8n` (XR-presburger4 round 3 P1,
/// Claude): `R` and `W_b` of the second block have `M - 1` tuples each, Θ(M²) pairs on
/// bf91c3aef; by the product of polynomials ([`zed_kernel::num::mul_uint`], transforms above
/// `MUL_LEAF` = 400 words, so both sizes take the same method: `L = 2 M - 1` is 799 and 6,399 words), O(M log M).
#[test]
fn a_sum_missing_one_residue_scale() {
    let inputs = scaling::inputs(N_MISSING, |n| {
        missing_residue(MISSING_ROWS, n as i64, [true; 3], &[0])
    });
    scaling::check_order("a sum modulo M missing a residue", N_MISSING, 1, |n| {
        by_sumset(&inputs[&n], |got| matches!(got, Some(Some(_))))
    });
}

/// [`missing_residue`] with the sums `E` and `E + 1` and no row capped, at `M = n` and `8n`
/// (XR-presburger4 round 3, Gemini's break A): the two sums share one coordinate, whose `W_b` is
/// the whole group, so the work is linear in `M`; held as two coordinates, Θ(M²) pairs.
#[test]
fn two_sums_of_one_direction_scale() {
    let inputs = scaling::inputs(N_MISSING, |n| {
        missing_residue(MISSING_ROWS, n as i64, [false; 3], &[0, 1])
    });
    scaling::check_order("two sums of one direction modulo M", N_MISSING, 1, |n| {
        by_sumset(&inputs[&n], |got| matches!(got, Some(Some(_))))
    });
}

/// [`moved_by_x_alone`] at `k = n` and `8n` (XR-presburger4 round 3 P2, Gemini): `k` sums moved
/// by `t_0` alone share one class coordinate, so each block copies O(1) words a tuple, and the
/// work is linear in `k`; held as `k` coordinates, Θ(k²).
#[test]
fn sums_moved_by_x_alone_scale() {
    let inputs = scaling::inputs(N_BY_X, moved_by_x_alone);
    scaling::check_order("k sums moved by x alone", N_BY_X, 1, |n| {
        by_sumset(&inputs[&n], |got| matches!(got, Some(None)))
    });
}

/// [`fixed_literals`] at `k = m = n` and `8n` (XR-presburger4 round 3 P2, Codex): the literals on
/// the `k` fixed sums are read once, so the clause read at each of the `m` tuples is one literal;
/// read at every tuple, Θ(m k).
#[test]
fn fixed_literals_beside_a_live_sum_scale() {
    let inputs = scaling::inputs(N_MISSING, |n| {
        fixed_literals([MISSING_ROWS[0], MISSING_ROWS[1]], n, n as i64)
    });
    scaling::check_order(
        "k fixed literals beside a sum modulo m",
        N_MISSING,
        1,
        |n| by_sumset(&inputs[&n], |got| matches!(got, Some(Some(_)))),
    );
}

/// The size of [`a_sum_missing_one_residue_scale`], [`two_sums_of_one_direction_scale`] and
/// [`fixed_literals_beside_a_live_sum_scale`].
const N_MISSING: usize = 400;

/// The size of [`sums_moved_by_x_alone_scale`].
const N_BY_X: usize = 100;
