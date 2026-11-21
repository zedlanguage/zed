//! The benchmarks of `r7_tests`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-crates). The correctness test that keeps a small instance of
//! what each checks besides the ratio is `the_benchmark_inputs_have_their_answers_at_small_sizes`.
//! Sizes are set (2026-11-14) so the 1x case takes about 0.3 to 1 s and a piece stays under
//! 20 s.

use super::*;

/// What `solve` adds where the Omega test refuses (FAIL-one-scope-pairs-seed-refusal), on
/// [`division_pairs`]: one run of the modular solver and one check of each row at its point.
/// The refused run of the Omega test before it is not timed here; it grows faster on these
/// systems (FAIL-omega-pairs-shadows-cost).
#[test]
fn division_pairs_scale() {
    let inputs = scaling::inputs(N_PAIRS, division_pairs);
    scaling::check_order("division pairs answered past a refusal", N_PAIRS, 1, |n| {
        assert!(crate::presburger::point_past_refusal(&inputs[&n]).is_some());
    });
}

/// The size of [`division_pairs_scale`].
const N_PAIRS: usize = 10_000;

/// The whole of `solve` on [`division_pairs`], which the Omega test refuses
/// (FAIL-omega-pairs-shadows-cost): its run up to the splinters, which it defers, and the
/// modular solver's point. The search of the splinters it skips was quadratic here.
#[test]
fn division_pairs_refused_scale() {
    let inputs = scaling::inputs(N_REFUSED, division_pairs);
    scaling::check_order("division pairs answered by solve", N_REFUSED, 1, |n| {
        assert!(matches!(
            crate::presburger::solve(&inputs[&n], false),
            Ok(Some(_))
        ));
    });
}

/// The size of [`division_pairs_refused_scale`].
const N_REFUSED: usize = 4_000;

/// Dropping the clauses a regime's units imply (FAIL-modular-unbounded-regime-undecided), on
/// [`absorbed_clauses`]: `n` clauses, each with the unit's own literal, so all are dropped and
/// the regime is the unit alone.
#[test]
fn absorbed_clauses_scale() {
    let inputs = scaling::inputs(N_ABSORBED, absorbed_clauses);
    scaling::check_order("clauses the units imply dropped", N_ABSORBED, 1, |n| {
        let (units, clauses) = inputs[&n].clone();
        assert!(found(&solve_regime_in(&None, &None, units, clauses)).is_some());
    });
}

/// The size of [`absorbed_clauses_scale`].
const N_ABSORBED: usize = 20_000;

/// `sweep_bounded` on [`wide_clauses`] emptied, a window of 100 periods of `P` from 2^200 on,
/// with `n` clauses (PERF-sweep-bounded-wide-interval): the small moduli read modulo 180, about
/// 50 pieces of each clause's large modulus, so `O(n log n)` events and `O(n)` additions to the
/// tree of 180 residues. Cutting every modulus into pieces made about 2^105 here.
#[test]
fn clauses_over_a_window_of_200_bits_scale() {
    let inputs = scaling::inputs(N_WIDE_CLAUSES, |n| wide_clauses(n, 100, true));
    scaling::check_order(
        "clauses over a window of 200 bits",
        N_WIDE_CLAUSES,
        1,
        |n| {
            let (l, h, units, clauses) = &inputs[&n];
            assert!(matches!(
                sweep_bounded(l, h, units, clauses),
                RegimeOut::Empty
            ));
        },
    );
}

/// The size of [`clauses_over_a_window_of_200_bits_scale`].
const N_WIDE_CLAUSES: usize = 2_000;

/// `sweep_bounded` on [`wide_clauses`] emptied, with 20 clauses, over `n` periods of `P`
/// (PERF-sweep-bounded-wide-interval): the pieces of the large moduli, and so the events, grow
/// with the width of the window while its bits grow by 3, the wide interval of the row.
#[test]
fn a_window_of_n_periods_scale() {
    let inputs = scaling::inputs(N_PERIODS, |n| wide_clauses(20, n as i64, true));
    scaling::check_order("a window of n periods", N_PERIODS, 1, |n| {
        let (l, h, units, clauses) = &inputs[&n];
        assert!(matches!(
            sweep_bounded(l, h, units, clauses),
            RegimeOut::Empty
        ));
    });
}

/// The size of [`a_window_of_n_periods_scale`].
const N_PERIODS: usize = 5_000;

/// A regime with one bound that the coprime base leaves undecided, swept on one period of its
/// moduli past the bound (FAIL-omega-negations-slow-7837918895420161952), on
/// [`one_bound_clauses`] with `n` clauses more: the period stays 4,680, so each clause adds a
/// fixed number of events, about `4680 / 4 + 4680 / 9` pieces of its moduli, which the split
/// chosen reads as large ones. Each event is one pop of [`LargeMerge`]'s heap, which holds one
/// waiting event per run, so `Theta(n)` of them: the work is `Theta(n log n)`, predicted at 8n
/// as `8 log(32,000) / log(4,000)`, about 10.0 for the heap alone. Measured 2026-11-20 (load 53):
/// 7.62e9 and 6.91e10 instructions, 9.06 times, 99% of it in `LargeMerge::next_change` and 62%
/// in its heap's `pop` (perf, cycles), so the ratio is that `n log n` (P300); 8.0 times the bytes.
#[test]
fn a_regime_with_one_bound_and_n_clauses_scales() {
    let inputs = scaling::inputs(N_ONE_BOUND, one_bound_clauses);
    scaling::check_order("a regime with one bound", N_ONE_BOUND, 1, |n| {
        let (l, units, clauses) = inputs[&n].clone();
        assert!(matches!(
            solve_regime_in(&Some(l), &None, units, clauses),
            RegimeOut::Empty
        ));
    });
}

/// The size of [`a_regime_with_one_bound_and_n_clauses_scales`].
const N_ONE_BOUND: usize = 2_000;

/// The peak bytes `sweep_bounded` holds on [`a_window_of_n_periods_scale`]'s inputs at `n` and
/// at `8n` periods are within twice each other (PERF-sweep-lazy-pieces): the pieces of the large
/// moduli are made one waiting event per run at a time ([`LargeMerge`]), so the memory is
/// O(runs + lists + q), the same at both sizes, where making all `P` pieces first held Θ(P),
/// about 8 times as much at `8n`. The total allocated (the `bytes` of `check_order`) still
/// grows with `P`, as each event makes its place's `Int`s, so it cannot show this.
#[test]
fn a_window_of_n_periods_peak_bytes_stay_flat() {
    let peak = |n: usize| {
        let (l, h, units, clauses) = wide_clauses(20, n as i64, true);
        let (out, live) = zed_alloc_count::live(|| sweep_bounded(&l, &h, &units, &clauses));
        assert!(matches!(out, RegimeOut::Empty));
        live.peak
    };
    let (small, large) = (peak(N_PERIODS), peak(8 * N_PERIODS));
    eprintln!("bench a window of n periods, peak bytes: n={N_PERIODS} peak={small}/{large}");
    assert!(
        large < 2 * small,
        "peak bytes {small} at n = {N_PERIODS} and {large} at 8n"
    );
}

#[test]
fn pncx_fixed_chain_scale() {
    let inputs = scaling::inputs(60_000, fixed_chain);
    scaling::check_order("atoms fixed one after another", 60_000, 1, |n| {
        assert!(matches!(solve_modular(&inputs[&n], false), Some(Some(_))));
    });
}
