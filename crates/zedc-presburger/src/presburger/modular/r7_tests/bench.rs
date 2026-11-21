//! The benchmarks of `r7_tests`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-crates). The correctness test that keeps a small instance of
//! what each checks besides the ratio is `the_benchmark_inputs_have_their_answers_at_small_sizes`.
//! Sizes are set (2026-11-14) so the 1x case takes about 0.3 to 1 s and a piece stays under
//! 20 s.

use super::*;

/// What `solve` adds where the Omega test refuses (FAIL-one-scope-pairs-seed-refusal), on
/// [`division_pairs`]: one run of the modular solver and one check of each row at its point,
/// called directly. Since FAIL-presburger-fresh-seed-refusals the Omega test answers these
/// systems itself, so `solve` no longer reaches this step on them; the step is timed here on
/// them as before.
#[test]
fn division_pairs_scale() {
    let inputs = scaling::inputs(N_PAIRS, division_pairs);
    scaling::check_order("division pairs answered past a refusal", N_PAIRS, 1, |n| {
        assert!(crate::presburger::point_past_refusal(&inputs[&n]).is_some());
    });
}

/// The size of [`division_pairs_scale`].
const N_PAIRS: usize = 10_000;

/// The whole of `solve` on [`division_pairs`]. Until FAIL-presburger-fresh-seed-refusals the
/// Omega test refused them (FAIL-omega-pairs-shadows-cost), and this timed its run up to the
/// splinters, which it defers, and the modular solver's point; the search of the splinters it
/// skips was quadratic here. Since then the Omega test takes the lossless stage of
/// `Omega::run` on them and answers with a point itself (checked from 7 to 16 pairs by
/// `division_pairs_have_their_point_found`).
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
/// fixed number of list changes, about `4680 / 4 + 4680 / 9` pieces of its moduli, which the
/// split chosen reads as large ones. Until FAIL-main-4af88445a [`LargeMerge`]'s heap held a run
/// per literal, `2 n` of them, each event a pop: `Theta(n log n)` work, measured 2026-11-20
/// (load 53) at 7.62e9 and 6.91e10 instructions, 9.06 times, 62% in the heap's `pop`; and the
/// sweep took 25.7 s at 16,000 (2026-11-21, load 45), past its phase's time limit. The `n`
/// clauses hold 13 intervals of residues between them, and a run is now one per interval, held
/// by every list that holds it (its proof (4)): 28 runs at every `n >= 9`
/// (`r7_tests::literals_with_one_interval_share_one_run`), so the events are fixed in `n` and
/// each changes the counts of the `Theta(n)` lists of its run, `Theta(n)` in all. Measured
/// 2026-11-21 (load 46): 4.46e8 and 3.28e9 instructions, 7.366 times, 91 ms and 383 ms, 7.8
/// times the bytes; the piece took 0.95 s, against 25.9 s to 36.7 s before.
///
/// Since [`SWEEP_SWITCHOVER`] the regime itself goes to the general path at these sizes (its
/// bound is 10,187,473 at n = 2,000), which decides its formula in 1.9 ms at n = 2,000 and
/// 17.6 ms at 16,000, where this sweep took 1.0 s and 25.7 s (2026-11-21, load 45). So this
/// bench calls [`sweep_bounded`] on the window `[l, l + p - 1]` directly: the sweep still runs
/// for a bounded regime the base writes and for one under the switchover, and its scaling is
/// what is checked here.
#[test]
fn a_regime_with_one_bound_and_n_clauses_scales() {
    let inputs = scaling::inputs(N_ONE_BOUND, |n| {
        let (l, units, clauses) = one_bound_clauses(n);
        let h = &(&l + &period_of(&units, &clauses)) - &Int::ONE;
        (l, h, units, clauses)
    });
    scaling::check_order("a regime with one bound", N_ONE_BOUND, 1, |n| {
        let (l, h, units, clauses) = &inputs[&n];
        assert!(matches!(
            sweep_bounded(l, h, units, clauses),
            RegimeOut::Empty
        ));
    });
}

/// The size of [`a_regime_with_one_bound_and_n_clauses_scales`].
const N_ONE_BOUND: usize = 2_000;

/// The regime step on [`coupled_empty_chain_over`] n and 8n moduli `3 a`, every `a` of 21 bits:
/// a regime the coprime base cannot write whose sweep bound is past [`SWEEP_SWITCHOVER`], found
/// `Undecided` by [`period_past_switchover`] without forming its period, so that the general
/// path decides it (FAIL-omega-negations-slow-7837918895420161952). Before the switchover the
/// sweep took the whole period; forming the period alone cost Theta(n^2) here, 55 times from
/// 512 to 4,096 moduli (2026-11-21). The moduli keep one size so that the input grows 8 times
/// in bits.
///
/// The whole decision is not what is timed here: the general path that then decides the
/// formula took 11.3 times the time from 64 to 512 moduli and 26 times from 512 to 4,096
/// (2026-11-21, load 45 to 61), from the tie [`System::least`] formed at every step; since
/// [`System::least_unfilled`] it is timed by
/// [`a_coupled_chain_past_the_switchover_is_decided_in_scale`]. Its answer here, no point, is
/// checked by `r7_tests::a_regime_over_nine_primes_the_base_cannot_write_is_decided` and by
/// `check_regime`.
#[test]
fn a_regime_past_the_switchover_scales() {
    let inputs = scaling::inputs(N_COUPLED, |n| {
        let a: Vec<i64> = (1i64 << 20..).filter(|a| a % 3 != 0).take(n).collect();
        coupled_empty_chain_over(&a)
    });
    scaling::check_order(
        "a regime over n moduli past the switchover",
        N_COUPLED,
        1,
        |n| {
            let (units, clauses) = inputs[&n].clone();
            assert!(matches!(
                solve_regime_in(&None, &None, units, clauses),
                RegimeOut::Undecided
            ));
        },
    );
}

/// The whole decision of [`a_regime_past_the_switchover_scales`]'s formula ([`regime_formula`] of
/// [`coupled_empty_chain_over`] n and 8n moduli `3 a`), which the general path decides: no
/// point. [`System::least`] formed the tie of the whole least class at each step, also where
/// the step reads it only at a fill of at most 0, O(n) rows at each of O(n) steps
/// (FAIL-omega-negations-slow-7837918895420161952); [`System::least_unfilled`] forms it only
/// there. The rows the tie reads are counted by
/// `r7_tests::ties_are_read_only_where_a_step_takes_them`.
#[test]
fn a_coupled_chain_past_the_switchover_is_decided_in_scale() {
    let inputs = scaling::inputs(N_COUPLED_DECIDED, |n| {
        let a: Vec<i64> = (1i64 << 20..).filter(|a| a % 3 != 0).take(n).collect();
        let (units, clauses) = coupled_empty_chain_over(&a);
        regime_formula(None, None, &units, &clauses)
    });
    scaling::check_order(
        "a coupled chain over n moduli decided past the switchover",
        N_COUPLED_DECIDED,
        1,
        |n| assert_eq!(crate::presburger::decide_named(&inputs[&n]), Ok(false)),
    );
}

/// The size of [`a_coupled_chain_past_the_switchover_is_decided_in_scale`]: at 512 and 4,096
/// moduli 8.31 times the instructions (1,026M and 8,523M) and 8.60 the bytes, about 0.17 s and
/// 1.5 s a run (2026-11-21, load 46); at 64 and 512, where a fixed cost of each run is a larger
/// part, 9.78. Before [`System::least_unfilled`] the tie alone grew about 57 times per factor 8
/// here, and the decision 26 times from 512 to 4,096 moduli.
const N_COUPLED_DECIDED: usize = 512;

/// The size of [`a_regime_past_the_switchover_scales`]: at 512 and 4,096 moduli the ratio was
/// 1.7, a fixed cost of each run still the larger part; at 4,096 and 32,768 it was 8.68, about
/// 32 ms and 270 ms a run (2026-11-21, load 56).
const N_COUPLED: usize = 4096;

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
