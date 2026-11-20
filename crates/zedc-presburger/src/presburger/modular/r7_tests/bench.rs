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

#[test]
fn pncx_fixed_chain_scale() {
    let inputs = scaling::inputs(60_000, fixed_chain);
    scaling::check_order("atoms fixed one after another", 60_000, 1, |n| {
        assert!(matches!(solve_modular(&inputs[&n], false), Some(Some(_))));
    });
}
