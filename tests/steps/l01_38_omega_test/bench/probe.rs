//! The benchmarks of `probe.rs` (TEST-bench-move-l0138), run by `tools/run_tests.sh --bench`.

use crate::probe::*;
use crate::repair::guards;
use std::sync::Arc;
use zed_tests::scaling;
use zedc::store::interval::{End, IntervalSet, Num};
use zedc::store::presburger::{Atom, decide, project_each, satisfiable};

/// The counter below zero with `k` guards on inputs `3k/4` wide, at `k = 16` and `128`: the
/// formula implies `i > k/4`, and the `k/4` disjuncts `i <= j - 1` for `j` up to `k/4 + 1`
/// have no point. Each was refuted by its own propagation of the whole chain, 17.1 M and
/// 712.1 M bytes, 41.7 times (ledger LIN-probe-refute); one search over the bounds the
/// disjuncts write refutes them all with `O(log k)` propagations, 11.0 times. Since
/// PROJECT-abs-chain-quadratic the bounds of the parts, carried along the chain, answer the
/// question with one propagation and no probe: 35.9 M and 345.3 M instructions, 9.6 times
/// (ledger PROBE-guards). The symbols `t10`, `t100` and `t2` do not sort in the chain's
/// order, so the propagation of bounds must follow the chain's structure, not its names.
#[test]
fn guards_beyond_the_inputs_scale() {
    let make = |n: usize| guards(n, 3 * n as i64 / 4, false);
    let (small, large) = (make(430), make(430 * scaling::FACTOR));
    scaling::check(
        "decide on a chain of k guards beyond inputs 3k/4 wide",
        430,
        |n| {
            assert_eq!(decide(if n == 430 { &small } else { &large }), Ok(true));
        },
    );
}

/// The projection onto `i` of the counter below zero with `k` guards on inputs `3k/4` wide,
/// at `k = 16` and `128`: `i` from `k/4 + 1` to `3k/4`. The `k/4` disjuncts `i <= j - 1`, `j`
/// up to `k/4 + 1`, have no point, and the others' searches failed alone without the bound
/// `i >= k/4 + 1`: halving down to each disjunct cost a search of the whole formula each,
/// 65.3 M and 2,679.6 M bytes, 41.0 times (limit 15.4, ledger PROBE-guards). Now the first
/// search that fails alone hands its disjunct to `learn`, whose bound every later search of the
/// round takes and which excludes the other dead disjuncts unsearched: 47.3 M and 440.6 M
/// bytes, 9.3 times, and 9.3 times the instructions.
#[test]
fn projecting_guards_beyond_the_inputs_scales() {
    let make = |n: usize| guards(n, 3 * n as i64 / 4, false);
    let (small, large) = (make(16), make(16 * scaling::FACTOR));
    let i = [Atom::Sym(Arc::from("i"))];
    scaling::check(
        "projection onto i of a chain of k guards beyond inputs 3k/4 wide",
        16,
        |n| {
            let (each, skipped) =
                project_each(if n == 16 { &small } else { &large }, &i).expect("projected");
            assert!(skipped.is_empty(), "{n}: {skipped:?}");
            let (lo, hi) = (n as i64 / 4 + 1, 3 * n as i64 / 4);
            let at =
                IntervalSet::from_pieces(vec![(End::Fin(Num::from(lo)), End::Fin(Num::from(hi)))]);
            assert_eq!(each[0].clone().expect("a set"), at, "{n}");
        },
    );
}

/// A nested chain of `n` absolute values: for each `k` from 1, the disjunct `p(k-1) <= 0`
/// (with `p(k-1) + p(k) == 1`) has no point, since `p(k-1)` is at least `n - k + 2` at every
/// point.
/// Each was removed by a propagation of the whole formula of its own, O(n²): 0.18 s at 16
/// levels and 2.7 s at 64 (PROJECT-abs-chain-quadratic). Four readings of the parts in order,
/// carrying bounds, remove them all (`drop_by_bounds`). Control (once, not kept): the old
/// path allocated 0.77 GB at 32 levels and 91 GB at 256, 118 times the bytes (the limit is
/// 14.1), in 170 s; this one 6.0 MB and 45 MB, and 32 and 265 million instructions, 8.2 times.
#[test]
fn a_nested_chain_of_absolute_values_scales() {
    let fs = scaling::inputs(1100, |n| abs_chain(n, false));
    scaling::check_order(
        "projection of a nested chain of absolute values",
        1100,
        1,
        |n| {
            projects_abs_chain(&fs[&n], n);
        },
    );
}

/// [`a_nested_chain_of_absolute_values_scales`] with the twin chain `t`, which the projection
/// merges with `p` before it projects (`twins_merged`), so every disjunction is asked twice:
/// 1.9 s at 32 levels and 6.6 s at 64 before. The bounds remove the dead disjuncts in the
/// asks of the merged formula too, and each disjunction they leave with one disjunct joins the
/// base at once. Control (once, not kept): the old path allocated 1.8 GB at 32 levels and
/// 134 GB at 256, 76 times the bytes, in 192 s; this one 36 MB and 269 MB, and 182 and 1441
/// million instructions, 7.9 times.
#[test]
fn twin_chains_of_absolute_values_scale() {
    let fs = scaling::inputs(310, |n| abs_chain(n, true));
    scaling::check_order(
        "projection of twin nested chains of absolute values",
        310,
        1,
        |n| {
            projects_abs_chain(&fs[&n], n);
        },
    );
}

/// `satisfiable` on [`a_nested_chain_of_absolute_values_scales`]'s chain: a point, `i` at
/// `n + 1` and up. MEASURE
#[test]
fn the_point_of_a_nested_chain_of_absolute_values_scales() {
    let fs = scaling::inputs(1100, |n| abs_chain(n, false));
    scaling::check("a point of a nested chain of absolute values", 1100, |n| {
        assert!(satisfiable(&fs[&n]).expect("decided").is_some(), "{n}");
    });
}

/// `probe::guards_beyond_the_inputs_are_answered` as first written, 1.9 s (2026-11-14, load
/// 25): inputs from 1 to 8 wide, guards from one past the width to three times it, both
/// demands.
#[test]
fn guards_beyond_the_inputs_are_answered_on_the_whole_grid() {
    for w in 1..=8i64 {
        for k_ in (w + 1)..=(3 * w) {
            guards_beyond_the_inputs_answer(k_ as usize, w);
        }
    }
}

/// `probe::guards_are_projected_onto_each_input` as first written, 7.1 s (2026-11-14, load
/// 25): the projections onto each input of the chains of 1 to 16 guards on inputs from 0 to 8
/// wide, both demands.
#[test]
fn guards_are_projected_onto_each_input_on_the_whole_grid() {
    for w in 0..=8 {
        for k_ in 1..=16 {
            for meet in [true, false] {
                projects_guards(k_, w, meet);
            }
        }
    }
}
