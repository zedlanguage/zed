//! The failed-literal search over disjunctions when guards lie beyond the inputs: a counter
//! that starts at `m` and is raised by each guard `i >= j`, `j = 1..k`, that fails, with `i`
//! and `m` in `[-w, w]` and `k > w`. The guards `j > w` hold at no input, and the question
//! whether the counter can stay below zero needs `i` near `w`: each disjunct `i <= j - 1` with
//! `j - 1` below the least `i` the formula allows has no point. Since LIN-probe-refute the
//! search finds that least `i` by a search over the bounds the disjuncts write, not by one
//! propagation per disjunct. The answers are checked against every point of the inputs.

use zed_tests::scaling;
use zedc::store::presburger::decide;

use super::repair::{answers, guards, guards_point};

/// Inputs from 1 to 8 wide, guards from one past the width to three times it, both demands.
#[test]
fn guards_beyond_the_inputs_are_answered() {
    for w in 1..=8 {
        for k_ in (w + 1)..=(3 * w) {
            for meet in [true, false] {
                let (k_, w) = (k_ as usize, w as i64);
                answers(&guards(k_, w, meet), guards_point(k_, w, meet));
            }
        }
    }
}

/// One guard, inside, at and beyond the inputs.
#[test]
fn one_guard_is_answered() {
    for w in 0..=3 {
        for meet in [true, false] {
            answers(&guards(1, w, meet), guards_point(1, w, meet));
        }
    }
}

/// With `i` and `m` fixed at zero every guard fails, the counter is `k`, and below zero it
/// has no point: each disjunct of the last disjunction the search tests is refuted.
#[test]
fn guards_with_no_point_below_zero_are_refuted() {
    for k_ in 1..=16 {
        answers(&guards(k_, 0, false), false);
        answers(&guards(k_, 0, true), true);
    }
}

/// Guards all inside the inputs, where a point meets each disjunct and none is refuted.
#[test]
fn guards_inside_the_inputs_are_answered() {
    for k_ in 1..=14 {
        for meet in [true, false] {
            let w = k_ as i64;
            answers(&guards(k_, w, meet), guards_point(k_, w, meet));
        }
    }
}

/// The counter below zero with `k` guards on inputs `3k/4` wide, at `k = 16` and `128`: the
/// formula implies `i > k/4`, and the `k/4` disjuncts `i <= j - 1` for `j` up to `k/4 + 1`
/// have no point. Each was refuted by its own propagation of the whole chain, 17.1 M and
/// 712.1 M bytes, 41.7 times (ledger LIN-probe-refute); one search over the bounds the
/// disjuncts write refutes them all with `O(log k)` propagations, 11.0 times. The symbols
/// `t10`, `t100` and `t2` do not sort in the chain's order, so the propagation of bounds must
/// follow the chain's structure, not its names.
#[test]
fn guards_beyond_the_inputs_scale() {
    let make = |n: usize| guards(n, 3 * n as i64 / 4, false);
    let (small, large) = (make(16), make(16 * scaling::FACTOR));
    scaling::check(
        "decide on a chain of k guards beyond inputs 3k/4 wide",
        16,
        |n| {
            assert_eq!(decide(if n == 16 { &small } else { &large }), Ok(true));
        },
    );
}
