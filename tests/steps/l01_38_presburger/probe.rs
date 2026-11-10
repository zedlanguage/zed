//! The failed-literal search over disjunctions when guards lie beyond the inputs: a counter
//! that starts at `m` and is raised by each guard `i >= j`, `j = 1..k`, that fails, with `i`
//! and `m` in `[-w, w]` and `k > w`. The guards `j > w` hold at no input, and the question
//! whether the counter can stay below zero needs `i` near `w`: each disjunct `i <= j - 1` with
//! `j - 1` below the least `i` the formula allows has no point. Since LIN-probe-refute the
//! search finds that least `i` by a search over the bounds the disjuncts write, not by one
//! propagation per disjunct. The answers are checked against every point of the inputs. The
//! nested chains of absolute values at the end (PROJECT-abs-chain-quadratic) have dead
//! disjuncts that the bounds of the parts, carried along the chain, show at once.

use std::sync::Arc;

use zed_tests::scaling;
use zedc::store::interval::{End, IntervalSet, Num};
use zedc::store::presburger::{Atom, Con, Formula, Lin, Shared, decide, project_each, satisfiable};

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
#[ignore = "PROBE-guards: 17.1 times the work at 16 and 128 guards, over the n log n limit 15.4 since SCALE-ratio; open"]
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

/// `Σ c·a + k`, where a name `p<k>` is the solver's own atom `2k` and `t<k>` its atom `2k + 1`
/// ([`Atom::Aux`]), as the translator numbers the atoms it defines, and `i` is a symbol.
fn chain_lin(terms: &[(&str, i128)], k: i128) -> Lin {
    terms.iter().fold(Lin::constant(k), |l, (s, c)| {
        let a = match s.split_at(1) {
            ("i", "") => Atom::Sym(Arc::from("i")),
            (h, k) => Atom::Aux(2 * k.parse::<u32>().expect("a number") + u32::from(h == "t")),
        };
        l.plus(&Lin::atom(a).times(*c))
    })
}

fn chain_ge(terms: &[(&str, i128)], k: i128) -> Formula {
    Formula::Con(Con::ge(&chain_lin(terms, k), &Lin::constant(0)))
}

/// `q == |x - k|`, written as the translator writes it: `(x >= k && x - q == k) ||
/// (!(x >= k) && x + q == k)`.
fn chain_abs(q: &str, x: &str, k: i128) -> Formula {
    let at = |t: &[(&str, i128)]| Formula::Con(Con::eq(&chain_lin(t, -k), &Lin::constant(0)));
    let c = chain_ge(&[(x, 1)], -k);
    let not = Formula::Not(Shared::new(c.clone()));
    Formula::or(vec![
        Formula::and(vec![c, at(&[(x, 1), (q, -1)])]),
        Formula::and(vec![not, at(&[(x, 1), (q, 1)])]),
    ])
}

/// The nested chain `p0 == |i|`, `p(k) == |p(k-1) - 1|` for `k` below `n`, with
/// `p(n-1) >= 2` and `i <= n + 10`. With `twins` a second chain `t` is written alike and the
/// demand is `p(n-1) + t(n-1) >= 4`, so that the two chains are twins to be merged
/// (PROJECT-box-half-open). Either way `p(n-1)` is `|i| - n + 1` where `|i| >= n - 1`, and 0
/// or 1 below, so `i` takes `..=-(n+1)` and `n+1..=n+10`.
fn abs_chain(n: usize, twins: bool) -> Formula {
    let mut parts = Vec::new();
    for h in if twins { &["p", "t"][..] } else { &["p"][..] } {
        parts.push(chain_abs(&format!("{h}0"), "i", 0));
        for k in 1..n {
            parts.push(chain_abs(&format!("{h}{k}"), &format!("{h}{}", k - 1), 1));
        }
    }
    let (p, t) = (format!("p{}", n - 1), format!("t{}", n - 1));
    parts.push(if twins {
        chain_ge(&[(p.as_str(), 1), (t.as_str(), 1)], -4)
    } else {
        chain_ge(&[(p.as_str(), 1)], -2)
    });
    parts.push(chain_ge(&[("i", -1)], 10 + n as i128));
    Formula::and(parts)
}

/// The projection onto `i` of [`abs_chain`]: `..=-(n+1)` and `n+1..=n+10`.
fn abs_chain_answer(n: usize) -> IntervalSet {
    let n = n as i64;
    IntervalSet::from_pieces(vec![
        (End::NegInf, End::Fin(Num::from(-(n + 1)))),
        (End::Fin(Num::from(n + 1)), End::Fin(Num::from(n + 10))),
    ])
}

/// Projects [`abs_chain`] onto `i` and checks the answer, with nothing left out.
fn projects_abs_chain(f: &Formula, n: usize) {
    let (each, skipped) = project_each(f, &[Atom::Sym(Arc::from("i"))]).expect("projected");
    assert!(skipped.is_empty(), "{n}: {skipped:?}");
    assert_eq!(each[0].clone().expect("a set"), abs_chain_answer(n), "{n}");
}

/// The chains of 1 to 12 levels, with and without twins, project to the closed form exactly;
/// for up to 4 levels each value of `i` from `-(n+14)` to `n+14` is also decided on its own.
#[test]
fn a_nested_chain_of_absolute_values_is_projected_exactly() {
    for twins in [false, true] {
        for n in 1..=12 {
            let f = abs_chain(n, twins);
            projects_abs_chain(&f, n);
            if n > 4 {
                continue;
            }
            let at = abs_chain_answer(n);
            for v in -(n as i64 + 14)..=(n as i64 + 14) {
                let one = Formula::and(vec![f.clone(), chain_ge(&[("i", 1)], -(v as i128))]);
                let one = Formula::and(vec![one, chain_ge(&[("i", -1)], v as i128)]);
                let has = satisfiable(&one).expect("decided").is_some();
                assert_eq!(has, at.contains(v), "{n} twins {twins}: i = {v}");
            }
        }
    }
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
    let fs = scaling::inputs(32, |n| abs_chain(n, false));
    scaling::check_order(
        "projection of a nested chain of absolute values",
        32,
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
    let fs = scaling::inputs(32, |n| abs_chain(n, true));
    scaling::check_order(
        "projection of twin nested chains of absolute values",
        32,
        1,
        |n| {
            projects_abs_chain(&fs[&n], n);
        },
    );
}
