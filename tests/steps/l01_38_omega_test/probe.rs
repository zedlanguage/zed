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

use zedc::store::interval::{End, IntervalSet, Num};
use zedc::store::presburger::{
    Atom, Con, Formula, Lin, Shared, project_each, satisfiable, with_parts_reversed,
};

use super::repair::{answers, guards, guards_point};

/// Inputs from 1 to 5 wide, with guards just past the inputs, at twice and at three times
/// their width, and 9 guards on inputs 8 wide, both demands. The whole grid, every number of
/// guards from one past the width to three times it on inputs 1 to 8 wide, is in `bench::probe`
/// (1.9 s at load 25).
#[test]
fn guards_beyond_the_inputs_are_answered() {
    for w in 1..=5i64 {
        let mut ks = vec![w + 1, 2 * w, 3 * w];
        ks.dedup();
        for k_ in ks {
            guards_beyond_the_inputs_answer(k_ as usize, w);
        }
    }
    guards_beyond_the_inputs_answer(9, 8);
}

/// [`guards`] of `k_` guards on inputs `w` wide, both demands, answered as every point answers.
pub(super) fn guards_beyond_the_inputs_answer(k_: usize, w: i64) {
    for meet in [true, false] {
        answers(&guards(k_, w, meet), guards_point(k_, w, meet));
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

/// The values of `i` (or of `m`, with `of_m`) at which some value of the other input in
/// `[-w, w]` meets [`guards`]' demand, counted from every point.
fn guards_values(k_: usize, w: i64, meet: bool, of_m: bool) -> Vec<i64> {
    let meets = |i: i64, m: i64| {
        let t = m + (1..=k_ as i64).filter(|&j| i < j).count() as i64;
        (t >= 0) == meet
    };
    (-w..=w)
        .filter(|&v| (-w..=w).any(|u| if of_m { meets(u, v) } else { meets(v, u) }))
        .collect()
}

/// Projects [`guards`] onto `i` and `m` and checks each set against [`guards_values`] at every
/// value from `-w - 2` to `w + 2`, with nothing left out, and that the sets are the same with
/// the disjunctions and their disjuncts read in reverse ([`with_parts_reversed`]).
pub(super) fn projects_guards(k_: usize, w: i64, meet: bool) {
    let f = guards(k_, w, meet);
    let syms = [Atom::Sym(Arc::from("i")), Atom::Sym(Arc::from("m"))];
    let (each, skipped) = project_each(&f, &syms).expect("projected");
    assert!(skipped.is_empty(), "k {k_} w {w} meet {meet}: {skipped:?}");
    let reversed = with_parts_reversed(|| project_each(&f, &syms)).expect("projected");
    assert_eq!(
        (&each, &skipped),
        (&reversed.0, &reversed.1),
        "k {k_} w {w} meet {meet}: reversed"
    );
    for (s, of_m) in each.into_iter().zip([false, true]) {
        let s = s.expect("a set");
        let values = guards_values(k_, w, meet, of_m);
        for v in (-w - 2)..=(w + 2) {
            let at = format!("k {k_} w {w} meet {meet} of_m {of_m}: {v}");
            assert_eq!(s.contains(v), values.contains(&v), "{at}");
        }
    }
}

/// The projections onto each input of chains of guards on inputs from 0 to 3 wide: one guard,
/// guards up to the width, one past it, past twice it, and 16 guards; and on inputs 8 wide, 9
/// guards, the slowest case of the grid. The guards lie inside, at and beyond the inputs, both
/// demands: the probe's searches take the bounds that the solver's `learn` finds when a search
/// fails, and drop the disjuncts those bounds exclude, so a bound learned too strong would
/// remove values here. The whole grid, 1 to 16 guards on inputs 0 to 8 wide, is in
/// `bench::probe` (7.1 s at load 25).
#[test]
fn guards_are_projected_onto_each_input() {
    for w in 0..=3i64 {
        let mut ks: Vec<usize> = [1, w, w + 1, 2 * w + 1, 16]
            .into_iter()
            .filter(|&k| k >= 1)
            .map(|k| k as usize)
            .collect();
        ks.sort();
        ks.dedup();
        for k_ in ks {
            for meet in [true, false] {
                projects_guards(k_, w, meet);
            }
        }
    }
    for meet in [true, false] {
        projects_guards(9, 8, meet);
    }
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
pub(super) fn abs_chain(n: usize, twins: bool) -> Formula {
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
pub(super) fn projects_abs_chain(f: &Formula, n: usize) {
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
