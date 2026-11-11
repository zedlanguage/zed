//! Chains of definitions guarded by one input, decided by cells of that input
//! (PERF-project-each-superlinear). The chain `t_j = if (i <= j mod 7 - 3) { t } else { c - t }`
//! over `i` in `[-20, 20]`, asked whether `t_n == 0` at some `i`, is the complement that the
//! transfer before S22a decides for `t_n != 0` (`preimage_ref::linear`): each level is a
//! disjunction whose two disjuncts bound `i` to `..=g` and `g+1..`, and each level's value is
//! written twice, once for each branch that reads it, as the translation writes it. Where no `i`
//! gives zero, the probe over the disjunctions tested each disjunct by a search or a
//! propagation of the whole chain, round after round. The ends of the guards cut `i` into 8
//! cells, in each of which the chain is one conjunction, solved once.

use std::sync::Arc;

use zed_tests::scaling;
use zedc::store::presburger::{Atom, Con, Formula, Lin, Shared, decide};

/// The guard at level `j`: `i <= j mod 7 - 3`.
fn guard(j: usize) -> i128 {
    (j % 7) as i128 - 3
}

/// The constant at level `j`: 2, or `j mod 5`.
fn constant(j: usize, varied: bool) -> i128 {
    if varied { (j % 5) as i128 } else { 2 }
}

/// The value of level `j`'s first copy (`twin` false) or second, as an auxiliary atom; level 0
/// is `i` itself.
fn level(j: usize, twin: bool) -> Lin {
    match j {
        0 => Lin::atom(Atom::Sym(Arc::from("i"))),
        _ => Lin::atom(Atom::Aux(2 * (j as u32 - 1) + u32::from(twin))),
    }
}

/// The chain of `n` levels with `t_n == 0` and `i` in `[-20, 20]`, each level but the last
/// written twice: `(i <= g && t == q) || (!(i <= g) && t' + q == c)`, `t` and `t'` the two
/// copies of the level below.
fn chain(n: usize, varied: bool) -> Formula {
    let i = level(0, false);
    let le = |l: &Lin, k: i128| Formula::Con(Con::ge(&Lin::constant(k), l));
    let mut parts = vec![le(&i, 20), Formula::Con(Con::ge(&i, &Lin::constant(-20)))];
    for j in 1..=n {
        let copies: &[bool] = if j < n { &[false, true] } else { &[false] };
        for &twin in copies {
            let q = level(j, twin);
            let g = le(&i, guard(j));
            parts.push(Formula::or(vec![
                Formula::and(vec![
                    g.clone(),
                    Formula::Con(Con::eq(&level(j - 1, false), &q)),
                ]),
                Formula::and(vec![
                    Formula::Not(Shared::new(g)),
                    Formula::Con(Con::eq(
                        &level(j - 1, true).plus(&q),
                        &Lin::constant(constant(j, varied)),
                    )),
                ]),
            ]));
        }
    }
    parts.push(Formula::Con(Con::eq(&level(n, false), &Lin::constant(0))));
    Formula::and(parts)
}

/// Whether some `i` in `[-20, 20]` gives `t_n == 0`, by running the chain at each.
fn reaches_zero(n: usize, varied: bool) -> bool {
    (-20..=20).any(|i: i128| {
        let t = (1..=n).fold(i, |t, j| {
            if i <= guard(j) {
                t
            } else {
                constant(j, varied) - t
            }
        });
        t == 0
    })
}

/// Decides [`chain`] and checks the answer against [`reaches_zero`].
fn decides(n: usize, varied: bool) {
    let got = decide(&chain(n, varied)).expect("decided");
    assert_eq!(got, reaches_zero(n, varied), "{n} levels, varied {varied}");
}

/// Every chain from 1 to 96 levels, with either constant, is decided as running it decides.
#[test]
fn guarded_chains_are_decided_as_run() {
    for varied in [false, true] {
        for n in 1..=96 {
            decides(n, varied);
        }
    }
}

/// The chain with no point at 80 levels (`c = 2`) and 10, in work linear in the levels. Control
/// (once, not kept): with the probe over the disjunctions in place of the cells, this test fails,
/// 82.6 times the bytes from 10 to 80 levels (122,171,546 to 10,094,059,976), against 16.75.
#[test]
fn guarded_chains_with_no_point_scale() {
    assert!(!reaches_zero(80, false), "80 levels have no point");
    let fs = scaling::inputs(10, |n| chain(n, false));
    scaling::check_order("decision of a guarded chain with no point", 10, 1, |n| {
        assert_eq!(
            decide(&fs[&n]).expect("decided"),
            reaches_zero(n, false),
            "{n}"
        );
    });
}
