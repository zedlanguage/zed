//! The greedy search of the Omega test over disjunctions: when the point found so far fails a
//! disjunction, each disjunct is tried with its own variables solved again, its neighbors held
//! at the point, and each of its variables kept within the bounds that the constraints of one
//! variable taken so far give it. Those bounds round a coefficient that does not divide, turn
//! with a negative coefficient, and fix a variable under an equality. A chain of `k` guards
//! `i >= j` on one input, the relation of a counter that `k` tests of `i` raise, gives `i` `k`
//! constraints of one variable, and the search must not read all of them at each of its `k`
//! repairs. The answers are checked against every point of a window.

use std::sync::Arc;

use zed_tests::scaling;
use zedc::store::int::Int;
use zedc::store::presburger::{Atom, Con, Formula, Lin, Model, decide, satisfiable};

use super::scaling::x;

fn var(name: &str) -> Lin {
    Lin::atom(Atom::Sym(Arc::from(name)))
}

fn k(v: i64) -> Lin {
    Lin::constant(v)
}

/// `a >= b`.
fn ge(a: &Lin, b: &Lin) -> Formula {
    Formula::Con(Con::ge(a, b))
}

/// `a == b`.
fn eq(a: &Lin, b: &Lin) -> Formula {
    Formula::Con(Con::eq(a, b))
}

/// `decide(f)` is `answer`, and `satisfiable(f)` agrees with a point that meets `f`.
pub(super) fn answers(f: &Formula, answer: bool) {
    assert_eq!(decide(f), Ok(answer), "{f}");
    let found = satisfiable(f).expect("answered");
    assert_eq!(found.is_some(), answer, "{f}");
    if let Some(m) = found {
        assert!(f.holds(&m), "{m:?} fails {f}");
    }
}

/// Whether some point `(x0, x1)` of `[-half, half]^2` meets `f`.
fn some_point(f: &Formula, half: i64) -> bool {
    (-half..=half).any(|a| {
        (-half..=half).any(|b| {
            let m: Model = [(0, a), (1, b)]
                .into_iter()
                .map(|(i, v)| (Atom::Sym(Arc::from(format!("x{i}"))), Int::from(v)))
                .collect();
            f.holds(&m)
        })
    })
}

/// Bounds of one variable each, then a disjunction of two variables that the first point may
/// fail: `3·x0 >= 1` and `7 >= 2·x0` keep `x0` in `[1, 3]` (rounded up and down), and `fix`
/// fixes `x1` by an equality, with a positive or a negative coefficient, or leaves it none.
#[test]
fn bounds_of_one_variable_keep_their_rounding_and_sign() {
    let fixes: [(&str, Vec<Formula>); 5] = [
        ("3·x1 == 6", vec![eq(&x(1).times(3), &k(6))]),
        (
            "-2·x1 + 4 == 0",
            vec![eq(&x(1).times(-2).plus(&k(4)), &k(0))],
        ),
        ("2·x1 == 3", vec![eq(&x(1).times(2), &k(3))]),
        (
            "-5 <= -2·x1 <= 1",
            vec![ge(&x(1).times(-2), &k(-5)), ge(&k(1), &x(1).times(-2))],
        ),
        ("x1 in [-4, 4]", vec![ge(&x(1), &k(-4)), ge(&k(4), &x(1))]),
    ];
    let mut points = 0;
    for (what, fix) in &fixes {
        let _ = what;
        for c in -3..=9 {
            for d in -6..=4 {
                let mut fs = vec![ge(&x(0).times(3), &k(1)), ge(&k(7), &x(0).times(2))];
                fs.extend(fix.iter().cloned());
                fs.push(Formula::or(vec![
                    ge(&x(0).plus(&x(1)), &k(c)),
                    Formula::and(vec![
                        ge(&x(0).minus(&x(1)), &k(d)),
                        ge(&x(1).minus(&x(0)), &k(d)),
                    ]),
                ]));
                let f = Formula::and(fs);
                let answer = some_point(&f, 6);
                points += usize::from(answer);
                answers(&f, answer);
            }
        }
    }
    // Both answers occur.
    assert!(points > 0 && points < fixes.len() * 13 * 11, "{points}");
}

/// The relation of `t_k`, a counter that starts at `m` and is raised once by each of the
/// guards `i >= j`, `j = 1..k`, that fail, with `i` and `m` in `[-w, w]`; with `t_k >= 0` when
/// `meet`, and `t_k < 0` otherwise.
pub(super) fn guards(k_: usize, w: i64, meet: bool) -> Formula {
    let t = |j: usize| var(&format!("t{j}"));
    let i = var("i");
    let mut fs = vec![
        ge(&i, &k(-w)),
        ge(&k(w), &i),
        ge(&var("m"), &k(-w)),
        ge(&k(w), &var("m")),
        eq(&t(0), &var("m")),
    ];
    for j in 1..=k_ {
        let j_ = j as i64;
        fs.push(Formula::or(vec![
            Formula::and(vec![ge(&i, &k(j_)), eq(&t(j), &t(j - 1))]),
            Formula::and(vec![ge(&k(j_ - 1), &i), eq(&t(j), &t(j - 1).plus(&k(1)))]),
        ]));
    }
    fs.push(if meet {
        ge(&t(k_), &k(0))
    } else {
        ge(&k(-1), &t(k_))
    });
    Formula::and(fs)
}

/// Whether some `i` and `m` in `[-w, w]` give `m` plus the number of `j` in `1..=k` above `i`
/// at least zero (`meet`) or below zero.
pub(super) fn guards_point(k_: usize, w: i64, meet: bool) -> bool {
    (-w..=w).any(|i| {
        (-w..=w).any(|m| {
            let t = m + (1..=k_ as i64).filter(|&j| i < j).count() as i64;
            (t >= 0) == meet
        })
    })
}

/// The chain's answers on both sides, with the guards inside, at and beyond the inputs' width.
#[test]
fn a_chain_of_guards_on_one_input_is_answered() {
    for k_ in 0..=12 {
        for w in [1, 3, k_ as i64, 12] {
            for meet in [true, false] {
                answers(&guards(k_, w, meet), guards_point(k_, w, meet));
            }
        }
    }
}

/// Each of the `k` repairs of the chain reads its two bounds of `i`, not the `k` guards on `i`
/// taken before it (LIN-cross: the guards made the search `k^2`, 134152 constraints read at
/// `k = 256` against 8968 at `k = 64`).
#[test]
fn a_chain_of_guards_on_one_input_scales() {
    let make = |n: usize| guards(n, n as i64, true);
    let (small, large) = (make(64), make(64 * scaling::FACTOR));
    for f in [&small, &large] {
        assert!(satisfiable(f).expect("answered").is_some());
    }
    scaling::check("satisfiable on a chain of k guards i >= j", 64, |n| {
        drop(satisfiable(if n == 64 { &small } else { &large }));
    });
}

/// The chain with its only point at an end of the inputs (`w = k - 2` and `t_k < 0` need
/// `i = k - 2`), where the greedy search fails and the failed-literal search over the
/// disjunctions runs; with the guards all met (`w >= k`), all unmet below `i`, and a mix of
/// both (`w` between), from `k = 1`.
#[test]
fn a_chain_whose_point_is_at_an_end_is_answered() {
    for k_ in 1..=14 {
        let ki = k_ as i64;
        for w in [ki - 2, ki - 1, ki, ki + 1, ki / 2] {
            if w < 0 {
                continue;
            }
            for meet in [true, false] {
                answers(&guards(k_, w, meet), guards_point(k_, w, meet));
            }
        }
    }
}

/// The failed-literal search on the chain whose point is at an end stays near linear: each
/// disjunct that a point found so far meets is kept without a propagation (LIN-probe: the
/// search ran one full propagation per disjunct, `k^2.4` in all).
#[test]
fn a_chain_whose_point_is_at_an_end_scales() {
    let make = |n: usize| guards(n, n as i64 - 2, false);
    let (small, large) = (make(256), make(256 * scaling::FACTOR));
    scaling::check(
        "decide on a chain of k guards with its point at an end",
        256,
        |n| {
            assert_eq!(decide(if n == 256 { &small } else { &large }), Ok(true));
        },
    );
}
