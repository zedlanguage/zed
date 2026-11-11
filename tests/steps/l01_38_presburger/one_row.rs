//! A box and one row, and one equation over atoms each confined to a few values, answered
//! without the solver's search (PRES-disj-cost-xr; COMPLEXITY.md row PRES-disj-cost).
//!
//! Each answer is checked against the points of a small window, or against a point the test
//! knows, and the cost of each shape is held to `n log n` at k and 8k atoms. Control: before
//! the change, the subset sum with target zero cost k^2.7 instructions in `decide` (k = 8 to
//! 256), and the box with one row k^2.6 in `project_each`.

use std::sync::Arc;

use zed_tests::scaling;
use zedc::store::interval::{End, IntervalSet, Num};
use zedc::store::presburger::{Atom, Con, Factor, Formula, Lin, decide, project_each, satisfiable};

fn sym(s: &str) -> Atom {
    Atom::Sym(Arc::from(s))
}

/// `Σ c·a + k`.
fn lin(terms: &[(Atom, i128)], k: i128) -> Lin {
    terms.iter().fold(Lin::constant(k), |l, (a, c)| {
        l.plus(&Lin::atom(a.clone()).times(*c))
    })
}

fn ge(terms: &[(Atom, i128)], k: i128) -> Formula {
    Formula::Con(Con::ge(&lin(terms, k), &Lin::constant(0)))
}

fn eq(terms: &[(Atom, i128)], k: i128) -> Formula {
    Formula::Con(Con::eq(&lin(terms, k), &Lin::constant(0)))
}

/// `lo <= a <= hi`.
fn within(a: &Atom, lo: i128, hi: i128) -> Vec<Formula> {
    vec![ge(&[(a.clone(), 1)], -lo), ge(&[(a.clone(), -1)], hi)]
}

fn range(lo: i64, hi: i64) -> IntervalSet {
    IntervalSet::range(End::Fin(Num::from(lo)), End::Fin(Num::from(hi)))
}

fn names(k: usize) -> Vec<Atom> {
    (0..k).map(|i| sym(&format!("y{i}"))).collect()
}

/// `0 <= y[i] <= 1000 + i` for each i, with `Σ y[i] == s` for `s` half the box's greatest sum.
fn dense(k: usize) -> Formula {
    let ys = names(k);
    let mut fs: Vec<Formula> = ys
        .iter()
        .enumerate()
        .flat_map(|(i, y)| within(y, 0, 1000 + i as i128))
        .collect();
    let s: i128 = (0..k as i128).map(|i| 1000 + i).sum();
    let terms: Vec<(Atom, i128)> = ys.iter().map(|y| (y.clone(), 1)).collect();
    fs.push(eq(&terms, -(s / 2)));
    Formula::and(fs)
}

/// The weights of the subset sums below, each of them 1000 or more.
fn weights(k: usize) -> Vec<i128> {
    (0..k as i128).map(|i| 1000 + 37 * i * i % 991).collect()
}

/// `(y[i] == 0 || y[i] == w[i])` for each i, with `Σ y[i] == t`: a subset sum.
fn choice_sum(w: &[i128], t: i128) -> Formula {
    let ys = names(w.len());
    let mut fs: Vec<Formula> = ys
        .iter()
        .zip(w)
        .map(|(y, w)| Formula::or(vec![eq(&[(y.clone(), 1)], 0), eq(&[(y.clone(), 1)], -w)]))
        .collect();
    let terms: Vec<(Atom, i128)> = ys.iter().map(|y| (y.clone(), 1)).collect();
    fs.push(eq(&terms, -t));
    Formula::and(fs)
}

/// Even weights and an odd target near half their sum: no point, by parity.
fn parity(k: usize) -> Formula {
    let w: Vec<i128> = weights(k).iter().map(|w| 2 * w).collect();
    let half = w.iter().sum::<i128>() / 2;
    choice_sum(&w, half + 1 - half % 2)
}

#[test]
fn a_box_and_one_row_has_a_point_where_its_sums_allow() {
    let (x, y, z) = (sym("x"), sym("y"), sym("z"));
    let boxed = |row: Formula| {
        let mut fs = within(&x, 0, 3);
        fs.extend(within(&y, -2, 5));
        fs.extend(within(&z, 1, 1));
        fs.push(row);
        Formula::and(fs)
    };
    // `x + y - z` ranges over -3..=7 in the box, every integer of it.
    for t in -5..=9 {
        let f = boxed(eq(&[(x.clone(), 1), (y.clone(), 1), (z.clone(), -1)], -t));
        assert_eq!(decide(&f), Ok((-3..=7).contains(&t)), "x + y - z == {t}");
    }
    // `3x - 2y >= t`: its greatest value is 13.
    for t in [12, 13, 14] {
        let f = boxed(ge(&[(x.clone(), 3), (y.clone(), -2)], -t));
        assert_eq!(decide(&f), Ok(t <= 13), "3x - 2y >= {t}");
    }
    // A bound rounded to an integer: `2x >= 7` is `x >= 4`, out of the box.
    let f = Formula::and(vec![ge(&[(x.clone(), 2)], -7), ge(&[(x.clone(), -1)], 3)]);
    assert_eq!(decide(&f), Ok(false));
    // An equation on one atom that no integer meets.
    assert_eq!(decide(&eq(&[(x.clone(), 2)], -3)), Ok(false));
    // An end left open: `x >= 0` and `x - y == 100` with `y <= 3` has `x` up to 103.
    let f = Formula::and(vec![
        ge(&[(x.clone(), 1)], 0),
        ge(&[(y.clone(), -1)], 3),
        eq(&[(x.clone(), 1), (y.clone(), -1)], -100),
    ]);
    assert_eq!(decide(&f), Ok(true));
    let (each, _) = project_each(&f, &[x.clone(), y.clone()]).unwrap();
    assert_eq!(
        each[0],
        Ok(IntervalSet::range(
            End::Fin(Num::from(0)),
            End::Fin(Num::from(103))
        ))
    );
    assert_eq!(
        each[1],
        Ok(IntervalSet::range(
            End::Fin(Num::from(-100)),
            End::Fin(Num::from(3))
        ))
    );
    // An equation with a coefficient other than 1 or -1 can have gaps; the solver answers it.
    let f = Formula::and(
        [
            within(&x, 0, 5),
            within(&y, 0, 5),
            vec![eq(&[(x.clone(), 2), (y.clone(), 2)], -3)],
        ]
        .concat(),
    );
    assert_eq!(decide(&f), Ok(false));
}

#[test]
fn a_box_and_one_row_projects_each_atom_exactly() {
    // Every point of the window is checked: each projection is the set of values an atom takes.
    let (x, y, z) = (sym("x"), sym("y"), sym("z"));
    let rows = [
        (
            vec![(x.clone(), 1), (y.clone(), 1), (z.clone(), 1)],
            4,
            true,
        ),
        (
            vec![(x.clone(), 1), (y.clone(), -1), (z.clone(), 1)],
            -3,
            true,
        ),
        (
            vec![(x.clone(), 2), (y.clone(), -3), (z.clone(), 1)],
            5,
            false,
        ),
        (vec![(x.clone(), -1), (y.clone(), -1)], -6, false),
    ];
    for (row, t, is_eq) in rows {
        let mut fs = within(&x, 0, 3);
        fs.extend(within(&y, -1, 2));
        fs.extend(within(&z, 0, 2));
        fs.push(if is_eq { eq(&row, -t) } else { ge(&row, -t) });
        let f = Formula::and(fs);
        let at = |p: [i128; 3]| {
            let s: i128 = row
                .iter()
                .map(|(a, c)| {
                    c * p[if *a == x {
                        0
                    } else if *a == y {
                        1
                    } else {
                        2
                    }]
                })
                .sum();
            if is_eq { s == t } else { s >= t }
        };
        let mut seen: [Option<(i64, i64)>; 3] = [None; 3];
        for p0 in 0..=3 {
            for p1 in -1..=2 {
                for p2 in 0..=2 {
                    if at([p0, p1, p2]) {
                        for (j, v) in [p0, p1, p2].into_iter().enumerate() {
                            let v = v as i64;
                            seen[j] = Some(seen[j].map_or((v, v), |(l, h)| (l.min(v), h.max(v))));
                        }
                    }
                }
            }
        }
        let (each, _) = project_each(&f, &[x.clone(), y.clone(), z.clone()]).unwrap();
        for j in 0..3 {
            let want = seen[j].map_or(IntervalSet::empty(), |(l, h)| range(l, h));
            assert_eq!(each[j], Ok(want), "atom {j} of {row:?} {t}");
        }
    }
}

#[test]
fn an_equation_over_choices_is_settled_by_its_residue_or_its_ends() {
    let w = weights(6);
    let ys = names(6);
    // Even weights and an odd target: no point.
    let f = parity(6);
    assert_eq!(decide(&f), Ok(false));
    let (each, _) = project_each(&f, &ys).unwrap();
    assert!(each.iter().all(|e| *e == Ok(IntervalSet::empty())));
    // Target zero: the one point is every atom at zero.
    let f = choice_sum(&w, 0);
    assert_eq!(decide(&f), Ok(true));
    let (each, _) = project_each(&f, &ys).unwrap();
    assert!(each.iter().all(|e| *e == Ok(range(0, 0))));
    // Target the whole sum: the one point is every atom at its weight.
    let f = choice_sum(&w, w.iter().sum());
    assert_eq!(decide(&f), Ok(true));
    let (each, _) = project_each(&f, &ys).unwrap();
    for (e, w) in each.iter().zip(&w) {
        assert_eq!(*e, Ok(range(*w as i64, *w as i64)));
    }
    // Past the whole sum, or below zero: no point.
    for t in [w.iter().sum::<i128>() + 1, -1] {
        assert_eq!(decide(&choice_sum(&w, t)), Ok(false), "target {t}");
    }
    // A target between the ends and on the lattice is left to the solver, which finds both
    // answers: the first and third weights, and one value no subset sums to.
    assert_eq!(decide(&choice_sum(&w, w[0] + w[2])), Ok(true));
    assert_eq!(decide(&choice_sum(&w, 1)), Ok(false));
}

#[test]
fn a_formula_with_a_product_atom_is_left_to_the_solver() {
    // The solver reads a product atom as a variable of its own (PRES-product-parity), and
    // propagation reads it through its factors; such a formula is not read here, so its answer
    // stays the solver's. Read linearly, `p == x + y + 10` has a point with `x` anywhere in
    // its box.
    let (x, y) = (sym("x"), sym("y"));
    let p = Atom::product_of(Factor::Sym(Arc::from("x")), Factor::Sym(Arc::from("y")));
    let f = Formula::and(
        [
            within(&x, 2, 3),
            within(&y, 2, 3),
            vec![eq(&[(p.clone(), 1), (x.clone(), -1), (y.clone(), -1)], -10)],
        ]
        .concat(),
    );
    assert_eq!(decide(&f), Ok(true));
    let (each, _) = project_each(&f, std::slice::from_ref(&x)).unwrap();
    assert_eq!(each[0], Ok(range(2, 3)));
}

#[test]
fn a_box_and_one_row_scale() {
    let k = 32;
    let (small, large) = (dense(k), dense(scaling::FACTOR * k));
    let (ys, yl) = (names(k), names(scaling::FACTOR * k));
    for f in [&small, &large] {
        assert_eq!(decide(f), Ok(true));
    }
    scaling::check_order("decide: a box and one row", k, 1, |m| {
        drop(decide(if m == k { &small } else { &large }));
    });
    scaling::check_order("project_each: a box and one row", k, 1, |m| {
        drop(if m == k {
            project_each(&small, &ys)
        } else {
            project_each(&large, &yl)
        });
    });
}

#[test]
fn residue_and_ends_of_a_row_scale() {
    let k = 32;
    for (name, build, answer) in [
        (
            "target zero",
            (|k| choice_sum(&weights(k), 0)) as fn(usize) -> Formula,
            true,
        ),
        ("even weights, odd target", parity, false),
    ] {
        let (small, large) = (build(k), build(scaling::FACTOR * k));
        let (ys, yl) = (names(k), names(scaling::FACTOR * k));
        for f in [&small, &large] {
            assert_eq!(decide(f), Ok(answer), "{name}");
        }
        scaling::check_order(&format!("decide: {name}"), k, 1, |m| {
            drop(decide(if m == k { &small } else { &large }));
        });
        scaling::check_order(&format!("project_each: {name}"), k, 1, |m| {
            drop(if m == k {
                project_each(&small, &ys)
            } else {
                project_each(&large, &yl)
            });
        });
    }
}

#[test]
fn satisfiable_answers_wherever_decide_does() {
    // The point `satisfiable` gives holds; an atom it leaves out is zero there.
    let agrees = |f: &Formula, what: &str| {
        let d = decide(f);
        match satisfiable(f) {
            Ok(Some(m)) => {
                assert_eq!(d, Ok(true), "{what}");
                assert!(f.holds(&m), "{what}: {m:?}");
            }
            Ok(None) => assert_eq!(d, Ok(false), "{what}"),
            Err(e) => panic!("{what}: satisfiable refused ({e:?}) where decide gave {d:?}"),
        }
    };
    // Four atoms alike in one box, with a sum each can reach: before the change the solver
    // refused this for the tie among them.
    let abcd = names(4);
    for t in [0, 9, 12, 13] {
        let mut fs: Vec<Formula> = abcd.iter().flat_map(|a| within(a, 0, 3)).collect();
        let terms: Vec<(Atom, i128)> = abcd.iter().map(|a| (a.clone(), 1)).collect();
        fs.push(eq(&terms, -t));
        let f = Formula::and(fs);
        assert_eq!(decide(&f), Ok(t <= 12), "sum {t}");
        agrees(&f, &format!("four atoms in [0, 3] with sum {t}"));
    }
    let w = weights(6);
    agrees(&parity(6), "even weights, odd target");
    agrees(&choice_sum(&w, 0), "target zero");
    agrees(&choice_sum(&w, w.iter().sum()), "target the whole sum");
    agrees(&dense(8), "a box and one row");
}

fn paired_chain(k: usize, reversed: bool) -> Formula {
    let ys: Vec<_> = (0..=k)
        .map(|i| sym(&format!("y{}", if reversed { k - i } else { i })))
        .collect();
    let mut fs = vec![eq(&[(ys[0].clone(), 1)], -1), eq(&[(ys[k].clone(), 1)], 0)];
    for pair in ys.windows(2) {
        fs.push(Formula::or(vec![
            Formula::and(pair.iter().map(|y| eq(&[(y.clone(), 1)], 0)).collect()),
            Formula::and(pair.iter().map(|y| eq(&[(y.clone(), 1)], -1)).collect()),
        ]));
    }
    Formula::and(fs)
}

#[test]
fn a_forced_contradiction_projects_to_empty_in_linear_work() {
    scaling::check_order(
        "paired chain projection via forced contradiction",
        64,
        1,
        |k| {
            let f = paired_chain(k, false);
            let (each, skipped) = project_each(&f, &[sym("y0")]).unwrap();
            assert_eq!(each, vec![Ok(IntervalSet::empty())]);
            assert!(skipped.is_empty());
        },
    );
}

#[test]
fn a_forced_contradiction_has_the_same_empty_projection_after_renaming() {
    for k in [8, 64, 512] {
        let f = paired_chain(k, false);
        let g = paired_chain(k, true);
        assert_eq!(decide(&f), Ok(false));
        assert_eq!(decide(&g), Ok(false));
        assert_eq!(satisfiable(&g).map(|m| m.is_some()), Ok(false));
        assert_eq!(
            project_each(&f, &[sym("y0")]),
            project_each(&g, &[sym(&format!("y{k}"))])
        );
    }
}
