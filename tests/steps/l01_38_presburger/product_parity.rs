//! A point `satisfiable` returns is a point of the formula as the solver reads it, each atom a
//! variable of its own, a product `x * y` included (PRES-product-parity). The solver once read
//! a product atom inside its search as the product of its factors' values: in
//! `((x*y >= 3 && x == q0 - 2) || (!(x*y >= 3) && q0 == 1)) && x == 0 && x*y == 3 &&
//! q0 == 2*q3 + 1` its point of the base gives `x*y` the value 3 and `y` none, so the second
//! disjunct's `x*y <= 2` read `0 * 0` and held there; the disjunct was kept, the search took
//! it, and the point `{x: 0, x*y: 3, q0: 1, q3: 0}` came back, though `x*y <= 2` fails at it
//! and the formula has no point at all. Propagation (`forced`) now answers that case before
//! the solver; the same case with `x` bounded by two rows, and a case with `x` free, still
//! reach the solver's search.

use std::collections::BTreeSet;
use std::sync::Arc;

use zed_tests::instances::Rng;
use zedc::store::int::Int;
use zedc::store::presburger::{Atom, Con, Formula, Lin, Model, Rel, decide, satisfiable};

fn sym(x: &str) -> Lin {
    Lin::atom(Atom::Sym(Arc::from(x)))
}

fn q(i: u32) -> Lin {
    Lin::atom(Atom::Aux(i))
}

fn k(v: i64) -> Lin {
    Lin::constant(v)
}

fn product() -> Lin {
    Lin::atom(Atom::product(&Arc::from("x"), &Arc::from("y")))
}

fn ge(a: &Lin, b: &Lin) -> Formula {
    Formula::Con(Con::ge(a, b))
}

fn eq(a: &Lin, b: &Lin) -> Formula {
    Formula::Con(Con::eq(a, b))
}

/// The value of `c` at `m` with each atom, a product included, a variable of its own and an
/// absent atom zero: the reading the solver decides.
fn con_holds(c: &Con, m: &Model) -> bool {
    let mut v = c.lin.constant.clone();
    for (a, coef) in &c.lin.terms {
        if let Some(x) = m.get(a) {
            v = &v + &(coef * x);
        }
    }
    match c.rel {
        Rel::Eq => v.is_zero(),
        Rel::Ge => !v.is_negative(),
    }
}

/// Whether `f` holds at `m`, read as [`con_holds`] reads each constraint. The formulas here are
/// a few levels deep, so plain recursion is enough.
fn holds(f: &Formula, m: &Model) -> bool {
    match f {
        Formula::Con(c) => con_holds(c, m),
        Formula::Not(g) => !holds(g, m),
        Formula::And(gs) => gs.iter().all(|g| holds(g, m)),
        Formula::Or(gs) => gs.iter().any(|g| holds(g, m)),
    }
}

/// The case PRES-small-front found: no point, since `x == 0` and `x * y == 3` take the first
/// disjunct, which makes `q0 == 2`, and `q0` is odd. Propagation (`forced`), which runs before
/// the solver, now answers this case itself; the cases below reach the solver.
fn found_case() -> Formula {
    let (p, x) = (product(), sym("x"));
    Formula::and(vec![
        Formula::or(vec![
            Formula::and(vec![ge(&p, &k(3)), eq(&x, &q(0).minus(&k(2)))]),
            Formula::and(vec![Formula::negate(ge(&p, &k(3))), eq(&q(0), &k(1))]),
        ]),
        eq(&x, &k(0)),
        eq(&p, &k(3)),
        eq(&q(0), &q(3).times(2).plus(&k(1))),
    ])
}

#[test]
fn a_product_fixed_beside_a_parity_row_leaves_no_point() {
    let f = found_case();
    assert_eq!(satisfiable(&f), Ok(None), "{f}");
    assert_eq!(decide(&f), Ok(false), "{f}");
}

/// [`found_case`] with `x == 0` written as two bounds, which propagation (`forced`) does not
/// read, so the solver itself must answer it.
#[test]
fn the_found_case_with_x_bounded_by_two_rows_reaches_the_solver_and_has_no_point() {
    let (p, x) = (product(), sym("x"));
    let f = Formula::and(vec![
        Formula::or(vec![
            Formula::and(vec![ge(&p, &k(3)), eq(&x, &q(0).minus(&k(2)))]),
            Formula::and(vec![Formula::negate(ge(&p, &k(3))), eq(&q(0), &k(1))]),
        ]),
        ge(&x, &k(0)),
        ge(&k(0), &x),
        eq(&p, &k(3)),
        eq(&q(0), &q(3).times(2).plus(&k(1))),
    ]);
    assert_eq!(satisfiable(&f), Ok(None), "{f}");
    assert_eq!(decide(&f), Ok(false), "{f}");
}

/// `x` is free, so propagation leaves the formula to the solver. The first disjunct needs
/// `q0 == 2`, which the parity row forbids, so the point must take the second, `x <= -2` and
/// `q0 == 3`. The solver once read `x * y` at its base point, `x` absent, as `0 * 0`, so
/// `x * y == q0 - 1` held with `q0 == 1` and the first disjunct was taken.
#[test]
fn a_free_factor_does_not_make_the_product_zero_inside_the_search() {
    let (p, x) = (product(), sym("x"));
    let f = Formula::and(vec![
        Formula::or(vec![
            Formula::and(vec![ge(&x, &k(-1)), eq(&p, &q(0).minus(&k(1)))]),
            Formula::and(vec![Formula::negate(ge(&x, &k(-1))), eq(&q(0), &k(3))]),
        ]),
        eq(&q(0), &q(10).times(2).plus(&k(1))),
        eq(&p, &k(1)),
    ]);
    let m = satisfiable(&f).expect("decided").expect("a point");
    assert!(holds(&f, &m), "{m:?} is no point of {f}");
    assert_eq!(m.get(&Atom::Aux(0)), Some(&Int::from(3)), "{m:?}");
}

#[test]
fn the_same_case_with_an_even_parity_row_has_its_point() {
    // `q0 == 2 * q3` lets the first disjunct hold with `q0 == 2`.
    let (p, x) = (product(), sym("x"));
    let f = Formula::and(vec![
        Formula::or(vec![
            Formula::and(vec![ge(&p, &k(3)), eq(&x, &q(0).minus(&k(2)))]),
            Formula::and(vec![Formula::negate(ge(&p, &k(3))), eq(&q(0), &k(1))]),
        ]),
        eq(&x, &k(0)),
        eq(&p, &k(3)),
        eq(&q(0), &q(3).times(2)),
    ]);
    let m = satisfiable(&f).expect("decided").expect("a point");
    assert!(holds(&f, &m), "{m:?} is no point of {f}");
    assert_eq!(m.get(&Atom::Aux(0)), Some(&Int::from(2)), "{m:?}");
}

#[test]
fn a_disjunct_whose_product_bound_the_base_breaks_is_not_taken() {
    // Without the parity row: the second disjunct needs `x * y <= 2`, which `x * y == 3`
    // breaks, so the point must take the first, `q0 == 2`.
    let (p, x) = (product(), sym("x"));
    let f = Formula::and(vec![
        Formula::or(vec![
            Formula::and(vec![ge(&p, &k(3)), eq(&x, &q(0).minus(&k(2)))]),
            Formula::and(vec![Formula::negate(ge(&p, &k(3))), eq(&q(0), &k(1))]),
        ]),
        eq(&x, &k(0)),
        eq(&p, &k(3)),
    ]);
    let m = satisfiable(&f).expect("decided").expect("a point");
    assert!(holds(&f, &m), "{m:?} is no point of {f}");
    assert_eq!(m.get(&Atom::Aux(0)), Some(&Int::from(2)), "{m:?}");
}

/// A random formula of the shape the preimage of a chain of `if` gives, with the product
/// `x * y` as an atom: definitions `(g && c * q_i == e1) || (!g && q_i == e2)` whose guard
/// `g` reads an input, the product or an earlier definition, rows of parity
/// `q_i == m * q_(10 + i) + r`, and the inputs and the product fixed, bounded or left free.
fn case(rng: &mut Rng) -> Formula {
    let p = product();
    let mut fs = Vec::new();
    let defs = 1 + rng.below(3) as u32;
    for i in 0..defs {
        let over = |rng: &mut Rng| match rng.below(4) {
            0 => sym("x"),
            1 => sym("y"),
            2 if i > 0 => q(rng.below(i as usize) as u32),
            _ => p.clone(),
        };
        let g = ge(&over(rng), &k(rng.int(-3, 3)));
        let c = rng.int(1, 2);
        let e1 = over(rng).plus(&k(rng.int(-3, 3)));
        let e2 = k(rng.int(-3, 3));
        fs.push(Formula::or(vec![
            Formula::and(vec![g.clone(), eq(&q(i).times(c), &e1)]),
            Formula::and(vec![Formula::negate(g), eq(&q(i), &e2)]),
        ]));
        if rng.below(3) > 0 {
            let m = rng.int(2, 3);
            let r = rng.int(0, m - 1);
            fs.push(eq(&q(i), &q(10 + i).times(m).plus(&k(r))));
        }
    }
    for a in [sym("x"), sym("y"), p] {
        let v = rng.int(-3, 3);
        match rng.below(5) {
            0 => {}
            1 => fs.push(ge(&a, &k(v))),
            2 => fs.push(ge(&k(v), &a)),
            _ => fs.push(eq(&a, &k(v))),
        }
    }
    Formula::and(fs)
}

/// Whether `f` holds at some point whose atoms lie in `-w..=w`, each atom read as
/// [`con_holds`] reads it.
fn point_in_window(f: &Formula, w: i64) -> Option<Model> {
    let atoms: Vec<Atom> = f.atoms().into_iter().collect();
    let mut at = vec![-w; atoms.len()];
    loop {
        let m: Model = atoms
            .iter()
            .cloned()
            .zip(at.iter().map(|v| Int::from(*v)))
            .collect();
        if holds(f, &m) {
            return Some(m);
        }
        let mut i = 0;
        loop {
            if i == at.len() {
                return None;
            }
            if at[i] < w {
                at[i] += 1;
                break;
            }
            at[i] = -w;
            i += 1;
        }
    }
}

/// Every point `satisfiable` returns on 300 random formulas of [`case`]'s shape, of a new seed
/// each run, holds there, as [`points_returned_hold`] checks. The 3000 formulas of seed
/// 0x5eed0f9a417e5 are in `bench::product_parity` (5.9 s at load 25); there 1 in 20 at most is
/// refused, and here at most 1 in 10.
#[test]
fn every_point_returned_holds_with_products_parity_rows_and_disjunctions() {
    let (mut rng, _) = Rng::fresh("products, parity rows and disjunctions");
    let t = points_returned_hold(&mut rng, 300);
    // Both answers occur often enough to be tested, and few questions are refused.
    assert!(t.points >= 50 && t.empty >= 50, "{t:?}");
    assert!(t.searched >= 10, "{t:?}");
    assert!(t.refused * 10 <= 300, "{t:?}");
    assert!(t.shapes.len() >= 3, "{t:?}");
}

/// What [`points_returned_hold`] counted.
#[derive(Debug)]
pub(super) struct PointCounts {
    pub(super) points: usize,
    pub(super) empty: usize,
    pub(super) refused: usize,
    pub(super) searched: usize,
    /// The numbers of atoms of the formulas with a point.
    pub(super) shapes: BTreeSet<usize>,
}

/// Every point `satisfiable` returns on `count` random formulas of [`case`]'s shape drawn from
/// `rng` holds there, read as the solver reads it; it returns one exactly when `decide`
/// answers `true`; and where it returns none and the formula has at most five atoms, no point
/// lies in `-3..=3`.
pub(super) fn points_returned_hold(rng: &mut Rng, count: usize) -> PointCounts {
    let (mut points, mut empty, mut refused, mut searched) = (0, 0, 0, 0);
    let mut shapes = BTreeSet::new();
    for _ in 0..count {
        let f = case(rng);
        let (Ok(m), Ok(d)) = (satisfiable(&f), decide(&f)) else {
            refused += 1;
            continue;
        };
        assert_eq!(m.is_some(), d, "satisfiable and decide of {f}");
        match m {
            Some(m) => {
                assert!(holds(&f, &m), "the point {m:?} is none of {f}");
                points += 1;
                shapes.insert(f.atoms().len());
            }
            None => {
                empty += 1;
                if f.atoms().len() <= 5 {
                    searched += 1;
                    let found = point_in_window(&f, 3);
                    assert_eq!(found, None, "{f} has a point, but the solver found none");
                }
            }
        }
    }
    eprintln!("points {points}, empty {empty} ({searched} searched), refused {refused}");
    PointCounts {
        points,
        empty,
        refused,
        searched,
        shapes,
    }
}
