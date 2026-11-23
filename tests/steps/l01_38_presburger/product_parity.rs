//! A point `satisfiable` returns is a point of the formula, and the solver's search reads each
//! atom as a variable of its own, a product `x * y` included (PRES-product-parity). It once read
//! a product atom inside its search as the product of its factors' values: in
//! `((x*y >= 3 && x == q0 - 2) || (!(x*y >= 3) && q0 == 1)) && x == 0 && x*y == 3 &&
//! q0 == 2*q3 + 1` its point of the base gives `x*y` the value 3 and `y` none, so the second
//! disjunct's `x*y <= 2` read `0 * 0` and held there; the disjunct was kept, the search took
//! it, and the point `{x: 0, x*y: 3, q0: 1, q3: 0}` came back, though `x*y <= 2` fails at it
//! and the formula has no point at all. Propagation (`forced`) now answers that case before
//! the solver; the same case with `x` bounded by two rows, and a case with `x` free, still
//! reach the solver's search. Since PRES-model-products, `satisfiable` and `decide` answer the
//! reading with each product the product of its factors: a point returned gives each product
//! that value, and the oracle below reads products so.

use std::collections::BTreeSet;
use std::sync::Arc;

use zed_tests::instances::Rng;
use zedc::store::int::Int;
use zedc::store::presburger::{Atom, Con, Formula, Lin, Model, Refusal, Rel, decide, satisfiable};

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

/// The value of `a` at `m`, an absent atom zero and a product the product of its factors'
/// values: the reading `satisfiable` and `decide` answer (PRES-model-products).
fn value(a: &Atom, m: &Model) -> Int {
    let at = |a: &Atom| m.get(a).cloned().unwrap_or(Int::ZERO);
    match a {
        Atom::Product(x, y) => &at(&x.atom()) * &at(&y.atom()),
        _ => at(a),
    }
}

/// The value of `c` at `m`, each atom read as [`value`] reads it.
fn con_holds(c: &Con, m: &Model) -> bool {
    let mut v = c.lin.constant.clone();
    for (a, coef) in &c.lin.terms {
        v = &v + &(coef * &value(a, m));
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
/// `q0 == 2`, which the parity row forbids. The solver once read `x * y` at its base point,
/// `x` absent, as `0 * 0`, so `x * y == q0 - 1` held with `q0 == 1` and the first disjunct
/// was taken. Read with `x * y` a variable of its own, the second disjunct had the point
/// `x <= -2, q0 == 3` (this test pinned it until PRES-model-products); read through the
/// factors it has none, since `x * y == 1` needs `x` to be `1` or `-1`. The search's point
/// disagrees, the slices at `x`'s values miss, and the cover of `x * y == 1` by the divisors
/// of 1 (`divisor_cover` in `presburger.rs`) shows the formula empty, exactly.
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
    assert_eq!(satisfiable(&f), Ok(None), "{f}");
    assert_eq!(decide(&f), Ok(false), "{f}");
}

#[test]
fn the_same_case_with_an_even_parity_row_has_its_point() {
    // `q0 == 2 * q3` lets the first disjunct hold with `q0 == 2`. Until PRES-model-products
    // the case had `x == q0 - 2` and `x == 0`, whose product `0` is not `3`: a point only with
    // `x * y` read as a variable of its own. With `x == q0 - 1` and `x == 1` the same
    // disjunct needs the same `q0 == 2`, and `y == 3` makes the point one through the factors.
    let (p, x) = (product(), sym("x"));
    let f = Formula::and(vec![
        Formula::or(vec![
            Formula::and(vec![ge(&p, &k(3)), eq(&x, &q(0).minus(&k(1)))]),
            Formula::and(vec![Formula::negate(ge(&p, &k(3))), eq(&q(0), &k(1))]),
        ]),
        eq(&x, &k(1)),
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
    // breaks, so the point must take the first, `q0 == 2`. Written with `x == 1` (and
    // `x == q0 - 1`) since PRES-model-products, as the case above is.
    let (p, x) = (product(), sym("x"));
    let f = Formula::and(vec![
        Formula::or(vec![
            Formula::and(vec![ge(&p, &k(3)), eq(&x, &q(0).minus(&k(1)))]),
            Formula::and(vec![Formula::negate(ge(&p, &k(3))), eq(&q(0), &k(1))]),
        ]),
        eq(&x, &k(1)),
        eq(&p, &k(3)),
    ]);
    let m = satisfiable(&f).expect("decided").expect("a point");
    assert!(holds(&f, &m), "{m:?} is no point of {f}");
    assert_eq!(m.get(&Atom::Aux(0)), Some(&Int::from(2)), "{m:?}");
}

/// A product with a fixed factor is the other factor times its value (PRES-model-products):
/// `x * y >= 1 && x == 0` has no point, though the solver, reading `x * y` as an atom of its
/// own, once found `{x: 0, x * y: 1}`. With `x == 2`, `x * y == 6` gives `y == 3` and keeps
/// the product in the point, at 6; `x * y == 5` has no point, as `2 * y` is even; and both
/// factors fixed make the product their product.
#[test]
fn a_product_with_a_fixed_factor_is_read_through_that_factor() {
    let (p, x, y) = (product(), sym("x"), sym("y"));
    let f = Formula::and(vec![ge(&p, &k(1)), eq(&x, &k(0))]);
    assert_eq!(satisfiable(&f), Ok(None), "{f}");
    assert_eq!(decide(&f), Ok(false), "{f}");
    let six = Formula::and(vec![eq(&p, &k(6)), eq(&x, &k(2)), ge(&k(9), &y)]);
    let m = satisfiable(&six).expect("decided").expect("a point");
    let at = |a: &Lin| m.get(a.terms.keys().next().unwrap()).cloned();
    assert_eq!(
        (at(&x), at(&y), at(&p)),
        (Some(Int::from(2)), Some(Int::from(3)), Some(Int::from(6))),
        "{m:?}"
    );
    let five = Formula::and(vec![eq(&p, &k(5)), eq(&x, &k(2))]);
    assert_eq!(satisfiable(&five), Ok(None), "{five}");
    assert_eq!(decide(&five), Ok(false), "{five}");
    let both = Formula::and(vec![ge(&p, &k(7)), eq(&x, &k(2)), eq(&y, &k(3))]);
    assert_eq!(decide(&both), Ok(false), "{both}");
    assert_eq!(satisfiable(&both), Ok(None), "{both}");
}

/// Both factors free: `x * y == 6 && x >= 4 && x <= 5` has no point read through the factors
/// (6 has no factor 4 or 5), but read with `x * y` a variable of its own it has `{x: 4,
/// x * y: 6}`. No step fixes a factor, so the solver's point is checked
/// (`products_agree`): its products disagree, and no other point is searched for, so the answer
/// is a refusal, never `true` or that point (PRES-model-products: answers are exact).
#[test]
fn a_point_whose_product_disagrees_with_free_factors_is_not_returned() {
    let (p, x) = (product(), sym("x"));
    let f = Formula::and(vec![eq(&p, &k(6)), ge(&x, &k(4)), ge(&k(5), &x)]);
    match satisfiable(&f) {
        Ok(Some(m)) => panic!("the point {m:?} of {f}: 6 has no factor 4 or 5"),
        Ok(None) | Err(Refusal::Products) => {}
        Err(e) => panic!("{f}: refused for {e:?}"),
    }
    assert_ne!(decide(&f), Ok(true), "{f}");
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

/// Whether `f` holds at some point whose atoms other than products lie in `-w..=w`, each atom
/// read as [`con_holds`] reads it, a product through its factors.
fn point_in_window(f: &Formula, w: i64) -> Option<Model> {
    let atoms: Vec<Atom> = (f.atoms().into_iter())
        .flat_map(|a| match a {
            Atom::Product(x, y) => vec![x.atom(), y.atom()],
            a => vec![a],
        })
        .collect::<BTreeSet<Atom>>()
        .into_iter()
        .collect();
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
/// each run, holds there, as [`points_returned_hold`] checks. Both answers, the search of an
/// empty formula's window and the share refused occur at every seed tried, but no count of them
/// is reached at every seed, so none is asserted here: the first 300 formulas of seed
/// 0x5eed0f9a417e5 below have exact counts, and the 3000 of the seed are in
/// `bench::product_parity` (5.9 s at load 25).
#[test]
fn every_point_returned_holds_with_products_parity_rows_and_disjunctions() {
    let (mut rng, _) = Rng::fresh("products, parity rows and disjunctions");
    points_returned_hold(&mut rng, 300);
}

/// The first 300 formulas of seed 0x5eed0f9a417e5, as
/// [`every_point_returned_holds_with_products_parity_rows_and_disjunctions`] checks them: both
/// answers, the search of the window of an empty formula of at most five atoms, and points on
/// formulas of several sizes each occur, and the refusals are counted exactly. Until
/// PRES-model-products the counts were (183, 117, 32, 0, 7), each product read as a variable
/// of its own. Of those 183 points, 72 gave `x * y` a value other than `x` times `y` (the
/// first, formula 0: `y == 0 && x * y == -2`, at `x * y == -2`); read through the factors, 68
/// of those formulas are empty and 4 refused ([`Refusal::Products`]), and the other 111 points
/// are the points returned now (each formula's answer on the old and the new code compared,
/// 2026-11-22). The 68 new empty answers are checked by the window of factor values in
/// [`points_returned_hold`].
#[test]
fn the_first_300_formulas_of_seed_0x5eed0f9a417e5_are_answered_as_counted() {
    let t = points_returned_hold(&mut Rng::new(0x0005_eed0_f9a4_17e5), 300);
    assert_eq!(
        (t.points, t.empty, t.searched, t.refused, t.shapes.len()),
        (111, 185, 62, 4, 7),
        "{t:?}"
    );
}

/// Formula 1024 of seed 0x5eed0f9a417e5 (counted from 0), checked as [`points_returned_hold`]
/// checks it. It reached the substitution, unit-coefficient and equality checks of
/// `cell_sweep::piecewise_implies_ge`; of the 3000 formulas of the seed in
/// `bench::product_parity` it was the first to. Until PRES-model-products it had a point with
/// `x * y` read as a variable of its own; read through the factors it has none, and the window
/// of factor values of [`points_returned_hold`] confirms the empty answer. Whether it still
/// reaches `piecewise_implies_ge` was not checked again.
#[test]
fn formula_1024_of_seed_0x5eed0f9a417e5_is_empty_read_through_its_factors() {
    let mut rng = Rng::new(0x0005_eed0_f9a4_17e5);
    for _ in 0..1024 {
        case(&mut rng);
    }
    let t = points_returned_hold(&mut rng, 1);
    assert_eq!((t.points, t.empty, t.refused), (0, 1, 0), "{t:?}");
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
/// `rng` holds there, each product read through its factors, and gives each product the
/// product of its factors' values (PRES-model-products); it returns one exactly when `decide`
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
                for (a, v) in &m {
                    assert_eq!(&value(a, &m), v, "{a:?} in the point {m:?} of {f}");
                }
                points += 1;
                shapes.insert(f.atoms().len());
            }
            None => {
                empty += 1;
                // Each pair of factor values in `-4..=4` makes every product linear, which
                // the search answers exactly (`reduced`), so a slice with a point would be a
                // point the answer missed: this checks the reading of the products on that
                // window whatever the number of atoms (PRES-model-products).
                for (a, b) in (-4..=4).flat_map(|a| (-4..=4).map(move |b| (a, b))) {
                    let g =
                        Formula::and(vec![f.clone(), eq(&sym("x"), &k(a)), eq(&sym("y"), &k(b))]);
                    assert_eq!(satisfiable(&g), Ok(None), "{f} has a point at x {a}, y {b}");
                }
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
