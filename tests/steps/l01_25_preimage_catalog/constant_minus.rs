//! Plan item S22b: the backward transfer of `c - x` for a constant `c`. The integers `x` with
//! `c - x` in `z` are `c - z`, each piece of `z` reflected and moved by `c`, so the preimage
//! keeps every piece of the demand and is exact. The transfer before took `c - z` as the
//! forward image of `{c} - z`, which caps the pieces of each sign region of the image
//! (`revision::map2`), so pieces moved across zero were merged and the merged box was still
//! marked exact.

use zed_kernel::{Prim, Term, Value};
use zed_tests::scaling;
use zedc::store::interval::{End, IntervalSet};
use zedc::store::preimage::{Demand, Domains, preimage};

use super::{check, doms, pre, shown};

fn var(x: &str) -> Term {
    Term::Var(x.into())
}

fn int(n: i64) -> Term {
    Term::Lit(Value::Int(n))
}

fn minus(c: i64, x: Term) -> Term {
    Term::Prim(Prim::Sub, vec![int(c), x])
}

fn pieces(ps: &[(End, End)]) -> IntervalSet {
    IntervalSet::from_pieces(ps.to_vec())
}

fn fin(ps: &[(i64, i64)]) -> IntervalSet {
    pieces(
        &ps.iter()
            .map(|&(a, b)| (End::Fin(a), End::Fin(b)))
            .collect::<Vec<_>>(),
    )
}

/// `x` over all integers.
fn any_x() -> Domains {
    doms(&[("x", None, None)])
}

/// The preimage of `z` under `c - x` over `ds`, checked against the interpreter on the
/// window `-60..=60` and printed.
fn reflected(c: i64, ds: &Domains, z: IntervalSet) -> String {
    let t = minus(c, var("x"));
    let d = Demand::Ints(z);
    let p = preimage(&t, ds, &d);
    check(&t, ds, &d, &p, (-60, 60));
    shown(&p)
}

/// A target and a tolerance: `x` is at least 5 from 12. `abs` gives `12 - x` two rays, one
/// on each side of zero; the transfer before merged them into every integer, exact.
#[test]
fn a_distance_from_a_target_keeps_both_rays() {
    let src = "ok(x) = abs(12 - x) >= 5;\n";
    let ds = [("x", None, None)];
    let p = pre(src, &ds, &Demand::Bool(true));
    let (_, body) = super::function(src);
    check(&body, &doms(&ds), &Demand::Bool(true), &p, (-60, 60));
    assert_eq!(shown(&p), "x [..=7, 17..]; exact");
    // Within 3 of 12: one piece, as before.
    let src = "ok(x) = abs(12 - x) <= 3;\n";
    let p = pre(src, &ds, &Demand::Bool(true));
    assert_eq!(shown(&p), "x [9..=15]; exact");
}

/// The case of the cross-check (xs22 VERIFY_CLAUDE flaw a): `abs(4 * 3) - x` over
/// `[-40, 40]`. Before, the box was `[-13, 22]`, exact, and held 9 points that fail.
#[test]
fn a_constant_folded_from_a_term_keeps_the_pieces_of_the_demand() {
    let t = Term::Prim(
        Prim::Sub,
        vec![
            Term::Prim(Prim::Abs, vec![Term::Prim(Prim::Mul, vec![int(4), int(3)])]),
            var("x"),
        ],
    );
    let ds = doms(&[("x", Some(-40), Some(40))]);
    let d = Demand::Ints(fin(&[(-10, 0), (10, 25)]));
    let p = preimage(&t, &ds, &d);
    check(&t, &ds, &d, &p, (-60, 60));
    assert_eq!(shown(&p), "x [-13..=2, 12..=22]; exact");
}

/// Each piece of the demand is one piece of the preimage, in reverse order, whichever side
/// of zero it lies on before and after.
#[test]
fn every_piece_of_the_demand_is_kept() {
    let z = fin(&[(-30, -20), (-5, -5), (-1, 1), (3, 4), (9, 40)]);
    assert_eq!(
        reflected(2, &any_x(), z.clone()),
        "x [-38..=-7, -2..=-1, 1..=3, 7..=7, 22..=32]; exact"
    );
    assert_eq!(
        reflected(0, &any_x(), z.clone()),
        "x [-40..=-9, -4..=-3, -1..=1, 5..=5, 20..=30]; exact"
    );
    assert_eq!(
        reflected(-7, &any_x(), z),
        "x [-47..=-16, -11..=-10, -8..=-6, -2..=-2, 13..=23]; exact"
    );
}

/// Rays, every integer, one point and the empty demand.
#[test]
fn rays_points_and_the_empty_demand() {
    let ray_down = pieces(&[(End::NegInf, End::Fin(-3)), (End::Fin(4), End::Fin(6))]);
    assert_eq!(reflected(5, &any_x(), ray_down), "x [-1..=1, 8..]; exact");
    let ray_up = pieces(&[(End::Fin(-2), End::Fin(-2)), (End::Fin(10), End::PosInf)]);
    assert_eq!(reflected(5, &any_x(), ray_up), "x [..=-5, 7..=7]; exact");
    assert_eq!(reflected(5, &any_x(), IntervalSet::top()), "x [..]; exact");
    assert_eq!(reflected(5, &any_x(), fin(&[(0, 0)])), "x [5..=5]; exact");
    let none = reflected(5, &any_x(), IntervalSet::empty());
    assert_eq!(none, "x []; exact");
}

/// The domain of `x` meets the reflected demand: pieces outside it are dropped.
#[test]
fn the_domain_of_the_input_meets_the_reflection() {
    let z = fin(&[(-30, -20), (-5, 5), (25, 30)]);
    assert_eq!(
        reflected(10, &doms(&[("x", Some(0), Some(35))]), z),
        "x [5..=15, 30..=35]; exact"
    );
}

/// The ends of `i64`: `i64::MAX - x` and `i64::MIN - x`. A reflected end past `i64` is read as
/// the infinity on its side or rounded outward, so the box keeps every point that meets the
/// demand; within `i64` it is exact.
#[test]
fn the_ends_of_i64() {
    let (max, min) = (i64::MAX, i64::MIN);
    let all = any_x();
    let at = |c, z: IntervalSet| {
        let t = minus(c, var("x"));
        preimage(&t, &all, &Demand::Ints(z))
    };
    // MAX - x in [MAX - 5, MAX] for x in [0, 5].
    let p = at(max, fin(&[(max - 5, max)]));
    assert_eq!(shown(&p), "x [0..=5]; exact");
    // MIN - x in [MIN, MIN + 2] for x in [-2, 0].
    let p = at(min, fin(&[(min, min + 2)]));
    assert_eq!(shown(&p), "x [-2..=0]; exact");
    // MAX - x in [MIN, -1] for x >= MAX + 1, past `i64`: the lower end is rounded down to
    // MAX, whose ray holds every integer beyond it, and the box is not exact.
    let p = at(max, pieces(&[(End::NegInf, End::Fin(-1))]));
    assert_eq!(shown(&p), "x [9223372036854775807..]; necessary");
    // MIN - x for z a ray down to MIN: x >= 0 at the top end.
    let p = at(min, pieces(&[(End::NegInf, End::Fin(min))]));
    assert_eq!(p.domains["x"], pieces(&[(End::Fin(0), End::PosInf)]));
}

/// A demand of `n` pieces on each side of zero: `n - 3 - x` keeps `2n` pieces, so the
/// transfer is linear in the pieces after sorting them.
fn comb(n: usize) -> (Term, Domains, Demand) {
    let n = n as i64;
    let ps: Vec<(i64, i64)> = (-n..n).map(|j| (4 * j, 4 * j + 1)).collect();
    (minus(n - 3, var("x")), any_x(), Demand::Ints(fin(&ps)))
}

#[test]
fn a_comb_of_pieces_is_kept_exactly() {
    let (t, ds, d) = comb(12);
    let p = preimage(&t, &ds, &d);
    check(&t, &ds, &d, &p, (-60, 60));
    assert!(p.exact, "{}", shown(&p));
    assert_eq!(p.domains["x"].pieces().len(), 24);
}

#[test]
fn a_comb_of_pieces_scales() {
    let n = 4096;
    let (a, b) = (comb(n), comb(n * scaling::FACTOR));
    scaling::check("the preimage of c - x over a demand of n pieces", n, |k| {
        let (t, ds, d) = if k == n { &a } else { &b };
        let p = preimage(t, ds, d);
        assert_eq!(p.domains["x"].pieces().len(), 2 * k);
    });
}
