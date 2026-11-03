//! Plan item S22b: the backward transfer of `c - x` for a constant `c`. The integers `x` with
//! `c - x` in `z` are `c - z`, each piece of `z` reflected and moved by `c`, so the preimage
//! keeps every piece of the demand and is exact. The transfer before took `c - z` as the
//! forward image of `{c} - z`, which caps the pieces of each sign region of the image
//! (`revision::map2`), so pieces moved across zero were merged and the merged box was still
//! marked exact.

use std::sync::Arc;

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
            .map(|&(a, b)| (End::of(a), End::of(b)))
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
    let ray_down = pieces(&[(End::NegInf, End::of(-3)), (End::of(4), End::of(6))]);
    assert_eq!(reflected(5, &any_x(), ray_down), "x [-1..=1, 8..]; exact");
    let ray_up = pieces(&[(End::of(-2), End::of(-2)), (End::of(10), End::PosInf)]);
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
    let p = at(max, pieces(&[(End::NegInf, End::of(-1))]));
    assert_eq!(shown(&p), "x [9223372036854775807..]; necessary");
    // MIN - x for z a ray down to MIN: x >= 0 at the top end.
    let p = at(min, pieces(&[(End::NegInf, End::of(min))]));
    assert_eq!(p.domains["x"], pieces(&[(End::of(0), End::PosInf)]));
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

// Plan item S22b-rest: the summary of a term of one input (`Pa`) reads `c - u` as the affine
// map `-1 * u + c` for every constant `c`; before, it read only `0 - u`, so an `if` chain with
// an arm `c - t` was left to the transfer level by level (`s22::chain_jt_range_live_scales`).
// The clip, the hull of a term's values met with each integer demand, reads `c - x` by the
// same reflection as the transfer; the forward image it used before gave the same set for the
// one interval a clip is, but raised the rounding flag for `i64::MIN - x` with `x` unbounded
// above and `i64::MAX - x` with `x` unbounded below, so the clip gave up there.

fn times(fs: &[i64]) -> Term {
    let mut it = fs.iter().map(|&f| int(f));
    let first = it.next().expect("a factor");
    it.fold(first, |a, b| Term::Prim(Prim::Mul, vec![a, b]))
}

/// `i64::MAX` and `i64::MIN` as products of small factors. The summary and the clip read a
/// term only when the magnitudes of its literals summed stay within `i64` (`Tx::fits`), so a
/// literal `i64::MAX` would turn them off.
fn max_c() -> Term {
    times(&[49, 73, 127, 337, 92737, 649657])
}

fn min_c() -> Term {
    times(&[-2147483648, 4294967296])
}

/// `if i >= 0 { c - i } else { c - (i + 3) }`: both arms reflect the one input, so the `if` is
/// summarized and the demand inverted through it.
fn reflected_arms(c: Term) -> Term {
    reflected_by(c, 3)
}

/// `if i >= 0 { c - i } else { c - (i + s) }`.
fn reflected_by(c: Term, s: i64) -> Term {
    let i = || var("i");
    let shifted = Term::Prim(Prim::Add, vec![i(), int(s)]);
    Term::If(
        Arc::new(Term::Prim(Prim::Ge, vec![i(), int(0)])),
        Arc::new(Term::Prim(Prim::Sub, vec![c.clone(), i()])),
        Arc::new(Term::Prim(Prim::Sub, vec![c, shifted])),
    )
}

/// The preimage of `z` under `t` over `i` in `[-60, 60]`, checked against the interpreter and
/// printed; every one here is exact.
fn summarized(t: &Term, z: IntervalSet) -> String {
    summarized_over(t, fin(&[(-60, 60)]), z)
}

/// [`summarized`] over `i` in `dom`.
fn summarized_over(t: &Term, dom: IntervalSet, z: IntervalSet) -> String {
    let ds: Domains = [("i".into(), dom)].into_iter().collect();
    let d = Demand::Ints(z);
    let p = preimage(t, &ds, &d);
    check(t, &ds, &d, &p, (-60, 60));
    assert!(p.exact, "{t}: {}", shown(&p));
    shown(&p)
}

/// A demand of pieces on both sides of zero through `5 - i` and `5 - (i + 3)`: each piece is
/// kept, reflected in the arm whose guard holds there.
#[test]
fn reflected_arms_keep_every_piece_of_the_demand() {
    let t = reflected_arms(int(5));
    let z = fin(&[(-30, -20), (-1, 1), (4, 9)]);
    assert_eq!(
        summarized(&t, z),
        "i [-7..=-2, 0..=1, 4..=6, 25..=35]; exact"
    );
    // c = 0, the one case the summary read before.
    let t = reflected_arms(int(0));
    let z = fin(&[(-30, -20), (-1, 1), (4, 9)]);
    assert_eq!(
        summarized(&t, z),
        "i [-12..=-7, -4..=-2, 0..=1, 20..=30]; exact"
    );
}

/// One point, the empty demand and every integer.
#[test]
fn reflected_arms_under_a_point_nothing_and_everything() {
    let t = reflected_arms(int(-7));
    assert_eq!(summarized(&t, fin(&[(0, 0)])), "i [-10..=-10]; exact");
    assert_eq!(
        summarized(&t, fin(&[(-9, -9)])),
        "i [-1..=-1, 2..=2]; exact"
    );
    assert_eq!(summarized(&t, fin(&[(-4, -4)])), "i [-6..=-6]; exact");
    assert_eq!(summarized(&t, IntervalSet::empty()), "i []; exact");
    assert_eq!(summarized(&t, IntervalSet::top()), "i [-60..=60]; exact");
}

/// `i64::MAX - i` with the else arm `i64::MAX - (i + 3)`, and `i64::MIN - i` with the else arm
/// `i64::MIN - (i - 3)`. Over the inputs where both arms stay in `i64`, `[-3, 60]` and
/// `[-60, 0]`, the `if` is summarized with `c` at an end of `i64`: no value lies near a demand
/// near zero, and every integer takes the whole domain. Over `[-60, 60]` an arm leaves `i64`,
/// the summary gives up on the `if` and the box of the transfer is listed; a value past `i64`
/// meets a demand only when the demand is unbounded on its side.
#[test]
fn reflected_arms_at_the_ends_of_i64() {
    let z = fin(&[(-30, -20), (-1, 1), (4, 9)]);
    let all = IntervalSet::top();
    let (max_in, min_in) = (fin(&[(-3, 60)]), fin(&[(-60, 0)]));
    let (max_t, min_t) = (reflected_by(max_c(), 3), reflected_by(min_c(), -3));
    let got = [
        summarized_over(&max_t, max_in.clone(), z.clone()),
        summarized_over(&min_t, min_in.clone(), z.clone()),
        summarized_over(&max_t, max_in, all.clone()),
        summarized_over(&min_t, min_in, all.clone()),
        summarized(&max_t, z.clone()),
        summarized(&min_t, z),
        summarized(&max_t, all.clone()),
        summarized(&min_t, all),
    ];
    let (none, listed) = ("i []; exact", "i []; exact; enumerated");
    let whole = "i [-60..=60]; exact";
    assert_eq!(
        got,
        [
            none,
            none,
            "i [-3..=60]; exact",
            "i [-60..=0]; exact",
            listed,
            listed,
            whole,
            whole
        ]
    );
}

/// The clip of `i64::MIN - x` for `x >= 0` and of `i64::MAX - x` for `x <= 0`: one point of
/// each, `x = 0`, has a value in `i64`, at an end of it, and no point meets a demand near zero.
/// The clip is the exact hull, `[.., i64::MIN]` and `[i64::MAX, ..]`, and the empty preimage is
/// exact at once. Before, the forward image raised the rounding flag at the split point `c - 1`
/// or `c + 1`, the clip gave up, and the box was listed to find it empty.
#[test]
fn the_clip_of_a_reflection_at_the_ends_of_i64() {
    let cases = [
        (min_c(), doms(&[("x", Some(0), None)])),
        (max_c(), doms(&[("x", None, Some(0))])),
    ];
    for (c, ds) in cases {
        let t = Term::Prim(Prim::Sub, vec![c, var("x")]);
        for z in [fin(&[(-5, 5)]), fin(&[(0, 0)]), IntervalSet::empty()] {
            let d = Demand::Ints(z);
            let p = preimage(&t, &ds, &d);
            check(&t, &ds, &d, &p, (-60, 60));
            assert!(p.exact, "{t}: {}", shown(&p));
            assert_eq!(shown(&p), "x []; exact");
        }
    }
}
