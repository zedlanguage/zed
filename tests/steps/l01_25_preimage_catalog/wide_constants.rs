//! Plan item PA-affine-i128: the piecewise-affine summary of a term of one input holds its
//! coefficients and constants in `i128`, and is given up only where a value it is read at
//! leaves `i64`. Before, `Pa::affine` gave up as soon as a constant left `i64`, so
//! `i64::MIN - (u + 3)`, whose constant is `i64::MIN - 3`, had no summary although every value
//! it takes for `u <= -3` lies in `i64`. Kernel integers are unbounded, so the interpreter is
//! the oracle at the ends of `i64` too.
//!
//! The summary is read here directly (`summary_preimage`), over bounded domains, and through
//! `preimage`. Since S22-WIDE the summary holds its values in `i128` too, an infinite end of a
//! piece as the limit of its line, and `preimage` reads it with no guard on the size of the
//! ends (`Tx::fits`, removed). The last tests are the case where that guard let a constant
//! built as a product of literals through, and the summary read the end of `i64` that stood
//! for an infinite end of the domain as an input.

use std::sync::Arc;

use zed_kernel::{Prim, Term, Value, eval};
use zedc::store::interval::{End, IntervalSet};
use zedc::store::preimage::{Demand, Domains, preimage, summary_preimage};

use super::{check, doms, shown};

const MAX: i64 = i64::MAX;
const MIN: i64 = i64::MIN;

fn u() -> Term {
    Term::Var("u".into())
}

fn int(n: i64) -> Term {
    Term::Lit(Value::Int(n))
}

fn prim(p: Prim, a: Term, b: Term) -> Term {
    Term::Prim(p, vec![a, b])
}

fn add(a: Term, b: Term) -> Term {
    prim(Prim::Add, a, b)
}

fn sub(a: Term, b: Term) -> Term {
    prim(Prim::Sub, a, b)
}

fn neg(a: Term) -> Term {
    Term::Prim(Prim::Neg, vec![a])
}

fn if_(g: Term, a: Term, b: Term) -> Term {
    Term::If(Arc::new(g), Arc::new(a), Arc::new(b))
}

/// `MIN - (u + 3)`: the constant `MIN - 3`; values in `i64` for `u <= -3`.
fn min_minus() -> Term {
    sub(int(MIN), add(u(), int(3)))
}

/// `MAX - (u - 3)`: the constant `MAX + 3`; values in `i64` for `u >= 3`.
fn max_minus() -> Term {
    sub(int(MAX), sub(u(), int(3)))
}

/// `-(u + MIN)`: the constant `MAX + 1`; values in `i64` for `u >= 1`.
fn neg_shift() -> Term {
    neg(add(u(), int(MIN)))
}

/// `2 * u + MAX + 1`: the constant `MAX + 1`; values in `i64` for `u <= -1`.
fn doubled() -> Term {
    add(add(prim(Prim::Mul, int(2), u()), int(MAX)), int(1))
}

/// `2 * (u + MIN)`: the constant `2 * MIN`; values in `i64` for `u >= 2^62`.
fn doubled_shift() -> Term {
    prim(Prim::Mul, int(2), add(u(), int(MIN)))
}

/// `u` over `lo..=hi`.
fn over(lo: i64, hi: i64) -> Domains {
    doms(&[("u", Some(lo), Some(hi))])
}

fn fin(ps: &[(i64, i64)]) -> IntervalSet {
    IntervalSet::from_pieces(ps.iter().map(|&(a, b)| (End::of(a), End::of(b))).collect())
}

/// Whether the value of `t` at `u = v`, by the interpreter, lies in `z`.
fn meets(t: &Term, v: i64, z: &IntervalSet) -> bool {
    let bound = Term::Let("u".into(), Arc::new(int(v)), Arc::new(t.clone()));
    let value = eval(&bound).unwrap_or_else(|e| panic!("{t} at u = {v}: {e:?}"));
    Demand::Ints(z.clone()).holds(&value)
}

/// The summary's preimage of `z` under `t` over `ds`, or `None` when it is given up; checked
/// against the interpreter on every input of `ds` in `window`: an input is in it exactly when
/// the value lies in `z`.
fn agrees(t: &Term, ds: &Domains, z: &IntervalSet, window: (i64, i64)) -> Option<IntervalSet> {
    let got = summary_preimage(t, ds, z)?
        .remove("u")
        .expect("the input u");
    for v in window.0..=window.1 {
        if ds["u"].contains(v) {
            assert_eq!(
                got.contains(v),
                meets(t, v, z),
                "{t} at u = {v}, z = {z}: {got}"
            );
        }
    }
    Some(got)
}

/// [`agrees`], where the summary must exist.
fn summarized(t: &Term, ds: &Domains, z: &IntervalSet, window: (i64, i64)) -> IntervalSet {
    agrees(t, ds, z, window)
        .unwrap_or_else(|| panic!("{t} over {ds:?}, z = {z}: the summary was given up"))
}

/// Each term over a domain at the bottom or at the top of `i64`, where its values lie in
/// `i64`: the summary exists and inverts a demand of two pieces exactly. On the other end the
/// values leave `i64`; whatever the summary answers there agrees with the interpreter.
#[test]
fn terms_with_constants_outside_i64_are_summarized_at_the_ends_of_i64() {
    let bottom = (over(MIN + 1, MIN + 40), (MIN, MIN + 41));
    let top = (over(MAX - 40, MAX - 1), (MAX - 41, MAX));
    // The term, its values' end of `i64`, a demand there, and the preimage.
    let cases = [
        (
            min_minus(),
            (&bottom, &top),
            fin(&[(-40, -30), (-6, -6)]),
            fin(&[(MIN + 3, MIN + 3), (MIN + 27, MIN + 37)]),
        ),
        (
            max_minus(),
            (&top, &bottom),
            fin(&[(4, 4), (20, 25)]),
            fin(&[(MAX - 22, MAX - 17), (MAX - 1, MAX - 1)]),
        ),
        (
            neg_shift(),
            (&top, &bottom),
            fin(&[(1, 1), (30, 35)]),
            fin(&[(MAX - 34, MAX - 29)]),
        ),
        (
            doubled(),
            (&bottom, &top),
            fin(&[(MIN + 2, MIN + 5), (MIN + 61, MIN + 61)]),
            fin(&[(MIN + 1, MIN + 2)]),
        ),
        (
            doubled_shift(),
            (&top, &bottom),
            fin(&[(-50, -49), (-10, -4)]),
            fin(&[(MAX - 24, MAX - 24), (MAX - 4, MAX - 1)]),
        ),
    ];
    for (t, ((ds, window), (other, w)), z, want) in &cases {
        assert_eq!(&summarized(t, ds, z, *window), want, "{t}");
        // Every value and none.
        assert_eq!(&summarized(t, ds, &IntervalSet::top(), *window), &ds["u"]);
        assert!(summarized(t, ds, &IntervalSet::empty(), *window).is_empty());
        // The other end.
        for z in [z.clone(), fin(&[(-5, 5)]), IntervalSet::top()] {
            agrees(t, other, &z, *w);
        }
    }
}

/// The last value of the domain is `MIN` or `MAX` (`MAX - 1` for the doubled term, whose
/// values are even offsets from `MIN`): the summary exists and inverts a demand beside that
/// end. One input further a value leaves `i64`; since S22-WIDE the summary holds it in `i128` and
/// is still read there, and the interpreter agrees with it on every input of the window.
#[test]
fn a_value_at_an_end_of_i64_is_kept() {
    let near_min = fin(&[(MIN + 1, MIN + 3)]);
    let near_max = fin(&[(MAX - 3, MAX - 1)]);
    // The term, the domain, the demand, the preimage, and the domain one input wider.
    let cases = [
        (
            min_minus(),
            over(-60, -3),
            &near_min,
            (-6, -4),
            over(-60, -2),
        ),
        (max_minus(), over(3, 60), &near_max, (4, 6), over(2, 60)),
        (neg_shift(), over(1, 60), &near_max, (2, 4), over(0, 60)),
        (
            doubled(),
            over(-60, -1),
            &fin(&[(MAX - 5, MAX - 1)]),
            (-3, -1),
            over(-60, 0),
        ),
    ];
    for (t, ds, z, (lo, hi), wider) in &cases {
        assert_eq!(summarized(t, ds, z, (-61, 61)), fin(&[(*lo, *hi)]), "{t}");
        assert_eq!(&summarized(t, ds, &IntervalSet::top(), (-61, 61)), &ds["u"]);
        assert!(agrees(t, wider, z, (-61, 61)).is_some(), "{t}");
    }
}

/// The constant exactly `MIN` or `MAX`, reached through one outside `i64`: `-(u - MIN)` is
/// `MIN - u` through `u + (MAX + 1)`, and `u + MAX + 1 - 1` is `u + MAX` through
/// `u + (MAX + 1)`.
#[test]
fn a_constant_at_an_end_of_i64_through_one_outside_it() {
    let min_c = neg(sub(u(), int(MIN)));
    let max_c = sub(add(add(u(), int(MAX)), int(1)), int(1));
    let z = fin(&[(MIN + 1, MIN + 3), (MAX - 3, MAX - 1)]);
    for t in [&min_c, &max_c] {
        assert_eq!(
            summarized(t, &over(-10, 0), &z, (-11, 11)),
            fin(&[(-3, -1)]),
            "{t}"
        );
        // At `u = 1` both leave `i64`, which the summary holds in `i128` since S22-WIDE.
        assert!(agrees(t, &over(-10, 1), &z, (-11, 11)).is_some(), "{t}");
    }
}

/// A domain of one input at each end of `i64`, and a demand that misses its value.
#[test]
fn a_domain_of_one_input() {
    let one = over(MIN + 5, MIN + 5);
    let w = (MIN + 4, MIN + 6);
    // `MIN - 3 - (MIN + 5)`.
    let got = summarized(&min_minus(), &one, &fin(&[(-8, -8)]), w);
    assert_eq!(got, fin(&[(MIN + 5, MIN + 5)]));
    assert!(summarized(&min_minus(), &one, &fin(&[(-7, 1)]), w).is_empty());
    let one = over(MAX - 5, MAX - 5);
    let w = (MAX - 6, MAX - 4);
    // `2 * (MAX - 5 + MIN)`.
    let got = summarized(&doubled_shift(), &one, &fin(&[(-12, -12)]), w);
    assert_eq!(got, fin(&[(MAX - 5, MAX - 5)]));
}

/// `MIN` as a product of literals, `-2^31 * 2^32`.
fn min_lit() -> Term {
    prim(Prim::Mul, int(-2147483648), int(4294967296))
}

/// `if u <= -3 { MIN - (u + 3) } else { -u }` and `if u >= 3 { MAX - (u - 3) } else { u }`
/// over `[-60, 60]`: each arm stays in `i64` where its guard takes it, so the `if` has a
/// summary now. `preimage` agrees with the interpreter, and so does an empty domain.
#[test]
fn an_if_with_an_arm_whose_constant_leaves_i64() {
    let low = if_(prim(Prim::Le, u(), int(-3)), min_minus(), neg(u()));
    let high = if_(prim(Prim::Ge, u(), int(3)), max_minus(), u());
    let ds = over(-60, 60);
    let near = fin(&[(-10, 1)]);
    let below = IntervalSet::range(End::NegInf, End::of(-100));
    for (t, summary, want_near, want_below) in [
        (&low, (-1, 10), "u [-1..=10]; exact", "u [-60..=-3]; exact"),
        (&high, (-10, 1), "u [-10..=1]; exact", "u []; exact"),
    ] {
        assert_eq!(summarized(t, &ds, &near, (-60, 60)), fin(&[summary]), "{t}");
        for (z, want) in [
            (&near, want_near),
            (&below, want_below),
            (&IntervalSet::empty(), "u []; exact"),
        ] {
            let d = Demand::Ints(z.clone());
            let p = preimage(t, &ds, &d);
            check(t, &ds, &d, &p, (-60, 60));
            assert_eq!(shown(&p), want, "{t}");
        }
        let d = Demand::Ints(fin(&[(0, 0)]));
        let p = preimage(t, &over(1, 0), &d);
        assert_eq!(shown(&p), "u []; exact", "{t}");
    }
}

/// `i128` ends as a set.
fn wide(ps: &[(i128, i128)]) -> IntervalSet {
    IntervalSet::from_pieces(
        ps.iter()
            .map(|&(a, b)| (End::from(a), End::from(b)))
            .collect(),
    )
}

/// `if u <= -3 { MIN + 5 - u } else { u }` and `if u <= -3 { MIN - (u + 3) } else { u }` over
/// every integer, with `MIN` written as a product of literals. Before S22-WIDE, `Tx::fits`
/// measured how far the term moves an end by its literals summed, about `2^33`, so it let the
/// summary read the `if`, and the summary took the end of `i64` as the input that stood for
/// `u`'s infinite lower end: the first returned `u [..=MIN + 5, 0..=10]` as exact, though
/// `u = MIN - 100` gives 105. Each value in `z` is now found exactly, at inputs below `MIN`
/// too. The second has no summary before this item, and would have had the same fault with
/// one.
#[test]
fn a_product_of_literals_near_an_end_of_i64_is_measured_by_its_value() {
    let ds = doms(&[("u", None, None)]);
    let min = i128::from(MIN);
    let le = || prim(Prim::Le, u(), int(-3));
    let cases = [
        (
            if_(le(), sub(add(min_lit(), int(5)), u()), u()),
            fin(&[(0, 10)]),
            wide(&[(min - 5, min + 5), (0, 10)]),
        ),
        (
            if_(le(), sub(min_lit(), add(u(), int(3))), u()),
            fin(&[(-5, 5)]),
            wide(&[(min - 8, min + 2), (-2, 5)]),
        ),
    ];
    for (t, z, want) in &cases {
        let d = Demand::Ints(z.clone());
        let p = preimage(t, &ds, &d);
        check(t, &ds, &d, &p, (MIN, MIN + 20));
        check(t, &ds, &d, &p, (-20, 20));
        assert_eq!(p.domains["u"], *want, "{t}: {}", shown(&p));
        assert!(p.exact, "{t}: {}", shown(&p));
    }
}
