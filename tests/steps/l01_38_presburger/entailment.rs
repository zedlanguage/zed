//! Rung 2 on the facts the design names, written as Zed functions over the same parameters.

use zedc::store::int::Int;
use zedc::store::presburger::{Atom, Entailment, entails};

use zedc::store::preimage::relations;

use super::{holds, point};
use crate::l01_25_preimage_catalog::function;

/// What rung 2 concludes from the body of `ok` in `premise` to the body of `ok` in `goal`,
/// the two translated in one call, so that their auxiliary variables are numbered apart.
pub(super) fn rung2(premise: &str, goal: &str) -> Entailment {
    let (ps, p) = function(premise);
    let (_, g) = function(goal);
    let rs = relations(&[&p, &g], &ps, true).expect("in the linear-relation domain");
    entails(&rs[0], &rs[1])
}

const GOAL: &str = "ok(y, w, x, h) = y * w + x < h * w;";

#[test]
fn a_row_major_index_is_in_bounds_from_the_bounds_on_its_factors() {
    let e = rung2("ok(y, w, x, h) = 0 <= y && y < h && 0 <= x && x < w;", GOAL);
    let Entailment::Proved(certificate) = &e else {
        panic!("not proved: {e}")
    };
    // The certificate holds the premises and the product `(h - 1 - y)·w >= 0` of the
    // premises on `y` and `w`, as `h * w - w * y - w >= 0`: the step the linear test cannot
    // take alone.
    let shown: Vec<String> = certificate.iter().map(|f| f.to_string()).collect();
    assert_eq!(shown[0], "y >= 0 && h >= y + 1 && x >= 0 && w >= x + 1");
    assert!(
        shown.iter().any(|s| s == "h + w + w * y <= y + h * w + 1"),
        "{shown:?}"
    );
}

#[test]
fn the_same_goal_from_y_at_most_h_is_refuted_with_a_countermodel() {
    let premise = "ok(y, w, x, h) = 0 <= y && y <= h && 0 <= x && x < w;";
    let e = rung2(premise, GOAL);
    assert_eq!(
        e.to_string(),
        "refuted: countermodel h = 0, w = 1, x = 0, y = 0"
    );
    // The countermodel is one: the interpreter runs both functions there.
    let Entailment::Refuted(m) = e else {
        unreachable!()
    };
    let (ps, p) = function(premise);
    let (_, g) = function(GOAL);
    let at = point(&m, &ps);
    assert!(holds(&p, &ps, &at) && !holds(&g, &ps, &at), "{at:?}");
}

#[test]
fn a_product_is_bounded_only_through_the_premises_on_its_factors() {
    // The product of the premises `y >= 0` and `w >= 0`.
    let e = rung2(
        "ok(y, w, x, h) = 0 <= y && 0 <= w;",
        "ok(y, w, x, h) = 0 <= y * w;",
    );
    assert!(matches!(e, Entailment::Proved(_)), "{e}");
    // With no premise on `w`, nothing bounds `h * w - w * y`: the linear reading fails at a
    // point whose product atoms are not the products, so the goal is not proved, and not
    // refuted either (it is false at `w = -1`, which rung 2 does not search for).
    let e = rung2(
        "ok(y, w, x, h) = y <= h;",
        "ok(y, w, x, h) = y * w <= h * w;",
    );
    // Any such point will do, so the point is checked, not its text: the premise holds, the
    // goal read linearly fails, and some product atom is not the product.
    let Entailment::NotProved(m) = &e else {
        panic!("{e}")
    };
    let v = |s: &str| m.get(&Atom::Sym(s.into())).cloned().unwrap_or(Int::ZERO);
    let p = |a: &str, b: &str| {
        m.get(&Atom::product(&a.into(), &b.into()))
            .cloned()
            .unwrap_or(Int::ZERO)
    };
    assert!(v("y") <= v("h"), "{e}");
    assert!(p("w", "y") > p("h", "w"), "{e}");
    assert!(
        p("w", "y") != &v("w") * &v("y") || p("h", "w") != &v("h") * &v("w"),
        "{e}"
    );
}

#[test]
fn the_next_index_is_not_in_bounds_from_the_current_one() {
    // The z3 fixture for `xs[i + 1]`, before L3 brings lists: from `0 <= i < n` the next
    // index can be `n`, at `n = 1, i = 0`.
    let e = rung2(
        "ok(i, n) = 0 <= i && i < n;",
        "ok(i, n) = 0 <= i + 1 && i + 1 < n;",
    );
    assert_eq!(e.to_string(), "refuted: countermodel i = 0, n = 1");
    // From `0 <= i < n - 1` it is.
    let e = rung2(
        "ok(i, n) = 0 <= i && i < n - 1;",
        "ok(i, n) = 0 <= i + 1 && i + 1 < n;",
    );
    assert!(matches!(e, Entailment::Proved(_)), "{e}");
}

#[test]
fn contradictory_premises_entail_anything() {
    let e = rung2("ok(x, y) = x < y && y < x;", "ok(x, y) = x == y + 7;");
    assert!(matches!(e, Entailment::Proved(_)), "{e}");
}

#[test]
fn euclidean_division_and_remainder_are_stated_exactly() {
    // `x mod 4` is in `[0..=3]` for every `x`, negative ones included, and `x div 4 * 4 +
    // x mod 4` is `x`.
    for goal in [
        "ok(x) = 0 <= x mod 4 && x mod 4 <= 3;",
        "ok(x) = x div 4 * 4 + x mod 4 == x;",
        "ok(x) = x mod -4 >= 0;",
    ] {
        let e = rung2("ok(x) = true;", goal);
        assert!(matches!(e, Entailment::Proved(_)), "{goal}: {e}");
    }
    // `x mod 4 == 3` does not follow from `x` odd: `x = 1` is a countermodel.
    let e = rung2("ok(x) = x mod 2 == 1;", "ok(x) = x mod 4 == 3;");
    assert_eq!(e.to_string(), "refuted: countermodel x = 1");
    // The remainders by 2 and by 4 are distinct auxiliary variables: `x = 3` is odd and `x mod 4`
    // is 3 there.
    let e = rung2("ok(x) = x mod 2 == 1;", "ok(x) = x mod 4 <= 1;");
    assert!(!matches!(e, Entailment::Proved(_)), "{e}");
}

#[test]
fn abs_and_branches_are_stated_through_their_cases() {
    // `min` and `max` are kernel primitives with no surface word; the random terms of
    // `random` take them.
    for (premise, goal) in [
        ("ok(a, b) = true;", "ok(a, b) = abs(a - b) >= 0;"),
        ("ok(a, b) = a < 0;", "ok(a, b) = abs(a) == -a;"),
        (
            "ok(a, b) = true;",
            "ok(a, b) = (if a < b { b - a } else { a - b }) == abs(a - b);",
        ),
    ] {
        let e = rung2(premise, goal);
        assert!(matches!(e, Entailment::Proved(_)), "{goal}: {e}");
    }
    let e = rung2("ok(a, b) = true;", "ok(a, b) = abs(a) == a;");
    assert_eq!(e.to_string(), "refuted: countermodel a = -1");
}

/// The inner level of a three-level index, `z * h + y` in bounds of `d * h`.
const INNER: &str = "ok(z, d, y, h) = 0 <= z && z < d && 0 <= y && y < h;";
/// The outer level, with `p` naming `z * h + y` and `dh` naming `d * h`.
const NAMED: &str = "ok(p, dh, x, w) = p * w + x < dh * w;";
/// The same index written flat.
const FLAT: &str = "ok(z, d, y, h, x, w) = (z * h + y) * w + x < d * h * w;";

#[test]
fn a_product_of_three_factors_is_proved_by_naming_the_inner_level() {
    // The inner level first: its bounds are the premises of the outer one.
    for g in [
        "ok(z, d, y, h) = 0 <= z * h + y;",
        "ok(z, d, y, h) = z * h + y < d * h;",
    ] {
        let e = rung2(INNER, g);
        assert!(matches!(e, Entailment::Proved(_)), "{g}: {e}");
    }
    // Then the outer level from those bounds, each product of two symbols.
    let e = rung2(
        "ok(p, dh, x, w) = 0 <= p && p < dh && 0 <= x && x < w;",
        NAMED,
    );
    let Entailment::Proved(certificate) = &e else {
        panic!("not proved: {e}")
    };
    // `(dh - 1 - p)·w >= 0`, the product of the premises on `p` and `w`.
    let shown: Vec<String> = certificate.iter().map(|f| f.to_string()).collect();
    assert!(
        shown
            .iter()
            .any(|s| s == "dh + w + p * w <= p + dh * w + 1"),
        "{shown:?}"
    );
    // The naming is the flat goal: the interpreter gives both the same value at every point
    // of a window, with `p = z * h + y` and `dh = d * h`.
    let (fs, flat) = function(FLAT);
    let (ns, named) = function(NAMED);
    let mut n = 0;
    for z in -1..=2 {
        for d in -1..=2 {
            for y in -1..=2 {
                for h in -1..=2 {
                    for x in -1..=2 {
                        for w in -1..=2 {
                            let f = holds(&flat, &fs, &[z, d, y, h, x, w]);
                            let g = holds(&named, &ns, &[z * h + y, d * h, x, w]);
                            assert_eq!(f, g, "z={z} d={d} y={y} h={h} x={x} w={w}");
                            n += 1;
                        }
                    }
                }
            }
        }
    }
    assert_eq!(n, 4096);
}

#[test]
fn the_flat_product_of_three_factors_is_not_taken_by_rung_2() {
    // `(z * h + y) * w` multiplies a sum by a symbol and `d * h * w` three symbols: a product
    // factor must be a symbol or an auxiliary variable (`Lin::product`), so the goal is outside the linear-relation
    // domain and rung 2 proves nothing; naming the inner level is what proves it.
    let (ps, g) = function(FLAT);
    assert!(super::relations(&[&g], &ps, true).is_none());
}
