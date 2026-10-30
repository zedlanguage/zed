//! Rung 2 on the facts the design names, written as Zed functions over the same parameters.

use zedc::store::presburger::{Entailment, entails};

use super::{holds, point, relation};
use crate::l01_25_preimage_catalog::function;

/// What rung 2 concludes from the body of `ok` in `premise` to the body of `ok` in `goal`.
fn rung2(premise: &str, goal: &str) -> Entailment {
    let (_, p) = relation(premise);
    let (_, g) = relation(goal);
    entails(&p, &g)
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
    assert_eq!(
        e.to_string(),
        "not proved: the linear reading fails at h = 0, h * w = -1"
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
