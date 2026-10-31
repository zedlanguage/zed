//! The linear stage of the preimage: the z3 fixtures, and the relation kept where the
//! preimage is not a box.

use zedc::store::preimage::{Demand, preimage};

use crate::l01_25_preimage_catalog::{doms, function, shown};

/// The preimage of `true` under `ok` in `src` over `ds`, printed, with the relation kept.
fn pre(src: &str, ds: &[(&str, Option<i64>, Option<i64>)]) -> String {
    let (_, body) = function(src);
    let p = preimage(&body, &doms(ds), &Demand::Bool(true));
    match &p.relation {
        Some(r) => format!("{}; relation {r}", shown(&p)),
        None => shown(&p),
    }
}

#[test]
fn the_z3_fixture_reproduces_exactly() {
    assert_eq!(
        pre("ok(x) = (x * 2 + 1) < 100;", &[("x", Some(0), Some(100))]),
        "x [0..=49]; exact"
    );
    // A sum the catalog projects only as necessary, which the relation makes exact: `x +
    // x mod 5 < 50` holds for `x` in `[0..=47]` exactly.
    assert_eq!(
        pre(
            "ok(x) = x + x mod 5 < 50;",
            &[("x", Some(0), Some(1_000_000))]
        ),
        "x [0..=47]; exact"
    );
    // A congruence the projection does not split is kept as a relation; the set is
    // necessary only.
    assert_eq!(
        pre(
            "ok(x) = (x * 2 + 1) < 100 && x mod 7 != 3;",
            &[("x", Some(0), Some(1_000_000))]
        ),
        "x [0..=2, 4..=49]; necessary; relation 2 * x <= 98 && !(q1 == 3) where q0 = x div 7, \
         q1 = x mod 7"
    );
}

#[test]
fn a_relation_among_two_inputs_is_kept_with_its_projection() {
    // The design's example: `(a + b).refine(v -> v < 50)` needs `a + b <= 49`.
    assert_eq!(
        pre(
            "ok(a, b) = a + b < 50;",
            &[("a", Some(0), Some(1000)), ("b", Some(0), Some(1000))]
        ),
        "a [0..=49]; b [0..=49]; necessary; relation a + b <= 49"
    );
    // Over three inputs, the relation alone says what the box misses.
    assert_eq!(
        pre(
            "ok(a, b, c) = a + b + c < 50;",
            &[
                ("a", Some(0), Some(1000)),
                ("b", Some(0), Some(1000)),
                ("c", Some(0), Some(1000))
            ]
        ),
        "a [0..=49]; b [0..=49]; c [0..=49]; necessary; relation a + b + c <= 49"
    );
    // The next index: `i <= n - 2`, with `i` and `n` narrowed to what it allows.
    assert_eq!(
        pre(
            "ok(i, n) = 0 <= i + 1 && i + 1 < n;",
            &[("i", Some(0), None), ("n", Some(0), Some(100_000))]
        ),
        "i [0..=99998]; n [2..=100000]; necessary; relation i >= -1 && i <= n - 2"
    );
}

#[test]
fn a_relation_the_box_entails_makes_the_preimage_exact() {
    // `x - y` over boxes where the catalog's projection is the whole answer once tested.
    assert_eq!(
        pre(
            "ok(x, y) = x - y >= 0;",
            &[("x", Some(10), Some(20_000)), ("y", Some(0), Some(5))]
        ),
        "x [10..=20000]; y [0..=5]; exact"
    );
    // No point at all: the empty preimage is exact.
    assert_eq!(
        pre(
            "ok(x, y) = x < y && y < x;",
            &[("x", None, None), ("y", None, None)]
        ),
        "x []; y []; exact"
    );
}
