//! `@exact`: the projection of the points that meet the demand, by branch and prune
//! (docs/thresholds.md, "`@exact`"), against the ordinary preimage of the same term.

use std::sync::Arc;

use zedc::store::lattice::Congruence;
use zedc::store::preimage::{Classes, Demand, exact_preimage, preimage};

use super::{doms, function, shown};

/// Each input's name and bounds, as `doms` takes them.
type Bounds<'a> = &'a [(&'a str, Option<i64>, Option<i64>)];

/// The ordinary preimage of `true` under `src` over `ds`, and the one under `@exact` with
/// `classes`.
fn both(src: &str, ds: &[(&str, Option<i64>, Option<i64>)], classes: &Classes) -> (String, String) {
    let (_, body) = function(src);
    let d = doms(ds);
    let t = Demand::Bool(true);
    (
        shown(&preimage(&body, &d, &t)),
        shown(&exact_preimage(&body, &d, classes, &t)),
    )
}

#[test]
fn exact_preimages_of_ranges() {
    let none = Classes::new();
    let cases: &[(&str, Bounds, &str, &str)] = &[
        (
            "ok(x) = x * x mod 10 == 9;\n",
            &[("x", Some(0), Some(30))],
            "x [3..=3, 5..=29]; necessary",
            "x [3..=3, 7..=7, 13..=13, 17..=17, 23..=23, 27..=27]; exact; enumerated",
        ),
        (
            "ok(x) = x * 7 mod 10 == 3;\n",
            &[("x", Some(0), Some(30))],
            "x [9..=29]; necessary",
            "x [9..=9, 19..=19, 29..=29]; exact; enumerated",
        ),
        (
            // Every `x` and every `y` in 1..=6 has a partner, but not every pair meets it.
            "ok(x, y) = x * y mod 7 == 3;\n",
            &[("x", Some(1), Some(6)), ("y", Some(1), Some(6))],
            "x [1..=6]; y [1..=6]; necessary",
            "x [1..=6]; y [1..=6]; necessary; enumerated",
        ),
        (
            // An unbounded input is not searched.
            "ok(x) = x * x mod 10 == 9;\n",
            &[("x", Some(0), None)],
            "x [0..]; necessary",
            "x [0..]; necessary",
        ),
    ];
    for &(src, ds, plain, exact) in cases {
        assert_eq!(both(src, ds, &none), (plain.into(), exact.into()), "{src}");
    }
}

#[test]
fn an_exact_preimage_searches_only_the_members_of_each_class() {
    // Of 3, 7, 13, 17, 23 and 27, only 13 and 17 are 1 mod 4.
    let classes: Classes = [(Arc::from("x"), Congruence::new(4, 1))].into();
    let (_, exact) = both(
        "ok(x) = x * x mod 10 == 9;\n",
        &[("x", Some(0), Some(30))],
        &classes,
    );
    assert_eq!(exact, "x [13..=13, 17..=17]; exact; enumerated");
}
