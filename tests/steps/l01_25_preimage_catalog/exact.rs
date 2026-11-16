//! `@exact`: the projection of the points that meet the demand, by branch and prune
//! (docs/thresholds.md, "`@exact`"), against the ordinary preimage of the same term.

use std::sync::Arc;

use zedc::store::lattice::Congruence;
use zedc::store::preimage::{Classes, Demand, exact_preimage, preimage, witness};

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

#[test]
fn a_witness_is_the_first_point_found_or_none() {
    let none = Classes::new();
    let t = Demand::Bool(true);
    let (_, body) = function("ok(x) = x * x mod 10 == 9;\n");
    let w = |lo, hi, c: &Classes| witness(&body, &doms(&[("x", lo, hi)]), c, &t);
    // A point that meets the term, in a range of 10^15 points.
    let found = w(Some(0), Some(1_000_000_000_000_000), &none)
        .expect("decided")
        .expect("a point");
    let x = found["x"].to_i64().expect("a point within the box");
    assert!(
        (x * x) % 10 == 9 && (0..=1_000_000_000_000_000).contains(&x),
        "{x}"
    );
    // None at all: `x * x` never ends in 9 when `x` ends in 5.
    let five: Classes = [(Arc::from("x"), Congruence::new(10, 5))].into();
    assert_eq!(w(Some(0), Some(1_000_000), &five), Some(None));
    // Unbounded: not searched.
    assert_eq!(w(Some(0), None, &none), None);
}

#[test]
fn the_classes_alone_decide_a_box_of_any_size() {
    // With `x` in `5 mod 10`, `x * x mod 10` is 5 at every point, so the arithmetic of the
    // classes shows no point meets `== 9` and every point meets `!= 9`, over 10^15 points.
    let t = Demand::Bool(true);
    let five: Classes = [(Arc::from("x"), Congruence::new(10, 5))].into();
    let d = doms(&[("x", Some(0), Some(1_000_000_000_000_000))]);
    let (_, no) = function("ok(x) = x * x mod 10 == 9;\n");
    let (_, yes) = function("ok(x) = x * x mod 10 != 9;\n");
    let t0 = zed_tests::scaling::cpu_time();
    assert_eq!(witness(&no, &d, &five, &t), Some(None));
    assert_eq!(
        witness(&yes, &d, &five, &t)
            .expect("decided")
            .expect("a point")["x"]
            .to_i64(),
        Some(5)
    );
    let took = zed_tests::scaling::cpu_time() - t0;
    assert!(took.as_secs() < 1, "took {took:?}");
}

#[test]
fn inputs_the_term_does_not_read_keep_their_sets() {
    // `y` and `z` are not read: the search holds `x` alone, and `y` keeps its set with its
    // ends in its class, as a box on which the preimage is exact keeps it (the odd `y` from 1
    // to 3, not split into its points), `z` its one value.
    let classes: Classes = [(Arc::from("y"), Congruence::new(2, 1))].into();
    let ds = &[
        ("x", Some(0), Some(30)),
        ("y", Some(0), Some(3)),
        ("z", Some(5), Some(5)),
    ];
    let (_, exact) = both("ok(x, y, z) = x * x mod 10 == 9;\n", ds, &classes);
    assert_eq!(
        exact,
        "x [3..=3, 7..=7, 13..=13, 17..=17, 23..=23, 27..=27]; y [1..=3]; z [5..=5]; \
         exact; enumerated"
    );
    // No point meets the term: every input's set is empty, the unread ones too.
    let (_, exact) = both("ok(x, y, z) = x * x mod 10 == 2;\n", ds, &classes);
    assert_eq!(exact, "x []; y []; z []; exact; enumerated");
    // Two read inputs and an unread one: the second search reads `x` and `y` alone.
    let (_, exact) = both(
        "ok(x, y, z) = x * y mod 7 == 3;\n",
        &[
            ("x", Some(1), Some(6)),
            ("y", Some(1), Some(6)),
            ("z", Some(0), Some(9)),
        ],
        &Classes::new(),
    );
    assert_eq!(
        exact,
        "x [1..=6]; y [1..=6]; z [0..=9]; necessary; enumerated"
    );
    // A witness gives each unread input its lowest value in its class.
    let (_, body) = function("ok(x, y, z) = x * x mod 10 == 9;\n");
    let w = witness(&body, &doms(ds), &classes, &Demand::Bool(true));
    let w = w.unwrap().unwrap();
    let w: Vec<String> = w.iter().map(|(k, v)| format!("{k} = {v}")).collect();
    assert_eq!(w, ["x = 3", "y = 1", "z = 5"]);
}
