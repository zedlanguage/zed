//! The catalog's entries on ordinary preconditions and guards. Each preimage is printed and
//! checked against the interpreter over a window of each domain.

use super::{check, doms, function, listed, pre, pre_listed, shown};
use zedc::store::preimage::Demand;

/// The preimage of `true` under `src` over `ds`, printed, after checking it on the window
/// `-60..=60`.
fn holds(src: &str, ds: &[(&str, Option<i64>, Option<i64>)]) -> String {
    let p = pre(src, ds, &Demand::Bool(true));
    let (_, body) = function(src);
    check(&body, &doms(ds), &Demand::Bool(true), &p, (-60, 60));
    shown(&p)
}

const ANY: (Option<i64>, Option<i64>) = (None, None);

fn any(n: &str) -> (&str, Option<i64>, Option<i64>) {
    (n, ANY.0, ANY.1)
}

#[test]
fn a_square_bound_is_read_as_a_power_and_inverted_exactly() {
    // The z3 fixture of sec:constraints gives `-9 <= x <= 9`.
    assert_eq!(
        holds("ok(x) = x * x <= 99;\n", &[any("x")]),
        "x [-9..=9]; exact"
    );
    assert_eq!(
        holds("ok(x) = x * x * x > 26;\n", &[any("x")]),
        "x [3..]; exact"
    );
    assert_eq!(
        holds("ok(x) = x ^ 2 >= 50;\n", &[any("x")]),
        "x [..=-8, 8..]; exact"
    );
}

#[test]
fn shifts_and_scalings_by_a_constant_invert_exactly() {
    assert_eq!(
        holds("ok(n) = 3 * n + 1 >= 10;\n", &[any("n")]),
        "n [3..]; exact"
    );
    assert_eq!(
        holds("ok(n) = 10 - n > 4;\n", &[any("n")]),
        "n [..=5]; exact"
    );
    assert_eq!(
        holds("ok(n) = -2 * n < 7;\n", &[any("n")]),
        "n [-3..]; exact"
    );
    assert_eq!(holds("ok(n) = n * 0 == 1;\n", &[any("n")]), "n []; exact");
}

#[test]
fn euclidean_division_and_remainder_by_a_constant_invert_exactly() {
    assert_eq!(
        holds("ok(i) = i div 4 == 2;\n", &[any("i")]),
        "i [8..=11]; exact"
    );
    assert_eq!(
        holds("ok(i) = i div -4 == 2;\n", &[any("i")]),
        "i [-8..=-5]; exact"
    );
    // Within two periods, the remainder pieces of each, exactly.
    assert_eq!(
        holds("ok(i) = i mod 10 == 3;\n", &[("i", Some(0), Some(19))]),
        "i [3..=3, 13..=13]; exact"
    );
    // Over more periods the transfer lists the first and last and merges those between; the
    // split by remainders (S22e-wide) reads the merged middle once more, which lists its
    // first and last, here every period, and finds every member in its class: exact.
    assert_eq!(
        holds("ok(i) = i mod 10 == 3;\n", &[("i", Some(0), Some(40))]),
        "i [3..=3, 13..=13, 23..=23, 33..=33]; exact"
    );
    // Over 10^8 periods the merged middle is read once more, which lists one more period at
    // each end (S22e-wide); the periods between stay one piece, necessary only.
    assert_eq!(
        holds(
            "ok(i) = i mod 10 == 3;\n",
            &[("i", Some(0), Some(1_000_000_000))]
        ),
        "i [3..=3, 13..=13, 23..=23, 33..=999999973, 999999983..=999999983, 999999993..=999999993]; necessary"
    );
    // With no bound on `i`, the remainders are not a finite union: necessary only.
    assert_eq!(
        holds("ok(i) = i mod 10 == 3;\n", &[any("i")]),
        "i [..]; necessary"
    );
    // Every remainder of 10 is below 10.
    assert_eq!(
        holds("ok(i) = i mod 10 < 10;\n", &[any("i")]),
        "i [..]; exact"
    );
    assert_eq!(holds("ok(i) = i mod 0 == 0;\n", &[any("i")]), "i []; exact");
}

#[test]
fn abs_and_negation_invert_at_their_endpoints() {
    assert_eq!(
        holds("ok(d) = abs(d) < 4;\n", &[any("d")]),
        "d [-3..=3]; exact"
    );
    assert_eq!(
        holds("ok(d) = abs(d) > 2;\n", &[("d", Some(-5), Some(10))]),
        "d [-5..=-3, 3..=10]; exact"
    );
    assert_eq!(holds("ok(d) = -d <= -3;\n", &[any("d")]), "d [3..]; exact");
}

#[test]
fn tests_combine_by_meet_and_union() {
    assert_eq!(
        holds("ok(x, y) = x >= 0 && y < 10;\n", &[any("x"), any("y")]),
        "x [0..]; y [..=9]; exact"
    );
    assert_eq!(
        holds("ok(x) = x < 0 || x > 9;\n", &[any("x")]),
        "x [..=-1, 10..]; exact"
    );
    // A union over two inputs is not a box: the join is necessary only.
    assert_eq!(
        holds("ok(x, y) = x < 0 || y < 0;\n", &[any("x"), any("y")]),
        "x [..]; y [..]; necessary"
    );
    assert_eq!(
        holds("ok(x) = !(x > 3 && x < 7);\n", &[any("x")]),
        "x [..=3, 7..]; exact"
    );
}

#[test]
fn a_branch_is_the_union_of_its_arms() {
    assert_eq!(
        holds("ok(x) = if x > 0 { x < 5 } else { x > -3 };\n", &[any("x")]),
        "x [-2..=4]; exact"
    );
}

#[test]
fn a_comparison_of_two_terms_constrains_their_difference() {
    // `x < y` on boxes is a relation, which L1.38 keeps; the box is its projection.
    assert_eq!(
        holds(
            "ok(x, y) = x < y;\n",
            &[("x", Some(5), None), ("y", None, Some(8))]
        ),
        "x [5..=7]; y [6..=8]; necessary"
    );
}

#[test]
fn a_listed_box_is_enumerated_and_a_range_is_not() {
    // The source lists each member, so the box is enumerated whatever the members are; the
    // listed sets merge adjacent members into pieces, and a piece of any width is listed.
    let src = "ok(x) = x * x mod 10 == 9;\n";
    for members in [
        &[0, 1, 3, 4, 7, 13, 14, 17, 18][..],
        &(0..=18).collect::<Vec<i64>>()[..],
    ] {
        let ds = listed(&[("x", members)]);
        let p = pre_listed(&function(src).1, &ds, &Demand::Bool(true));
        check(&function(src).1, &ds, &Demand::Bool(true), &p, (0, 20));
        assert_eq!(
            shown(&p),
            "x [3..=3, 7..=7, 13..=13, 17..=17]; exact; enumerated"
        );
    }
    // The same members as a range are left to the catalog, however few they are.
    assert_eq!(
        holds(src, &[("x", Some(0), Some(18))]),
        "x [3..=3, 5..=17]; necessary"
    );
    // A list and a range of the same members differ by spelling: `{0, 1, 2}` is enumerated
    // and `int[0..=2]` is not.
    let src = "ok(x) = x * (x - 1) == 0;\n";
    let ds = listed(&[("x", &[0, 1, 2])]);
    let p = pre_listed(&function(src).1, &ds, &Demand::Bool(true));
    check(&function(src).1, &ds, &Demand::Bool(true), &p, (0, 2));
    assert_eq!(shown(&p), "x [0..=1]; exact; enumerated");
    assert_eq!(
        holds(src, &[("x", Some(0), Some(2))]),
        "x [0..=2]; necessary"
    );
    // Not a box: the projection, necessary only.
    assert_eq!(
        holds(
            "ok(x, y) = x + y == 3;\n",
            &[("x", Some(0), Some(3)), ("y", Some(0), Some(3))]
        ),
        "x [0..=3]; y [0..=3]; necessary"
    );
}

#[test]
fn ranges_of_every_width_are_read_by_one_method() {
    // `x * (x - 1)` is 0 at 0 and 1 only. A range is never enumerated, so `int[0..=1]`,
    // `int[0..=2]` and `int[0..=3]` are all read by the catalog, which keeps each whole as
    // necessary: adding a member does not change the kind of answer. Before LIST-size
    // `int[0..=1]` alone was enumerated, to `x [0..=1]; exact; enumerated`.
    let src = "ok(x) = x * (x - 1) == 0;\n";
    let shown_at = |hi: i64| holds(src, &[("x", Some(0), Some(hi))]);
    assert_eq!(
        [shown_at(1), shown_at(2), shown_at(3)],
        [
            "x [0..=1]; necessary",
            "x [0..=2]; necessary",
            "x [0..=3]; necessary"
        ]
    );
    for hi in 1..=3 {
        let p = pre(src, &[("x", Some(0), Some(hi))], &Demand::Bool(true));
        assert!(!p.enumerated, "int[0..={hi}] was enumerated: {}", shown(&p));
    }
}

#[test]
fn a_division_that_can_fail_keeps_only_the_points_that_do_not() {
    // `100 div d` fails at `d == 0`, which no preimage of a demand holds.
    let src = "ok(d) = 100 div d >= 20;\n";
    let ds = listed(&[("d", &[-10, -1, 0, 2, 5, 6, 10])]);
    let p = pre_listed(&function(src).1, &ds, &Demand::Bool(true));
    check(&function(src).1, &ds, &Demand::Bool(true), &p, (-10, 10));
    assert_eq!(shown(&p), "d [2..=2, 5..=5]; exact; enumerated");
}

#[test]
fn a_call_is_read_through() {
    assert_eq!(
        holds(
            "ok(x) = sq(x + 1) <= 16;\nsq(positional v) = v * v;\n",
            &[any("x")]
        ),
        "x [-5..=3]; exact"
    );
}

/// A summary reached again from another call keeps only the inputs it narrows: each call of
/// `f1` reads `f0` over the other's interval, and once kept the interval of the first call's
/// parameter with it, which cut `x = 50` from the second.
#[test]
fn a_summary_reached_from_another_call_keeps_only_what_it_narrows() {
    let src = "ok(x) = f2(x) >= 204;\nf2(positional v) = f1(v) + f1(v + 1);\n\
               f1(positional v) = f0(v) + f0(v + 1);\nf0(positional v) = v;\n";
    assert_eq!(
        holds(src, &[("x", Some(0), Some(50))]),
        "x [50..=50]; exact"
    );
}

/// Kernel integers are unbounded, so a sum past `i64` is an integer like any other. A lower
/// end past `i64::MAX` was rounded to `+inf`, which emptied the interval it began, and the
/// backward pass then cut every input.
#[test]
fn bounds_past_i64_keep_the_box() {
    let b = 1i64 << 62;
    let xy = [("x", Some(0), Some(1)), ("y", Some(-2), Some(2))];
    for src in [
        format!("ok(x, y) = x + {b} + {b} + {b} - y >= 0;\n"),
        format!("ok(x, y) = (x + {b}) + (x + {b}) + (x + {b}) - y >= 0;\n"),
        format!("ok(x, y) = x * {b} * 4 + {b} * 4 - y >= 0;\n"),
        format!("ok(x, y) = -x - {b} - {b} - {b} + y <= 0;\n"),
        format!("ok(x, y) = -(x + {b} + {b}) - y < 0;\n"),
        format!("ok(x, y) = (x + {b} + {b} + {b}) div 3 - y >= 0;\n"),
        format!("ok(x, y) = (x + {b} + {b}) * 2 - y > 0;\n"),
    ] {
        assert_eq!(holds(&src, &xy), "x [0..=1]; y [-2..=2]; exact", "{src}");
    }
    let m = i64::MAX;
    assert_eq!(
        holds(
            &format!("ok(x) = x + {m} > {m};\n"),
            &[("x", Some(0), Some(1))]
        ),
        "x [1..=1]; exact"
    );
    // `x * 2^64` is past `i64` at `x = 1` and is computed exactly, in both directions.
    for src in [
        format!("ok(x) = x * {b} * 4 > {b};\n"),
        format!("ok(x) = -x * {b} * 4 < -{b};\n"),
    ] {
        assert_eq!(
            holds(&src, &[("x", Some(0), Some(1))]),
            "x [1..=1]; exact",
            "{src}"
        );
    }
    // Exact arithmetic, and still not exact: at `x = 0` the points with `y > 0` fail, so the
    // points that hold are not a box, and the box that holds them is the whole box.
    let src = format!("ok(x, y) = x * {b} * 4 - y >= 0;\n");
    assert_eq!(
        holds(&src, &xy),
        "x [0..=1]; y [-2..=2]; necessary",
        "{src}"
    );
}

/// A literal of 2^200 in the source is an end like any other: the sums against it are exact.
#[test]
fn a_literal_of_2_to_the_200_is_an_exact_end() {
    let p = num_bigint::BigInt::from(1) << 200;
    for src in [
        format!("ok(x) = x + {p} > {p};\n"),
        format!("ok(x) = x - {p} > -{p};\n"),
        format!("ok(x) = {p} * x >= {p};\n"),
    ] {
        assert_eq!(
            holds(&src, &[("x", Some(-1), Some(1))]),
            "x [1..=1]; exact",
            "{src}"
        );
    }
}

#[test]
fn the_forward_pass_confirms_a_box_the_backward_pass_cannot() {
    // The difference `x - y <= 0` is not inverted exactly over two inputs, but every point of
    // the box meets it, which the forward pass finds without enumerating.
    assert_eq!(
        holds(
            "ok(x, y) = x <= y;\n",
            &[("x", None, Some(3)), ("y", Some(3), None)]
        ),
        "x [..=3]; y [3..]; exact"
    );
    assert_eq!(
        holds(
            "ok(x, y) = x * y >= 1;\n",
            &[("x", Some(1), None), ("y", Some(1), None)]
        ),
        "x [1..]; y [1..]; exact"
    );
}

#[test]
fn a_set_of_many_pieces_is_kept_exact() {
    // No limit merges the pieces a program writes: nine exclusions give ten pieces.
    let src = "ok(x) = x != 1 && x != 3 && x != 5 && x != 7 && x != 9 && x != 11 && x != 13 \
               && x != 15 && x != 17;\n";
    let p = pre(src, &[any("x")], &Demand::Bool(true));
    assert!(p.exact, "{}", shown(&p));
    assert_eq!(p.domains["x"].pieces().len(), 10, "{}", shown(&p));
    check(
        &function(src).1,
        &doms(&[any("x")]),
        &Demand::Bool(true),
        &p,
        (-60, 60),
    );
}

#[test]
fn a_test_that_can_fail_is_not_combined_as_a_boolean() {
    // At `x == 0` both sides fail, and `==` finds two equal failures equal.
    assert_eq!(
        holds(
            "ok(x) = (10 div x < 100) == (10 div x < 50);\n",
            &[("x", Some(-3), Some(3))]
        ),
        "x [-3..=3]; necessary"
    );
    let src = "ok(x) = (10 div x < 100) == (10 div x < 50);\n";
    let ds = listed(&[("x", &[-3, 0, 3])]);
    let p = pre_listed(&function(src).1, &ds, &Demand::Bool(true));
    check(&function(src).1, &ds, &Demand::Bool(true), &p, (-3, 3));
    assert_eq!(shown(&p), "x [-3..=-3, 0..=0, 3..=3]; exact; enumerated");
}

#[test]
fn a_strict_disjunction_with_a_failing_side_is_necessary_only() {
    use zed_kernel::{Prim, Term, Value};
    use zedc::store::preimage::preimage;
    // The kernel's `||` passes a failure through: `x div 0 > 1` fails at every `x`, so no
    // point meets the test, though the left side alone holds on `[0..]`.
    let (x, n) = (|| Term::Var("x".into()), |v| Term::Lit(Value::Int(v)));
    let t = Term::Prim(
        Prim::Or,
        vec![
            Term::Prim(Prim::Ge, vec![x(), n(0)]),
            Term::Prim(
                Prim::Gt,
                vec![Term::Prim(Prim::IntDiv, vec![x(), n(0)]), n(1)],
            ),
        ],
    );
    let ds = doms(&[any("x")]);
    let p = preimage(&t, &ds, &Demand::Bool(true));
    assert_eq!(check(&t, &ds, &Demand::Bool(true), &p, (-60, 60)), 0);
    assert_eq!(shown(&p), "x [0..]; necessary");
}
