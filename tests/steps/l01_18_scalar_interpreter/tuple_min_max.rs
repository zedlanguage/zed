//! `min` and `max` of two tuples (DESIGN.md sec:reduction, item 5; plan row MINMAX-tuples): the
//! first component in which they differ decides, by `min` or `max` of that pair.

use super::x;
use zed_kernel::{Prim, Term, Value};
use zed_tests::step_helpers::l01_16_elaboration::{checked, errors};
use zed_tests::step_helpers::l01_26_type_resolution::sig;

#[test]
fn the_first_component_that_differs_decides() {
    assert_eq!(x("min((1, 2), (1, 3))"), "(1, 2)");
    assert_eq!(x("max((1, 2), (1, 3))"), "(1, 3)");
    assert_eq!(x("min((2, 0), (1, 9))"), "(1, 9)");
    assert_eq!(x("max((1r/2r, 2), (1r/3r, 9))"), "(1r/2r, 2)");
    assert_eq!(x("min((1, (2, 3)), (1, (2, 1)))"), "(1, (2, 1))");
    assert_eq!(x("(1, 2).min((0, 9))"), "(0, 9)");
    assert_eq!(x("max(min((5, 1), (4, 9)), (4, 8))"), "(4, 9)");
}

#[test]
fn the_nearest_pair_of_clusters_as_corpus_14_finds_it() {
    // Corpus 14 folds `(d2, label, label)` with `>< min`; the fold is step L3.2, the pairwise
    // `min` it folds with is here.
    assert_eq!(
        x("min(min((2.0, 1, 3), (0.5, 2, 4)), (0.5, 1, 9))"),
        "(0.5, 1, 9)"
    );
    assert_eq!(
        sig(
            "f(positional p: (f64, int, int), positional q: (f64, int, int)) = min(p, q);\n",
            "f"
        ),
        "((f64, int, int), (f64, int, int)) -> (f64, int, int)"
    );
}

#[test]
fn a_float_part_is_ordered_as_ieee_minimum_and_maximum() {
    // A NaN in the first component that differs is taken by both, as at the top level.
    assert_eq!(x("min((2.0, 1), (0.0 / 0.0, 0))"), "(nan, 0)");
    assert_eq!(x("max((2.0, 1), (0.0 / 0.0, 0))"), "(nan, 0)");
    assert_eq!(x("min((1, 0.0 / 0.0), (1, 2.0))"), "(1, nan)");
    // `-0.0` is below `0.0` in either order, so `min` commutes.
    assert_eq!(x("min((0.0, 1), (-0.0, 1))"), "(-0.0, 1)");
    assert_eq!(x("min((-0.0, 1), (0.0, 1))"), "(-0.0, 1)");
    assert_eq!(x("max((-0.0, 1), (0.0, 1))"), "(0.0, 1)");
}

#[test]
fn tuples_min_and_max_cannot_order_are_refused() {
    assert_eq!(
        errors("x = min((1, 2), (1, 2, 3));\n"),
        [
            "`min` does not take (1, 2) and (1, 2, 3): a tuple of 2 components has none of its length to compare with [min((1, 2), (1, 2, 3))]",
            "`min` does not take (1, 2) and (1, 2, 3): a tuple of 3 components has none of its length to compare with [min((1, 2), (1, 2, 3))]",
        ]
    );
    assert_eq!(
        errors("x = min((1, \"a\"), (1, \"b\"));\n"),
        ["`min` does not take (\"a\", \"b\") [min((1, \"a\"), (1, \"b\"))]"]
    );
    assert_eq!(
        errors("x = min((1, 2.0), (1, 3));\n"),
        ["`min` does not take (2.0, 3) [min((1, 2.0), (1, 3))]"]
    );
    assert_eq!(
        errors("x = min((1, 2), 3);\n"),
        ["`min` does not take (1, 2) and 3: it takes two tuples or two numbers [min((1, 2), 3)]"]
    );
    assert_eq!(
        errors("x = min((int(\"x\"), 2), (1, 3));\n"),
        [
            "`min` does not order #invalid in a tuple; handle it before `min` [min((int(\"x\"), 2), (1, 3))]"
        ]
    );
}

/// `min` (`min` true) or `max` of `a` and `b` by the kernel.
fn pick(min: bool, a: &Value, b: &Value) -> Value {
    let p = if min { Prim::Min } else { Prim::Max };
    zed_kernel::eval(&Term::Prim(
        p,
        vec![Term::Lit(a.clone()), Term::Lit(b.clone())],
    ))
    .unwrap()
}

#[test]
fn the_laws_hold_over_every_triple_of_small_tuples() {
    // Every tuple of a float and an int from small sets, and every triple of them: `min` and
    // `max` are commutative, associative, idempotent and selective, bit for bit (printed text
    // tells NaN and `-0.0` apart); without NaN and `-0.0` they agree with the natural order; a
    // 1-tuple agrees with the scalar word.
    let floats = [f64::NAN, f64::NEG_INFINITY, -0.0, 0.0, 1.0, f64::INFINITY];
    let ts: Vec<Value> = floats
        .iter()
        .flat_map(|&f| {
            (0..2).map(move |i| Value::tuple(vec![Value::float(f), Value::int(i.into())]))
        })
        .collect();
    let s = |v: &Value| v.to_string();
    for min in [true, false] {
        for a in &ts {
            assert_eq!(s(&pick(min, a, a)), s(a));
            for b in &ts {
                let ab = pick(min, a, b);
                assert_eq!(s(&ab), s(&pick(min, b, a)), "{a} {b}");
                assert!(s(&ab) == s(a) || s(&ab) == s(b), "{a} {b}");
                let plain = |v: &Value| !s(v).contains("nan") && !s(v).contains("-0.0");
                if plain(a) && plain(b) {
                    let natural = if min { a.min(b) } else { a.max(b) };
                    assert_eq!(s(&ab), s(natural), "{a} {b}");
                }
                for c in &ts {
                    assert_eq!(
                        s(&pick(min, &ab, c)),
                        s(&pick(min, a, &pick(min, b, c))),
                        "{a} {b} {c}"
                    );
                }
            }
        }
        for &f in &floats {
            for &g in &floats {
                let one = |x: f64| Value::tuple(vec![Value::float(x)]);
                let scalar = pick(min, &Value::float(f), &Value::float(g));
                assert_eq!(s(&pick(min, &one(f), &one(g))), format!("({scalar},)"));
            }
        }
    }
}

#[test]
fn min_of_two_tuples_of_n_components_scales() {
    let pair = |n: usize| {
        let t = |last: i64| {
            let mut v: Vec<Value> = (0..n).map(|i| Value::float(i as f64)).collect();
            v.push(Value::int(last.into()));
            Value::tuple(v)
        };
        (t(2), t(1))
    };
    let built = zed_tests::scaling::inputs(20_000, pair);
    zed_tests::scaling::check("`min` of two tuples of n components", 20_000, |n| {
        let (a, b) = &built[&n];
        pick(true, a, b);
    });
    let (a, b) = pair(3);
    assert_eq!(pick(true, &a, &b), b);
}

#[test]
fn min_of_two_tuples_nested_n_deep_through_shared_parts_scales() {
    // `t(k + 1) = (t(k), t(k))`: 2^n paths, n distinct pairs of parts. Two equal tuples built
    // apart are read to the end; the walk reads each pair of shared parts once.
    let deep = |n: usize| {
        let t = || {
            (0..n).fold(Value::tuple(vec![Value::float(1.0)]), |t, _| {
                Value::tuple(vec![t.clone(), t])
            })
        };
        (t(), t())
    };
    let built = zed_tests::scaling::inputs(1000, deep);
    zed_tests::scaling::check("`min` of two tuples nested n deep", 1000, |n| {
        let (a, b) = &built[&n];
        pick(true, a, b);
    });
}

#[test]
fn checking_a_chain_of_n_tuple_mins_scales() {
    let unit = |n: usize| {
        let mut text = String::from("a0 = (0, 1.0, 0);\n");
        for i in 1..n {
            text.push_str(&format!("a{i} = min(a{}, ({i}, 0.5, {i}));\n", i - 1));
        }
        checked(&text)
    };
    let built = zed_tests::scaling::inputs(1000, unit);
    zed_tests::scaling::check("checking n `min`s of tuples in a chain", 1000, |n| {
        built[&n].check();
    });
}

#[test]
fn checking_min_of_two_tuples_of_n_components_scales() {
    let unit = |n: usize| {
        let parts = |last: usize| {
            let mut v: Vec<String> = (0..n).map(|i| format!("{i}.0")).collect();
            v.push(last.to_string());
            v.join(", ")
        };
        checked(&format!("x = min(({}), ({}));\n", parts(2), parts(1)))
    };
    let built = zed_tests::scaling::inputs(2000, unit);
    zed_tests::scaling::check("checking `min` of two tuples of n components", 2000, |n| {
        built[&n].check();
    });
}
