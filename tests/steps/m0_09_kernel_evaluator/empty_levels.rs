//! Empty inner levels (DESIGN.md sec:kernel, reference semantics (d) and (e); sec:remap_law).
//! A key whose inner level is empty, `"a"` in `{"a" -> {}}`, is a keypath that ends early: the
//! family differs from `{}`, its domain holds `"a"`, a fold gives `"a"` the empty level's
//! result, and a remap keeps the key where its output keypath starts with levels computed from
//! the keys the short keypath binds. A move that puts an unbound level first drops it.

use zed_kernel::term::build::{if_, lit, prim};
use zed_kernel::{Family, KernelError, Prim, Term, Value, eval};
use zed_tests::kernel::*;
use zed_tests::scaling;

fn empty() -> Value {
    Value::Family(Family::new())
}

/// A family from two-key leaves, with each key of `bare` above an empty level.
fn table(leaves: &[(&str, i64, i64)], bare: &[&str]) -> Value {
    let full = leaves
        .iter()
        .map(|&(a, b, v)| (vec![s(a), Value::Int(b)], Value::Int(v)));
    let short = bare.iter().map(|&a| (vec![s(a)], empty()));
    Value::Family(Family::from_leaves(full.chain(short)).unwrap())
}

fn show(t: &Term) -> String {
    eval(t).unwrap().to_string()
}

/// `as (k -> j -> v) into (outer(k) -> j -> v)`.
fn rekey_outer(f: Term, outer: impl FnOnce(Term) -> Term) -> Term {
    reindex(
        f,
        func(|[p, _]| path(vec![outer(key(p.clone(), 0)), key(p, 1)])),
        func(|[_, v]| v),
    )
}

#[test]
fn an_empty_inner_level_is_a_value_of_its_own() {
    let a = lit(Family::of([("a", empty())]));
    assert_eq!(show(&a), r#"{"a" -> {}}"#);
    assert_ne!(eval(&a).unwrap(), empty());
    // Its domain holds "a", and its count is one entry.
    assert_eq!(show(&keyset(a.clone())), r#"{"a"}"#);
    assert_eq!(eval(&count(a)).unwrap(), Value::Int(1));
    // A table built over a domain keeps a key whose entry is the empty family.
    let one = Value::Family(Family::of([("y", 1i64)]));
    let t = fam_with(lit(Family::set(["x", "y"])), |k| {
        if_(eq(k, lit(s("y"))), lit(one), lit(empty()))
    });
    assert_eq!(show(&t), r#"{"x" -> {}, "y" -> {"y" -> 1}}"#);
}

#[test]
fn folding_an_empty_inner_level_keeps_its_key() {
    // `{"a" -> {}} >< max` is `{"a" -> #empty}`: no identity, so the empty level's result.
    let a = lit(Family::of([("a", empty())]));
    assert_eq!(
        show(&fold_at(a, 2, Term::PrimFn(Prim::Max), None)),
        r#"{"a" -> #empty}"#
    );
    // `.count` per outer key counts each inner level, the empty one as 0.
    let m = lit(table(&[("b", 1, 7)], &["a"]));
    let ones = map(m, |_| lit(1));
    assert_eq!(
        show(&fold_at(ones, 2, Term::PrimFn(Prim::Add), Some(lit(0)))),
        r#"{"a" -> 0, "b" -> 1}"#
    );
    // Higher up, an empty level is not the one folded: its key keeps the empty level.
    let deep = Family::from_leaves(vec![
        (vec![s("x"), s("p"), Value::Int(1)], Value::Int(2)),
        (vec![s("x"), s("p"), Value::Int(2)], Value::Int(3)),
        (vec![s("y")], empty()),
        (vec![s("z"), s("q")], empty()),
    ])
    .unwrap();
    assert_eq!(
        show(&fold_at(lit(deep), 3, Term::PrimFn(Prim::Add), None)),
        r#"{"x" -> {"p" -> 5}, "y" -> {}, "z" -> {"q" -> #empty}}"#
    );
    // An empty level where the type puts a leaf is a leaf at another depth.
    let flat = lit(Family::of([("a", empty())]));
    assert_eq!(
        eval(&fold(flat, Term::PrimFn(Prim::Add), None)).unwrap_err(),
        KernelError::MixedDepth
    );
}

#[test]
fn a_discard_that_empties_a_level_keeps_its_key() {
    // Keep the classes whose grade is above 3: class "c" has none left, and is still listed.
    let grades = lit(table(&[("a", 1, 5), ("a", 2, 2), ("c", 1, 1)], &["d"]));
    let passing = discard_with(grades, |p, v| {
        if_(
            eq(prim(Prim::PathLen, vec![p]), lit(1)),
            lit(true),
            prim(Prim::Gt, vec![v, lit(3)]),
        )
    });
    assert_eq!(show(&passing), r#"{"a" -> {1 -> 5}, "c" -> {}, "d" -> {}}"#);
}

#[test]
fn a_remap_keeps_the_key_where_its_output_can_place_it() {
    let m = || lit(table(&[("b", 1, 7)], &["a"]));
    // `into (k.upper -> j -> v)`: the new outer key comes from `k` alone.
    let upper = rekey_outer(m(), |k| prim(Prim::Upper, vec![k]));
    assert_eq!(show(&upper), r#"{"A" -> {}, "B" -> {1 -> 7}}"#);
    // `map` keeps every keypath, the short one included.
    assert_eq!(
        show(&map(m(), |v| mul(v, lit(2)))),
        r#"{"a" -> {}, "b" -> {1 -> 14}}"#
    );
    // A key built from the outer key and the value keeps the outer part: `into (k -> v -> j)`.
    let lift = reindex(
        m(),
        func(|[p, v]| path(vec![key(p.clone(), 0), v, key(p, 1)])),
        func(|[_, v]| v),
    );
    assert_eq!(show(&lift), r#"{"a" -> {}, "b" -> {7 -> {1 -> 7}}}"#);
    // Two short keypaths sent to one key merge, since an empty level writes no leaf.
    let same = rekey_outer(lit(table(&[], &["a", "b"])), |_| lit(0));
    assert_eq!(show(&same), "{0 -> {}}");
    // An empty level where a leaf lands is two writers for one keypath: `into ("all" -> v)`
    // sends the empty level of "a" and the leaf of "b" to the key "all".
    let clash = reindex(m(), func(|[_, _]| lit(s("all"))), func(|[_, v]| v));
    assert_eq!(
        eval(&clash).unwrap_err(),
        KernelError::Collision {
            keypath: vec![s("all")]
        }
    );
}

#[test]
fn a_move_that_puts_an_unbound_level_first_drops_the_key() {
    let m = || lit(table(&[("b", 1, 7)], &["a"]));
    // Transpose: `into (j -> k -> v)`.
    let swap = reindex(
        m(),
        func(|[p, _]| path(vec![key(p.clone(), 1), key(p, 0)])),
        func(|[_, v]| v),
    );
    assert_eq!(show(&swap), r#"{1 -> {"b" -> 7}}"#);
    assert_eq!(
        show(&reindex(
            lit(Family::of([("a", empty())])),
            func(|[p, _]| path(vec![key(p.clone(), 1), key(p, 0)])),
            func(|[_, v]| v),
        )),
        "{}"
    );
    // Flatten to a tuple key: the tuple needs the inner key too.
    let flat = reindex(
        m(),
        func(|[p, _]| prim(Prim::Tuple, vec![key(p.clone(), 0), key(p, 1)])),
        func(|[_, v]| v),
    );
    assert_eq!(show(&flat), r#"{("b", 1) -> 7}"#);
    // Group by value: the short keypath has no value to group by.
    let by_value = group_by(m(), |v| v);
    assert_eq!(show(&by_value), r#"{7 -> {"b" -> 7}}"#);
}

#[test]
fn rank_over_the_outer_level_ranks_an_empty_level() {
    // `rank` of the outer keys in key order: each key to the number of keys below it.
    let m = lit(table(&[("b", 1, 7), ("c", 2, 8)], &["a"]));
    let below = |x: Term| count(discard_with(keyset(m.clone()), |q, _| lt(key(q, 0), x)));
    let ranked = rekey_outer(m.clone(), below);
    assert_eq!(show(&ranked), "{0 -> {}, 1 -> {1 -> 7}, 2 -> {2 -> 8}}");
}

/// `n` classes, every other one with no entries, the rest with two.
fn classes(n: usize) -> Value {
    let mut leaves = Vec::with_capacity(n * 2);
    for c in 0..n as i64 {
        match c % 2 {
            0 => leaves.push((vec![Value::Int(c)], empty())),
            _ => {
                leaves.push((vec![Value::Int(c), Value::Int(0)], Value::Int(c)));
                leaves.push((vec![Value::Int(c), Value::Int(1)], Value::Int(-c)));
            }
        }
    }
    Value::Family(Family::from_leaves(leaves).unwrap())
}

#[test]
fn empty_levels_scale() {
    let n = 2000;
    let inputs = scaling::inputs(n, |n| lit(classes(n)));
    // Build, read back, rekey, filter (emptying the levels with a negative entry) and fold.
    scaling::check(
        "empty levels: building, leaves, a rekey of the outer level, a discard and a fold, by \
         classes",
        n,
        |n| {
            let f = classes(n);
            let Value::Family(fam) = &f else {
                unreachable!()
            };
            assert_eq!(Family::from_leaves(fam.leaves()).unwrap().len(), n);
            let m = &inputs[&n];
            let up = rekey_outer(m.clone(), |k| add(k, lit(1)));
            let kept = discard_with(up, |p, v| {
                if_(
                    eq(prim(Prim::PathLen, vec![p]), lit(1)),
                    lit(true),
                    lt(lit(0), v),
                )
            });
            let total = fold_at(kept, 2, Term::PrimFn(Prim::Add), Some(lit(0)));
            let Value::Family(out) = eval(&total).unwrap() else {
                panic!("a fold of two levels gives a family")
            };
            assert_eq!(out.len(), n);
        },
    );
}

#[test]
fn a_fold_over_many_levels_that_need_no_call_runs_in_constant_stack() {
    // Each order's total, for 100 000 orders of one line or none: no level calls `+`, and
    // the fold goes from one level to the next in a loop, not a call deeper each time.
    let n = 100_000i64;
    let leaves = (0..n).map(|c| match c % 2 {
        0 => (vec![Value::Int(c)], empty()),
        _ => (vec![Value::Int(c), Value::Int(0)], Value::Int(c)),
    });
    let orders = lit(Family::from_leaves(leaves).unwrap());
    let totals = fold_at(orders, 2, Term::PrimFn(Prim::Add), Some(lit(0)));
    let Value::Family(out) = eval(&totals).unwrap() else {
        panic!("a fold of two levels gives a family")
    };
    assert_eq!(out.len(), n as usize);
    assert_eq!(out.get(&Value::Int(4)), Some(&Value::Int(0)));
    assert_eq!(out.get(&Value::Int(5)), Some(&Value::Int(5)));
}
