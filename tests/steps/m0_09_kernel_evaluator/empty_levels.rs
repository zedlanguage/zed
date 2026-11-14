//! Empty inner levels (DESIGN.md sec:kernel, reference semantics (d) and (e); sec:remap_law).
//! A key whose inner level is empty, `"a"` in `{"a" -> {}}`, is a keypath that ends early: the
//! family differs from `{}`, its domain holds `"a"`, a fold gives `"a"` the empty level's
//! result, and a remap keeps the key where its output keypath starts with levels computed from
//! the keys the short keypath binds. A move that puts an unbound level first drops it.
//! The benchmark of these levels' time is in `bench/empty_levels.rs`; its checks run here at
//! small sizes (TEST-bench-move-rest).

use zed_kernel::term::build::{if_, lit, prim};
use zed_kernel::{Family, KernelError, Prim, Term, Value, eval};
use zed_tests::kernel::*;

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
pub(super) fn classes(n: usize) -> Value {
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

/// Each order's total, for `n` orders of one line or none: no level calls `+`, and the fold
/// goes from one level to the next in a loop, not a call deeper each time.
pub(super) fn fold_over_levels(n: i64) {
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
    for c in 0..n.min(6) {
        let total = if c % 2 == 0 { 0 } else { c };
        assert_eq!(out.get(&Value::Int(c)), Some(&Value::Int(total)));
    }
}

/// The same over 100,000 levels, in constant stack, is in `bench/empty_levels.rs`.
#[test]
fn a_fold_over_a_few_levels_that_need_no_call_gives_each_total() {
    for n in [1, 2, 9] {
        fold_over_levels(n);
    }
}

/// Outer keys `#notFound` and `#red`, atoms held as data, and `"b"`; with `full`, each over
/// one entry, else the two atoms over empty levels.
fn atom_keyed(full: bool) -> Term {
    let atoms = [(Value::atom("notFound"), 5), (Value::atom("red"), 6)];
    let rows = atoms.into_iter().map(|(a, v)| match full {
        true => (vec![a, Value::Int(1)], Value::Int(v)),
        false => (vec![a], empty()),
    });
    let b = (vec![s("b"), Value::Int(3)], Value::Int(7));
    lit(Family::from_leaves(rows.chain([b])).unwrap())
}

/// Keeps the entries above 5, and every key of the outer level.
fn above_five(f: Term) -> Term {
    discard_with(f, |p, v| {
        if_(
            eq(prim(Prim::PathLen, vec![p]), lit(1)),
            lit(true),
            prim(Prim::Gt, vec![v, lit(5)]),
        )
    })
}

#[test]
fn a_key_that_is_an_atom_is_not_taken_for_an_unbound_key() {
    let total = |f| fold_at(f, 2, Term::PrimFn(Prim::Add), Some(lit(0)));
    // At full keypaths: the identity reindex keeps each atom key and its level.
    let full = atom_keyed(true);
    let written = r#"{#notFound -> {1 -> 5}, #red -> {1 -> 6}, "b" -> {3 -> 7}}"#;
    assert_eq!(show(&full), written);
    assert_eq!(show(&rekey_outer(full.clone(), |k| k)), written);
    assert_eq!(
        show(&total(full.clone())),
        r#"{#notFound -> 5, #red -> 6, "b" -> 7}"#
    );
    assert_eq!(
        show(&above_five(full)),
        r#"{#notFound -> {}, #red -> {1 -> 6}, "b" -> {3 -> 7}}"#
    );
    // Above empty levels: the same, and only a move that puts an unbound level first drops them.
    let short = atom_keyed(false);
    let written = r#"{#notFound -> {}, #red -> {}, "b" -> {3 -> 7}}"#;
    assert_eq!(show(&short), written);
    assert_eq!(show(&rekey_outer(short.clone(), |k| k)), written);
    assert_eq!(
        show(&total(short.clone())),
        r#"{#notFound -> 0, #red -> 0, "b" -> 7}"#
    );
    assert_eq!(show(&above_five(short.clone())), written);
    let swapped = reindex(
        short,
        func(|[p, _]| path(vec![key(p.clone(), 1), key(p, 0)])),
        func(|[_, v]| v),
    );
    assert_eq!(show(&swapped), r#"{3 -> {"b" -> 7}}"#);
}

#[test]
fn a_key_map_that_reads_past_the_end_gets_the_unbound_key_only_there() {
    // A key map that returns `#notFound` itself, at a full keypath and above an empty level,
    // writes it as a key: only reads past the end of the keypath are unbound.
    let m = lit(table(&[("b", 1, 7)], &["a"]));
    let tagged = reindex(
        m.clone(),
        func(|[p, _]| path(vec![key(p, 0), lit(Value::atom("notFound"))])),
        func(|[_, v]| v),
    );
    assert_eq!(
        show(&tagged),
        r#"{"a" -> {#notFound -> {}}, "b" -> {#notFound -> 7}}"#
    );
    // `pathKey` past the end of another keypath is still `#notFound`.
    let other = reindex(
        m,
        func(|[p, _]| path(vec![key(p, 0), key(path(vec![lit(s("z"))]), 1)])),
        func(|[_, v]| v),
    );
    assert_eq!(
        show(&other),
        r#"{"a" -> {#notFound -> {}}, "b" -> {#notFound -> 7}}"#
    );
}

#[test]
fn rank_ranks_keys_that_hold_atoms_as_data() {
    // `<` passes a bare atom through (DESIGN.md M0.9 (a)), so the kernel ranks keys that hold
    // atoms inside a tuple, `(#notFound, 0)`, which `<` orders like any other tuple.
    let t = |a: Value, n: i64| Value::tuple(vec![a, Value::Int(n)]);
    let m = lit(Family::from_leaves([
        (vec![t(Value::atom("notFound"), 0)], empty()),
        (
            vec![t(Value::atom("notFound"), 1), Value::Int(1)],
            Value::Int(7),
        ),
        (vec![t(Value::atom("red"), 0), Value::Int(2)], Value::Int(8)),
    ])
    .unwrap());
    let below = |x: Term| count(discard_with(keyset(m.clone()), |q, _| lt(key(q, 0), x)));
    let ranked = rekey_outer(m.clone(), below);
    assert_eq!(show(&ranked), "{0 -> {}, 1 -> {1 -> 7}, 2 -> {2 -> 8}}");
}

/// The `n` classes of [`classes`] read back from their leaves, and `m`, their literal, rekeyed
/// one up, filtered (emptying the levels with a negative entry) and folded, keep `n` classes.
pub(super) fn empty_levels_pass(n: usize, m: &Term) {
    let f = classes(n);
    let Value::Family(fam) = &f else {
        unreachable!()
    };
    assert_eq!(Family::from_leaves(fam.leaves()).unwrap().len(), n);
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
}

/// What the benchmark of `bench/empty_levels.rs` asserts besides its ratio, at small sizes.
#[test]
fn empty_levels_are_built_read_rekeyed_filtered_and_folded_at_small_sizes() {
    for n in [1, 2, 9] {
        empty_levels_pass(n, &lit(classes(n)));
    }
}
