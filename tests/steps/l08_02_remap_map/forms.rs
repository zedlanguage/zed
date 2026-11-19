//! Each composition of `map` with a remap in source form, its result written by hand, and the
//! kernel term of the M0 model where one is written: `map` at the leaves is `reindex(F,
//! (p, v) -> p, (p, v) -> f(v))` (sec:keypaths), a repack is `reindex` with the permuted
//! keypath, a level collapsed by `><` is `fold` at that depth (sec:reduction).

use zed_kernel::term::build::{lit, prim};
use zed_kernel::{Family, Prim, Term, Value};
use zed_tests::kernel::*;
use zed_tests::step_helpers::l01_16_elaboration::{errors, value};

use super::{M, models, prints};

fn i(n: i64) -> Value {
    Value::Int(n)
}

/// `m` of [`M`] as a kernel family.
fn two() -> Term {
    lit(Value::Family(
        Family::from_leaves(vec![
            (vec![s("a"), i(1)], i(10)),
            (vec![s("a"), i(2)], i(20)),
            (vec![s("b"), i(1)], i(30)),
        ])
        .unwrap(),
    ))
}

/// The keypath of each leaf rebuilt from the source keypath's keys at `order`.
fn permute(f: Term, order: &[i64]) -> Term {
    let order = order.to_vec();
    reindex(
        f,
        func(|[p, _]| path(order.iter().map(|&j| key(p.clone(), j)).collect())),
        func(|[_, v]| v),
    )
}

/// The sum of the innermost of `depth` levels.
fn sum_inner(f: Term, depth: usize) -> Term {
    fold_at(f, depth, func(|[a, b]| add(a, b)), Some(lit(0)))
}

fn plus_one(v: Term) -> Term {
    add(v, lit(1))
}

fn with_m(src: &str) -> String {
    format!("{M}{src}")
}

/// `m.map(r -> r.map(v -> v + 1))`, the map at the leaves of `m` written in source form.
const BUMPED: &str = "m.map(r -> r.map(v -> v + 1))";

// ---- Repack ----

#[test]
fn map_before_and_after_a_transpose() {
    let src = with_m(&format!(
        "x = {BUMPED} as (k1 -> k2 -> v) into (k2 -> k1 -> v);\n\
         y = (m as (k1 -> k2 -> v) into (k2 -> k1 -> v)).map(r -> r.map(v -> v + 1));\n"
    ));
    let want = r#"{1 -> {"a" -> 11, "b" -> 31}, 2 -> {"a" -> 21}}"#;
    prints(&src, "x", want);
    prints(&src, "y", want);
    models(&src, "x", &permute(map(two(), plus_one), &[1, 0]));
    models(&src, "y", &map(permute(two(), &[1, 0]), plus_one));
}

#[test]
fn map_before_and_after_a_flattening_to_a_tuple_key() {
    let src = with_m(&format!(
        "x = {BUMPED} as (k1 -> k2 -> v) into ((k1, k2) -> v);\n\
         y = (m as (k1 -> k2 -> v) into ((k1, k2) -> v)).map(v -> v + 1);\n"
    ));
    let want = r#"{("a", 1) -> 11, ("a", 2) -> 21, ("b", 1) -> 31}"#;
    prints(&src, "x", want);
    prints(&src, "y", want);
    let flat = |f: Term| {
        reindex(
            f,
            func(|[p, _]| path(vec![prim(Prim::Tuple, vec![key(p.clone(), 0), key(p, 1)])])),
            func(|[_, v]| v),
        )
    };
    models(&src, "x", &flat(map(two(), plus_one)));
}

#[test]
fn map_before_and_after_a_key_shift() {
    let src = "xs = [10, 20, 30];\nx = xs.map(v -> v * 2) as (k -> v) into (k + 1 -> v);\n\
               y = (xs as (k -> v) into (k + 1 -> v)).map(v -> v * 2);\n";
    prints(src, "x", "{1 -> 20, 2 -> 40, 3 -> 60}");
    prints(src, "y", "{1 -> 20, 2 -> 40, 3 -> 60}");
}

// ---- A reducer `><` at each level, with `map` on each side ----

#[test]
fn reducer_at_the_inner_level_a_map_before_and_after() {
    // `v -> v * 2` distributes over `+`, so the two sides agree; `v -> v + 1` does not: before
    // the reducer it adds 1 per entry, after it once per group.
    let src = with_m(
        "a = m.map(r -> r.map(v -> v * 2)) as (k1 -> k2 -> v) into (k1 -> k2 >< (+) -> v);\n\
         b = (m as (k1 -> k2 -> v) into (k1 -> k2 >< (+) -> v)).map(v -> v * 2);\n\
         c = m.map(r -> r.map(v -> v + 1)) as (k1 -> k2 -> v) into (k1 -> k2 >< (+) -> v);\n\
         d = (m as (k1 -> k2 -> v) into (k1 -> k2 >< (+) -> v)).map(v -> v + 1);\n",
    );
    prints(&src, "a", r#"{"a" -> 60, "b" -> 60}"#);
    prints(&src, "b", r#"{"a" -> 60, "b" -> 60}"#);
    prints(&src, "c", r#"{"a" -> 32, "b" -> 31}"#);
    prints(&src, "d", r#"{"a" -> 31, "b" -> 31}"#);
    models(&src, "c", &sum_inner(map(two(), plus_one), 2));
    models(&src, "d", &map(sum_inner(two(), 2), plus_one));
}

#[test]
fn reducer_at_the_outer_level_a_map_before_and_after() {
    let src = with_m(
        "c = m.map(r -> r.map(v -> v + 1)) as (k1 -> k2 -> v) into (k1 >< (+) -> k2 -> v);\n\
         d = (m as (k1 -> k2 -> v) into (k1 >< (+) -> k2 -> v)).map(v -> v + 1);\n",
    );
    prints(&src, "c", "{1 -> 42, 2 -> 21}");
    prints(&src, "d", "{1 -> 41, 2 -> 21}");
    models(
        &src,
        "c",
        &sum_inner(permute(map(two(), plus_one), &[1, 0]), 2),
    );
    models(
        &src,
        "d",
        &map(sum_inner(permute(two(), &[1, 0]), 2), plus_one),
    );
}

#[test]
fn reducer_at_both_levels_after_a_map() {
    let src = with_m(
        "a = m.map(r -> r.map(v -> v + 1)) as (k1 -> k2 -> v) into (k1 >< (+) -> k2 >< (+) -> v);\n\
         b = m.map(r -> r.map(v -> v * 2)) as (k1 -> k2 -> v) into (k1 >< (+) -> k2 >< (+) -> v);\n",
    );
    prints(&src, "a", "63");
    prints(&src, "b", "120");
}

#[test]
fn reducer_at_the_middle_of_three_levels_a_map_before_and_after() {
    // `sales` of sec:level_names: west's two days merge per sku.
    let src = "sales = { \"east\" -> [{ \"B7\" -> 5 }], \"west\" -> [{ \"A12\" -> 3, \"B7\" -> 1 }, { \"A12\" -> 2 }] };\n\
               x = sales.map(d -> d.map(s -> s.map(q -> q * 10))) as (r -> d -> s -> q) into (r -> d >< (+) -> s -> q);\n\
               y = (sales as (r -> d -> s -> q) into (r -> d >< (+) -> s -> q)).map(t -> t.map(q -> q * 10));\n\
               z = (sales as (r -> d -> s -> q) into (r -> d >< (+) -> s -> q)).map(t -> t.map(q -> q + 1));\n";
    let want = r#"{"east" -> {"B7" -> 50}, "west" -> {"A12" -> 50, "B7" -> 10}}"#;
    prints(src, "x", want);
    prints(src, "y", want);
    prints(
        src,
        "z",
        r#"{"east" -> {"B7" -> 6}, "west" -> {"A12" -> 6, "B7" -> 2}}"#,
    );
}

#[test]
fn a_map_of_a_fold_equals_the_reducer_level() {
    // Folding the inner families by `map` gives what `><` at the inner level gives.
    let src = with_m(
        "a = (m as (k1 -> k2 -> v) into (k2 -> k1 -> v)).map(r -> r.sum);\n\
         b = m as (k1 -> k2 -> v) into (k2 -> k1 >< (+) -> v);\n",
    );
    prints(&src, "a", "{1 -> 40, 2 -> 20}");
    prints(&src, "b", "{1 -> 40, 2 -> 20}");
}

// ---- Widen ----

#[test]
fn map_before_and_after_a_widen_by_a_key_function() {
    let src = "xs = [10, 20, 30, 40, 50];\n\
               x = xs.map(v -> v + 1) as (i -> v) into (i div 2 -> i -> v);\n\
               y = (xs as (i -> v) into (i div 2 -> i -> v)).map(g -> g.map(v -> v + 1));\n";
    let want = "{0 -> {0 -> 11, 1 -> 21}, 1 -> {2 -> 31, 3 -> 41}, 2 -> {4 -> 51}}";
    prints(src, "x", want);
    prints(src, "y", want);
}

#[test]
fn a_widen_by_the_value_does_not_commute_with_map() {
    // The value is a key of the widened level, so a `map` before the remap changes the keys;
    // after it, only the leaves.
    let src = with_m(&format!(
        "x = {BUMPED} as (k1 -> k2 -> v) into (k1 -> (k2, v) -> v);\n\
         y = (m as (k1 -> k2 -> v) into (k1 -> (k2, v) -> v)).map(r -> r.map(v -> v + 1));\n"
    ));
    prints(
        &src,
        "x",
        r#"{"a" -> {(1, 11) -> 11, (2, 21) -> 21}, "b" -> {(1, 31) -> 31}}"#,
    );
    prints(
        &src,
        "y",
        r#"{"a" -> {(1, 10) -> 11, (2, 20) -> 21}, "b" -> {(1, 30) -> 31}}"#,
    );
}

// ---- Truncate ----

#[test]
fn a_map_before_a_truncation_leaves_its_keys() {
    let src = with_m(&format!(
        "x = {BUMPED} as (k1 -> k2 -> v) into (k1 -> k2 -> _);\n\
         y = m as (k1 -> k2 -> v) into (k1 -> k2 -> _);\n\
         z = {BUMPED} as (k1 -> k2 -> v) into (k1 -> _);\n"
    ));
    prints(&src, "x", r#"{"a" -> {1, 2}, "b" -> {1}}"#);
    prints(&src, "y", r#"{"a" -> {1, 2}, "b" -> {1}}"#);
    prints(&src, "z", r#"{"a", "b"}"#);
}

#[test]
fn a_map_after_a_truncation_reads_the_key_sets() {
    let src = with_m(
        "x = (m as (k1 -> k2 -> v) into (k1 -> k2 -> _)).map(ks -> ks.sum);\n\
         y = (m as (k1 -> k2 -> v) into (k2 -> k1 -> _)).map(ks -> ks.count);\n",
    );
    prints(&src, "x", r#"{"a" -> 3, "b" -> 1}"#);
    prints(&src, "y", "{1 -> 2, 2 -> 1}");
}

// ---- `map` inside the value expression of a remap ----

#[test]
fn map_in_the_value_of_a_remap() {
    // The value expression builds a list from each leaf and maps it: a third level.
    let src = with_m(
        "x = m as (k1 -> k2 -> v) into (k2 -> k1 -> [v, v + 1].map(w -> w * 2));\n\
         s = m as (k1 -> k2 -> v) into (k2 -> k1 -> [v, v + 1].map(w -> w * 2).sum);\n\
         want = { 1 -> { \"a\" -> [20, 22], \"b\" -> [60, 62] }, 2 -> { \"a\" -> [40, 42] } };\n",
    );
    prints(&src, "x", &value(&src, "want"));
    prints(
        &src,
        "x",
        r#"{1 -> {"a" -> {0 -> 20, 1 -> 22}, "b" -> {0 -> 60, 1 -> 62}}, 2 -> {"a" -> {0 -> 40, 1 -> 42}}}"#,
    );
    prints(
        &src,
        "s",
        r#"{1 -> {"a" -> 42, "b" -> 122}, 2 -> {"a" -> 82}}"#,
    );
}

#[test]
fn map_of_a_row_bound_by_a_shorter_pattern_waits_for_its_step() {
    // `m as (k -> r) into (k -> r.map(f))` binds `r` to a whole row: an `as` pattern of fewer
    // levels than its source, plan row REMAP-fewer-binders. Until it lands the checker refuses
    // it as a later step; that row moves this case to a value check.
    let src = with_m("x = m as (k -> r) into (k -> r.map(v -> v + 1));\n");
    let es = errors(&src).join("\n");
    assert!(
        es.contains("a remap whose `as` pattern names 1 key levels of a source with more"),
        "{es}"
    );
}

#[test]
fn a_remap_in_the_function_of_a_map() {
    // The inverse nesting: each row is shifted by a remap inside `map`'s function.
    let src = with_m("x = m.map(r -> r as (k -> v) into (k + 10 -> v + 1));\n");
    prints(
        &src,
        "x",
        r#"{"a" -> {11 -> 11, 12 -> 21}, "b" -> {11 -> 31}}"#,
    );
}

// ---- Corner cases ----

#[test]
fn map_and_remap_of_an_empty_list() {
    let src = "xs = [1, 2, 3].where(v -> v > 5);\n\
               x = xs.map(v -> v + 1) as (k -> v) into (k + 1 -> v);\n\
               y = (xs as (k -> v) into (k + 1 -> v)).map(v -> v + 1);\n";
    prints(src, "x", "{}");
    prints(src, "y", "{}");
}

#[test]
fn a_map_to_a_constant_then_a_transpose() {
    // Every leaf the same value: the transpose keeps every keypath, none collide.
    let src = with_m("x = m.map(r -> r.map(v -> 0)) as (k1 -> k2 -> v) into (k2 -> k1 -> v);\n");
    prints(&src, "x", r#"{1 -> {"a" -> 0, "b" -> 0}, 2 -> {"a" -> 0}}"#);
}
