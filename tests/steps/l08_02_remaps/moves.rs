//! The three legal moves in source form: repack, widen, truncate (DESIGN.md sec:remap_law,
//! "The legal moves"), with rank insertion (sec:remap_law, "Ranking").

use crate::source::{does_not_parse, same, with_sales};
// The spec examples of these moves that read level names (`sales into (sku -> region -> day ->
// quantitySold)`) and the rank insertions (`asc`, `desc`) wait in
// /home/luke/Work/wt/failing-tests, rows L8.2b and L8.2.

const M: &str = "m = { \"a\" -> { 1 -> 10, 2 -> 20 }, \"b\" -> { 1 -> 30 } };\n";

fn with_m(src: &str) -> String {
    format!("{M}{src}")
}

// ---- Repack ----

#[test]
fn transpose_levels() {
    // sec:remap_law: `as (k1 -> k2 -> v) into (k2 -> k1 -> v)  // transpose levels`.
    let src = with_m(
        "x = m as (k1 -> k2 -> v) into (k2 -> k1 -> v);\n\
         want = { 1 -> { \"a\" -> 10, \"b\" -> 30 }, 2 -> { \"a\" -> 20 } };\n",
    );
    same(&src, "x", "want");
}

#[test]
fn permute_levels_by_as_binders() {
    // sec:level_names: `sales as (r -> d -> s -> q) into (s -> r -> d -> q)`.
    let src = with_sales(
        "x = sales as (r -> d -> s -> q) into (s -> r -> d -> q);\n\
         want = { \"A12\" -> { \"west\" -> { 0 -> 3, 1 -> 2 } }, \"B7\" -> { \"east\" -> { 0 -> 5 }, \"west\" -> { 0 -> 1 } } };\n",
    );
    same(&src, "x", "want");
}

#[test]
fn as_alone_is_the_identity() {
    // sec:remap_law: "`as` alone (`m as (r -> c -> v)`) is the identity remap and only names
    // levels".
    let src = with_m("x = m as (r -> c -> v);\n");
    same(&src, "x", "m");
}

#[test]
fn flatten_to_a_tuple_key() {
    // sec:remap_law: `as (k1 -> k2 -> v) into ((k1, k2) -> v)  // flatten to a tuple key`.
    let src = with_m(
        "x = m as (k1 -> k2 -> v) into ((k1, k2) -> v);\n\
         want = { (\"a\", 1) -> 10, (\"a\", 2) -> 20, (\"b\", 1) -> 30 };\n",
    );
    same(&src, "x", "want");
}

#[test]
fn untuple_a_tuple_key() {
    // The inverse of the flattening: tupling is a catalog witness both ways (sec:grouping,
    // "tupling/permutation of witnessed components").
    let src = with_m(
        "t = m as (k1 -> k2 -> v) into ((k1, k2) -> v);\n\
         x = t as (p -> v) into (p[0] -> p[1] -> v);\n",
    );
    same(&src, "x", "m");
}

#[test]
fn bijective_key_transform() {
    // sec:remap_law: `as (k -> v) into (k + 1 -> v)  // bijective key transform`.
    let src = "xs = [10, 20, 30];\nx = xs as (k -> v) into (k + 1 -> v);\nwant = { 1 -> 10, 2 -> 20, 3 -> 30 };\n";
    same(src, "x", "want");
}

// ---- Widen ----

#[test]
fn widen_a_key_with_the_value() {
    // sec:remap_law: `as (k1 -> k2 -> v) into (k1 -> (k2, v) -> v)`.
    let src = with_m(
        "x = m as (k1 -> k2 -> v) into (k1 -> (k2, v) -> v);\n\
         want = { \"a\" -> { (1, 10) -> 10, (2, 20) -> 20 }, \"b\" -> { (1, 30) -> 30 } };\n",
    );
    same(&src, "x", "want");
}

#[test]
fn widen_by_a_key_function() {
    // Bounds table, row `m as (k -> v) into (w(k) -> k -> v)`: each group holds the keys `w`
    // sends to it.
    let src = "xs = [10, 20, 30, 40, 50];\nx = xs as (i -> v) into (i div 2 -> i -> v);\n\
               want = { 0 -> { 0 -> 10, 1 -> 20 }, 1 -> { 2 -> 30, 3 -> 40 }, 2 -> { 4 -> 50 } };\n";
    same(src, "x", "want");
}

// ---- Truncate ----

#[test]
fn truncate_to_set_leaves() {
    // sec:remap_law: `as (k1 -> k2 -> v) into (k1 -> k2 -> _)  // ... result type
    // K1 -> (K2 -> K2) (set-leaf)`.
    let src = with_m(
        "x = m as (k1 -> k2 -> v) into (k1 -> k2 -> _);\nwant = { \"a\" -> {1, 2}, \"b\" -> {1} };\n",
    );
    same(&src, "x", "want");
}

#[test]
fn a_trailing_key_is_sugar_for_truncate() {
    // sec:remap_law: "`(k1 -> k2)` is sugar for `(k1 -> k2 -> _)`".
    let src = with_m(
        "x = m as (k1 -> k2 -> v) into (k1 -> k2);\ny = m as (k1 -> k2 -> v) into (k1 -> k2 -> _);\n",
    );
    same(&src, "x", "y");
}

#[test]
fn truncate_to_the_outer_level() {
    // sec:remap_law, truncate: the last kept level's keys become the leaves.
    let src = with_sales(
        "x = sales as (r -> d -> s -> q) into (r -> _);\nwant = {\"east\", \"west\"};\n",
    );
    same(&src, "x", "want");
}

// ---- Rank insertion ----

const SCORES: &str = "scores = { \"ann\" -> 3, \"bob\" -> 5, \"cy\" -> 3 };\n";

#[test]
fn a_single_sort_key_takes_no_trailing_comma() {
    // sec:lexical, `,`: "a single key of an output level takes none (`into (desc score,)` is
    // an error)". Rule `Level` of sec:grammar takes `','` before `')'` only after two sort
    // keys or more, so the parser rejects it.
    let src = format!("{SCORES}x = scores as (name -> score) into (desc score,);\n");
    does_not_parse(&src);
}
