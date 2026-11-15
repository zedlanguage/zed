//! Empty levels and the miss atoms of reads on remap results (DESIGN.md sec:remap_law, the
//! paragraph on a key whose inner level is empty; sec:corner_cases, "Empty everything";
//! sec:type_language, the miss atoms of a read).
//!
//! sec:remap_law: "A key whose inner level is empty, `"a"` in `{"a" -> {}}`, is a keypath
//! that ends early, and a remap carries it wherever the output pattern can place it." Its
//! example `into (k.upper -> j -> v)` is a collision as written, since `upper` is not in the
//! witness catalog of sec:grouping (case mapping sends "a" and "A" to one key), so these
//! tests use the witnessed `k + 1` for the same rule. The warning `#emptyLevelDropped` waits
//! for row EMPTY-level-swap, and a fold by `max` or `min` in a pattern for row
//! REDUCE-by-function (/home/luke/Work/wt/failing-tests).

use crate::source::{prints, rejected, same};

/// Key 1 has an empty inner level; key 2 holds one entry.
const M: &str = "m = { 1 -> {}, 2 -> { 0 -> 5 } };\n";

fn with_m(src: &str) -> String {
    format!("{M}{src}")
}

// ---- Where the output can place the short keypath, it keeps its key ----

#[test]
fn an_outer_level_computed_from_the_key_keeps_the_empty_level() {
    // "When the output keypath begins with levels computed only from the keys that short
    // keypath binds, the result keeps their image with an empty level beneath".
    let src = with_m(
        "x = m as (k -> j -> v) into (k + 1 -> j -> v);\nwant = { 2 -> {}, 3 -> { 0 -> 5 } };\n",
    );
    same(&src, "x", "want");
}

#[test]
fn a_tuple_of_key_functions_keeps_the_empty_level() {
    let src = with_m(
        "x = m as (k -> j -> v) into ((k, 2 * k) -> j -> v);\n\
         want = { (1, 2) -> {}, (2, 4) -> { 0 -> 5 } };\n",
    );
    same(&src, "x", "want");
}

#[test]
fn truncation_keeps_the_empty_level_as_an_empty_set() {
    let src = with_m("x = m as (k -> j -> v) into (k -> j -> _);\nwant = { 1 -> {}, 2 -> {0} };\n");
    same(&src, "x", "want");
}

#[test]
fn widening_the_inner_level_keeps_the_empty_level() {
    let src = with_m(
        "x = m as (k -> j -> v) into (k -> (j, v) -> v);\nwant = { 1 -> {}, 2 -> { (0, 5) -> 5 } };\n",
    );
    same(&src, "x", "want");
}

// ---- Where it cannot, the key is dropped ----

#[test]
fn a_transpose_drops_the_key_of_an_empty_level() {
    // "Only a move that puts a level the short keypath does not bind ahead of its keys has
    // nowhere to place it, and drops the key: `{"a" -> {}}` transposed is `{}`."
    let src = "m = { \"a\" -> { 1 -> 10 } }.map(r -> r.where(v -> v > 99));\n\
               x = m as (k -> j -> v) into (j -> k -> v);\n";
    prints(src, "x", "{}");
    let src = with_m("x = m as (k -> j -> v) into (j -> k -> v);\nwant = { 0 -> { 2 -> 5 } };\n");
    same(&src, "x", "want");
}

#[test]
fn flattening_to_a_tuple_key_drops_the_key_of_an_empty_level() {
    // The tuple key `(k, j)` needs a `j` the short keypath does not bind.
    let src = with_m("x = m as (k -> j -> v) into ((k, j) -> v);\nwant = { (2, 0) -> 5 };\n");
    same(&src, "x", "want");
}

#[test]
fn a_fold_of_the_outer_level_drops_the_key_of_an_empty_level() {
    // The fold of `k` puts `j` first; key 1 has no `j`.
    let src = with_m("x = m as (k -> j -> v) into (k >< (+) -> j -> v);\nwant = { 0 -> 5 };\n");
    same(&src, "x", "want");
}

// ---- A fold of an empty level (sec:corner_cases, "Reduce over empty: identity if the operator
// has one, else `#empty`") ----

#[test]
fn a_sum_of_an_empty_level_is_zero() {
    let src = "m = { \"a\" -> { 1 -> 10 }, \"b\" -> {} };\n\
               x = m as (k1 -> k2 -> v) into (k1 -> k2 >< (+) -> v);\nwant = { \"a\" -> 10, \"b\" -> 0 };\n";
    same(src, "x", "want");
}

#[test]
fn a_sum_and_a_product_of_a_level_emptied_by_a_filter() {
    // The inner level of "a" is emptied at run time by `where`; the fold gives the identity
    // of `+`, 0, and of `*`, 1.
    let src = "m = { \"a\" -> [1], \"b\" -> [5] }.map(r -> r.where(v -> v > 3));\n\
               s = m as (k -> j -> v) into (k -> j >< (+) -> v);\nwantS = { \"a\" -> 0, \"b\" -> 5 };\n\
               p = m as (k -> j -> v) into (k -> j >< (*) -> v);\nwantP = { \"a\" -> 1, \"b\" -> 5 };\n";
    same(src, "s", "wantS");
    same(src, "p", "wantP");
}

#[test]
fn and_and_or_of_an_empty_level_are_their_identities() {
    // The identity of `&&` is `true`, of `||` `false`.
    let src = "m = { 1 -> {}, 2 -> { 0 -> true } };\n\
               a = m as (k -> j -> v) into (k -> j >< (&&) -> v);\nwantA = { 1 -> true, 2 -> true };\n\
               o = m as (k -> j -> v) into (k -> j >< (||) -> v);\nwantO = { 1 -> false, 2 -> true };\n";
    same(src, "a", "wantA");
    same(src, "o", "wantO");
}

// ---- Miss atoms of a read on a remap result (sec:type_language: "`a[i] : T | #outOfBounds`
// on an array, `m[k] : V | #notFound` on a map") ----

#[test]
fn the_identity_remap_of_a_list_misses_as_a_list() {
    // `#outOfBounds` is the miss "at a level whose keys are one integer interval, every key
    // present" (sec:type_language, "An operation that always fails is rejected"); the
    // identity remap keeps the keys 0..<2 of the list.
    let src = "xs = [10, 20];\nx = xs as (k -> v);\nf(u: int) = x[u];\ng(u: int) = xs[u];\n\
               y = f(u: 5);\nz = g(u: 5);\n";
    prints(src, "y", "#outOfBounds");
    prints(src, "z", "#outOfBounds");
}

#[test]
fn a_shifted_remap_misses_with_not_found() {
    // `k + 1` moves the keys to 1..<3; the result is a map whose keys the remap computed, and
    // a read at 0 misses with `#notFound`.
    let src = "xs = [10, 20];\nx = xs as (k -> v) into (k + 1 -> v);\nf(u: int) = x[u];\n\
               y = f(u: 0);\nhit = f(u: 2);\n";
    prints(src, "y", "#notFound");
    prints(src, "hit", "20");
}

#[test]
fn a_constant_read_past_the_keys_is_rejected() {
    // sec:type_language: "An operation that always fails is rejected": `x[5]` on keys 0..<2
    // can only miss.
    let src = "xs = [10, 20];\nx = xs as (k -> v);\ny = x[5];\n";
    rejected(src, &["x[5]"]);
}
