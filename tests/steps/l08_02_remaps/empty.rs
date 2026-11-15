//! Empty levels and the miss atoms of reads on remap results (DESIGN.md sec:remap_law, the
//! paragraph on a key whose inner level is empty; sec:corner_cases, "Empty everything";
//! sec:type_language, the miss atoms of a read).
//!
//! sec:remap_law: "A key whose inner level is empty, `"a"` in `{"a" -> {}}`, is a keypath
//! that ends early, and a remap carries it wherever the output pattern can place it." Its
//! example widens the key to `(k, k.upper)`; `k.upper` alone is a collision, since case
//! mapping sends "a" and "A" to one key (DESIGN d2c5d1e). The warning `#emptyLevelDropped` waits
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
fn the_design_example_widened_by_upper_keeps_the_empty_level() {
    // sec:remap_law: "`{"a" -> {}} as (k -> j -> v) into ((k, k.upper) -> j -> v)` is
    // `{("a", "A") -> {}}`".
    let src = "a = { \"a\" -> {} };\nx = a as (k -> j -> v) into ((k, k.upper) -> j -> v);\n";
    prints(src, "x", "{(\"a\", \"A\") -> {}}");
}

#[test]
fn upper_alone_as_the_outer_key_collides() {
    // "`k.upper` alone is no witness, since `"a"` and `"A"` meet at `"A"`".
    let src = "a = { \"a\" -> {} };\nx = a as (k -> j -> v) into (k.upper -> j -> v);\n";
    rejected(src, &["k.upper"]);
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

#[test]
fn max_and_min_of_an_empty_int_level_are_empty() {
    // sec:reduction, "Identity as data": "`max` over a possibly-empty domain at `int`, which
    // has no identity for it, is `T | #empty`"; `min` likewise. The `f64` case gets `-inf` from
    // its own identity (the float tests below).
    let src = "m = { \"a\" -> [1], \"b\" -> [5] }.map(r -> r.where(v -> v > 3));\n\
               hi = m.map(r -> r >< max);\nlo = m.map(r -> r >< min);\n";
    prints(src, "hi", "{\"a\" -> #empty, \"b\" -> 5}");
    prints(src, "lo", "{\"a\" -> #empty, \"b\" -> 5}");
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

// ---- A fold of an empty float level (DESIGN.md sec:reduction, "Identity as data"; rows
// SPEC-empty-f64-sum and FAIL-f64-max-empty-identity) ----

/// The level of "a" is emptied at run time by `where`.
const F: &str = "m = { \"a\" -> [1.0], \"b\" -> [5.0] }.map(r -> r.where(v -> v > 3.0));\n";

#[test]
fn max_of_an_empty_f64_level_is_minus_infinity() {
    // "`max` at `f64` gets `-inf` from its own" identity; `min` gets `inf` the same way, the
    // identities of IEEE 754-2019 `maximum` and `minimum`.
    let src = format!("{F}hi = m.map(r -> r >< max);\nlo = m.map(r -> r >< min);\n");
    prints(&src, "hi", "{\"a\" -> -inf, \"b\" -> 5.0}");
    prints(&src, "lo", "{\"a\" -> inf, \"b\" -> 5.0}");
}

#[test]
fn an_f64_max_fold_has_no_empty_in_its_type() {
    // "none of the four folds has `#empty` in its type"; at `int`, `max` keeps it.
    use zed_tests::step_helpers::l01_26_type_resolution::info;
    let top = |src: &str| info(src).0.tops["x"].to_string();
    for op in ["max", "min", "(+)", "(*)"] {
        let t = top(&format!("{F}x = m.map(r -> r >< {op});\n"));
        assert!(t.contains("f64") && !t.contains("#empty"), "{op}: {t}");
    }
    let t = top(
        "m = { \"a\" -> [1], \"b\" -> [5] }.map(r -> r.where(v -> v > 3));\n\
                 x = m.map(r -> r >< max);\n",
    );
    assert!(t.contains("#empty"), "{t}");
}

#[test]
fn a_sum_of_an_empty_f64_level_is_minus_zero_and_a_product_one() {
    // `-0.0` is the identity of float `+`: `-0.0 + x` is `x` for every `x`, while
    // `0.0 + -0.0` is `0.0` (IEEE 754-2019 sec. 6.3); `1.0` is the identity of `*`.
    let src = format!("{F}s = m.map(r -> r >< (+));\np = m.map(r -> r >< (*));\n");
    prints(&src, "s", "{\"a\" -> -0.0, \"b\" -> 5.0}");
    prints(&src, "p", "{\"a\" -> 1.0, \"b\" -> 5.0}");
}

#[test]
fn a_sum_of_sums_over_an_empty_level_is_the_flat_sum() {
    // With `0.0` as the empty sum the outer fold would give `0.0 + -0.0`, which is `0.0`,
    // where the flat sum of the one entry `-0.0` is `-0.0`.
    let src = "m = { \"a\" -> [1.0], \"b\" -> [-0.0] }.map(r -> r.where(v -> v < 1.0));\n\
               nested = m.map(r -> r >< (+)) >< (+);\n\
               flat = m as (k -> j -> v) into (k >< (+) -> j >< (+) -> v);\n";
    prints(src, "nested", "-0.0");
    prints(src, "flat", "-0.0");
}

#[test]
fn the_empty_folds_of_an_f32_level_are_its_identities() {
    let src = "m = { \"a\" -> [1.0f32], \"b\" -> [5.0f32] }.map(r -> r.where(v -> v > 3.0f32));\n\
               s = m.map(r -> r >< (+));\np = m.map(r -> r >< (*));\n\
               hi = m.map(r -> r >< max);\nlo = m.map(r -> r >< min);\n";
    prints(src, "s", "{\"a\" -> -0.0f32, \"b\" -> 5.0f32}");
    prints(src, "p", "{\"a\" -> 1.0f32, \"b\" -> 5.0f32}");
    prints(src, "hi", "{\"a\" -> -inff32, \"b\" -> 5.0f32}");
    prints(src, "lo", "{\"a\" -> inff32, \"b\" -> 5.0f32}");
}

#[test]
fn the_sum_and_product_of_an_empty_int_level_are_zero_and_one() {
    // "`sum` gets its identity, `0` at `int`", in a function's body as outside one.
    let src = "m = { \"a\" -> [1], \"b\" -> [5] }.map(r -> r.where(v -> v > 3));\n\
               s = m.map(r -> r >< (+));\np = m.map(r -> r >< (*));\n";
    prints(src, "s", "{\"a\" -> 0, \"b\" -> 5}");
    prints(src, "p", "{\"a\" -> 1, \"b\" -> 5}");
}

#[test]
fn a_named_function_folded_at_one_carrier_takes_its_identity() {
    // The one fold `top`'s body elaborates to runs at `f64` alone, at both calls.
    let src = format!(
        "top(positional xs) = xs >< max;\n{F}hi = m.map(r -> top(r));\none = top([2.0, 3.0]);\n"
    );
    prints(&src, "hi", "{\"a\" -> -inf, \"b\" -> 5.0}");
    prints(&src, "one", "3.0");
}

#[test]
fn a_fold_run_at_two_carriers_with_different_empty_folds_is_not_compiled_yet() {
    // The one fold `top`'s body elaborates to cannot give `#empty` at `int` and `-inf` at
    // `f64`, and an empty level holds no entry that shows its carrier at run time.
    rejected(
        "top(positional xs) = xs >< max;\na = top([1, 2]);\nb = top([1.0, 2.0]);\n",
        &[
            "an empty level folds to `#empty` at `int` and `-inf` at `f64`",
            "does not compile it yet",
        ],
    );
    // Calls at `int` alone, where `max` has no identity, fold an empty level to `#empty`.
    let src = "top(positional xs) = xs >< max;\na = top([1, 2]);\nb = top([3, 4]);\n";
    prints(src, "b", "4");
}

#[test]
fn a_fold_of_an_empty_display_and_of_a_float_level_in_one_function_is_not_compiled_yet() {
    // `top([])` has no carrier and folds to `#empty`; `top([1.0])` folds an empty level to
    // `-inf`; the one fold gives one of the two, so neither type would hold at both.
    rejected(
        "top(positional xs) = xs >< max;\na = top([]);\nb = top([1.0, 2.0]);\n",
        &["does not compile it yet"],
    );
}

#[test]
fn a_fold_reached_through_two_functions_takes_the_identity_of_its_one_carrier() {
    // `g` calls `top` on its own parameter, so the fold's carrier is known only at `g`'s
    // calls; each is checked at the fold's own place.
    let src = format!(
        "top(positional xs) = xs >< max;\ng(positional ys) = top(ys);\n{F}hi = m.map(r -> g(r));\n"
    );
    prints(&src, "hi", "{\"a\" -> -inf, \"b\" -> 5.0}");
    rejected(
        "top(positional xs) = xs >< max;\ng(positional ys) = top(ys);\na = g([1, 2]);\n\
         b = g([1.0, 2.0]);\n",
        &[
            "`#empty` at `int` and `-inf` at `f64`",
            "does not compile it yet",
        ],
    );
}

#[test]
fn reduce_in_a_generic_function_takes_the_identity_of_its_one_carrier() {
    // `.reduce(op)` is the fold `><` written as a method, and shares its checks.
    let src = format!(
        "s(positional xs) = xs.reduce((+));\ntop(positional xs) = xs.reduce(max);\n{F}\
         lo = m.map(r -> s(r));\nhi = m.map(r -> top(r));\n"
    );
    prints(&src, "lo", "{\"a\" -> -0.0, \"b\" -> 5.0}");
    prints(&src, "hi", "{\"a\" -> -inf, \"b\" -> 5.0}");
    rejected(
        "top(positional xs) = xs.reduce(max);\na = top([1, 2]);\nb = top([1.0, 2.0]);\n",
        &["does not compile it yet"],
    );
}

// ---- `.sum` in a generic function (row FAIL-generic-sum-method): DESIGN.md's method
// register, "tot = xs.sum; // = xs >< (+)"; on a tuple `.sum` is the prelude word of layer 1 ----

#[test]
fn sum_in_a_generic_function_folds_a_family() {
    let src = format!("s(positional xs) = xs.sum;\n{F}lo = m.map(r -> s(r));\n");
    prints(&src, "lo", "{\"a\" -> -0.0, \"b\" -> 5.0}");
    let src = "s(positional xs) = xs.sum;\nt = s([1, 2, 3]);\n";
    prints(src, "t", "6");
}

#[test]
fn sum_in_a_generic_function_adds_a_tuple() {
    let src = "s(positional xs) = xs.sum;\nt = s((1, 2, 3));\n";
    prints(src, "t", "6");
}

#[test]
fn sum_in_a_generic_function_called_on_a_family_and_on_a_tuple() {
    // One body serves both calls: the value is tested at run time, a tuple summed by the
    // prelude word and a family folded by `(+)` with the identity of its one carrier.
    let src = format!(
        "s(positional xs) = xs.sum;\n{F}lo = m.map(r -> s(r));\nt = s((1.5f64, 2.5f64));\n"
    );
    prints(&src, "lo", "{\"a\" -> -0.0, \"b\" -> 5.0}");
    prints(&src, "t", "4.0");
}

#[test]
fn sum_reached_through_two_generic_functions_is_decided_at_the_outer_calls() {
    let src = format!(
        "s(positional xs) = xs.sum;\ng(positional ys) = s(ys);\n{F}lo = m.map(r -> g(r));\n\
         t = g((1, 2));\n"
    );
    prints(&src, "lo", "{\"a\" -> -0.0, \"b\" -> 5.0}");
    prints(&src, "t", "3");
}

#[test]
fn sum_in_a_generic_function_at_two_carriers_is_not_compiled_yet() {
    // `0` at `int` and `-0.0` at `f64` are two empty sums for one fold (row
    // REDUCE-generic-identity), as for `><` and `.reduce`.
    rejected(
        "s(positional xs) = xs.sum;\na = s([1, 2]);\nb = s([1.0, 2.0]);\n",
        &["does not compile it yet"],
    );
}

#[test]
fn sum_in_a_generic_function_rejects_what_is_neither_numbers_nor_a_family_of_them() {
    rejected(
        "s(positional xs) = xs.sum;\nt = s((\"a\", 1));\n",
        &["`sum` does not take"],
    );
    rejected(
        "s(positional xs) = xs.sum;\nt = s(3);\n",
        &["`sum` does not take"],
    );
}
