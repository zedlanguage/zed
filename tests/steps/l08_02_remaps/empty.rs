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
    // identities of IEEE 754-2019 `maximum` and `minimum` (doi:10.1109/IEEESTD.2019.8766229,
    // section 9.6; the full comment is in zed-kernel `value.rs`, fn `ieee_min_max`).
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
    // `0.0 + -0.0` is `0.0` (IEEE 754-2019 sec. 6.3); `1.0` is the identity of `*`. Citation:
    // IEEE Std 754-2019, doi:10.1109/IEEESTD.2019.8766229, section 6.3, "The sign bit"; the
    // full comment is in zedc-check `check/walk.rs`, at the identity of a float `+` fold.
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

/// `mi`, the `int` twin of `m` in `F`: key "a" has an empty level, key "b" holds `5`.
const I: &str = "mi = { \"a\" -> [1], \"b\" -> [5] }.map(r -> r.where(v -> v > 3));\n";

#[test]
fn a_fold_run_at_two_carriers_takes_the_identity_of_each() {
    // "`max` over a possibly-empty domain at `int`, which has no identity for it, is
    // `T | #empty`", while "`max` at `f64` gets `-inf` from its own": an empty level holds no
    // entry that shows its carrier at run time, so each call takes a body made at its own
    // identity (row REDUCE-generic-identity).
    let src = format!(
        "top(positional xs) = xs >< max;\n{F}{I}a = top([1, 2]);\nb = top([1.0, 2.0]);\n\
         hi = m.map(r -> top(r));\nhii = mi.map(r -> top(r));\n"
    );
    prints(&src, "a", "2");
    prints(&src, "b", "2.0");
    prints(&src, "hi", "{\"a\" -> -inf, \"b\" -> 5.0}");
    prints(&src, "hii", "{\"a\" -> #empty, \"b\" -> 5}");
    // Calls at `int` alone, where `max` has no identity, fold an empty level to `#empty`.
    let src = "top(positional xs) = xs >< max;\na = top([1, 2]);\nb = top([3, 4]);\n";
    prints(src, "b", "4");
}

#[test]
fn a_fold_of_an_empty_display_and_of_a_float_level_in_one_function_takes_each_identity() {
    // "`[]` takes the identity of the type the call site fixes, or `#empty` with none": `[]`
    // fixes no carrier, so `top([])` is `#empty`, and `top([1.0, 2.0])` is `2.0`.
    let src = format!(
        "top(positional xs) = xs >< max;\n{F}a = top([]);\nb = top([1.0, 2.0]);\n\
         hi = m.map(r -> top(r));\n"
    );
    prints(&src, "a", "#empty");
    prints(&src, "b", "2.0");
    prints(&src, "hi", "{\"a\" -> -inf, \"b\" -> 5.0}");
}

#[test]
fn a_fold_reached_through_two_functions_takes_the_identity_of_its_one_carrier() {
    // `g` calls `top` on its own parameter, so the fold's carrier is known only at `g`'s
    // calls; each is checked at the fold's own place.
    let src = format!(
        "top(positional xs) = xs >< max;\ng(positional ys) = top(ys);\n{F}hi = m.map(r -> g(r));\n"
    );
    prints(&src, "hi", "{\"a\" -> -inf, \"b\" -> 5.0}");
    // At `int` and at `f64` both, each call of `g` takes a body of `g` whose call of `top`
    // takes the body of `top` at the identity the outer call decided.
    let src = format!(
        "top(positional xs) = xs >< max;\ng(positional ys) = top(ys);\n{F}{I}a = g([1, 2]);\n\
         b = g([1.0, 2.0]);\nhi = m.map(r -> g(r));\nhii = mi.map(r -> g(r));\n"
    );
    prints(&src, "a", "2");
    prints(&src, "b", "2.0");
    prints(&src, "hi", "{\"a\" -> -inf, \"b\" -> 5.0}");
    prints(&src, "hii", "{\"a\" -> #empty, \"b\" -> 5}");
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
    let src = format!(
        "top(positional xs) = xs.reduce(max);\n{F}{I}a = top([1, 2]);\nb = top([1.0, 2.0]);\n\
         hi = m.map(r -> top(r));\nhii = mi.map(r -> top(r));\n"
    );
    prints(&src, "a", "2");
    prints(&src, "b", "2.0");
    prints(&src, "hi", "{\"a\" -> -inf, \"b\" -> 5.0}");
    prints(&src, "hii", "{\"a\" -> #empty, \"b\" -> 5}");
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
fn sum_in_a_generic_function_at_two_carriers_takes_the_identity_of_each() {
    // "`sum` gets its identity, `0` at `int`", and at a float "`-0.0` for `+`": two empty
    // sums for one fold, so each call takes a body at its own (row REDUCE-generic-identity),
    // as for `><` and `.reduce`.
    let src = format!(
        "s(positional xs) = xs.sum;\n{F}{I}a = s([1, 2]);\nb = s([1.0, 2.0]);\n\
         lo = m.map(r -> s(r));\nloi = mi.map(r -> s(r));\nt = s((1, 2));\n"
    );
    prints(&src, "a", "3");
    prints(&src, "b", "3.0");
    prints(&src, "lo", "{\"a\" -> -0.0, \"b\" -> 5.0}");
    prints(&src, "loi", "{\"a\" -> 0, \"b\" -> 5}");
    prints(&src, "t", "3");
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

// ---- A type parameter joined with a family or a tuple, and keypaths (row
// TEST-generic-sum-branches). DESIGN.md's method register: "tot = xs.sum; // = xs >< (+)";
// sec:kernel: "`m >< op` / `.reduce(op)` / `.sum` | `fold(m, op, ev)`"; layer 1: "`sum` of a
// tuple ... is a type error on mixed number kinds"; sec:premise: "One operation behaves the
// same in every context: ... in generic and in specific code", so a call of a generic
// function is accepted or rejected as its body written at the call's types is. ----

/// `xs` joined with the family `[1, 2]`: the receiver of the fold is `X | (int -> int)`.
const JOINED: &str = "(if b { xs } else { [1, 2] })";

#[test]
fn a_parameter_joined_with_a_family_is_folded_at_each_call() {
    // At `X` a family of `int`: the concrete `(if b { [3, 4] } else { [1, 2] }).sum` is `7`
    // when `b` holds and `3` when it does not.
    let src = format!(
        "s(positional xs, positional b) = {JOINED}.sum;\nt = s([3, 4], true);\nf = s([3, 4], false);\n"
    );
    prints(&src, "t", "7");
    prints(&src, "f", "3");
    let src = format!("s(positional xs, positional b) = {JOINED} >< (+);\nt = s([3, 4], true);\n");
    prints(&src, "t", "7");
}

#[test]
fn a_parameter_joined_with_a_family_rejects_what_is_no_family_at_the_call() {
    // `><` and `.reduce` have one arrow, from a family (sec:reduction), so
    // `(if b { (3, 4) } else { [1, 2] }) >< (+)` is rejected, and the call that makes `xs` a
    // tuple is rejected too. Before row TEST-generic-sum-branches the checker read only
    // `[1, 2]`'s entries, accepted the call, and the run stopped in the kernel's fold on a
    // value that is no family. `.sum` has a second arrow, from a tuple (step L1.18), and takes
    // the union region by region (sec:type_resolution, rule 6: "over each region of the
    // argument type, the codomains of all arrows covering that region intersect; across
    // regions, results union"), so at `(3, 4)` it gives `3 + 4` (row FAIL-sum-word-family);
    // a string or a number is in the region of neither arrow ("If no arrow applies, that is
    // the error").
    let src = format!("s(positional xs, positional b) = {JOINED}.sum;\n");
    prints(&format!("{src}t = s((3, 4), true);\n"), "t", "7");
    prints(&format!("{src}t = s((3, 4), false);\n"), "t", "3");
    for arg in ["\"ab\"", "5"] {
        rejected(
            &format!("{src}t = s({arg}, true);\n"),
            &["`sum` does not take"],
        );
    }
    for (fold, arg) in [(" >< (+)", "(3, 4)"), (".reduce((+))", "(3, 4)")] {
        rejected(
            &format!("s(positional xs, positional b) = {JOINED}{fold};\nt = s({arg}, true);\n"),
            &["folds the entries of a family"],
        );
    }
}

#[test]
fn a_parameter_joined_with_a_family_of_another_carrier_is_not_compiled_yet() {
    // At `X` a family of `f64` the fold runs at `int` and at `f64`, which have two identities,
    // `0` and `-0.0` (sec:reduction, "Identity as data"); the concrete
    // `(if b { [3.5, 4.0] } else { [1, 2] }).sum` is refused as not supported too.
    rejected(
        &format!("s(positional xs, positional b) = {JOINED}.sum;\nt = s([3.5, 4.0], false);\n"),
        &["not supported by this version of zedc"],
    );
    rejected(
        "f(positional b) = (if b { [3.5, 4.0] } else { [1, 2] }).sum;\nt = f(false);\n",
        &["not supported by this version of zedc"],
    );
}

#[test]
fn a_parameter_joined_with_the_empty_family_folds_at_the_parameters_carrier() {
    // sec:reduction, "Identity as data": "`sum` gets its identity, `0` at `int`", and "`max`
    // ... at `int`, which has no identity for it, is `T | #empty`". The concrete
    // `(if b { [3, 4] } else { [] }).sum` gives `0` when `b` does not hold; before this row
    // the generic body gave `#empty`.
    let src = "s(positional xs, positional b) = (if b { xs } else { [] }).sum;\n\
               t = s([3, 4], true);\nf = s([3, 4], false);\n";
    prints(src, "t", "7");
    prints(src, "f", "0");
    let src = "s(positional xs, positional b) = (if b { xs } else { [] }) >< max;\n\
               t = s([3, 4], true);\nf = s([3, 4], false);\n";
    prints(src, "t", "4");
    prints(src, "f", "#empty");
    // A tuple passed there is summed by adding, and `[]` beside it has no carrier, as in the
    // concrete `(if b { (3, 4) } else { [] }).sum` (rule 6 of sec:type_resolution; row
    // FAIL-sum-empty-family-beside-parameter).
    let src = "s(positional xs, positional b) = (if b { xs } else { [] }).sum;\n\
               t = s((3, 4), true);\nf = s((3, 4), false);\n";
    prints(src, "t", "7");
    prints(src, "f", "#empty");
}

#[test]
fn two_parameters_joined_each_take_the_fold() {
    // `if b { xs } else { ys }` is `X | Y`: each variable is checked at the call, not only the
    // first. `.sum` at a tuple is the word of layer 1, `(1, 2)` gives `3`; a string is
    // refused by it; `><` at a tuple is refused as `(1, 2) >< (+)` is.
    let sum = "s(positional xs, positional ys, positional b) = (if b { xs } else { ys }).sum;\n";
    let src = format!("{sum}t = s([3, 4], (1, 2), true);\nf = s([3, 4], (1, 2), false);\n");
    prints(&src, "t", "7");
    prints(&src, "f", "3");
    rejected(
        &format!("{sum}t = s([3, 4], \"ab\", false);\n"),
        &["`sum` does not take"],
    );
    rejected(
        "s(positional xs, positional ys, positional b) = (if b { xs } else { ys }) >< (+);\n\
         t = s([3, 4], (1, 2), false);\n",
        &["folds the entries of a family"],
    );
}

#[test]
fn a_parameter_joined_with_a_tuple_is_summed_as_a_tuple() {
    // `X | (int, int)`: at a tuple `.sum` is the word of layer 1 and adds. At a family it is
    // the fold, region by region, as the concrete `(if b { [3, 4] } else { (1, 2) }).sum` is
    // (sec:type_resolution, rule 6: "over each region of the argument type, the codomains of
    // all arrows covering that region intersect; across regions, results union"; row
    // FAIL-sum-word-family). A string is in the region of neither arrow.
    let src = "s(positional xs, positional b) = (if b { xs } else { (1, 2) }).sum;\n";
    prints(&format!("{src}t = s((3, 4), true);\n"), "t", "7");
    prints(&format!("{src}f = s((3, 4), false);\n"), "f", "3");
    prints(&format!("{src}t = s([3, 4], true);\n"), "t", "7");
    prints(&format!("{src}f = s([3, 4], false);\n"), "f", "3");
    rejected(
        &format!("{src}t = s(\"ab\", true);\n"),
        &["`sum` does not take"],
    );
}

#[test]
fn a_family_made_by_a_reindex_takes_the_fold_branch() {
    // `group` builds its classes by the kernel's `reindex`, whose keypaths are the one value
    // the run-time tuple test of a generic `.sum` would also take; none reaches a program's
    // terms (the proof at `Elab::generic_sum`). sec:grouping: `group` keys each entry by its
    // class, then its key, so the classes of `[1, 2, 3, 4]` by `v mod 2` are
    // `{0 -> {1 -> 2, 3 -> 4}, 1 -> {0 -> 1, 2 -> 3}}`, and their sums `6` and `4`.
    let src = "s(positional xs) = xs.sum;\nm = [1, 2, 3, 4];\n\
               t = m.group(v -> v mod 2).map(g -> s(g));\n";
    prints(src, "t", "{0 -> 6, 1 -> 4}");
}

#[test]
fn two_parameters_in_nested_branches_beside_a_family_each_take_the_fold() {
    // `X0 | X1 | (int -> int)`: each parameter is checked at the call, as the concrete body is.
    // `[5, 6]` in the inner branch gives `5 + 6`; a family keyed by another type gives its
    // entry. A tuple there takes `.sum`'s tuple arrow, region by region, as the concrete
    // `(if b { [3, 4] } else { if c { (1, 2) } else { [1, 2] } }).sum` does (sec:type_resolution,
    // rule 6; row FAIL-sum-word-family): `(1, 2)` gives `3`. A string there, or a tuple folded
    // by `><`, which has the family arrow alone, is rejected.
    let s = "s(positional x0, positional x1, positional b, positional c) = \
             (if b { x0 } else { if c { x1 } else { [1, 2] } })";
    prints(
        &format!("{s}.sum;\nt = s([3, 4], [5, 6], false, true);\n"),
        "t",
        "11",
    );
    prints(
        &format!("{s}.sum;\nt = s([3, 4], {{ 7 -> 1 }}, false, true);\n"),
        "t",
        "1",
    );
    prints(
        &format!("{s}.sum;\nt = s([3, 4], (1, 2), false, true);\n"),
        "t",
        "3",
    );
    prints(
        "f(positional b, positional c) = \
         (if b { [3, 4] } else { if c { (1, 2) } else { [1, 2] } }).sum;\nt = f(false, true);\n",
        "t",
        "3",
    );
    rejected(
        &format!("{s}.sum;\nt = s([3, 4], \"ab\", false, false);\n"),
        &["`sum` does not take"],
    );
    rejected(
        &format!("{s} >< (+);\nt = s([3, 4], (1, 2), false, false);\n"),
        &["folds the entries of a family"],
    );
    // Under one condition the inner `then` branch is known not to run and is dropped, in
    // generic and in concrete code alike: both give `3`.
    prints(
        "s(positional x0, positional x1, positional b) = \
         (if b { x0 } else { if b { x1 } else { [1, 2] } }).sum;\nt = s([3, 4], (1, 2), false);\n",
        "t",
        "3",
    );
    prints(
        "f(positional b) = (if b { [3, 4] } else { if b { (1, 2) } else { [1, 2] } }).sum;\n\
         t = f(false);\n",
        "t",
        "3",
    );
}

// ---- The fold of a generic function ends on every cycle of classes, and hand-made ZIR does
// not make it give a wrong value (row PROOF-fold-level-recursion-terminates; the proofs at
// `Class::resolved` in zedc-check and at `Elab::generic_sum` in zedc-elab) ----

#[test]
fn a_cycle_of_parameters_through_calls_folds_at_each_call() {
    // `r` swaps the parameters and `s` swaps them back, so `s(a, b, c)` is `q(a, b, c)`
    // (sec:values_morphisms, a call is its body with the arguments put for the parameters).
    // `[1, 2].sum` is `[1, 2] >< (+)`, `3` (the method register, "tot = xs.sum; // = xs >< (+)"),
    // and `(3, 4).sum` is `7` (L1.18, `sum` of a tuple).
    let q = "r(positional xs, positional ys, positional b) = q(ys, xs, b);\n\
             s(positional xs, positional ys, positional b) = r(ys, xs, b);\n";
    let src = format!(
        "q(positional xs, positional ys, positional b) = (if b {{ xs }} else {{ ys }}).sum;\n{q}\
         t = s([1, 2], (3, 4), true);\nu = s([1, 2], (3, 4), false);\n"
    );
    prints(&src, "t", "3");
    prints(&src, "u", "7");
    let src = format!(
        "q(positional xs, positional ys, positional b) = (if b {{ xs }} else {{ ys }}) >< (+);\n\
         {q}t = s([1, 2], [3, 4], false);\n"
    );
    prints(&src, "t", "7");
    // Both orders at once: `s(a, b, false)` is `b.reduce((+)) + a.reduce((+))`, `7 + 3`.
    let src = "q(positional xs, positional ys, positional b) = \
               (if b { xs } else { ys }).reduce((+));\n\
               r(positional xs, positional ys, positional b) = q(ys, xs, b) + q(xs, ys, b);\n\
               s(positional xs, positional ys, positional b) = r(ys, xs, b);\n\
               t = s([1, 2], [3, 4], false);\n";
    prints(src, "t", "10");
}

#[test]
fn one_type_variable_on_two_parameters_folds_once() {
    // `T` written twice makes `xs` and `ys` one class (sec:type_resolution); `[3, 4].sum` is 7.
    let src = "s(positional xs: T, positional ys: T, positional b) = \
               (if b { xs } else { ys }).sum;\nt = s([1, 2], [3, 4], false);\n";
    prints(src, "t", "7");
}

#[test]
fn a_lambda_given_the_parameters_swapped_folds_at_its_call() {
    // The lambda takes `ys` as `a`, so with `b` it folds `[3, 4]`, 7; the `map` folds `xs`
    // at each of the two keys of `[xs, xs]`.
    let src = "s(positional xs, positional ys, positional b) = \
               ((positional a, positional c) -> (if b { a } else { c }).sum)(ys, xs);\n\
               t = s([1, 2], [3, 4], true);\n";
    prints(src, "t", "7");
    let src = "s(positional xs, positional b) = [xs, xs].map(v -> (if b { v } else { xs }).sum);\n\
               t = s([1, 2], false);\n";
    prints(src, "t", "{0 -> 3, 1 -> 3}");
}

#[test]
fn a_generic_fold_of_a_generic_fold_folds_each_level() {
    // `q` folds each inner level, `[1, 2]` to 3 and `[3]` to 3, and `s` folds those, 6.
    let src = "q(positional xs) = xs >< (+);\ns(positional xs) = xs.map(v -> q(v)) >< (+);\n\
               t = s([[1, 2], [3]]);\n";
    prints(src, "t", "6");
}

#[test]
fn a_parameter_joined_with_a_family_of_itself_is_refused_and_the_check_ends() {
    // A class beside a family whose entries are that class: the fold's entries have no
    // carrier this zedc compiles, so it is refused at the definition, for each form.
    for fold in [".sum", " >< (+)"] {
        rejected(
            &format!(
                "s(positional xs, positional b) = (if b {{ xs }} else {{ [xs] }}){fold};\n\
                 t = s([1, 2], true);\n"
            ),
            &["not supported by this version of zedc"],
        );
    }
    rejected(
        "s(positional xs, positional b) = (if b { xs } else { { 0 -> xs, 1 -> [xs] } }).sum;\n\
         t = s([1, 2], true);\n",
        &["not supported by this version of zedc"],
    );
}

/// The ZIR text of `t` in `s(positional xs) = xs.sum; t = s((3, 4));`, with the argument of
/// the call given as the constant `arg`, written in the text form by hand.
fn sum_with_argument_by_hand(arg: &str) -> zed_kernel::Term {
    use zed_tests::step_helpers::l01_16_elaboration::{elab, with_prelude};
    let u = elab("s(positional xs) = xs.sum;\nt = s((3, 4));\n").unwrap();
    let g = zedc::zir::lower::lower(&with_prelude(u.get("t").unwrap().clone())).unwrap();
    let text = zedc::zir::text::print(&g);
    let tuple = (text.lines())
        .find_map(|l| l.strip_suffix(" prim tuple (3, 4) -> (_)"))
        .unwrap_or_else(|| panic!("no tuple node in\n{text}"));
    let from = format!(", {tuple}^0) -> (_ hint name \"t\")");
    assert_eq!(text.matches(&from).count(), 1, "{text}");
    let text = text.replace(&from, &format!(", {arg}) -> (_ hint name \"t\")"));
    let g = zedc::zir::text::parse(&text).unwrap_or_else(|e| panic!("{e}\n{text}"));
    zedc::zir::validate::validate(&g).unwrap_or_else(|e| panic!("{e}\n{text}"));
    zedc::zir::lower::raise(&g).unwrap_or_else(|e| panic!("{e}\n{text}"))
}

#[test]
fn a_keypath_written_into_zir_by_hand_stops_the_sum() {
    // The writers give a keypath constant only inside a key map (`Elab::generic_sum`, case
    // (c)); the validator checks structure, not the types of values (DESIGN.md step L1.31),
    // so a keypath written by hand as the argument of a generic `.sum` is read, validated
    // and run. It takes the tuple branch, and `sum` stops on it, in the kernel and natively,
    // as on a tuple of strings written by hand: neither gives a value. The tuple `(3, 4)`
    // written the same way gives 7, `(3, 4).sum` (L1.18).
    use zed_tests::step_helpers::l01_36_cranelift::{kernel, native};
    let t = sum_with_argument_by_hand("(3, 4)");
    assert_eq!(kernel(&t).map(|v| v.to_string()), Ok("7".to_string()));
    assert_eq!(native(&t).map(|o| o.value.to_string()), Ok("7".to_string()));
    for arg in ["[3 -> 4]", "[]", "(\"a\", 4)"] {
        let t = sum_with_argument_by_hand(arg);
        let k = kernel(&t).expect_err(arg);
        assert!(k.contains("`sum` applied to"), "{arg}: {k}");
        let n = native(&t).expect_err(arg);
        assert!(n.contains("`sum` applied to"), "{arg}: {n}");
    }
}

// ---- Where the identity in force is the one each call decided (row REDUCE-generic-identity):
// sec:reduction, "Identity as data": "`max` at `f64` gets `-inf`", while "`max` over a
// possibly-empty domain at `int`, which has no identity for it, is `T | #empty`"; "`sum` gets
// its identity, `0` at `int`", `-0.0` at a float, and `*` folds an empty level to `1` and
// `1.0`. `mi["a"]` and `m["a"]` are empty levels ----

/// `top`, a fold by `max` that takes its carrier from its calls.
const TOP: &str = "top(positional xs) = xs >< max;\n";

#[test]
fn a_fold_under_a_map_in_a_generic_function_takes_the_identity_of_each_call() {
    // The fold's need waits in the lambda's signature, held by `.map`'s need on `mm`, so the
    // calls of `g` decide it: `g(mi)` at `int`, `g(m)` at `f64`.
    let src = format!("{TOP}{F}{I}g(positional mm) = mm.map(r -> top(r));\na = (g(mi), g(m));\n");
    prints(
        &src,
        "a",
        "({\"a\" -> #empty, \"b\" -> 5}, {\"a\" -> -inf, \"b\" -> 5.0})",
    );
    // One function more between the calls and the fold.
    let src = format!(
        "{TOP}{F}{I}g(positional mm) = mm.map(r -> top(r));\nk(positional mm) = g(mm);\n\
         a = (k(mi), k(m));\n"
    );
    prints(
        &src,
        "a",
        "({\"a\" -> #empty, \"b\" -> 5}, {\"a\" -> -inf, \"b\" -> 5.0})",
    );
    let src = format!("{F}{I}s(positional mm) = mm.map(r -> r.sum);\na = (s(mi), s(m));\n");
    prints(
        &src,
        "a",
        "({\"a\" -> 0, \"b\" -> 5}, {\"a\" -> -0.0, \"b\" -> 5.0})",
    );
    let src = format!("{F}{I}s(positional mm) = mm.map(r -> r.reduce((*)));\na = (s(mi), s(m));\n");
    prints(
        &src,
        "a",
        "({\"a\" -> 1, \"b\" -> 5}, {\"a\" -> 1.0, \"b\" -> 5.0})",
    );
}

#[test]
fn a_fold_bound_in_a_block_of_a_generic_function_takes_the_identity_of_each_call() {
    let src = format!(
        "{TOP}{F}{I}g(positional ys) = {{ z = top(ys); z }};\na = (g(mi[\"a\"]), g(m[\"a\"]));\n"
    );
    prints(&src, "a", "(#empty, -inf)");
}

#[test]
fn a_map_inside_a_map_at_one_carrier_takes_its_identity_at_each_depth() {
    // The inner `.map` decides the fold at `int` where the outer one has already decided it at
    // `int`: one identity, so both reads take it.
    let src = format!(
        "{TOP}{F}{I}a = mi.map(q -> (top(q), mi.map(r -> top(r))));\nb = m.map(r -> top(r));\n"
    );
    prints(
        &src,
        "a",
        "{\"a\" -> (#empty, {\"a\" -> #empty, \"b\" -> 5}), \"b\" -> (5, {\"a\" -> #empty, \"b\" -> 5})}",
    );
    prints(&src, "b", "{\"a\" -> -inf, \"b\" -> 5.0}");
}

#[test]
fn a_fold_in_a_function_declared_in_a_block_takes_the_identity_of_each_call() {
    // sec:reduction, "Identity as data": `max` at `int`, which has no identity for it, folds an
    // empty level to `#empty`, and at `f64` to `-inf`. A function declared in a block takes a
    // body made at the identities of each of its calls, as a top-level one does (row
    // REDUCE-generic-identity-rest).
    let at = |body: &str| format!("{TOP}{F}{I}{body}");
    let h = "h(positional q) = top(q);";
    prints(
        &at(&format!("a = {{ {h} (h(mi[\"a\"]), h(m[\"a\"])) }};\n")),
        "a",
        "(#empty, -inf)",
    );
    prints(
        &at(&format!("a = {{ {h} (h(mi[\"b\"]), h(m[\"b\"])) }};\n")),
        "a",
        "(5, 5.0)",
    );
    // In a generic function's block, `h(ys)` is decided by `g`'s call.
    let g = format!("g(positional ys) = {{ {h} (h(ys), h(m[\"a\"])) }};\n");
    prints(
        &at(&format!("{g}a = g(mi[\"a\"]);\n")),
        "a",
        "(#empty, -inf)",
    );
    prints(
        &at(&format!(
            "{g}a = (g(mi[\"a\"]), g(m[\"a\"]), g(mi[\"b\"]));\n"
        )),
        "a",
        "((#empty, -inf), (-inf, -inf), (5, -inf))",
    );
    // In a lambda a built-in runs in place, at each entry of `mi`.
    prints(
        &at(&format!(
            "a = mi.map(r -> {{ {h} (top(r), h(m[\"a\"])) }});\n"
        )),
        "a",
        "{\"a\" -> (#empty, -inf), \"b\" -> (5, -inf)}",
    );
    // Through a second function of the block, and through one declared in `h`'s own body.
    prints(
        &at(&format!(
            "a = {{ {h} k(positional z) = h(z); (k(mi[\"a\"]), k(m[\"a\"]), h(m[\"b\"])) }};\n"
        )),
        "a",
        "(#empty, -inf, 5.0)",
    );
    prints(
        &at(
            "a = { h(positional q) = { h2(positional p) = top(p); h2(q) }; \
             (h(mi[\"a\"]), h(m[\"a\"])) };\n",
        ),
        "a",
        "(#empty, -inf)",
    );
    // Named as a value at one carrier, the written body runs, at that carrier's identity.
    prints(
        &at(&format!(
            "a = {{ {h} p = h; (h(m[\"a\"]), p(m[\"b\"])) }};\n"
        )),
        "a",
        "(-inf, 5.0)",
    );
}

#[test]
fn a_function_declared_in_a_block_and_named_as_a_value_at_two_carriers_runs_at_each() {
    // DESIGN.md sec:reduction, "Identity as data": each call folds an empty level to the
    // identity of its own carrier, `#empty` at `int` and `-inf` at `f64`, whether it calls
    // `h` by name, through a name bound to it, or through a parameter `h` is passed to
    // (REDUCE-generic-identity-values).
    for body in [
        // A name bound to `h` stands for it.
        "a = { h(positional q) = top(q); p = h; (h(mi[\"a\"]), p(m[\"a\"])) };\n",
        "a = { h(positional q) = top(q); k(positional z) = h(z); p = k; \
         (k(mi[\"a\"]), p(m[\"a\"])) };\n",
        // Passed to a call that runs it before it returns, at the types the call fixes.
        "ap(positional f, positional x) = f(x);\n\
         a = { h(positional q) = top(q); (ap(h, mi[\"a\"]), ap(h, m[\"a\"])) };\n",
    ] {
        prints(&format!("{TOP}{F}{I}{body}"), "a", "(#empty, -inf)");
    }
}

#[test]
fn a_generic_fold_at_two_carriers_through_a_function_value_runs_at_each() {
    // As above, through a lambda bound to a name, a name bound to `top`, `top` passed as an
    // argument, and where two calls deciding one fold are in force at one use: each use takes
    // the identity of the call that checked it (REDUCE-generic-identity-values).
    for body in [
        "a = { f = x -> top(x); (f(mi[\"a\"]), f(m[\"a\"])) };\n",
        "a = { f = top; (f(mi[\"a\"]), f(m[\"a\"])) };\n",
        "f = top;\na = (f(mi[\"a\"]), f(m[\"a\"]));\n",
        // A name bound to a name bound to `top`.
        "f = top;\ng = f;\na = (g(mi[\"a\"]), g(m[\"a\"]));\n",
        "a = { f = top; g = f; (g(mi[\"a\"]), f(m[\"a\"])) };\n",
        "ap(positional f, positional x) = f(x);\na = (ap(top, mi[\"a\"]), ap(top, m[\"a\"]));\n",
    ] {
        prints(&format!("{TOP}{F}{I}{body}"), "a", "(#empty, -inf)");
    }
    prints(
        &format!("{TOP}{F}{I}a = mi.map(r -> {{ f = x -> top(x); (top(r), f(m[\"a\"])) }});\n"),
        "a",
        "{\"a\" -> (#empty, -inf), \"b\" -> (5, -inf)}",
    );
    // Two identities in force at `top(q)`: the `int` of `q`'s map, which checked it, and the
    // `f64` of `r`'s.
    prints(
        &format!("{TOP}{F}{I}a = mi.map(q -> (top(q), m.map(r -> (top(r), top(q)))));\n"),
        "a",
        "{\"a\" -> (#empty, {\"a\" -> (-inf, #empty), \"b\" -> (5.0, #empty)}), \
         \"b\" -> (5, {\"a\" -> (-inf, 5), \"b\" -> (5.0, 5)})}",
    );
    // Three `.map` calls nested, at `int`, `f64` and `int`, each level reading `top` of its
    // own row and of the row around: three calls deciding one fold in force at the innermost
    // reads, each read taking the one that checked it.
    prints(
        &format!(
            "{TOP}ni = {{ \"a\" -> [5] }}.map(r -> r.where(v -> v > 3));\n\
             nf = {{ \"a\" -> [1.0] }}.map(r -> r.where(v -> v > 3.0));\n\
             a = ni.map(q0 -> (top(q0), 0, nf.map(q1 -> (top(q1), top(q0), \
             ni.map(q2 -> (top(q2), top(q1), 0))))));\n"
        ),
        "a",
        "{\"a\" -> (5, 0, {\"a\" -> (-inf, 5, {\"a\" -> (5, -inf, 0)})})}",
    );
    // `g`'s call decides `int`, and the `.map` inside it `f64`, for one fold.
    prints(
        &format!(
            "{TOP}{F}{I}g(positional ys) = (top(ys), m.map(r -> top(r)));\na = g(mi[\"a\"]);\n"
        ),
        "a",
        "(#empty, {\"a\" -> -inf, \"b\" -> 5.0})",
    );
}

#[test]
fn a_function_a_call_returns_and_runs_at_another_carrier_is_not_compiled_yet() {
    // `h3` returns the lambda it is passed, and `p[1]` runs it at `int` after the call ran it
    // at `f64`: one value at two identities, which needs the identity passed when the program
    // runs. Refused, never run at the wrong identity (row REDUCE-identity-escaping-values; the
    // proof is at the refusal, zedc-elab `Elab::check_instances`). Each other form keeps the function in a value
    // the call returns, and runs it later at the other carrier: in a family, in a tuple in a
    // family, in a tuple a returned lambda gives, returned by a lambda, bound to a name, made
    // in a block of the called function, or with the fold written in the lambda itself.
    for body in [
        "h3(positional f, positional y) = (f(y), f);\n\
         a = { p = h3(x -> top(x), m[\"a\"]); (p[0], p[1](mi[\"a\"])) };\n",
        "h3(positional f, positional y) = (f(y), f);\n\
         a = { p = h3(x -> top(x), mi[\"a\"]); (p[0], p[1](m[\"a\"])) };\n",
        "h3(positional f, positional y) = (f(y), f);\n\
         a = { p = h3(x -> x >< max, m[\"a\"]); (p[0], p[1](mi[\"a\"])) };\n",
        "h3(positional f, positional y) = (f(y), f);\n\
         a = { p = h3(top, m[\"a\"]); (p[0], p[1](mi[\"a\"])) };\n",
        "h4(positional f, positional y) = (f(y), [f]);\n\
         a = { p = h4(x -> top(x), m[\"a\"]); (p[0], p[1][0](mi[\"a\"])) };\n",
        "h5(positional f, positional y) = (f(y), [(1, f)]);\n\
         a = { p = h5(x -> x >< max, m[\"a\"]); (p[0], p[1][0][1](mi[\"a\"])) };\n",
        "h6(positional f, positional y) = (f(y), {\"k\" -> (f, 1)});\n\
         a = { p = h6(x -> top(x), m[\"a\"]); (p[0], p[1][\"k\"][0](mi[\"a\"])) };\n",
        "hz(positional f, positional y) = (f(y), z -> (z, f));\n\
         a = { p = hz(x -> x >< max, m[\"a\"]); (p[0], p[1](0)[1](mi[\"a\"])) };\n",
        "hy(positional f) = z -> f;\n\
         a = { p = hy(x -> x >< max); (p(0)(m[\"a\"]), p(0)(mi[\"a\"])) };\n",
        "q(positional f) = f;\na = { g = q(x -> x >< max); (g(m[\"a\"]), g(mi[\"a\"])) };\n",
        "k(positional xs) = { f = y -> y >< max; (f(xs), f) };\n\
         a = { p = k(m[\"a\"]); (p[0], p[1](mi[\"a\"])) };\n",
        // The call and the later run inside a generic function, whose calls bind the carriers.
        "h3(positional f, positional y) = (f(y), f);\n\
         o(positional ys, positional zs) = { p = h3(x -> top(x), ys); (p[0], p[1](zs)) };\n\
         a = o(m[\"a\"], mi[\"a\"]);\n",
        "h3(positional f, positional y) = (f(y), f);\n\
         o(positional ys) = { p = h3(x -> x >< max, m[\"a\"]); (p[0], p[1](ys)) };\n\
         a = o(mi[\"a\"]);\n",
        // The returned function passed on to a function that runs it.
        "h3(positional f, positional y) = (f(y), f);\nr(positional g, positional zs) = g(zs);\n\
         a = { p = h3(x -> x >< max, m[\"a\"]); (p[0], r(p[1], mi[\"a\"])) };\n",
        // A lambda in the tuple that calls `f` (row FAIL-tuple-lambda-calls-param), at depth 1
        // and 2: the need on `f` goes with the lambda, and the call stays one `f` may run after.
        "ht(positional f, positional y) = (f(y), z -> f(z));\n\
         a = { p = ht(x -> x >< max, m[\"a\"]); (p[0], p[1](mi[\"a\"])) };\n",
        "ht(positional f, positional y) = (f(y), (1, z -> f(z)));\n\
         a = { p = ht(x -> top(x), m[\"a\"]); (p[0], p[1][1](mi[\"a\"])) };\n",
        // The lambda in a family's entry (row FAIL-family-lambda-calls-param).
        "hf(positional f, positional y) = (f(y), {\"k\" -> (z -> f(z))});\n\
         a = { p = hf(x -> top(x), m[\"a\"]); (p[0], p[1][\"k\"](mi[\"a\"])) };\n",
    ] {
        rejected(
            &format!("{TOP}{F}{I}{body}"),
            &["not supported by this version of zedc"],
        );
    }
}

#[test]
fn a_function_a_call_returns_and_runs_at_the_same_carrier_runs_at_its_identity() {
    // The forms above, with the returned function run at the carrier the call ran it at, or a
    // lambda the call makes run at one carrier only: one identity for each fold, so each is
    // compiled and gives the value of DESIGN.md sec:reduction ("Identity as data").
    for body in [
        "h3(positional f, positional y) = (f(y), f);\n\
         a = { p = h3(x -> top(x), m[\"a\"]); (p[0], p[1](m[\"b\"])) };\n",
        "h3(positional f, positional y) = (f(y), f);\n\
         a = { p = h3(x -> x >< max, m[\"a\"]); (p[0], p[1](m[\"b\"])) };\n",
        "h5(positional f, positional y) = (f(y), [(1, f)]);\n\
         a = { p = h5(x -> x >< max, m[\"a\"]); (p[0], p[1][0][1](m[\"b\"])) };\n",
        "hz(positional f, positional y) = (f(y), z -> (z, f));\n\
         a = { p = hz(x -> top(x), m[\"a\"]); (p[0], p[1](0)[1](m[\"b\"])) };\n",
        "ht(positional f, positional y) = (f(y), z -> f(z));\n\
         a = { p = ht(x -> x >< max, m[\"a\"]); (p[0], p[1](m[\"b\"])) };\n",
        "ht(positional f, positional y) = (f(y), (1, z -> f(z)));\n\
         a = { p = ht(x -> top(x), m[\"a\"]); (p[0], p[1][1](m[\"b\"])) };\n",
        "hf(positional f, positional y) = (f(y), {\"k\" -> (z -> f(z))});\n\
         a = { p = hf(x -> top(x), m[\"a\"]); (p[0], p[1][\"k\"](m[\"b\"])) };\n",
    ] {
        prints(&format!("{TOP}{F}{I}{body}"), "a", "(-inf, 5.0)");
    }
    // `g`'s call runs `top` at `f64`; the lambda it returns runs its own fold at `int` only.
    prints(
        &format!(
            "{TOP}{F}{I}g(positional xs) = (top(xs), y -> y >< max);\n\
             a = {{ p = g(m[\"a\"]); (p[0], p[1](mi[\"a\"])) }};\n"
        ),
        "a",
        "(-inf, #empty)",
    );
}

#[test]
fn a_call_whose_result_holds_the_function_at_any_depth_is_one_it_may_run_after() {
    // Each call's result holds `f` where a later read can reach it: in a lambda's result
    // (`hz`), in a family's values (`h5`; a family's type is an arrow from key to value), in
    // an atom's payload (`h8`; reading a payload is not supported yet, so only the check is
    // tested), or its type says only "some tuple" (`hk`, through `k`'s `(..)`), which may hold
    // it. Each call is recorded as one a function passed to it may run after
    // (`Info::escaping_calls`), and elaboration puts no identity of it in force for the
    // lambda passed (row REDUCE-identity-escaping-values).
    for (h, decls, body) in [
        ("hz", "", "(f(y), z -> (z, f))"),
        ("h5", "", "(f(y), [(1, f)])"),
        ("h8", "", "(f(y), #box(f))"),
        ("hk", "k(positional t: (..)) = t;\n", "(f(y), k((1, f)))"),
        // A lambda that calls `f`, in a tuple, a nested tuple and a payload.
        ("ht", "", "(f(y), z -> f(z))"),
        ("hn", "", "(f(y), (1, z -> f(z)))"),
        ("hb", "", "(f(y), #box(z -> f(z)))"),
        // ... and in a family's entry.
        ("hf", "", "(f(y), {\"k\" -> (z -> f(z))})"),
        ("ha", "", "(f(y), [(z -> f(z))])"),
    ] {
        let src = format!(
            "{TOP}{F}{I}{decls}{h}(positional f, positional y) = {body};\n\
             a = {{ p = {h}(x -> top(x), m[\"a\"]); p[0] }};\nb = top(mi[\"a\"]);\n"
        );
        let at = src.find(&format!("{h}(x")).unwrap();
        let info = zed_tests::step_helpers::l01_16_elaboration::checked(&src).info;
        assert!(
            info.escaping_calls.iter().any(|c| c.start == at),
            "{h}: {:?}",
            info.escaping_calls
        );
    }
}

#[test]
fn a_call_whose_result_holds_an_earlier_call_s_result_is_found_by_what_that_one_held() {
    // Each `hw` call decides `top`'s fold (only such calls are listed), and its result holds
    // its third argument in a payload as it is, so the answer for escaping calls reads what
    // was found in that argument's rows and payloads at the earlier call (`Ty::may_hold_needs`
    // keeps it on each row and shape, row FAIL-escaping-calls-nested-ratio). Around `ht`'s result,
    // which holds a lambda with needs, each `hw` call is escaping; around `1` neither is.
    let src = format!(
        "{TOP}{F}{I}ht(positional f, positional y) = (f(y), z -> f(z));\n\
         hw(positional f, positional y, positional x) = (f(y), #a(x));\n\
         a = {{ p = ht(x -> top(x), m[\"a\"]); q = hw(x -> top(x), m[\"a\"], p); \
         s = hw(x -> top(x), m[\"a\"], q); s[0] }};\n\
         b = {{ q = hw(x -> top(x), m[\"a\"], 1); s = hw(x -> top(x), m[\"a\"], q); s[0] }};\n\
         c = top(mi[\"a\"]);\n"
    );
    let info = zed_tests::step_helpers::l01_16_elaboration::checked(&src).info;
    let starts: Vec<usize> = info.escaping_calls.iter().map(|c| c.start).collect();
    let at = |from: usize, call: &str| from + src[from..].find(call).unwrap();
    let (a, b) = (src.find("a = {").unwrap(), src.find("b = {").unwrap());
    let cases = [
        (at(a, "ht(x"), true),
        (at(a, "hw(x"), true),
        (at(at(a, "s = "), "hw(x"), true),
        (at(b, "hw(x"), false),
        (at(at(b, "s = "), "hw(x"), false),
    ];
    for (at, escaping) in cases {
        assert_eq!(starts.contains(&at), escaping, "{}: {starts:?}", &src[at..]);
    }
}

// ---- A lambda that calls a parameter, returned inside a tuple (row
// FAIL-tuple-lambda-calls-param) ----

#[test]
fn a_tuple_holding_a_lambda_that_calls_a_parameter_runs() {
    // DESIGN.md sec:values_morphisms (application): `f(1)` is 2 and `p[1](2)` is `f(2)`, 3.
    // The need "`f` takes what the lambda is passed" goes with the lambda wherever the result
    // holds it, as it does for the lambda returned bare, `h(positional f) = z -> f(z)`.
    prints(
        "h(positional f) = (f(1), z -> f(z));\na = { p = h(x -> x + 1); (p[0], p[1](2)) };\n",
        "a",
        "(2, 3)",
    );
    prints(
        "h(positional f, positional y) = (y, z -> f(z));\na = { p = h(x -> x + 1, 1); p[1](2) };\n",
        "a",
        "3",
    );
    prints(
        "h(positional f) = (f(1), z -> f(z));\nsucc(positional x) = x + 1;\na = h(succ)[1](2);\n",
        "a",
        "3",
    );
    // The lambda one tuple deeper, and two lambdas that each call `f`.
    prints(
        "h(positional f) = (f(1), (0, z -> f(z)));\na = { p = h(x -> x + 1); p[1][1](2) };\n",
        "a",
        "3",
    );
    prints(
        "h(positional f) = (z -> f(z), w -> f(f(w)));\na = { p = h(x -> x + 1); (p[0](1), p[1](1)) };\n",
        "a",
        "(2, 3)",
    );
    // A lambda that does not take what `f` takes stays refused at its own call.
    rejected(
        "h(positional f) = (f(1), z -> f(z));\na = { p = h(x -> x + 1); p[1](\"s\") };\n",
        &["does not take"],
    );
}

// ---- A lambda that calls a parameter, returned in a family's entry (row
// FAIL-family-lambda-calls-param) ----

#[test]
fn a_family_holding_a_lambda_that_calls_a_parameter_runs() {
    // DESIGN.md sec:values_morphisms (application): `p["k"](2)` is `f(2)`, 3, and `f(1)` is 2.
    // The parentheses around each lambda are needed: `{"k" -> z -> f(z)}` and `[z -> f(z)]`
    // do not parse.
    prints(
        "h(positional f) = {\"k\" -> (z -> f(z))};\na = { p = h(x -> x + 1); p[\"k\"](2) };\n",
        "a",
        "3",
    );
    prints(
        "h(positional f) = (f(1), {\"k\" -> (z -> f(z))});\n\
         a = { p = h(x -> x + 1); (p[0], p[1][\"k\"](2)) };\n",
        "a",
        "(2, 3)",
    );
    // The lambda in a tuple in an entry, in a family in an entry, and two lambdas in an array.
    prints(
        "h(positional f) = {\"k\" -> (0, z -> f(z))};\na = { p = h(x -> x + 1); p[\"k\"][1](2) };\n",
        "a",
        "3",
    );
    prints(
        "h(positional f) = {\"k\" -> {\"j\" -> (z -> f(z))}};\n\
         a = { p = h(x -> x + 1); p[\"k\"][\"j\"](2) };\n",
        "a",
        "3",
    );
    prints(
        "h(positional f) = [(z -> f(z)), (w -> f(f(w)))];\na ={ p = h(x -> x + 1); (p[0](1), p[1](1)) };\n",
        "a",
        "(2, 3)",
    );
    // A lambda that does not take what `f` takes stays refused at its own call.
    rejected(
        "h(positional f) = {\"k\" -> (z -> f(z))};\na = { p = h(x -> x + 1); p[\"k\"](\"s\") };\n",
        &["does not take"],
    );
}

#[test]
fn a_family_with_needs_holding_a_lambda_that_calls_a_parameter_runs() {
    // `h`'s family holds `f(1)`'s result, so the need "`f` takes `1`" goes with the family.
    // `k` calls `h` with a lambda that returns `z -> g(z)`, a lambda that calls `k`'s parameter,
    // so the family `k` returns holds a lambda with the need "`g` takes `z`". DESIGN.md
    // sec:values_morphisms (application): `p["k"]` is `z -> g(z)`, and `p["k"](2)` is `g(2)`, 3.
    let h = "h(positional f) = {\"k\" -> f(1)};\n";
    prints(
        &format!(
            "{h}k(positional g) = h(x -> (z -> g(z)));\na = {{ p = k(y -> y + 1); p[\"k\"](2) }};\n"
        ),
        "a",
        "3",
    );
    // The same with the lambda beside a value in a tuple, and with the family in a tuple.
    prints(
        &format!(
            "{h}k(positional g) = (g(0), h(x -> (x, z -> g(z))));\n\
             a = {{ p = k(y -> y + 1); (p[0], p[1][\"k\"][1](2)) }};\n"
        ),
        "a",
        "(1, 3)",
    );
    // The lambda `h` is passed also closes over `x`, the value `f` is applied to: `p["k"]` is
    // `z -> g(z + 1)`, and `p["k"](2)` is `g(3)`, 4.
    prints(
        &format!(
            "{h}k(positional g) = h(x -> (z -> g(z + x)));\n\
             a = {{ p = k(y -> y + 1); p[\"k\"](2) }};\n"
        ),
        "a",
        "4",
    );
    // The same family built by `map` from an unannotated parameter is refused before this
    // walk is reached, at `m.map(f)` and at `m.map(x -> f(x))`: row
    // FAIL-map-generic-parameter-function.
}

// ---- `sum(x)` is `x.sum`, and a receiver that may be a family or a tuple is summed region by
// region (row FAIL-sum-word-family) ----

#[test]
fn sum_called_as_a_function_folds_a_family() {
    // DESIGN.md sec:lexical, the row of `.`: "`x.f(a)` passes `x` as `f`'s first parameter",
    // so `sum(x)` and `x.sum` are one call; the method register's "tot = xs.sum; // = xs >< (+)"
    // makes both the fold on a family, and L1.18 the sum of the components on a tuple.
    prints("t = sum([1, 2]);\n", "t", "3");
    prints("t = [1, 2].sum;\n", "t", "3");
    prints("t = sum((3, 4));\n", "t", "7");
    same("t = sum([]);\nu = [].sum;\n", "t", "u");
    same(
        "t = sum([1.5f64, 2.5f64]);\nu = [1.5f64, 2.5f64].sum;\n",
        "t",
        "u",
    );
    // In a generic function, at a call passing a family and at one passing a tuple.
    let src = "s(positional xs) = sum(xs);\nt = s([1, 2]);\nu = s((3, 4));\n";
    prints(src, "t", "3");
    prints(src, "u", "7");
}

#[test]
fn sum_of_a_family_or_a_tuple_is_taken_region_by_region() {
    // DESIGN.md sec:type_resolution, rule 6: "over each region of the argument type, the
    // codomains of all arrows covering that region intersect; across regions, results
    // union". `sum` takes a family by the fold and a tuple by adding its components, so a
    // value that is `[3, 4]` or `(1, 2)` is summed by whichever it is: 7 and 3.
    for call in [
        "(if b { [3, 4] } else { (1, 2) }).sum",
        "sum(if b { [3, 4] } else { (1, 2) })",
    ] {
        let src = format!("f(positional b) = {call};\nt = f(true);\nu = f(false);\n");
        prints(&src, "t", "7");
        prints(&src, "u", "3");
    }
    // The same with the family a type parameter: the fold at the call that passes a family.
    let src = "s(positional xs, positional b) = (if b { xs } else { (1, 2) }).sum;\n\
               t = s([3, 4], true);\nu = s([3, 4], false);\nv = s((5, 6), true);\n";
    prints(src, "t", "7");
    prints(src, "u", "3");
    prints(src, "v", "11");
    // A family with no entries beside a tuple: `[]` has no carrier to take an identity from
    // and folds to `#empty` (sec:reduction), the tuple adds.
    let src = "f(positional b) = (if b { (3, 4) } else { [] }).sum;\nt = f(true);\nu = f(false);\n";
    prints(src, "t", "7");
    prints(src, "u", "#empty");
    // The call form through a generic function on a family alone, and on a tuple alone.
    let src = "s(positional xs) = sum(xs);\nt = s({ 7 -> 1, 9 -> 2 });\nu = s((1, 2, 3));\n";
    prints(src, "t", "3");
    prints(src, "u", "6");
}

// ---- A fold rejected at a call of a generic function names the form written (row
// FAIL-need-fold-form-message) ----

#[test]
fn a_generic_fold_rejected_at_a_call_names_the_form_written() {
    // DESIGN.md sec:diagnostics, "A short headline, the detail in the notes": the headline
    // "shows the offending piece of the program as code". The program wrote `.reduce((+))`
    // or `.sum`; a headline naming `><` shows code the program does not hold. The concrete
    // fold of a tuple says the form written, and the fold checked at the call of a generic
    // function says the same.
    rejected(
        "f(positional b) = (if b { (3, 4) } else { [1, 2] }).reduce((+));\nt = f(true);\n",
        &["`.reduce` folds the entries of a family"],
    );
    rejected(
        "s(positional xs, positional b) = (if b { xs } else { [1, 2] }).reduce((+));\n\
         t = s((3, 4), true);\n",
        &["`.reduce` folds the entries of a family"],
    );
    rejected(
        "s(positional xs) = xs.reduce(max);\nt = s((3, 4));\n",
        &["`.reduce` folds the entries of a family"],
    );
    // `><` written stays `><`.
    rejected(
        "s(positional xs, positional b) = (if b { xs } else { [1, 2] }) >< (+);\n\
         t = s((3, 4), true);\n",
        &["`><` folds the entries of a family"],
    );
    // `.sum` beside a family with no entries folds that family with what each call passes
    // (row FAIL-sum-empty-family-beside-parameter), so a string passed there is rejected by
    // the fold: sec:reduction, a fold takes a family; the message names `.sum`, as the
    // concrete `(if b { "ab" } else { [] }).sum` does.
    rejected(
        "f(positional b) = (if b { \"ab\" } else { [] }).sum;\nt = f(true);\n",
        &["`.sum` folds the entries of a family"],
    );
    rejected(
        "s(positional xs, positional b) = (if b { xs } else { [] }).sum;\n\
         t = s(\"ab\", true);\n",
        &["`.sum` folds the entries of a family"],
    );
}

// ---- `.sum` of a type parameter beside a family with no entries is taken region by region
// (row FAIL-sum-empty-family-beside-parameter) ----

#[test]
fn sum_of_a_parameter_beside_an_empty_family_is_taken_region_by_region() {
    // DESIGN.md sec:type_resolution, rule 6: "over each region of the argument type, the
    // codomains of all arrows covering that region intersect; across regions, results union".
    // A tuple is summed by adding its components and a family by the fold; `[]` has no carrier
    // and folds to `#empty` (sec:reduction, "Identity as data"). The concrete
    // `(if b { (3, 4) } else { [] }).sum` gives `7` and `#empty`, and so does the generic body
    // at a call that passes the tuple.
    let src = "s(positional xs, positional b) = (if b { xs } else { [] }).sum;\n";
    prints(&format!("{src}t = s((3, 4), true);\n"), "t", "7");
    prints(&format!("{src}t = s((3, 4), false);\n"), "t", "#empty");
    let src = "f(positional b) = (if b { (3, 4) } else { [] }).sum;\nt = f(true);\nu = f(false);\n";
    prints(src, "t", "7");
    prints(src, "u", "#empty");
    // The call form `sum(x)` takes the same path.
    let src = "s(positional xs, positional b) = sum(if b { xs } else { [] });\n";
    prints(&format!("{src}t = s((3, 4), true);\n"), "t", "7");
    prints(&format!("{src}t = s((3, 4), false);\n"), "t", "#empty");
    // At `int` the empty level gives `0`, a number the caller can add to.
    let src = "s(positional xs, positional b) = (if b { xs } else { [] }).sum;\n\
               t = s([3, 4], false) + 1;\n";
    prints(src, "t", "1");
}

#[test]
fn each_call_folds_the_empty_family_at_the_carrier_it_gives() {
    // sec:reduction, "Identity as data": the empty level folds to the identity of `+` at the
    // carrier of the call's entries, `0` at `int` and `-0.0` at `f64`, and to `#empty` where
    // the call gives no carrier, beside a tuple. One program holds the three calls, so the
    // fold has one body per identity, chosen at each call (REDUCE-generic-identity).
    let src = "s(positional xs, positional b) = (if b { xs } else { [] }).sum;\n\
               t = (s((3, 4), false), s([3, 4], false), s([1.5], false));\n\
               u = (s((3, 4), true), s([3, 4], true), s([1.5], true));\n";
    prints(src, "t", "(#empty, 0, -0.0)");
    prints(src, "u", "(7, 7, 1.5)");
    // Through another generic function, whose calls decide the identity.
    let src = "s(positional xs, positional b) = (if b { xs } else { [] }).sum;\n\
               k(positional ys, positional c) = s(ys, c);\n\
               t = (k((3, 4), false), k([3, 4], false), k((3, 4), true));\n";
    prints(src, "t", "(#empty, 0, 7)");
}

#[test]
fn a_tuple_and_an_empty_family_beside_a_parameter_are_summed_as_the_concrete_join_is() {
    // The tuple `(1, 2)` beside `[]` is summed at the definition; `[]` folds at the carrier the
    // call gives `xs`, as in the concrete `(if b { [3, 4] } else { if c { (1, 2) } else { [] }
    // }).sum`, where `[3, 4]` and `[]` are one region, folded at `int`.
    let body = "(if b { xs } else { if c { (1, 2) } else { [] } }).sum";
    let src = format!(
        "s(positional xs, positional b, positional c) = {body};\n\
         t = (s([3, 4], true, true), s([3, 4], false, true), s([3, 4], false, false));\n\
         u = (s((5, 6), true, true), s((5, 6), false, true), s((5, 6), false, false));\n"
    );
    prints(&src, "t", "(7, 3, 0)");
    prints(&src, "u", "(11, 3, #empty)");
    let concrete = "f(positional b, positional c) = \
                    (if b { [3, 4] } else { if c { (1, 2) } else { [] } }).sum;\n\
                    g(positional b, positional c) = \
                    (if b { (5, 6) } else { if c { (1, 2) } else { [] } }).sum;\n\
                    t = (f(true, true), f(false, true), f(false, false));\n\
                    u = (g(true, true), g(false, true), g(false, false));\n";
    prints(concrete, "t", "(7, 3, 0)");
    prints(concrete, "u", "(11, 3, #empty)");
}

#[test]
fn an_empty_level_at_a_call_takes_the_carrier_the_other_parameters_give() {
    // Two parameters beside `[]`: at one call the fold is checked once for each, and `[]`
    // folds at the carrier any of them gives, as in the concrete join, where `(1, 2)` beside
    // `[3, 4]` and `[]` sums the families at `int` and `[]` gives `0`.
    let sum = "s(positional xs, positional ys, positional b, positional c) = \
               (if b { xs } else { if c { ys } else { [] } }).sum;\n";
    let src = format!(
        "{sum}t = (s((1, 2), [3, 4], false, false), s((1, 2), (5, 6), false, false), \
         s([1], [2], false, false), s((1, 2), [3, 4], false, true));\n"
    );
    prints(&src, "t", "(0, #empty, 0, 7)");
    let concrete = "f(positional c) = (if c { [3, 4] } else { [] }).sum;\n\
                    g(positional b, positional c) = \
                    (if b { (1, 2) } else { if c { [3, 4] } else { [] } }).sum;\n\
                    t = (g(false, false), f(false));\n";
    prints(concrete, "t", "(0, 0)");
    // A parameter given `[]` beside one given a family: the empty level takes that family's
    // carrier, as the concrete `(if b { [] } else { [1, 2] }).sum` folds at `int`.
    let src = "s(positional xs, positional ys, positional b) = (if b { xs } else { ys }).sum;\n\
               t = s([], [1, 2], true);\n";
    prints(src, "t", "0");
    prints(
        "f(positional b) = (if b { [] } else { [1, 2] }).sum;\nt = f(true);\n",
        "t",
        "0",
    );
    let src = "s(positional xs, positional ys, positional b) = (if b { xs } else { ys }) >< max;\n\
               t = s([], [1.0], true);\nu = s([], [1], true);\n";
    prints(src, "t", "-inf");
    prints(src, "u", "#empty");
    prints(
        "f(positional b) = (if b { [] } else { [1.0] }) >< max;\nt = f(true);\n",
        "t",
        "-inf",
    );
}

#[test]
fn the_region_split_of_a_parameter_beside_a_tuple_takes_each_calls_identity() {
    // Row FAIL-sum-word-family split `sum(x)` by region; REDUCE-generic-identity gives the
    // fold one body per identity. Together: the family region of each call folds an empty
    // level at that call's carrier, `0` at `int` and `-0.0` at `f64`, and the tuple region
    // is added, in one program.
    let src = "s(positional xs, positional b) = sum(if b { xs } else { (1, 2) });\n\
               ei = [1].where(v -> v > 3);\nef = [1.0].where(v -> v > 3.0);\n\
               t = (s(ei, true), s(ef, true), s(ei, false), s([3, 4], true), s((5, 6), true));\n";
    prints(src, "t", "(0, -0.0, 3, 7, 11)");
    let src = "s(positional xs, positional b) = (if b { xs } else { (1, 2) }).sum;\n\
               ei = [1].where(v -> v > 3);\nef = [1.0].where(v -> v > 3.0);\n\
               t = (s(ei, true), s(ef, true), s(ei, false));\n";
    prints(src, "t", "(0, -0.0, 3)");
}

/// Row FAIL-map-generic-parameter-function: `m.map(f)` with `f` and `m` parameters of no
/// written type applies `f` to each entry of `m` (DESIGN.md sec:values_morphisms), as with a
/// written function; the uses are checked at each call, where `f` and `m` are known.
#[test]
fn map_by_a_function_parameter_runs() {
    prints(
        "h(positional f, positional m) = m.map(f);\na = h(x -> x + 1, {\"k\" -> 1})[\"k\"];\n",
        "a",
        "2",
    );
    prints(
        "h(positional f, positional m) = m.map(f);\n\
         a = { p = h(x -> (z -> z + x), {\"k\" -> 1}); p[\"k\"](2) };\n",
        "a",
        "3",
    );
    prints(
        "h(positional f, positional m) = m.map(f);\n\
         k(positional g) = h(x -> g(x), {\"k\" -> 1});\n\
         a = k(y -> y + 1)[\"k\"];\n",
        "a",
        "2",
    );
}

/// Row FAIL-map-generic-parameter-function: `where`, `foldl`, `foldr`, `flatMap` and `group`
/// take a parameter with no written type as their function, as `map` does, on a receiver
/// that is a parameter too or a family of known type; each call checks the function it passes.
#[test]
fn the_words_that_take_a_function_take_a_function_parameter() {
    let m = "{\"a\" -> 1, \"b\" -> 5}";
    prints(
        &format!("h(positional f, positional m) = m.where(f);\na = h(x -> x > 2, {m})[\"b\"];\n"),
        "a",
        "5",
    );
    prints(
        &format!("w(positional f) = {m}.where(f);\na = w(x -> x > 2)[\"a\"] else 0;\n"),
        "a",
        "0",
    );
    prints(
        &format!("k(positional f) = {m}.map(f);\na = k(x -> x * 10)[\"b\"];\n"),
        "a",
        "50",
    );
    prints(
        "h(positional f, positional m) = m.foldl(0, f);\na = h((a, x) -> a * 10 + x, [1, 2, 3]);\n",
        "a",
        "123",
    );
    prints(
        "h(positional f, positional m) = m.foldr(f, 0);\na = h((x, a) -> a * 10 + x, [1, 2, 3]);\n",
        "a",
        "321",
    );
    // The same value as `[1, 2].flatMap(v -> [v, v * 10])` written out.
    let flat = "{0 -> {0 -> 1, 1 -> 10}, 1 -> {0 -> 2, 1 -> 20}}";
    prints(
        "h(positional f, positional m) = m.flatMap(f);\na = h(v -> [v, v * 10], [1, 2]);\n",
        "a",
        flat,
    );
    prints(
        "h(positional f) = [1, 2].flatMap(f);\na = h(v -> [v, v * 10]);\n",
        "a",
        flat,
    );
    prints("a = [1, 2].flatMap(v -> [v, v * 10]);\n", "a", flat);
    prints(
        "h(positional f, positional m) = m.group(f);\na = h(v -> v mod 2, [1, 2, 3]).count;\n",
        "a",
        "2",
    );
    prints(
        "h(positional f) = [1, 2, 3].group(f);\na = h(v -> v mod 2)[1][2] else 0;\n",
        "a",
        "3",
    );
}

/// Row FAIL-map-generic-parameter-function: the function a call passes to such a parameter is
/// checked as a written one is: `where` needs a `bool` of it, and a fold a function of two
/// parameters.
#[test]
fn a_function_parameter_of_those_words_is_checked_at_each_call() {
    rejected(
        "w(positional f) = {\"a\" -> 1}.where(f);\na = w(x -> x + 2)[\"a\"] else 0;\n",
        &["`where` does not take int, only bool"],
    );
    rejected(
        "h(positional f) = [1, 2, 3].foldl(0, f);\na = h(x -> x);\n",
        &["`foldl` calls its function with 2 arguments, and this function takes 1"],
    );
}

/// Row FAIL-fold-unknown-fn-known-family: `x.foldl(init, f)` folds the entries of `x` by `f`
/// from `init` (DESIGN.md sec:reduction, the `foldl`/`foldr` row); with `x` a family of known
/// type and `f` a parameter whose type is not written, the fold is checked at each call, where
/// `f` is known.
#[test]
fn a_fold_over_a_known_family_by_a_function_parameter_runs() {
    prints(
        "h(positional f) = [1, 2, 3].foldl(0, f);\na = h((a, x) -> a * 10 + x);\n",
        "a",
        "123",
    );
    prints(
        "h(positional f) = [1, 2, 3].foldr(f, 0);\na = h((x, a) -> a * 10 + x);\n",
        "a",
        "321",
    );
    prints(
        "h(positional f) = [1.5, 2.5].foldl(0.0, f);\na = h((a, x) -> a + x);\n",
        "a",
        "4.0",
    );
}

/// Row FAIL-map-lambda-calls-param-entry: `m.map(g)` applies `g` to each entry (DESIGN.md
/// sec:values_morphisms), and a parameter with no written type is inferred, so a lambda that
/// calls a parameter `f` on each entry of a parameter `m` runs at each call.
#[test]
fn map_of_a_parameter_by_a_lambda_calling_a_parameter_runs() {
    prints(
        "h(positional f, positional m) = m.map(x -> f(x));\na = h(x -> x + 1, {\"k\" -> 1})[\"k\"];\n",
        "a",
        "2",
    );
    prints(
        "h(positional f, positional m) = m.map(x -> f(x));\n\
         a = { p = h(x -> (z -> z + x), {\"k\" -> 1}); p[\"k\"](2) };\n",
        "a",
        "3",
    );
    prints(
        "h(positional f, positional m) = m.map(x -> f(x));\n\
         k(positional g) = h(x -> g(x), {\"k\" -> 1});\n\
         a = k(y -> y + 1)[\"k\"];\n",
        "a",
        "2",
    );
    // A family with needs built by `map` from a parameter's results, holding a lambda that
    // calls `k`'s parameter.
    prints(
        "h(positional f, positional m) = m.map(x -> f(x));\n\
         k(positional g) = h(x -> (z -> g(z + x)), {\"k\" -> 1});\n\
         a = { p = k(y -> y + 1); p[\"k\"](2) };\n",
        "a",
        "4",
    );
}

/// Row FAIL-map-lambda-calls-param-entry, the other words that pass each entry of a parameter
/// to a lambda calling a parameter: `where`, `flatMap` and `group` run at each call too, and a
/// function that does not take the entries is rejected at the call, naming the entry's type
/// where it named `_` before.
#[test]
fn the_other_words_by_a_lambda_calling_a_parameter_run() {
    prints(
        "h(positional f, positional m) = m.where(x -> f(x));\n\
         a = h(x -> x > 0, {\"k\" -> 1, \"j\" -> -1})[\"k\"] else 0;\n",
        "a",
        "1",
    );
    prints(
        "h(positional f, positional m) = m.flatMap(x -> f(x));\na = h(x -> [x, x + 1], [1, 2])[1][1];\n",
        "a",
        "3",
    );
    prints(
        "h(positional f, positional m) = m.group(x -> f(x));\n\
         a = h(x -> x > 1, {\"k\" -> 1, \"j\" -> 3})[true][\"j\"] else 0;\n",
        "a",
        "3",
    );
    rejected(
        "h(positional f, positional m) = m.map(x -> f(x));\na = h(x -> x + 1, {\"k\" -> \"s\"});\n",
        &["`f` does not take (\"s\")"],
    );
}

/// Row FAIL-group-key-function: what the function of `group` gives is a key, so data, whether
/// the function is written, a parameter, or the receiver is a parameter too; and a key a
/// display makes from a parameter's call is data at each call. Each passed the checker and
/// stopped the run with "a bug in zedc itself".
#[test]
fn a_key_made_by_a_function_is_data_at_each_call() {
    let key = "Cannot use a value that may hold a function as a key";
    rejected("a = [1, 2, 3].group(v -> (z -> z)).count;\n", &[key]);
    rejected(
        "g(positional f) = [1, 2, 3].group(f);\na = g(v -> (z -> z)).count;\n",
        &[key, "in `g(v -> (z -> z))`"],
    );
    rejected(
        "g(positional f, positional m) = m.group(f);\na = g(v -> (z -> z), [1, 2, 3]).count;\n",
        &[key],
    );
    rejected(
        "k(positional f) = { f(1) -> 2 };\na = k(v -> (z -> z)).count;\n",
        &[key, "in `k(v -> (z -> z))`"],
    );
    prints(
        "k(positional f) = { f(1) -> 2 };\na = k(v -> v + 1)[2];\n",
        "a",
        "2",
    );
    prints(
        "g(positional f) = [1, 2, 3].group(f);\na = g(v -> (v, 0))[(3, 0)][2] else 0;\n",
        "a",
        "3",
    );
}

// ---- The one-level words on a generic receiver (plan row FP-ops-generic-receivers) ----

/// `.count`, `.first`, `.last`, `.any`, `.all`, `.find`, `.scan` and `.chunkBy` on a value
/// whose type is a type parameter are each decided at each call from the type the parameter
/// takes there, as `.sum` is (found by FP-ops-scan).
#[test]
fn the_one_level_words_in_a_generic_function_read_a_family() {
    let src = "f(positional xs) = xs.scan((+));\nt = f([1, 2, 3]) == [1, 3, 6];\n";
    prints(src, "t", "true");
    let src = "g(positional xs) = xs.count;\nt = g({\"a\" -> 1, \"b\" -> 2});\n";
    prints(src, "t", "2");
    let src = "h(positional xs) = xs.any(x -> x > 2);\nt = h([1, 2, 3]);\n";
    prints(src, "t", "true");
    let src = "c(positional xs) = xs.chunkBy(x -> x).count;\nt = c([1, 1, 2]);\n";
    prints(src, "t", "2");
    let src = "l(positional xs) = xs.last;\nt = l([4, 5]);\n";
    prints(src, "t", "5");
}

/// The rest of the words, each at two calls of other types; a parameter joined with a
/// family, which takes the word as it stands while the parameter takes it at each call; a
/// generic function passing its parameter on to another; a scan by `max` at `int` and at
/// `f64`; `foldr` at two calls and `foldl` on a parameter joined with a family; and a call
/// that passes no family, rejected at the call in the word's own message (plan row
/// FP-ops-generic-receivers).
#[test]
fn each_one_level_word_is_decided_at_each_call_of_a_generic_function() {
    let src = "f(positional xs) = xs.first;\nt = (f([4, 5]), f({\"b\" -> 2.5, \"a\" -> 1.5}));\n";
    prints(src, "t", "(4, 1.5)");
    let src = "a(positional xs) = xs.all(x -> x > 0);\nt = (a([1, 2]), a({\"a\" -> -1}));\n";
    prints(src, "t", "(true, false)");
    let src = "f(positional xs) = xs.find(x -> x > 1);\n\
               t = (f([1, 2]) == 1, f({\"a\" -> 1, \"b\" -> 5}) == \"b\", f([0]) == #none);\n";
    prints(src, "t", "(true, true, true)");
    let src = "s(positional xs) = xs.scan(max);\n\
               t = (s([1, 3, 2]) == [1, 3, 3], s([1.5, 0.5]) == [1.5, 1.5]);\n";
    prints(src, "t", "(true, true)");
    let src = "c(positional xs) = xs.chunkBy(x -> x > 1);\n\
               t = c({\"a\" -> 1, \"b\" -> 2, \"c\" -> 3}) == {0 -> {\"a\" -> 1}, 1 -> {\"b\" -> 2, \"c\" -> 3}};\n";
    prints(src, "t", "true");
    let src = "j(positional xs, positional b) = (if b { xs } else { [7, 8, 9] }).count;\n\
               t = (j([1], true), j([1], false), j({\"a\" -> 1, \"b\" -> 2}, true));\n";
    prints(src, "t", "(1, 3, 2)");
    let src = "k(positional xs) = xs.scan((+));\nm(positional ys) = k(ys).last;\n\
               t = (m([1, 2, 3]), m([0.5, 0.25]));\n";
    prints(src, "t", "(6, 0.75)");
    let src = "l(positional xs) = xs.foldr((x, a) -> x * 10 + a, 0);\n\
               t = (l([1, 2]), l({\"a\" -> 5}));\n";
    prints(src, "t", "(30, 50)");
    let src = "j(positional xs, positional b) = \
               (if b { xs } else { [7, 8] }).foldl(0, (a, x) -> a * 10 + x);\n\
               t = (j([1, 2], true), j([1], false), j({\"a\" -> 5}, true));\n";
    prints(src, "t", "(12, 78, 5)");
    rejected(
        "g(positional xs) = xs.count;\nt = g(3);\n",
        &[
            "`count` reads the entries of a family, and this value is 3",
            "[g(3)]",
        ],
    );
    rejected(
        "h(positional xs) = xs.any(x -> x > 2);\nt = h([\"a\"]);\n",
        &["the function given to `any` does not take", "[h([\"a\"])]"],
    );
}
