//! The remap rules of step L8.2 one at a time, in forms this zedc compiles (DESIGN.md
//! sec:remap_law, sec:grouping): truncation, the trailing key binder, folds, the witness
//! catalog and the collision menu, the source's shape, and the pattern's own errors. The
//! spec's examples that need forms of other steps (level names, refinements, declared types)
//! are in `moves`, `collisions` and `names`; where such an example's rule can be written
//! without those forms, its variant is here.

use crate::source::{rejected, same};

const M: &str = "m = { \"a\" -> { 1 -> 10, 2 -> 20 }, \"b\" -> { 1 -> 30 } };\n";

/// `sales` of sec:level_names without its declared type, which needs the level names of
/// step L7.1b: the values and the levels are the same.
const SALES: &str = "sales = { \"east\" -> [{ \"B7\" -> 5 }], \"west\" -> [{ \"A12\" -> 3, \"B7\" -> 1 }, { \"A12\" -> 2 }] };\n";

fn with_m(src: &str) -> String {
    format!("{M}{src}")
}

fn with_sales(src: &str) -> String {
    format!("{SALES}{src}")
}

// ---- Truncation ----

#[test]
fn truncation_drops_the_values() {
    let src = with_m(
        "x = m as (k1 -> k2 -> v) into (k1 -> k2 -> _);\nwant = { \"a\" -> {1, 2}, \"b\" -> {1} };\n",
    );
    same(&src, "x", "want");
}

#[test]
fn truncation_to_the_outer_level_drops_a_level() {
    let src = with_m("x = m as (k1 -> k2 -> v) into (k1 -> _);\nwant = {\"a\", \"b\"};\n");
    same(&src, "x", "want");
}

#[test]
fn a_trailing_key_binder_is_truncation_sugar() {
    // sec:remap_law: "a trailing key binder `… -> bk` is sugar for `… -> bk -> _`".
    let src = with_m(
        "x = m as (k1 -> k2 -> v) into (k2 -> k1);\ny = m as (k1 -> k2 -> v) into (k2 -> k1 -> _);\n\
         want = { 1 -> {\"a\", \"b\"}, 2 -> {\"a\"} };\n",
    );
    same(&src, "x", "want");
    same(&src, "y", "want");
}

#[test]
fn the_worked_collision_repairs_run() {
    // sec:remap_law, the three repairs of the worked collision, on `sales` without its names.
    let src = with_sales(
        "a = sales as (region -> day -> sku -> r) into (region -> day -> sku -> _);\n\
         wantA = { \"east\" -> [{\"B7\"}], \"west\" -> [{\"A12\", \"B7\"}, {\"A12\"}] };\n\
         b = sales as (region -> day -> sku -> r) into (region -> day -> sku -> r);\n\
         c = sales as (region -> day -> sku -> r) into (region -> day -> sku >< (+) -> r);\n\
         wantC = { \"east\" -> [5], \"west\" -> [4, 2] };\n",
    );
    same(&src, "a", "wantA");
    same(&src, "b", "sales");
    same(&src, "c", "wantC");
}

// ---- Folds ----

#[test]
fn a_fold_at_the_inner_level() {
    let src = with_m(
        "x = m as (k1 -> k2 -> v) into (k1 -> k2 >< (+) -> v);\nwant = { \"a\" -> 30, \"b\" -> 30 };\n",
    );
    same(&src, "x", "want");
}

#[test]
fn a_fold_written_first_folds_its_level() {
    // The folded level goes beneath the kept ones, wherever it is written.
    let src = with_m(
        "x = m as (k1 -> k2 -> v) into (k1 >< (+) -> k2 -> v);\n\
         y = m as (k1 -> k2 -> v) into (k2 -> k1 >< (+) -> v);\nwant = { 1 -> 40, 2 -> 20 };\n",
    );
    same(&src, "x", "want");
    same(&src, "y", "want");
}

#[test]
fn every_level_folded_gives_the_total() {
    let src = with_m("x = m as (k1 -> k2 -> v) into (k1 >< (+) -> k2 >< (+) -> v);\n");
    crate::source::prints(&src, "x", "60");
}

#[test]
fn a_fold_by_multiplication_and_a_transformed_leaf() {
    let src = with_m(
        "x = m as (k1 -> k2 -> v) into (k1 -> k2 >< (*) -> v + 1);\nwant = { \"a\" -> 231, \"b\" -> 31 };\n",
    );
    same(&src, "x", "want");
}

// ---- The witness catalog ----

#[test]
fn widening_by_the_value_and_by_a_function_of_the_key() {
    // sec:remap_law: `as (k -> v) into ((k, f(k)) -> v)`, `f` without a declared result type.
    let src = "f(positional k: int) = k * k;\nxs = [10, 20, 30];\n\
               x = xs as (k -> v) into ((k, f(k)) -> v);\n\
               want = { (0, 0) -> 10, (1, 1) -> 20, (2, 4) -> 30 };\n\
               y = xs as (k -> v) into (v -> k -> v);\n\
               wantY = { 10 -> { 0 -> 10 }, 20 -> { 1 -> 20 }, 30 -> { 2 -> 30 } };\n";
    same(src, "x", "want");
    same(src, "y", "wantY");
}

#[test]
fn modulo_on_keys_within_the_modulus() {
    // "`k mod p` where the domain is at most `p` contiguous integers": the display's keys are
    // the integers 5, 6 and 9, within five.
    let src = "m = { 5 -> 50, 6 -> 60, 9 -> 90 };\nx = m as (k -> v) into (k mod 5 -> v);\n\
               want = { 0 -> 50, 1 -> 60, 4 -> 90 };\n";
    same(src, "x", "want");
}

#[test]
fn modulo_one_wider_is_rejected() {
    let src = "m = { 5 -> 50, 10 -> 100 };\nx = m as (k -> v) into (k mod 5 -> v);\n";
    rejected(
        src,
        &[
            "Cannot show that `k mod 5` keeps the keys of `k` apart: `into (k mod 5 -> v)`. Try `into (k mod 5 -> k -> v)` instead.",
            "`k mod p` on at most `p` contiguous integers",
            "write the residue:           into (k mod 5 -> k -> v)",
            "or supply a witness:",
            "#collision",
        ],
    );
}

#[test]
fn affine_packing_and_one_stride_short() {
    // "`(k1, k2) ↦ k1·s + k2` on `k2 : int[0..<s]`": the second components are 0 and 2.
    let src = "m = { (0, 2) -> 2, (1, 0) -> 10 };\nx = m as (t -> v) into (t[0] * 3 + t[1] -> v);\n\
               want = { 2 -> 2, 3 -> 10 };\n";
    same(src, "x", "want");
    let src =
        "m = { (0, 2) -> 2, (1, 0) -> 10 };\nx = m as (t -> v) into (t[0] * 2 + t[1] -> v);\n";
    rejected(src, &["`t[0] * 2 + t[1]`", "affine packing"]);
}

#[test]
fn div_and_mod_together_recover_the_key() {
    let src = "m = { -3 -> 1, -1 -> 2, 2 -> 3 };\nx = m as (k -> v) into ((k div 3, k mod 3) -> v);\n\
               want = { (-1, 0) -> 1, (-1, 2) -> 2, (0, 2) -> 3 };\n";
    same(src, "x", "want");
    let src = "xs = [10, 20, 30];\nx = xs as (i -> v) into (i div 2 -> v);\n";
    rejected(src, &["sends 2 keys to each value", "`(i div 2, i mod 2)`"]);
}

#[test]
fn a_float_key_is_read_only_whole() {
    // Float arithmetic rounds, so `k + 1.0` is no affine map.
    let src = "m = { 0.5 -> 1, 1.5 -> 2 };\nx = m as (k -> v) into (k + 1.0 -> v);\n";
    rejected(
        src,
        &["Cannot show that `k + 1.0` keeps the keys of `k` apart"],
    );
    let src = "m = { 0.5 -> 1, 1.5 -> 2 };\nx = m as (k -> v) into ((k, 1) -> v);\n\
               want = { (0.5, 1) -> 1, (1.5, 1) -> 2 };\n";
    same(src, "x", "want");
}

// ---- The collision menu ----

#[test]
fn the_worked_collision_menu() {
    // sec:remap_law, "The illegal move", line by line, on `sales` without its names.
    let src = with_sales("x = sales as (region -> day -> sku -> r) into (region -> day -> r);\n");
    rejected(
        &src,
        &[
            "Cannot map many values to one key: `into (region -> day -> r)`. Try `into (region -> day -> sku -> _)` instead.",
            "the `(region, day, sku)` keypaths collapse onto `(region, day)`, but their values survive.",
            "drop the values too:         into (region -> day -> sku -> _)",
            "keeps each sku and drops its value",
            "or keep the inner key:       into (region -> day -> sku -> r)",
            "keeps each value under its sku",
            "or say how the values merge: into (region -> day -> sku >< op -> r)",
            "merges each day's values with op, which must be associative",
        ],
    );
    let es = zed_tests::step_helpers::l01_16_elaboration::errors(&src).join("\n");
    assert!(!es.contains("@injective"), "{es}");
    assert!(!es.contains("#collision"), "{es}");
}

#[test]
fn the_collision_is_found_for_one_entry_per_group_too() {
    let src = "m = { \"a\" -> { 1 -> 10 }, \"b\" -> { 2 -> 20 } };\nx = m as (k1 -> k2 -> v) into (k1 -> v);\n";
    rejected(
        src,
        &[
            "Cannot map many values to one key: `into (k1 -> v)`. Try `into (k1 -> k2 -> _)` instead.",
        ],
    );
}

// ---- The source and the pattern ----

#[test]
fn the_source_must_be_a_family_of_the_pattern_s_depth() {
    rejected(
        "n = 3;\nx = n as (k -> v) into (v -> k);\n",
        &["a remap rearranges the keys of a family, and its source `n` is"],
    );
    rejected(
        "xs = [1, 2];\nx = xs as (a -> b -> v) into (b -> a -> v);\n",
        &["this remap's `as` pattern names 2 key levels, and its source `xs`"],
    );
}

#[test]
fn fewer_binders_than_levels_waits_for_a_later_step() {
    rejected(
        &with_m("x = m as (k -> v) into (k -> v);\n"),
        &["a remap whose `as` pattern names 1 key levels of a source with more"],
    );
}

#[test]
fn the_pattern_s_own_errors() {
    rejected(
        &with_m("x = m as (k1 -> k2 -> v) into (_ -> k1 -> v);\n"),
        &["`_` stands only at the leaf of an `into` pattern"],
    );
    rejected(
        &with_m("x = m as (k1 -> k2 -> v) into (k1 -> k2 -> v >< (+));\n"),
        &["the last level of an `into` pattern is its leaf"],
    );
    rejected(
        &with_m("x = m as (k1 -> k2 -> v) into (k1 >< (+) -> k2 -> _);\n"),
        &["there are none for `><` to fold"],
    );
    rejected(
        &with_m("x = m as (k1 -> k2 -> v) into (v);\n"),
        &["an `into` pattern keeps at least one key level before its leaf"],
    );
}
