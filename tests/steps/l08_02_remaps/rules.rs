//! The remap rules of step L8.2 one at a time, in forms this zedc compiles (DESIGN.md
//! sec:remap_law, sec:grouping): truncation, the trailing key binder, folds, the witness
//! catalog and the collision menu, the source's shape, and the pattern's own errors. The
//! spec's examples that need forms of other steps (level names, refinements, declared types,
//! sort keys) wait in /home/luke/Work/wt/failing-tests under the row that builds the form;
//! where such an example's rule can be written without those forms, its variant is here.

use crate::source::{prints, rejected, same, with_sales};

const M: &str = "m = { \"a\" -> { 1 -> 10, 2 -> 20 }, \"b\" -> { 1 -> 30 } };\n";

fn with_m(src: &str) -> String {
    format!("{M}{src}")
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

// A fold may stand at any level (sec:reduction, the rows "any level" of its table); in a remap
// it stands at a level of the output pattern, and the folded level goes beneath the kept ones.
// On `sales`: east has day 0 {B7: 5}; west has day 0 {A12: 3, B7: 1} and day 1 {A12: 2}.

#[test]
fn a_fold_at_the_middle_level_of_three() {
    // Folding `day` sums each sku over the days of its region: west A12 is 3 + 2.
    let src = with_sales(
        "x = sales as (region -> day -> sku -> r) into (region -> day >< (+) -> sku -> r);\n\
         want = { \"east\" -> { \"B7\" -> 5 }, \"west\" -> { \"A12\" -> 5, \"B7\" -> 1 } };\n",
    );
    same(&src, "x", "want");
}

#[test]
fn a_fold_at_the_outer_level_of_three() {
    // Folding `region` sums each (day, sku) over the regions: day 0 B7 is 5 + 1.
    let src = with_sales(
        "x = sales as (region -> day -> sku -> r) into (region >< (+) -> day -> sku -> r);\n\
         want = { 0 -> { \"A12\" -> 3, \"B7\" -> 6 }, 1 -> { \"A12\" -> 2 } };\n",
    );
    same(&src, "x", "want");
}

#[test]
fn folds_at_two_levels_of_three() {
    // The two inner levels: east 5, west 3 + 1 + 2. The two outer ones: A12 3 + 2, B7 5 + 1.
    let src = with_sales(
        "x = sales as (region -> day -> sku -> r) into (region -> day >< (+) -> sku >< (+) -> r);\n\
         wantX = { \"east\" -> 5, \"west\" -> 6 };\n\
         y = sales as (region -> day -> sku -> r) into (region >< (+) -> day >< (+) -> sku -> r);\n\
         wantY = { \"A12\" -> 5, \"B7\" -> 6 };\n",
    );
    same(&src, "x", "wantX");
    same(&src, "y", "wantY");
}

#[test]
fn every_level_of_three_folded_gives_the_total() {
    // 5 + 3 + 1 + 2.
    let src = with_sales(
        "x = sales as (region -> day -> sku -> r) into (region >< (+) -> day >< (+) -> sku >< (+) -> r);\n",
    );
    prints(&src, "x", "11");
}

#[test]
fn folds_by_and_and_by_or() {
    // `(&&)` and `(||)` are associative and commutative (sec:reduction), so they fold a level.
    let src = "m = { \"a\" -> { 1 -> true, 2 -> false }, \"b\" -> { 1 -> true } };\n\
               x = m as (k1 -> k2 -> v) into (k1 -> k2 >< (&&) -> v);\n\
               wantX = { \"a\" -> false, \"b\" -> true };\n\
               y = m as (k1 -> k2 -> v) into (k1 -> k2 >< (||) -> v);\n\
               wantY = { \"a\" -> true, \"b\" -> true };\n";
    same(src, "x", "wantX");
    same(src, "y", "wantY");
}

#[test]
fn a_fold_of_a_level_between_two_kept_ones() {
    // The folded level `b` goes away and `c` moves up under `a`.
    let src = "m = { \"a\" -> { \"x\" -> [1, 2], \"y\" -> [10] } };\n\
               x = m as (a -> b -> c -> v) into (a -> b >< (+) -> c -> v);\n\
               want = { \"a\" -> { 0 -> 11, 1 -> 2 } };\n";
    same(src, "x", "want");
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

// ---- An `as` pattern of fewer key levels than its source (plan row REMAP-fewer-binders) ----

#[test]
fn fewer_binders_than_levels_bind_the_whole_row() {
    // `m as (k -> v) into (k -> v)` on a family of two levels binds `v` to the row `m[k]`, so
    // it gives `m` back; a key that tuples its binder moves each row whole.
    let src = with_m(
        "x = m as (k -> r) into (k -> r);\n\
         y = m as (k -> r) into ((k, 0) -> r);\n\
         z = m as (k -> r) into (k -> r[1]);\n",
    );
    prints(
        &src,
        "x",
        r#"{"a" -> {1 -> 10, 2 -> 20}, "b" -> {1 -> 30}}"#,
    );
    prints(
        &src,
        "y",
        r#"{("a", 0) -> {1 -> 10, 2 -> 20}, ("b", 0) -> {1 -> 30}}"#,
    );
    prints(&src, "z", r#"{"a" -> 10, "b" -> 30}"#);
}

#[test]
fn fewer_binders_keep_rows_apart_in_a_truncation_and_in_a_transpose() {
    // A truncation keys each row by its outer key alone: the two leaves of row "a" do not
    // meet. Two binders of a family of three levels transpose the outer two and carry each
    // innermost row whole.
    let src = with_m(
        "s = m as (k -> r) into (k -> _);\n\
         n = { 1 -> { 2 -> { 3 -> 4, 5 -> 6 } }, 7 -> { 2 -> { 8 -> 9 } } };\n\
         t = n as (a -> b -> r) into (b -> a -> r);\n",
    );
    prints(&src, "s", r#"{"a", "b"}"#);
    prints(&src, "t", "{2 -> {1 -> {3 -> 4, 5 -> 6}, 7 -> {8 -> 9}}}");
}

#[test]
fn a_row_bound_whole_may_be_empty() {
    // An empty row is a keypath that ends early; bound whole, it is the value `{}`.
    let src = "e = { \"a\" -> [1, 2], \"b\" -> [3].where(v -> v > 5) };\n\
               x = e as (k -> r) into (k -> r);\n";
    prints(src, "x", r#"{"a" -> {0 -> 1, 1 -> 2}, "b" -> {}}"#);
}

#[test]
fn as_many_binders_as_levels_bind_no_row() {
    // Negative control: a pattern of the source's depth walks to the leaves as before.
    let src = with_m("x = m as (k -> j -> v) into (k -> j -> v + 1);\n");
    prints(
        &src,
        "x",
        r#"{"a" -> {1 -> 11, 2 -> 21}, "b" -> {1 -> 31}}"#,
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

// ---- group and rekey (sec:grouping, step L4.1) ----

#[test]
fn group_declares_the_deeper_level() {
    // sec:grouping: `byLower = words into (w.lower -> i -> w);` "the same program: the word
    // `group` declares the same deeper type, Lower ->? (i -> w)".
    let src = "words = [\"The\", \"cat\", \"the\"];\n\
               a = words as (i -> w) into (w.lower -> i -> w);\n\
               b = words.group(w -> w.lower);\n\
               want = { \"cat\" -> { 1 -> \"cat\" }, \"the\" -> { 0 -> \"The\", 2 -> \"the\" } };\n";
    same(src, "a", "want");
    same(src, "b", "want");
}

#[test]
fn group_on_a_map_by_an_integer_class() {
    let src = "m = { \"a\" -> 1, \"b\" -> 4, \"c\" -> 7, \"d\" -> 2 };\nx = m.group(v -> v mod 3);\n\
               want = { 1 -> { \"a\" -> 1, \"b\" -> 4, \"c\" -> 7 }, 2 -> { \"d\" -> 2 } };\n\
               e = m.where(v -> v > 9).group(v -> v);\n";
    same(src, "x", "want");
    crate::source::prints(src, "e", "{}");
}

#[test]
fn group_by_a_constant_gives_one_class() {
    let src = "xs = [5, 6];\nx = xs.group(v -> 0);\nwant = { 0 -> { 0 -> 5, 1 -> 6 } };\n";
    same(src, "x", "want");
}

#[test]
fn group_then_fold_each_group() {
    // A reduce-by-key is a `group` and a fold of each group (sec:kernel, law 4: "`fold(op) ∘
    // group(f) =` reduce-by-key"): the pattern with the fold at the residue level and `group`
    // then `map` give one value.
    let src = "xs = [1, 2, 3, 4];\n\
               a = xs as (i -> v) into (v mod 2 -> i >< (+) -> v);\n\
               b = xs.group(v -> v mod 2).map(g -> g >< (+));\n\
               want = { 0 -> 6, 1 -> 4 };\n\
               hi = xs.group(v -> v mod 2).map(g -> g >< max);\nwantHi = { 0 -> 4, 1 -> 3 };\n\
               lo = xs.group(v -> v mod 2).map(g -> g >< min);\nwantLo = { 0 -> 2, 1 -> 1 };\n";
    same(src, "a", "want");
    same(src, "b", "want");
    same(src, "hi", "wantHi");
    same(src, "lo", "wantLo");
}

#[test]
fn word_count_folds_a_constant_leaf() {
    // sec:tour_collections, the word count `as (i -> w) into (w.lower -> i -> 1) >< (+)`, with the
    // fold written at the residue level of the pattern (the trailing `>< (+)` on the nested
    // result waits for row REDUCE-family-entries; failing-tests/REDUCE-family-entries.rs).
    let src = "words = [\"a\", \"b\", \"a\"];\n\
               x = words as (i -> w) into (w -> i >< (+) -> 1);\n\
               want = { \"a\" -> 2, \"b\" -> 1 };\n";
    same(src, "x", "want");
}

#[test]
fn widen_by_a_key_function_of_the_value_as_an_outer_level() {
    // sec:remap_law, widen: a level computed from the value, put above the keys it groups.
    let src = with_m(
        "x = m as (k1 -> k2 -> v) into (v mod 20 -> k1 -> k2 -> v);\n\
         want = { 0 -> { \"a\" -> { 2 -> 20 } }, 10 -> { \"a\" -> { 1 -> 10 }, \"b\" -> { 1 -> 30 } } };\n",
    );
    same(&src, "x", "want");
}

#[test]
fn widen_a_list_by_the_parity_of_its_keys() {
    // The bounds table's row `m as (k -> v) into (w(k) -> k -> v)`, `w` the parity.
    let src = "xs = [10, 20, 30, 40, 50];\nx = xs as (i -> v) into (i mod 2 -> i -> v);\n\
               want = { 0 -> { 0 -> 10, 2 -> 30, 4 -> 50 }, 1 -> { 1 -> 20, 3 -> 40 } };\n";
    same(src, "x", "want");
}

#[test]
fn rekey_without_a_witness_is_rejected_with_its_menu() {
    // sec:grouping: `m.rekey(f)` claims flatness: "compile error if no catalog witness
    // applies ("this key derivation could collide — use `group`; prove `f` injective (an
    // `@injective` claim counts only at proof grade); or write the check: `group(f)`, then a
    // fold that keeps each key's one value and gives `#collision` where there are more")".
    let src = "words = [\"The\", \"cat\", \"the\"];\nx = words.rekey(w -> w.lower);\n";
    rejected(
        src,
        &[
            "Cannot show that `w -> w.lower` keeps the entries of `words` apart: `words.rekey(w -> w.lower)`. Try `words.group(w -> w.lower)` instead.",
            "use group:                   words.group(w -> w.lower)",
            "@injective",
            "#collision",
        ],
    );
}

#[test]
fn group_s_own_errors() {
    rejected(
        "n = 3;\nx = n.group(v -> v);\n",
        &["`group` works on the entries of a family, and `n` is"],
    );
    rejected(
        "xs = [1];\nx = xs.group(5);\n",
        &["`group` takes a function, and this value is"],
    );
    rejected(
        "xs = [1];\nx = xs.group(v -> v, v -> v);\n",
        &["`group` takes one function, passed by position"],
    );
}

// ---- group of a family whose entries are families (plan row GROUP-nested) ----
//
// `f` takes each entry `m[k]` whole and the group keeps it whole: the `reindex` takes `m` with
// each entry held in a tuple of one (`Info::boxed_groups`, `Elab::boxed_at`), so it stops above
// the leaves. Until GROUP-nested the checker refused these as a later step.

#[test]
fn group_a_family_of_families_by_a_fold_of_each() {
    let src = "m = { \"a\" -> { 1 -> 10 }, \"b\" -> { 1 -> 30, 2 -> 5 } };\n\
               x = m.group(r -> r >< (+));\n\
               want = { 10 -> { \"a\" -> { 1 -> 10 } }, 35 -> { \"b\" -> { 1 -> 30, 2 -> 5 } } };\n";
    same(src, "x", "want");
}

#[test]
fn group_a_list_of_lists_keeps_each_entry_whole() {
    // One group per class, the entries that share a class side by side, and the one-entry
    // list `[1]` kept whole: with no boxing the walk reaches its leaf `1` instead.
    same(
        "xs = [[1]];\nx = xs.group(v -> 0);\nwant = { 0 -> { 0 -> [1] } };\n",
        "x",
        "want",
    );
    same(
        "xs = [[1, 2], [3], [4, 5]];\nx = xs.group(r -> r.count);\n\
         want = { 1 -> { 1 -> [3] }, 2 -> { 0 -> [1, 2], 2 -> [4, 5] } };\n",
        "x",
        "want",
    );
}

#[test]
fn group_keeps_an_empty_inner_family() {
    // An empty entry has no leaf, so a walk to the leaves loses it; boxed, it is an entry.
    same(
        "xs = [[1, 2], [], [3]];\nx = xs.group(r -> r.count);\n\
         want = { 0 -> { 1 -> [] }, 1 -> { 2 -> [3] }, 2 -> { 0 -> [1, 2] } };\n",
        "x",
        "want",
    );
}

// ---- flatMap (sec:grouping, "Multiple emissions are typed, not repaired"; step L4.1) ----

#[test]
fn flat_map_adjoins_the_emitted_level() {
    // sec:grouping: "`flatMap` on `K -> V0` with body `V0 -> Seq(V)` yields `K -> rank -> V`".
    let src = "xs = [1, 2];\nx = xs.flatMap(v -> [v, v * 10]);\nwant = [[1, 10], [2, 20]];\n\
               m = { \"a\" -> 3 };\ny = m.flatMap(v -> [v]);\nwantY = { \"a\" -> [3] };\n";
    same(src, "x", "want");
    same(src, "y", "wantY");
}

#[test]
fn flat_map_keeps_an_empty_emission_as_an_empty_level() {
    // The bound table's `flatMap` row: "inner level adjoined per entry, exact (`L = U`) with
    // cardinality the emission count — possibly `0`: an *empty* inner level, never a missing
    // key".
    let src = "xs = [0, 2];\nx = xs.flatMap(v -> if v > 1 { [v, 1] } else { [] });\n";
    crate::source::prints(src, "x", "{0 -> {}, 1 -> {0 -> 2, 1 -> 1}}");
}

#[test]
fn flat_map_s_own_errors() {
    rejected(
        "xs = [1];\nx = xs.flatMap(v -> v + 1);\n",
        &[
            "`flatMap` adjoins the list its function gives for each entry as a rank level, and this function gives",
        ],
    );
    rejected(
        "xs = [1];\nx = xs.flatMap(v -> [v], v -> [v]);\n",
        &["`flatMap` takes one function, passed by position"],
    );
    // A family with keys of its own is no list: sec:grouping gives `flatMap` a body
    // `V0 -> Seq(V)` and the result `K -> rank -> V`; `map` keeps such keys.
    rejected(
        "xs = [1, 2];\nx = xs.flatMap(v -> xs.where(w -> w > v));\n",
        &["`flatMap` adjoins the list its function gives for each entry as a rank level"],
    );
    // A range from `2` has the keys 2, 3, 4, one interval but no ranks, so it is no list
    // either, though a read past it misses with `#outOfBounds` as a list's does
    // (RANGE-read-out-of-bounds); a range from `0` is one.
    rejected(
        "xs = [1, 2];\nx = xs.flatMap(v -> 2 ..< 5);\n",
        &["`flatMap` adjoins the list its function gives for each entry as a rank level"],
    );
    same(
        "xs = [1, 2];\nx = xs.flatMap(v -> 0 ..< 2);\nwant = [[0, 1], [0, 1]];\n",
        "x",
        "want",
    );
    // The message names the word written, not `map`, which checks it (MSG-flatmap-labeled-map).
    rejected(
        "n = 3;\nx = n.flatMap(v -> [v]);\n",
        &["`flatMap` works on each entry of a family"],
    );
}

// ---- Result types guarantee no key (the bound table's "else empty") ----

#[test]
fn a_read_of_a_remap_or_group_result_may_miss() {
    // A remap or `group` result holds only the keys its entries reach, so each level's read
    // has `#notFound` in its type: a transpose of a ragged family misses `x[1]["b"]`, and a
    // class `group` never formed misses.
    use zed_tests::step_helpers::l01_16_elaboration::value;
    use zed_tests::step_helpers::l01_26_type_resolution::sig;
    let ragged = "m = { \"a\" -> { 1 -> 10 }, \"b\" -> { 2 -> 20 } };\n";
    let words = "xs = [\"a\", \"B\"];\nx = xs.group(w -> w.lower);\n";
    for (src, read, ty, val) in [
        (
            format!("{ragged}x = m as (i -> j -> v) into (j -> i -> v);\n"),
            "x[1][\"b\"]",
            "(u: int) -> 10 | 20 | #notFound",
            "#notFound",
        ),
        (
            format!("{ragged}x = m as (i -> j -> v) into (j -> i -> _);\n"),
            "x[1]",
            // The inner family is partial, so it prints `->?` (plain `K -> V` is exact, DESIGN.md
            // sec:type_language; FAIL-main-red-exact-domain), and `"a" | "b"`, now written twice,
            // is named.
            "type Part1 = \"a\" | \"b\";\n(u: int) -> (Part1 ->? Part1) | #notFound",
            "{\"a\"}",
        ),
        (
            words.to_string(),
            "x[\"a\"][1]",
            "(u: int) -> \"B\" | \"a\" | #notFound",
            "#notFound",
        ),
        (
            words.to_string(),
            "x[\"zz\"]",
            "(u: int) -> ((0 | 1) ->? \"B\" | \"a\") | #notFound",
            "#notFound",
        ),
    ] {
        let text = format!("{src}f(u: int) = {read};\ny = f(u: 0);\n");
        assert_eq!(sig(&text, "f"), ty, "{text}");
        assert_eq!(value(&text, "y"), val, "{text}");
    }
}

// ---- The source is a `map` lambda's parameter ----
//
// Inside `m.map(g -> ...)` the parameter `g` stands for each inner family of `m` in turn, so a
// remap or a `group` of `g` gives what the same remap or group gives on each inner family
// written out by hand.

const NESTED: &str = "m = { \"a\" -> { 1 -> 1, 2 -> 2 }, \"b\" -> { 1 -> 3 } };\n";

#[test]
fn a_remap_of_a_map_lambdas_parameter() {
    let src = format!(
        "{NESTED}x = m.map(g -> g as (k -> v) into (k + 1 -> v));\n\
         want = {{ \"a\" -> {{ 2 -> 1, 3 -> 2 }}, \"b\" -> {{ 2 -> 3 }} }};\n"
    );
    same(&src, "x", "want");
}

#[test]
fn a_group_of_a_map_lambdas_parameter() {
    let src = format!(
        "{NESTED}x = m.map(g -> g.group(v -> v mod 2));\n\
         want = {{ \"a\" -> {{ 0 -> {{ 2 -> 2 }}, 1 -> {{ 1 -> 1 }} }}, \"b\" -> {{ 1 -> {{ 1 -> 3 }} }} }};\n"
    );
    same(&src, "x", "want");
}

#[test]
fn a_fold_of_every_level_of_a_map_lambdas_parameter() {
    let src = format!(
        "{NESTED}x = m.map(g -> g as (k -> v) into (k >< (+) -> v));\n\
         want = {{ \"a\" -> 3, \"b\" -> 3 }};\n"
    );
    same(&src, "x", "want");
}

#[test]
fn an_identity_remap_of_a_map_lambdas_parameter() {
    let src = format!("{NESTED}x = m.map(g -> g as (k -> v) into (k -> v));\n");
    same(&src, "x", "m");
}

#[test]
fn a_remap_and_a_group_of_a_generic_functions_parameter() {
    // A parameter with no declared type is generic: the remap is checked at each call, at the
    // argument's type.
    let src = "f(g) = g as (k -> v) into (k + 1 -> v);\n\
               h(g) = g.group(v -> v mod 2);\n\
               x = f(g: { 1 -> 10, 2 -> 20 });\n\
               want = { 2 -> 10, 3 -> 20 };\n\
               y = h(g: { 1 -> 1, 2 -> 2 });\n\
               want2 = { 0 -> { 2 -> 2 }, 1 -> { 1 -> 1 } };\n";
    same(src, "x", "want");
    same(src, "y", "want2");
}

#[test]
fn a_generic_function_never_called_is_accepted() {
    let src = "f(g) = g as (k -> v) into (k + 1 -> v);\n\
               h(g) = g.group(v -> v mod 2);\n\
               x = 1;\n";
    prints(src, "x", "1");
}

#[test]
fn a_map_lambdas_parameter_that_is_no_family_is_rejected() {
    rejected(
        "xs = [1, 2];\nx = xs.map(g -> g.group(v -> v));\n",
        &["`group` works on the entries of a family, and `g` is"],
    );
    rejected(
        "xs = [1, 2];\nx = xs.map(g -> g as (k -> v) into (k + 1 -> v));\n",
        &["a remap rearranges the keys of a family, and its source `g` is"],
    );
}

#[test]
fn rekey_of_a_map_lambdas_parameter_is_rejected_as_any_rekey() {
    rejected(
        &format!("{NESTED}x = m.map(g -> g.rekey(v -> v));\n"),
        &["Cannot show that `v -> v` keeps the entries of `g` apart"],
    );
}

#[test]
fn a_generic_remap_at_two_types_records_both_reasons() {
    // `(k mod 3, k)` keeps the keys apart by `modulo` and by `literal` on the keys 0 and 1,
    // and by `literal` alone on 0 and 5, wider than the modulus. The remap is one piece of
    // code for both calls, and its witness lists both reasons.
    let src = "f(g) = g as (k -> v) into ((k mod 3, k) -> v);\n\
               x = f(g: { 0 -> 1, 5 -> 2 });\n\
               want = { (0, 0) -> 1, (2, 5) -> 2 };\n\
               y = f(g: { 0 -> 1, 1 -> 2 });\n\
               want2 = { (0, 0) -> 1, (1, 1) -> 2 };\n";
    same(src, "x", "want");
    same(src, "y", "want2");
    let info = zed_tests::step_helpers::l01_16_elaboration::checked(src).info;
    let mut witnesses: Vec<&str> = info.remaps.values().map(|p| &*p.witness).collect();
    witnesses.sort();
    assert_eq!(witnesses, ["literal+modulo"], "{src}");
}

#[test]
fn a_generic_remap_s_pattern_errors_are_given_without_a_call() {
    rejected(
        "f(g) = g as (k -> v) into (_ -> k -> v);\n",
        &["`_` stands only at the leaf of an `into` pattern"],
    );
    rejected(
        "f(g) = g as (k -> v) into (k -> v >< (+));\n",
        &["`><` folds a key level, and the last level of an `into` pattern is its leaf"],
    );
}

#[test]
fn a_remap_or_group_of_a_map_lambdas_parameter_over_empty_families() {
    // The class of `g` takes no family, or an empty one: the remap and the group still
    // compile, and give an empty result.
    for (m, x) in [
        ("{}", "m.map(g -> g as (k -> v) into (k + 1 -> v))"),
        ("{}", "m.map(g -> g.group(v -> v mod 2))"),
        (
            "{ \"a\" -> {} }",
            "m.map(g -> g as (k -> v) into (k + 1 -> v))",
        ),
        ("{ \"a\" -> {} }", "m.map(g -> g.group(v -> v mod 2))"),
    ] {
        let src = format!("m = {m};\nx = {x};\n");
        same(&src, "x", "m");
    }
}

#[test]
fn a_remap_of_a_map_lambdas_parameter_below_a_known_level() {
    let src = "m = [[1, 2], [3]];\n\
               x = m.map(r -> ({ 0 -> r }) as (a -> k -> v) into (k -> a -> v));\n\
               want = [{ 0 -> { 0 -> 1 }, 1 -> { 0 -> 2 } }, { 0 -> { 0 -> 3 } }];\n";
    same(src, "x", "want");
}

#[test]
fn a_remap_of_a_generic_functions_parameter_below_a_known_level() {
    let src = "f(g) = ({ 0 -> g }) as (a -> k -> v) into (k -> a -> v);\n\
               x = f(g: [1, 2]);\n\
               want = { 0 -> { 0 -> 1 }, 1 -> { 0 -> 2 } };\n";
    same(src, "x", "want");
}

#[test]
fn a_remap_below_a_known_level_rejects_a_value_that_is_not_a_family() {
    rejected(
        "x = [1, 2].map(r -> ({ 0 -> r }) as (a -> k -> v) into (k -> a -> v));\n",
        &[
            "this remap's `as` pattern names 2 key levels, and its source `({ 0 -> r })`",
            "after 1 key level, which is not a family",
        ],
    );
}

#[test]
fn a_remap_below_a_known_level_is_checked_at_each_type_and_through_calls() {
    let src = "f(g) = ({ 0 -> g }) as (a -> k -> v) into (k -> a -> v);\n\
               h(g) = f(g: g);\n\
               x = (f(g: [1, 2]), h(g: { \"a\" -> 3 }));\n\
               want = ({ 0 -> { 0 -> 1 }, 1 -> { 0 -> 2 } }, { \"a\" -> { 0 -> 3 } });\n";
    same(src, "x", "want");
}

#[test]
fn a_remap_two_levels_below_a_known_level() {
    let src = "m = [[[1, 2]], [[3]]];\n\
               x = m.map(r -> ({ 0 -> r }) as (a -> b -> k -> v) into (k -> b -> a -> v));\n\
               want = [{ 0 -> { 0 -> { 0 -> 1 } }, 1 -> { 0 -> { 0 -> 2 } } }, \
               { 0 -> { 0 -> { 0 -> 3 } } }];\n";
    same(src, "x", "want");
}

// ---- The names a generic remap reads besides its source ----

#[test]
fn a_remap_of_a_parameter_checks_the_function_its_leaf_or_key_calls() {
    // Row FAIL-remap-need-free-names-unbound: the remap of a generic function's parameter is
    // checked at each call as a need, and `f`, which its key or leaf reads, is the function
    // the call passes, not the body's own unknown `f`. Before the fix both were accepted and
    // the run stopped with "a bug in zedc ... `+` applied to `String`, `int`".
    let words = "main(m: MainArgs) {\n  words = [\"The\", \"cat\", \"the\"];\n";
    let group2 = "group2(positional m, positional f) = m as (k -> v) into (f(v) -> k -> v);\n";
    let src =
        format!("{group2}{words}  c = group2(words, w -> w + 1);\n  m.stdout <- \"${{c}}\";\n}}\n");
    rejected(&src, &["does not take"]);
    let map2 = "map2(positional m, positional f) = m as (k -> v) into (k -> f(v));\n";
    let src =
        format!("{map2}{words}  c = map2(words, w -> w + 1);\n  m.stdout <- \"${{c}}\";\n}}\n");
    rejected(&src, &["does not take"]);
}

#[test]
fn a_remap_of_a_parameter_checks_its_function_where_the_remap_is_nested_or_passed_on() {
    // Row FAIL-remap-need-free-names-unbound, the other places a remap's need is made: inside
    // a lambda of `map`, as the leaf of a remap each entry of a list makes, and through a
    // function that passes its parameter on to one that remaps it. Each was accepted before
    // the fix and the run stopped with "a bug in zedc".
    let words = "main(m: MainArgs) {\n  words = [\"The\", \"cat\", \"the\"];\n";
    let rows = "main(m: MainArgs) {\n  words = [[\"a\"], [\"b\"]];\n";
    let map2 = "map2(positional m, positional f) = m as (k -> v) into (k -> f(v));\n";
    let defs = [
        (
            "rm3(positional m, positional f) = [1].map(i -> m as (k -> v) into (k -> f(v)));\n",
            words,
            "rm3",
        ),
        (
            "ap5(positional x, positional f) = x.map(y -> y as (k -> v) into (k -> f(v)));\n",
            rows,
            "ap5",
        ),
        (
            "pass(positional m, positional f) = map2(m, f);\n",
            words,
            "pass",
        ),
    ];
    for (def, main, g) in defs {
        let src = format!(
            "{def}{map2}{main}  c = {g}(words, w -> w + 1);\n  m.stdout <- \"${{c}}\";\n}}\n"
        );
        rejected(&src, &["does not take"]);
    }
}

#[test]
fn a_remap_of_a_parameter_by_a_function_that_takes_its_values_is_accepted() {
    // Negative control for the two tests above: where the function passed takes the values,
    // the remap written in the program gives what the built-in word gives.
    let src = "words = [\"The\", \"cat\", \"the\"];\n\
               group2(positional m, positional f) = m as (k -> v) into (f(v) -> k -> v);\n\
               map2(positional m, positional f) = m as (k -> v) into (k -> f(v));\n\
               a = group2(words, w -> w.lower);\nb = words.group(w -> w.lower);\n\
               c = map2(words, w -> w ++ \"s\");\nd = words.map(w -> w ++ \"s\");\n";
    same(src, "a", "b");
    same(src, "c", "d");
}
