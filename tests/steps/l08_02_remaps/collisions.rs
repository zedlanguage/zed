//! The collision rule in source form: the witness catalog accepts each of its entries, and a
//! pattern outside it is rejected with the menu of the diagnostics row "Collision
//! (T-Reindex)" (DESIGN.md sec:remap_law, sec:grouping, sec:diagnostics).

use crate::source::{rejected, same, with_sales};

// ---- The worked collision (sec:remap_law, "The illegal move") ----

#[test]
fn dropping_a_discriminator_is_the_worked_collision() {
    // sec:remap_law: the compiler rejects `as (region -> day -> sku -> r) into (region -> day
    // -> r)` with the message written there, line by line.
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
}

#[test]
fn the_dropped_level_menu_has_no_witness_line() {
    // sec:remap_law: "No witness line and no line writing the check appear, because the
    // pattern drops the level `sku` outright".
    let src = with_sales("x = sales as (region -> day -> sku -> r) into (region -> day -> r);\n");
    let es = zed_tests::step_helpers::l01_16_elaboration::errors(&src).join("\n");
    assert!(!es.contains("@injective"), "{es}");
    assert!(!es.contains("#collision"), "{es}");
}

#[test]
fn each_repair_of_the_worked_collision_is_accepted() {
    // sec:remap_law: the three repairs of the menu, and "the only path from many values to
    // fewer is an explicit reduction": `into (region -> day -> sku >< (+) -> r)`.
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

#[test]
fn the_check_reads_the_pattern_not_the_data() {
    // sec:remap_law: "The check reads the pattern, not the data, so it rejects the remap even
    // for an input whose inner levels each hold one entry."
    let src = "m = { \"a\" -> { 1 -> 10 }, \"b\" -> { 2 -> 20 } };\nx = m as (k1 -> k2 -> v) into (k1 -> v);\n";
    rejected(src, &["Cannot map many values to one key"]);
}

// ---- rekey and group (sec:grouping) ----

#[test]
fn rekey_without_a_witness_is_rejected_with_its_menu() {
    // sec:grouping: `m.rekey(f)` claims flatness — "compile error if no catalog witness
    // applies ("this key derivation could collide — use `group`; prove `f` injective (an
    // `@injective` claim counts only at proof grade); or write the check: `group(f)`, then a
    // fold that keeps each key's one value and gives `#collision` where there are more")".
    let src = "words = [\"The\", \"cat\", \"the\"];\nx = words.rekey(w -> w.lower);\n";
    rejected(
        src,
        &["words.group(w -> w.lower)", "@injective", "#collision"],
    );
}

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
fn a_flat_pattern_on_a_derived_key_is_rejected_with_the_residue_repair() {
    // sec:diagnostics row "Collision (T-Reindex)": the menu writes the residue, "showing the
    // pattern with the discriminator restored", and the check, `group` then a fold.
    let src = "words = [\"The\", \"cat\", \"the\"];\nx = words as (i -> w) into (w.lower -> w);\n";
    rejected(src, &["into (w.lower -> i -> w)", "#collision"]);
}

#[test]
fn inverting_a_relation_into_sets() {
    // sec:power: `whoTeaches = teacherOf as (teacher -> course) into (course -> teacher ->
    // _);  // teacherOf : Teacher -> Course; result Course ->? {Teacher}`.
    let src = "teacherOf = { \"ann\" -> \"math\", \"bob\" -> \"art\", \"cy\" -> \"math\" };\n\
               x = teacherOf as (teacher -> course) into (course -> teacher -> _);\n\
               want = { \"art\" -> {\"bob\"}, \"math\" -> {\"ann\", \"cy\"} };\n";
    same(src, "x", "want");
}

// ---- The witness catalog, entry by entry (sec:grouping) ----

#[test]
fn witness_monotone_arithmetic() {
    // "strictly monotone arithmetic on refined integer ranges (`k+1`, `2*k`)".
    let src = "xs = [10, 20, 30];\nx = xs as (k -> v) into (2 * k -> v);\nwant = { 0 -> 10, 2 -> 20, 4 -> 30 };\n";
    same(src, "x", "want");
}

#[test]
fn witness_modulo_at_the_width_of_the_modulus() {
    // "`k mod p` where the domain is at most `p` contiguous integers".
    let src = "f(positional m: int[5..<10] ->? int) = m as (k -> v) into (k mod 5 -> v);\n\
               x = f({ 5 -> 50, 6 -> 60, 9 -> 90 });\nwant = { 0 -> 50, 1 -> 60, 4 -> 90 };\n";
    same(src, "x", "want");
}

#[test]
fn witness_modulo_one_wider_is_rejected() {
    // "the side condition is essential, and one integer wider it fails".
    let src = "f(positional m: int[5..=10] ->? int) = m as (k -> v) into (k mod 5 -> v);\n";
    rejected(src, &["k mod 5", "into (k mod 5 -> k -> v)"]);
}

#[test]
fn witness_affine_packing() {
    // "`(k1, k2) ↦ k1·s + k2` on `k2 : int[0..<s]`".
    let src = "f(positional m: (int[0..<2], int[0..<3]) ->? int) = m as (t -> v) into (t[0] * 3 + t[1] -> v);\n\
               x = f({ (0, 2) -> 2, (1, 0) -> 10 });\nwant = { 2 -> 2, 3 -> 10 };\n";
    same(src, "x", "want");
}

#[test]
fn witness_affine_packing_one_short_is_rejected() {
    // "Each stride must dominate the span of the keys beneath it ... one integer short and the
    // packing collides".
    let src = "f(positional m: (int[0..<2], int[0..<3]) ->? int) = m as (t -> v) into (t[0] * 2 + t[1] -> v);\n";
    rejected(src, &["t[0] * 2 + t[1]"]);
}

#[test]
fn witness_unpacking_by_euclidean_div_and_mod() {
    // "the quotient/remainder pair `k ↦ (k div s, k mod s)` as its two-sided inverse — under
    // the Euclidean `div`/`mod`", on negative keys too.
    let src = "f(positional m: int[-3..<3] ->? int) = m as (k -> v) into ((k div 3, k mod 3) -> v);\n\
               x = f({ -3 -> 1, -1 -> 2, 2 -> 3 });\nwant = { (-1, 0) -> 1, (-1, 2) -> 2, (0, 2) -> 3 };\n";
    same(src, "x", "want");
}

#[test]
fn witness_unimodular_skew() {
    // "the skew `(i, j) ↦ (i, i + j)` of a wavefront schedule ... with inverse `(a, c) ↦ (a,
    // c - a)`".
    let src = "m = { (0, 0) -> 0, (0, 1) -> 1, (1, 0) -> 10, (1, 1) -> 11 };\n\
               s = m as (t -> v) into ((t[0], t[0] + t[1]) -> v);\n\
               wantS = { (0, 0) -> 0, (0, 1) -> 1, (1, 1) -> 10, (1, 2) -> 11 };\n\
               back = s as (t -> v) into ((t[0], t[1] - t[0]) -> v);\n";
    same(src, "s", "wantS");
    same(src, "back", "m");
}

#[test]
fn witness_rank_one_affine_map_is_rejected() {
    // "integer affine maps of full column rank": `(i, j) ↦ i + j` has rank one, outside the
    // entry.
    let src = "m = { (0, 0) -> 0, (0, 1) -> 1, (1, 0) -> 10 };\nx = m as (t -> v) into (t[0] + t[1] -> v);\n";
    rejected(src, &["t[0] + t[1]"]);
}

#[test]
fn witness_componentwise_maps() {
    // "the key map `(k1, k2) ↦ (f(k1), g(k2))` — a product of injections is an injection".
    let src = "m = { (0, 0) -> 0, (1, 1) -> 11 };\nx = m as (t -> v) into ((t[0] + 1, 2 * t[1]) -> v);\n\
               want = { (1, 0) -> 0, (2, 2) -> 11 };\n";
    same(src, "x", "want");
}

#[test]
fn witness_injective_at_proof_grade() {
    // "an `@injective` claim counts only at proof grade": `2 * k + 1` is proved injective.
    let src = "@injective\nodd(positional k: int) -> int = 2 * k + 1;\nxs = [10, 20];\n\
               x = xs.rekey(k -> odd(k));\nwant = { 1 -> 10, 3 -> 20 };\n";
    same(src, "x", "want");
}

#[test]
fn a_finitely_invertible_key_is_rejected() {
    // sec:push_pull, conversion table: "finitely invertible (`i div 2`)" is not injective.
    let src = "xs = [10, 20, 30];\nx = xs as (i -> v) into (i div 2 -> v);\n";
    rejected(src, &["into (i div 2 -> i -> v)"]);
}

#[test]
fn an_output_name_that_shadows_a_value_in_scope() {
    // sec:diagnostics row "Remap output name that names a source level and resolves to a value
    // in scope": the menu is "the `as` form, or rename the outer binding".
    let src = with_sales("day = 3;\nx = sales into (day -> region -> sku -> quantitySold);\n");
    rejected(
        &src,
        &[
            "sales as (region -> day -> sku -> quantitySold) into (day -> region -> sku -> quantitySold)",
        ],
    );
}

#[test]
fn a_binder_naming_a_type_in_a_pattern() {
    // Step L8.2a: the row "Binder naming a type" at the binders of `as` and `into` patterns.
    let src = "m = { \"a\" -> 1 };\nx = m as (int -> v) into (v -> int);\n";
    rejected(src, &["int"]);
}
