//! The collision rule in source form: the witness catalog accepts each of its entries, and a
//! pattern outside it is rejected with the menu of the diagnostics row "Collision
//! (T-Reindex)" (DESIGN.md sec:remap_law, sec:grouping, sec:diagnostics).

use crate::source::{rejected, same};

// ---- The worked collision (sec:remap_law, "The illegal move"; its menu and repairs on `sales`
// are in `rules`) ----

#[test]
fn the_check_reads_the_pattern_not_the_data() {
    // sec:remap_law: "The check reads the pattern, not the data, so it rejects the remap even
    // for an input whose inner levels each hold one entry."
    let src = "m = { \"a\" -> { 1 -> 10 }, \"b\" -> { 2 -> 20 } };\nx = m as (k1 -> k2 -> v) into (k1 -> v);\n";
    rejected(src, &["Cannot map many values to one key"]);
}

// ---- Grouping by a written residue (sec:grouping; `group` and `rekey` are in `rules`) ----

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
fn witness_strictly_decreasing_arithmetic() {
    // "strictly monotone arithmetic on refined integer ranges": a decreasing map is strictly
    // monotone too, and a shift by a constant is.
    let src = "xs = [10, 20, 30];\n\
               a = xs as (k -> v) into (5 - k -> v);\nwantA = { 3 -> 30, 4 -> 20, 5 -> 10 };\n\
               b = xs as (k -> v) into (k - 3 -> v);\nwantB = { -3 -> 10, -2 -> 20, -1 -> 30 };\n";
    same(src, "a", "wantA");
    same(src, "b", "wantB");
}

#[test]
fn witness_tupling_and_permutation_of_witnessed_components() {
    // "tupling/permutation of witnessed components": the two keys swapped, and one of them
    // shifted, each into one tuple key.
    let src = "m = { \"a\" -> { 1 -> 10, 2 -> 20 }, \"b\" -> { 1 -> 30 } };\n\
               a = m as (k1 -> k2 -> v) into ((k2, k1) -> v);\n\
               wantA = { (1, \"a\") -> 10, (1, \"b\") -> 30, (2, \"a\") -> 20 };\n\
               b = m as (k1 -> k2 -> v) into ((k1, k2 + 1) -> v);\n\
               wantB = { (\"a\", 2) -> 10, (\"a\", 3) -> 20, (\"b\", 2) -> 30 };\n";
    same(src, "a", "wantA");
    same(src, "b", "wantB");
}

#[test]
fn witness_affine_packing_at_three_levels() {
    // "applied lexicographically at any depth": `(t0, t1, t2) ↦ t0·6 + t1·3 + t2` with `t2` in
    // 0..<3 and `t1·3 + t2` in 0..<6, so (0, 1, 2) goes to 5 and (1, 0, 1) to 7.
    let src = "m = { (0, 1, 2) -> 50, (1, 0, 1) -> 70 };\n\
               x = m as (t -> v) into (t[0] * 6 + t[1] * 3 + t[2] -> v);\nwant = { 5 -> 50, 7 -> 70 };\n";
    same(src, "x", "want");
}

#[test]
fn witness_affine_map_of_full_column_rank_that_is_not_square() {
    // "integer affine maps of full column rank — `k ↦ A·k + b` ... with no range condition":
    // `(i, j) ↦ (i + j, i - j, 7)` has independent columns (1, 1, 0) and (1, -1, 0).
    let src = "m = { (0, 0) -> 1, (0, 1) -> 2, (1, 0) -> 3 };\n\
               a = m as (t -> v) into ((t[0] + t[1], t[0] - t[1], 7) -> v);\n\
               wantA = { (0, 0, 7) -> 1, (1, -1, 7) -> 2, (1, 1, 7) -> 3 };\n\
               b = m as (t -> v) into ((t[0] + t[1], t[0] - t[1]) -> v);\n\
               wantB = { (0, 0) -> 1, (1, -1) -> 2, (1, 1) -> 3 };\n";
    same(src, "a", "wantA");
    same(src, "b", "wantB");
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
fn a_finitely_invertible_key_is_rejected() {
    // sec:push_pull, conversion table: "finitely invertible (`i div 2`)" is not injective.
    let src = "xs = [10, 20, 30];\nx = xs as (i -> v) into (i div 2 -> v);\n";
    rejected(src, &["into (i div 2 -> i -> v)"]);
}

// ---- The collision menu for each kind of non-injective key (sec:diagnostics, "Collision
// (T-Reindex)") ----

#[test]
fn a_constant_key_collides_with_its_menu() {
    // A constant keeps nothing apart. The menu writes the residue under the constant, the
    // truncation, the fold at each dropped level, a witness and the check.
    let src = "m = { \"a\" -> { 1 -> 10, 2 -> 20 }, \"b\" -> { 1 -> 30 } };\n\
               x = m as (k1 -> k2 -> v) into (0 -> v);\n";
    rejected(
        src,
        &[
            "Cannot show that `0` keeps the keys of `(k1, k2)` apart: `into (0 -> v)`. Try `into (0 -> k1 -> k2 -> v)` instead.",
            "write the residue:           into (0 -> k1 -> k2 -> v)",
            "or drop the values too:      into (0 -> k1 -> k2 -> _)",
            "or say how the values merge: into (0 -> k1 >< op -> k2 >< op -> v)",
            "or supply a witness:",
            "or write the check:",
        ],
    );
}

#[test]
fn a_projection_of_a_tuple_key_collides() {
    // `t[0]` forgets `t[1]`: (1, 2) and (1, 3) meet at 1.
    let src = "m = { (1, 2) -> 10, (1, 3) -> 20 };\nx = m as (t -> v) into (t[0] -> v);\n";
    rejected(
        src,
        &[
            "Cannot show that `t[0]` keeps the keys of `t` apart",
            "into (t[0] -> t -> v)",
        ],
    );
}

#[test]
fn a_key_computed_from_the_value_collides() {
    // `v mod 2` is 0 for all three values, so the keys meet.
    let src = "xs = [10, 20, 30];\nx = xs as (k -> v) into (v mod 2 -> v);\n";
    rejected(src, &["Try `into (v mod 2 -> k -> v)` instead."]);
}

#[test]
fn the_value_as_the_only_key_collides() {
    // The pattern drops the level `k` outright, so the menu is the dropped-level one of
    // sec:remap_law: "Cannot map many values to one key".
    let src = "xs = [10, 20, 10];\nx = xs as (k -> v) into (v -> v);\n";
    rejected(
        src,
        &[
            "Cannot map many values to one key: `into (v -> v)`. Try `into (v -> k -> _)` instead.",
            "the `k` keypaths collapse onto `v`, but their values survive.",
        ],
    );
}

#[test]
fn a_square_that_is_not_monotone_collides() {
    // `k * k` is not in the catalog on keys of either sign: -1 and 1 meet at 1.
    let src = "m = { -1 -> 1, 1 -> 2 };\nx = m as (k -> v) into (k * k -> v);\n";
    rejected(src, &["k * k", "into (k * k -> k -> v)"]);
}

#[test]
fn a_binder_naming_a_type_in_a_pattern() {
    // Step L8.2a: the row "Binder naming a type" at the binders of `as` and `into` patterns.
    let src = "m = { \"a\" -> 1 };\nx = m as (int -> v) into (v -> int);\n";
    rejected(src, &["int"]);
}
