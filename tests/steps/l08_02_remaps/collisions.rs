//! The collision rule in source form: the witness catalog accepts each of its entries, and a
//! pattern outside it is rejected with the menu of the diagnostics row "Collision
//! (T-Reindex)" (DESIGN.md sec:remap_law, sec:grouping, sec:diagnostics).

use crate::source::{rejected, same};

// ---- The worked collision (sec:remap_law, "The illegal move") ----

#[test]
fn the_check_reads_the_pattern_not_the_data() {
    // sec:remap_law: "The check reads the pattern, not the data, so it rejects the remap even
    // for an input whose inner levels each hold one entry."
    let src = "m = { \"a\" -> { 1 -> 10 }, \"b\" -> { 2 -> 20 } };\nx = m as (k1 -> k2 -> v) into (k1 -> v);\n";
    rejected(src, &["Cannot map many values to one key"]);
}

// ---- rekey and group (sec:grouping) ----

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

#[test]
fn a_binder_naming_a_type_in_a_pattern() {
    // Step L8.2a: the row "Binder naming a type" at the binders of `as` and `into` patterns.
    let src = "m = { \"a\" -> 1 };\nx = m as (int -> v) into (v -> int);\n";
    rejected(src, &["int"]);
}
