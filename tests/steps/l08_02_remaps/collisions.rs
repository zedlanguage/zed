//! The collision rule in source form: the witness catalog accepts each of its entries, and a
//! pattern outside it is rejected with the menu of the diagnostics row "Collision
//! (T-Reindex)" (DESIGN.md sec:remap_law, sec:grouping, sec:diagnostics).

use crate::source::{all_errors, rejected, same};

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
fn the_component_blamed_is_the_one_that_reads_the_lost_key_inside_a_block() {
    // FAIL-remap-mentions: the message names the key component that reads the lost binder,
    // here `i`, read only in a statement of a block. The walk that looks for the read skipped
    // blocks, so it found no component reading `i` and blamed the first, `j * 1`, which keeps
    // `j` apart. (`{ i * 0 }` is a set display, not a block, and was blamed rightly.)
    let src =
        "m = {1 -> {2 -> 3}};\nx = m as (i -> j -> v) into (j * 1 -> { k = i * 0; k } -> v);\n";
    assert_eq!(
        all_errors(src),
        [
            "Cannot show that `{ k = i * 0; k }` keeps the keys of `i` apart: `into (j * 1 -> { \
             k = i * 0; k } -> v)`. Try `into (j * 1 -> { k = i * 0; k } -> i -> v)` instead.\n  \
             no entry of the witness catalog shows `{ k = i * 0; k }` one-to-one; the nearest is \
             a function proved one-to-one.\n  write the residue:           into (j * 1 -> { k = \
             i * 0; k } -> i -> v)\n      keeps each value under its i\n  or drop the values \
             too:      into (j * 1 -> { k = i * 0; k } -> i -> _)\n      keeps each i and drops \
             its value\n  or say how the values merge: into (j * 1 -> { k = i * 0; k } -> i >< \
             op -> v)\n      merges each { k = i * 0; k }'s values with op, which must be \
             associative\n  or supply a witness:         prove `{ k = i * 0; k }` one-to-one; \
             an `@injective` claim counts only at proof grade\n  or write the check:          \
             `group` by the key, then a fold that keeps each key's one value and gives \
             `#collision` where there are more [m as (i -> j -> v) into (j * 1 -> { k = i * 0; \
             k } -> v)]"
        ],
        "{src}"
    );
    // A block that binds its own `i` reads that one, not the key: no component reads the
    // key `i`, and the first is blamed.
    let src =
        "m = {1 -> {2 -> 3}};\nx = m as (i -> j -> v) into (j * 1 -> { i = 5; i * 0 } -> v);\n";
    rejected(
        src,
        &[
            "Cannot show that `j * 1` keeps the keys of `i` apart: `into (j * 1 -> { i = 5; i * 0 } -> v)`.",
        ],
    );
}

#[test]
fn a_binder_naming_a_type_in_a_pattern() {
    // Step L8.2a: the row "Binder naming a type" at the binders of `as` and `into` patterns.
    let src = "m = { \"a\" -> 1 };\nx = m as (int -> v) into (v -> int);\n";
    rejected(src, &["int"]);
}

// ---- Catalog entries on a key domain a range type bounds (RANGE-keys) ----

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
    // "`(k1, k2) ↦ k1·s + k2` on `k2 : int[0..<s]`". The key is one level holding a tuple,
    // `((A, B)) ->? C`; `(A, B) ->? C` would be two levels (DESIGN.md sec:grammar).
    let src = "f(positional m: ((int[0..<2], int[0..<3])) ->? int) = m as (t -> v) into (t[0] * 3 + t[1] -> v);\n\
               x = f({ (0, 2) -> 2, (1, 0) -> 10 });\nwant = { 2 -> 2, 3 -> 10 };\n";
    same(src, "x", "want");
}

#[test]
fn witness_affine_packing_one_short_is_rejected() {
    // "Each stride must dominate the span of the keys beneath it ... one integer short and the
    // packing collides".
    let src = "f(positional m: ((int[0..<2], int[0..<3])) ->? int) = m as (t -> v) into (t[0] * 2 + t[1] -> v);\n";
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

// ---- Calls of a function whose partial-map parameter has a range on its key (RANGE-keys) ----
// The witness above reads the range, so each call must show the keys it passes lie in it.

/// The function of the modulo witness: a remap of `m` by `k mod 5` on keys in 5 to 9.
const MOD5: &str = "f(positional m: int[5..<10] ->? int) = m as (k -> v) into (k mod 5 -> v);\n";

#[test]
fn a_key_outside_the_range_is_rejected_at_the_call() {
    // 3 and 8 would both give the key 3.
    let src = format!("{MOD5}x = f({{ 3 -> 1, 8 -> 2 }});\n");
    rejected(
        &src,
        &[
            "`f` takes `m` as a family, which a remap reads, with keys in int[5..=9]: `{ 3 -> 1, 8 -> 2 }` may not be one",
        ],
    );
}

#[test]
fn a_function_is_rejected_where_a_remap_reads_the_parameter() {
    // The remap rearranges entries at run time, and a function has none. (A lambda's
    // parameter takes no range yet, so its key is `int`; the family is checked first.)
    let src = format!("{MOD5}x = f((k: int) -> k);\n");
    rejected(&src, &["`f` takes `m` as a family, which a remap reads"]);
}

#[test]
fn a_function_of_every_int_is_rejected_where_the_key_is_ranged() {
    // No remap reads `m` here, but the keys of a map of every int do not lie in 5 to 9.
    let src = "f(positional m: int[5..<10] ->? int) = m(6) else 0;\nx = f((k: int) -> k);\n";
    rejected(
        src,
        &["`f` takes `m` with keys in int[5..=9]: `(k: int) -> k` may not be one"],
    );
}

#[test]
fn a_parameter_with_a_range_inside_passes_its_keys_on() {
    let src = format!(
        "{MOD5}g(positional m: int[6..<9] ->? int) = f(m);\nx = g({{ 7 -> 1 }});\nwant = {{ 2 -> 1 }};\n"
    );
    same(&src, "x", "want");
}

#[test]
fn a_parameter_with_a_wider_range_is_rejected() {
    let src = format!("{MOD5}g(positional m: int[0..<9] ->? int) = f(m);\n");
    rejected(
        &src,
        &[
            "`f` takes `m` as a family, which a remap reads, with keys in int[5..=9], and `m` is declared with keys that may lie outside",
        ],
    );
}

#[test]
fn a_parameter_of_no_declared_type_takes_the_need_on_to_its_calls() {
    let pass =
        format!("{MOD5}g(positional m) = f(m);\nx = g({{ 7 -> 1 }});\nwant = {{ 2 -> 1 }};\n");
    same(&pass, "x", "want");
    let fail = format!("{MOD5}g(positional m) = f(m);\nx = g({{ 3 -> 1, 8 -> 2 }});\n");
    rejected(
        &fail,
        &["with keys in int[5..=9]: `{ 3 -> 1, 8 -> 2 }` may not be one"],
    );
}

/// The step from a parameter's floor to the outer calls (row PROOF-keys-at-outer-calls, the
/// proof at `keys_at` in walk.rs): a need passed on through two parameters of no declared type
/// reaches the outermost call, and a call through a name bound to the function, or through a
/// parameter that holds it, checks the need as a call by the function's own name does.
#[test]
fn the_need_on_keys_reaches_every_outer_call() {
    let two = format!("{MOD5}g(positional m) = f(m);\nh(positional m) = g(m);\n");
    same(
        &format!("{two}x = h({{ 7 -> 1 }});\nwant = {{ 2 -> 1 }};\n"),
        "x",
        "want",
    );
    let bad = "{ 3 -> 1, 8 -> 2 }";
    let refused = format!("with keys in int[5..=9]: `{bad}` may not be one");
    for call in [
        format!("{two}x = h({bad});\n"),
        format!("{MOD5}g(positional m) = f(m);\nk = g;\nx = k({bad});\n"),
    ] {
        rejected(&call, &[&refused]);
    }
    // Through a parameter that holds `g` the call is rejected for the same range, but the
    // message quotes the whole outer call where the argument belongs (`app(…, p: g)` "may not
    // be one"); only the range is asserted here, the quoting is a row of its own.
    let through = format!(
        "{MOD5}g(positional m) = f(m);\napp(positional m, p) = p(m);\nx = app({bad}, p: g);\n"
    );
    rejected(
        &through,
        &["`p` takes `m` as a family", "with keys in int[5..=9]"],
    );
}

#[test]
fn a_tuple_key_component_outside_its_range_is_rejected() {
    // (0, 3) and (1, 0) would both give the key 3.
    let src = "f(positional m: ((int[0..<2], int[0..<3])) ->? int) = m as (t -> v) into (t[0] * 3 + t[1] -> v);\n\
               x = f({ (0, 3) -> 1, (1, 0) -> 2 });\n";
    rejected(
        src,
        &[
            "key component 0 in int[0..=1] and key component 1 in int[0..=2]: `{ (0, 3) -> 1, (1, 0) -> 2 }` may not be one",
        ],
    );
}
