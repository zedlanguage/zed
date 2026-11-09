//! A record display whose values are bare names, or chains of `&&` or `else`. Since the else
//! chain became left recursion (LR4), `Expr12` passes a lone operand up as its own node, so the
//! value `mx` in `{ mean: mx }` arrives as a `Name` node, as the field `mean` does. The display
//! tells the two apart by the `:` after a field's name; telling them apart by the rule's name
//! read `{ count: n }` as the two fields `count` and `n`.

use super::{check, fmt};

#[test]
fn a_bare_name_is_a_value() {
    check(&[
        (
            "stats = { mean: mx, sd:, cov: };",
            "(= (stats) (record (mean: mx) (sd: sd) (cov: cov)))",
        ),
        (
            "f(xs) = { n = xs.len; { count: n } };",
            "(def f (xs) = (block (= (n) (. xs len)) (return (record (count: n)))))",
        ),
        (
            "box = { lo: lo, hi: hi };",
            "(= (box) (record (lo: lo) (hi: hi)))",
        ),
        // A field given without a value and one given its own name read the same.
        ("p = { x:, y: y };", "(= (p) (record (x: x) (y: y)))"),
        // A name repeated as a value is not a field given twice.
        ("q = { a: z, b: z };", "(= (q) (record (a: z) (b: z)))"),
    ]);
}

#[test]
fn a_field_named_twice_is_still_refused() {
    check(&[(
        "r = { a: b, a: c };",
        "error: the field `a` is given twice, and each field is given once. Remove one of \
             the two.; the first field `a` at byte 6",
    )]);
}

#[test]
fn a_chain_of_and_is_one_value() {
    check(&[
        ("ok = { a: b && c };", "(= (ok) (record (a: (&& b c))))"),
        (
            "ok = { a: b && c && d, e: f };",
            "(= (ok) (record (a: (&& (&& b c) d)) (e: f)))",
        ),
    ]);
}

#[test]
fn a_chain_of_else_is_one_value() {
    check(&[
        ("v = { a: x else y };", "(= (v) (record (a: (else x y))))"),
        (
            "v = { a: x else y else z, b: w };",
            "(= (v) (record (a: (else (else x y) z)) (b: w)))",
        ),
    ]);
}

/// The formatter writes `lo: lo` as `lo:`, which reads back as the same record.
#[test]
fn bare_name_values_round_trip() {
    assert_eq!(
        fmt("box = {lo:lo,hi:hi};\nt = {a:x else y,b:c&&d};\n"),
        "box = { lo:, hi: };\nt = { a: x else y, b: c && d };\n"
    );
}
