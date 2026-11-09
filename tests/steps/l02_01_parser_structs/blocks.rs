//! Between a block and a display the separator decides: a binding or a `;` makes a block, and
//! `name: v` entries a record display. In body position a brace is always a block, so a
//! display there is parenthesized.

use super::check;

#[test]
fn name_colon_entries_make_a_record_display() {
    check(&[
        (
            "origin = { x: 0.0, y: 0.0 };",
            "(= (origin) (record (x: 0.0) (y: 0.0)))",
        ),
        // `sd:` is short for `sd: sd`.
        (
            "stats = { mean: mx, sd:, cov: };",
            "(= (stats) (record (mean: mx) (sd: sd) (cov: cov)))",
        ),
        (
            "row = { id: w[0] else \"\", n: int(w[1]) else 0, };",
            "(= (row) (record (id: (else (index w 0) (str))) (n: (else (call int (index w 1)) 0))))",
        ),
    ]);
}

#[test]
fn a_binding_or_a_semicolon_makes_a_block() {
    check(&[
        (
            "f(xs) = { n = xs.len; { count: n } };",
            "(def f (xs) = (block (= (n) (. xs len)) (return (record (count: n)))))",
        ),
        (
            "g(p) = { return { x: p.y, y: p.x }; };",
            "(def g (p) = (block (return (record (x: (. p y)) (y: (. p x))))))",
        ),
    ]);
}

#[test]
fn return_exports_a_record_display() {
    check(&[(
        "summary(xs) {\n  lo = xs.min;\n  hi = xs.max;\n  return { lo:, hi:, span: hi - lo };\n}",
        "(def summary (xs) (block (= (lo) (. xs min)) (= (hi) (. xs max)) \
         (return (record (lo: lo) (hi: hi) (span: (- hi lo))))))",
    )]);
}

#[test]
fn a_display_in_body_position_is_parenthesized() {
    check(&[
        (
            "swap = p -> ({ x: p.y, y: p.x });",
            "(= (swap) (fn (p) (record (x: (. p y)) (y: (. p x)))))",
        ),
        ("d = r else ({ x: 0 });", "(= (d) (else r (record (x: 0))))"),
        (
            "v = if c { { x: 1 } } else { { x: 2 } };",
            "(= (v) (if c (block (return (record (x: 1)))) (block (return (record (x: 2))))))",
        ),
    ]);
    // Unparenthesized, each is rejected as a display in body position (sec:diagnostics).
    for text in ["swap = p -> { x: p.y, y: p.x };", "d = r else { x: 0 };"] {
        let got = super::sx(text);
        assert!(
            got.starts_with("error: a record display in body position:"),
            "{text}: {got}"
        );
    }
}

#[test]
fn a_display_field_given_twice_is_an_error() {
    check(&[(
        "p = { x: 1, y: 2, x: 3 };",
        "error: the field `x` is given twice, and each field is given once. Remove one of \
             the two.; the first field `x` at byte 6",
    )]);
}

#[test]
fn other_displays_are_sets_and_maps() {
    check(&[
        ("s = { 1, 2 };", "(= (s) (set 1 2))"),
        ("s = {};", "(= (s) (map))"),
        ("m = { \"a\" -> 1 };", "(= (m) (map (-> (str \"a\") 1)))"),
        // One entry without a name and a colon is the singleton set.
        ("s = { x };", "(= (s) (set x))"),
    ]);
}
