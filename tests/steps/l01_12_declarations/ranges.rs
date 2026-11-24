//! The range suffix of a parameter's type (DESIGN.md step L1.12, RANGE-L1): `T[lo..<hi]`,
//! `T[lo..=hi]` and `T[lo..]`, with `_` for a missing bound. Each parses as one range, prints
//! back as written, and a bound that names a parameter or a field is refused naming L10, as
//! are the named refinements and a list of two ranges.

use super::check;
use zed_tests::step_helpers::l01_13_formatter::fmt;
use zed_tests::step_helpers::l01_29_diagnostics::{accepted_with_main, rejected};

/// `src` with a `main`, so that `load` runs it as a program.
fn program(src: &str) -> String {
    format!("{src}\nmain(m: MainArgs) -> int {{ m.stdout <- \"a\"; return 0; }}\n")
}

#[test]
fn each_range_parses_as_one_range() {
    check(&[
        (
            "f(x: int[0..<10]) = x;",
            "(def f ((x: (..< int 0 10))) = x)",
        ),
        (
            "f(x: int[0..=255]) = x;",
            "(def f ((x: (..= int 0 255))) = x)",
        ),
        ("f(x: int[1..]) = x;", "(def f ((x: (.. int 1))) = x)"),
        (
            "f(x: int[_..=10]) = x;",
            "(def f ((x: (..= int _ 10))) = x)",
        ),
        (
            "f(x: int[_..<10]) = x;",
            "(def f ((x: (..< int _ 10))) = x)",
        ),
        ("f(x: int[_..]) = x;", "(def f ((x: (.. int _))) = x)"),
        ("f(x: int[0.._]) = x;", "syntax"),
        (
            "f(x: int[-5..=5]) = x;",
            "(def f ((x: (..= int (- 5) 5))) = x)",
        ),
        // DESIGN.md writes the bound `N`; a type variable is named [A-Z][0-9]* (Q23), so
        // the name bound to 10 is written `n`.
        (
            "n = 10;\nf(x: int[0..<n]) = x;",
            "(= (n) 10)\n(def f ((x: (..< int 0 n))) = x)",
        ),
        (
            "f(x: int[0..<2 * 5]) = x;",
            "(def f ((x: (..< int 0 (* 2 5)))) = x)",
        ),
    ]);
}

#[test]
fn a_tuple_key_is_one_parameter_and_two_types_are_two() {
    check(&[
        (
            "f(g: ((int, int)) -> int) = 0;",
            "(def f ((g: (-> ((tuple int int)) int))) = 0)",
        ),
        (
            "f(g: (int, int) -> int) = 0;",
            "(def f ((g: (-> (int int) int))) = 0)",
        ),
    ]);
}

#[test]
fn a_range_prints_back_as_written() {
    for src in [
        "f(x: int[0..<10]) = x;\n",
        "f(x: int[0..=255]) = x;\n",
        "f(x: int[1..]) = x;\n",
        "f(x: int[_..=10]) = x;\n",
        "f(x: int[_..]) = x;\n",
        "f(x: int[-5..=5]) = x;\n",
        "f(x: int[0..<2 * 5]) = x;\n",
        "n = 10;\nf(x: int[n + 1..=n * 2]) = x;\n",
    ] {
        assert_eq!(fmt(src), src);
    }
    // The formatter's own spacing: none around the range operator, as DESIGN writes it.
    assert_eq!(
        fmt("f(x: int[ 0 ..= 9 ]) = x;\n"),
        "f(x: int[0..=9]) = x;\n"
    );
}

/// A bound that names a parameter is a dependent domain (steps L10.4, L10.4b), refused naming
/// L10; so are the named refinements and a list of ranges (step L10.1), and `matching` (L20).
#[test]
fn a_dependent_bound_and_the_named_forms_are_refused_naming_their_layer() {
    let cases = [
        (
            "f(n: int, k: int[0..<n]) = k;",
            "1:22: ",
            zed_tests::not_yet!(
                "a range bound that names the parameter `n`, a dependent domain of layer L10,"
            ),
        ),
        (
            "f(x: int[x <= 5]) = x;",
            "1:9: ",
            zed_tests::not_yet!("the refinement of layer L10 `[x <= 5]`"),
        ),
        (
            "f(x: Utf8String[len 1..=80]) = x;",
            "1:16: ",
            zed_tests::not_yet!("the refinement of layer L10 `[len 1..=80]`"),
        ),
        (
            "f(x: int[0..=3, 2..=9]) = x;",
            "1:9: ",
            zed_tests::not_yet!("the refinement of layer L10 `[0..=3, 2..=9]`"),
        ),
    ];
    let mut wrong = Vec::new();
    for (src, at, want) in cases {
        let out = rejected(&program(src));
        let first = out.lines().next().unwrap_or("");
        let first = first.split_once(".zed:").map_or(first, |(_, r)| r);
        if first != format!("{at}{want}") {
            wrong.push(format!("{src}\n  got  {first}\n  want {at}{want}"));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

/// Name resolution lets a range through only as the whole type of a declared function's
/// parameter, over `int`: anywhere else it waits for a later step.
#[test]
fn a_range_anywhere_but_a_declared_parameter_over_int_is_a_later_form() {
    for (src, at, what) in [
        (
            "f(x: (int[0..=9], int)) = 0;",
            "1:7: ",
            "a range type in any place but the whole type of a parameter",
        ),
        (
            "f(x: int[0..=9] | #none) = 0;",
            "1:6: ",
            "a range type in any place but the whole type of a parameter",
        ),
        (
            "f(x: rat[0..=9]) = x;",
            "1:6: ",
            "a range over a type other than `int`",
        ),
        (
            "g = (x: int[0..=9]) -> x;",
            "1:9: ",
            "a range on a lambda's parameter",
        ),
        // A partial map's key takes a range on the whole key or on each component of a tuple
        // key (RANGE-keys); a range deeper in, or on a key of two levels, waits. An exact
        // arrow of one positional ranged parameter is accepted (below).
        (
            "f(m: (((int[0..<2], int), int)) ->? int) = 0;",
            "1:9: ",
            "a range type in any place but the whole type of a parameter",
        ),
        (
            "f(m: (int[0..<2], int) ->? int) = 0;",
            "1:7: ",
            "a range type in any place but the whole type of a parameter",
        ),
        (
            "f(m: rat[0..<2] ->? int) = 0;",
            "1:6: ",
            "a range over a type other than `int`",
        ),
    ] {
        let out = rejected(&program(src));
        let first = out.lines().next().unwrap_or("");
        assert!(
            first.starts_with(&format!("{at}{what}")),
            "{src}\n  got  {first}"
        );
    }
    // An exact arrow of one positional ranged parameter, `int[0..<2] -> int`, is the one text
    // of a function declared that range and of a family with those keys (row
    // PRINT-positional-range-ambiguous, option A): its range is resolved as a key is.
    let src = program("f(m: int[0..<2] -> int) = 0;");
    assert!(accepted_with_main(&src), "{src}\n  refused");
}
