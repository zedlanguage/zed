//! Each fix in the menu of an `UnfixedDecimal` or `LiteralCarrier` rejection is the corrected
//! source line followed by what the program then holds (DESIGN.md sec:diagnostics). These
//! tests read each fix out of the message, write it in place of the rejected line, and check
//! that the checker accepts the program and, where the fix names a binder's value, that the
//! binder holds that value.

use zed_tests::step_helpers::l01_16_elaboration::value;
use zed_tests::step_helpers::l01_26_type_resolution::type_errors;

/// The heading line of a menu.
const HEAD: &str = "  fixes, each checked here:";

/// The fixes of the one rejection of `src`, each `(line, holds)`: the corrected line and the
/// text after the gap of at least two spaces that follows it.
pub(super) fn fixes(src: &str) -> Vec<(String, String)> {
    let errors = type_errors(src);
    assert_eq!(errors.len(), 1, "{src}: {errors:?}");
    // The message without the ` [text]` the helper adds.
    let message = errors[0].rsplit_once(" [").unwrap().0;
    let rest = message
        .split_once(&format!("\n{HEAD}\n"))
        .unwrap_or_else(|| panic!("{src}: no menu in {message:?}"))
        .1;
    rest.lines()
        .take_while(|l| l.starts_with("    ") && !l.starts_with("     "))
        .map(|l| {
            let l = l.trim_start();
            let (line, holds) = l
                .split_once("  ")
                .unwrap_or_else(|| panic!("{src}: no value after {l:?}"));
            (line.to_string(), holds.trim_start().to_string())
        })
        .collect()
}

/// Checks each fix of the rejection of `src`, whose rejected line is its last: the program
/// with that line replaced is accepted, and a binder the fix names holds the value it names.
/// Returns the fixes, for the caller to pin.
pub(super) fn checked(src: &str) -> Vec<(String, String)> {
    let fixes = fixes(src);
    assert!(!fixes.is_empty(), "{src}: an empty menu");
    let lines: Vec<&str> = src.lines().collect();
    let (last, before) = lines.split_last().unwrap();
    for (line, holds) in &fixes {
        let fixed: String = (before.iter().copied())
            .chain([line.as_str()])
            .map(|l| format!("{l}\n"))
            .collect();
        assert_eq!(
            type_errors(&fixed),
            Vec::<String>::new(),
            "the fix {line:?} of {last:?}"
        );
        if let Some((name, v)) = holds.split_once(" is ")
            && line.starts_with(&format!("{name} = "))
        {
            assert_eq!(value(&fixed, name), v, "the fix {line:?} of {last:?}");
        }
    }
    fixes
}

pub(super) fn pairs(fixes: &[(&str, &str)]) -> Vec<(String, String)> {
    (fixes.iter())
        .map(|(a, b)| (a.to_string(), b.to_string()))
        .collect()
}

#[test]
fn a_division_of_integer_literals_lists_three_lines() {
    // The suffixes come first and the cast last, as in DESIGN.md's menu for
    // `q = (1 + 2) / (3 + 4)` (sec:diagnostics, "A `/` of integer literals").
    assert_eq!(
        checked("half = 1 / 2;\n"),
        pairs(&[
            ("half = 1.0f64 / 2;", "half is 0.5"),
            ("half = 1r / 2;", "half is 1r/2r"),
            ("half = f64(1) / 2;", "half is 0.5"),
        ])
    );
    assert_eq!(
        checked("r = -1 / 3;\n"),
        pairs(&[
            ("r = -1.0f64 / 3;", "r is -0.3333333333333333"),
            ("r = -1r / 3;", "r is -1r/3r"),
            ("r = -f64(1) / 3;", "r is -0.3333333333333333"),
        ])
    );
    // One carrier reaches both sides of the `/`, so the first literal alone takes it.
    assert_eq!(
        checked("q = (1 + 2) / (3 + 4);\n"),
        pairs(&[
            ("q = (1.0f64 + 2) / (3 + 4);", "q is 0.42857142857142855"),
            ("q = (1r + 2) / (3 + 4);", "q is 3r/7r"),
            ("q = (f64(1) + 2) / (3 + 4);", "q is 0.42857142857142855"),
        ])
    );
}

#[test]
fn an_unfixed_decimal_lists_a_line_for_each_carrier() {
    assert_eq!(
        checked("y = 0.5;\n"),
        pairs(&[("y = 0.5f64;", "y is 0.5"), ("y = 0.5r;", "y is 1r/2r")])
    );
    assert_eq!(
        checked("y = 0.5 * 2 + 1;\n"),
        pairs(&[
            ("y = 0.5f64 * 2 + 1;", "y is 2.0"),
            ("y = 0.5r * 2 + 1;", "y is 2r"),
        ])
    );
    assert_eq!(
        checked("y = 1 == 1.0;\n"),
        pairs(&[
            ("y = 1 == 1.0f64;", "y is true"),
            ("y = 1 == 1.0r;", "y is true")
        ])
    );
    assert_eq!(
        checked("y = 1 + 2 < 0.5;\n"),
        pairs(&[
            ("y = 1 + 2 < 0.5f64;", "y is false"),
            ("y = 1 + 2 < 0.5r;", "y is false"),
        ])
    );
    // A suffix on `0.5` reaches `1 + 2`, an operation on literals alone, which takes the
    // carrier of what it meets, so the fixes write the decimal the message names.
    assert_eq!(
        checked("y = (1 + 2) * 0.5;\n"),
        pairs(&[
            ("y = (1 + 2) * 0.5f64;", "y is 1.5"),
            ("y = (1 + 2) * 0.5r;", "y is 3r/2r"),
        ])
    );
    assert_eq!(
        checked("y = (1 + 2) * 0.5 ^ 2;\n"),
        pairs(&[("y = (1 + 2) * 0.5f64 ^ 2;", "y is 0.75")])
    );
    assert_eq!(
        checked("y = (1 + 2) * (3 + 0.5);\n"),
        pairs(&[
            ("y = (1 + 2) * (3 + 0.5f64);", "y is 10.5"),
            ("y = (1 + 2) * (3 + 0.5r);", "y is 21r/2r"),
        ])
    );
}

#[test]
fn a_power_lists_no_rat() {
    let fixes = checked("y = (2 ^ 3) / 4;\n");
    assert!(fixes.iter().all(|(l, _)| !l.contains('r')), "{fixes:?}");
    assert!(fixes.iter().all(|(_, h)| h == "y is 2.0"), "{fixes:?}");
}

#[test]
fn a_decimal_at_an_int_lists_the_cast_to_rat_only() {
    // The cast `f64(x)` of an unbounded `int` can lose information, so it is never a fix
    // (DESIGN.md sec:diagnostics).
    assert_eq!(
        checked("twice(x: int) = x * 2.0;\n"),
        pairs(&[
            ("twice(x: int) = x * 2;", "2 takes the int of x"),
            (
                "twice(x: int) = rat(x) * 2.0;",
                "x is cast to rat, and `*` takes two rat"
            ),
        ])
    );
}

#[test]
fn a_literal_with_no_one_carrier_lists_each() {
    let src = "f(positional x: f64 | rat) = x;\ny = f(1);\n";
    assert_eq!(
        checked(src),
        pairs(&[
            ("y = f(1r);", "the literal is then exactly 1, a rat"),
            ("y = f(1.0f64);", "the literal is then the f64 1.0"),
        ])
    );
}

#[test]
fn a_literal_with_no_exact_value_lists_the_nearest() {
    let src = "id(positional v: f64) = v;\nx = id(9007199254740993);\n";
    assert_eq!(
        checked(src),
        pairs(&[(
            "x = id(9007199254740992);",
            "the literal is then 9007199254740992.0, the nearer f64 by ties to even"
        )])
    );
}

#[test]
fn a_comparison_no_number_can_equal_lists_what_fits() {
    assert_eq!(
        checked("f(x: bool) = x == 1;\n"),
        pairs(&[
            ("f(x: bool) = x == true;", "compares with a truth value"),
            ("f(x: bool) = x == false;", "compares with a truth value"),
        ])
    );
    assert_eq!(
        checked("f(x: (int, int)) = x == 1;\n"),
        pairs(&[
            ("f(x: (int, int)) = x[0] == 1;", "compares component 0"),
            ("f(x: (int, int)) = x[1] == 1;", "compares component 1"),
        ])
    );
    assert_eq!(
        checked("f(s: String) = s == 1;\n"),
        pairs(&[
            ("f(s: String) = s == \"1\";", "compares the text"),
            (
                "f(s: String) = int(s) == 1;",
                "compares the number the text holds"
            ),
        ])
    );
    assert_eq!(
        checked("f(p: (String, int)) = p == (1, 2);\n"),
        pairs(&[(
            "f(p: (String, int)) = p == (\"1\", 2);",
            "compares the text"
        )])
    );
}

#[test]
fn a_negative_literal_keeps_its_minus_in_each_fix() {
    let at = |t: &str, lit: &str| format!("f(positional x: {t}) = x;\ny = f({lit});\n");
    assert_eq!(
        checked(&at("int", "-3.0")),
        pairs(&[("y = f(-3);", "the literal is then the int -3")])
    );
    // The value is the number the fix writes, without the suffix of the rejected literal.
    assert_eq!(
        checked(&at("rat", "-2.5f64")),
        pairs(&[("y = f(-2.5r);", "the literal is then exactly -2.5, a rat")])
    );
    assert_eq!(
        checked(&at("f64 | rat", "-3")),
        pairs(&[
            ("y = f(-3r);", "the literal is then exactly -3, a rat"),
            ("y = f(-3.0f64);", "the literal is then the f64 -3.0"),
        ])
    );
    assert_eq!(
        checked(&at("f64 | rat", "-2.5")),
        pairs(&[
            ("y = f(-2.5r);", "the literal is then exactly -2.5, a rat"),
            ("y = f(-2.5f64);", "the literal is then the f64 -2.5"),
        ])
    );
    assert_eq!(
        checked(&at("f64", "-9007199254740993")),
        pairs(&[(
            "y = f(-9007199254740992);",
            "the literal is then -9007199254740992.0, the nearer f64 by ties to even"
        )])
    );
    assert_eq!(
        checked("offset(positional x: int) = x + -2.5;\n"),
        pairs(&[(
            "offset(positional x: int) = rat(x) + -2.5;",
            "x is cast to rat, and `+` takes two rat"
        ),])
    );
}

#[test]
fn a_fix_leaves_out_a_comment_after_the_line() {
    assert_eq!(
        checked("half = 1 / 2; // the rejected line\n"),
        pairs(&[
            ("half = 1.0f64 / 2;", "half is 0.5"),
            ("half = 1r / 2;", "half is 1r/2r"),
            ("half = f64(1) / 2;", "half is 0.5"),
        ])
    );
    assert_eq!(
        checked("y = 0.5;    /* a note */\n"),
        pairs(&[("y = 0.5f64;", "y is 0.5"), ("y = 0.5r;", "y is 1r/2r")])
    );
    // A comment between the tokens of the line stays.
    assert_eq!(
        checked("y = 0.5 /* half */ * 1; // done\n"),
        pairs(&[
            ("y = 0.5f64 /* half */ * 1;", "y is 0.5"),
            ("y = 0.5r /* half */ * 1;", "y is 1r/2r")
        ])
    );
    // A `//` in a string is not a comment.
    assert_eq!(
        checked("y = 0.5; s = \"a // b\"; // c\n"),
        pairs(&[
            ("y = 0.5f64; s = \"a // b\";", "y is 0.5"),
            ("y = 0.5r; s = \"a // b\";", "y is 1r/2r")
        ])
    );
    // A block comment that the line opens and a later line closes is kept whole: the text
    // after the edit does not lex on its own.
    assert_eq!(
        fixes("y = 0.5; /* a note\n   that goes on */\n"),
        pairs(&[
            ("y = 0.5f64; /* a note", "y is 0.5"),
            ("y = 0.5r; /* a note", "y is 1r/2r")
        ])
    );
}
