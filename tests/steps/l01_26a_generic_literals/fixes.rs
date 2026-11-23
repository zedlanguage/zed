//! Each fix in the menu of an `UnfixedDecimal` or `LiteralCarrier` rejection is the corrected
//! source line followed by what the program then holds (DESIGN.md sec:diagnostics). These
//! tests read each fix out of the message, write it in place of the rejected line, and check
//! that the checker accepts the program and, where the fix names a binder's value, that the
//! binder holds that value.

use zed_tests::step_helpers::l01_16_elaboration::{checked as l01_16_checked, value};
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
            // A `rat` value reached through a `^` is named by the operation as the fix writes
            // it (DESIGN.md sec:diagnostics, "The value a fix names"), which holds that value.
            let v = match v.contains('^') {
                true => value(&format!("{name} = {v};\n"), name),
                false => v.to_string(),
            };
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
    // The exact carrier first, then `f64` written on a literal, and the cast last, as in
    // DESIGN.md's menu for `q = (1 + 2) / (3 + 4)` (sec:diagnostics, "A `/` of integer
    // literals"). DESIGN.md also lists each carrier declared on the binder, `q: rat = …` and
    // `q: f64 = …`; this zedc does not compile a binding with a declared type yet, so it
    // leaves those out.
    assert_eq!(
        checked("half = 1 / 2;\n"),
        pairs(&[
            ("half = 1r / 2;", "half is 1r/2r"),
            ("half = 1.0 / 2;", "half is 0.5"),
            ("half = f64(1) / 2;", "half is 0.5"),
        ])
    );
    assert_eq!(
        checked("r = -1 / 3;\n"),
        pairs(&[
            ("r = -1r / 3;", "r is -1r/3r"),
            ("r = -1.0 / 3;", "r is -0.3333333333333333"),
            ("r = -f64(1) / 3;", "r is -0.3333333333333333"),
        ])
    );
    // One carrier reaches both sides of the `/`, so the first literal alone takes it.
    assert_eq!(
        checked("q = (1 + 2) / (3 + 4);\n"),
        pairs(&[
            ("q = (1r + 2) / (3 + 4);", "q is 3r/7r"),
            ("q = (1.0 + 2) / (3 + 4);", "q is 0.42857142857142855"),
            ("q = (f64(1) + 2) / (3 + 4);", "q is 0.42857142857142855"),
        ])
    );
}

/// A literal beside a call that the walk reads at `f64` lists the `rat` fix as well. Each fix
/// is checked by checking the operation again with the literal retyped (`Ck::trial`), which
/// reads the call at `rat` where the walk read it at `f64`; the checker took that second
/// reading for a span rebuilt twice and dropped the fix, so these menus listed `1.0f64`
/// alone (PROOF-fit-twice-only-arrow-lambda).
#[test]
fn a_literal_beside_a_call_read_at_f64_lists_the_rat_fix() {
    for (head, op, holds) in [
        ("f(x) = 0;\n", "f(x: 1) + (1 / 2)", "1r/2r"),
        ("", "(v60 -> 0)(1) + (1 / 2)", "1r/2r"),
        ("", "(v60 -> 0)(1) * (1 / 2)", "0r"),
    ] {
        let rat = op.replace("(1 / 2)", "(1r / 2)");
        let f64 = op.replace("(1 / 2)", "(1.0f64 / 2)");
        assert_eq!(
            checked(&format!("{head}r = {op};\n")),
            pairs(&[
                (
                    &format!("r = {rat};"),
                    "the literal is then exactly 1, a rat"
                ),
                (&format!("r = {f64};"), "the literal is then the f64 1.0"),
            ]),
            "{op}"
        );
        assert_eq!(value(&format!("{head}r = {rat};\n"), "r"), holds, "{op}");
    }
    assert_eq!(
        checked("r = if (v60 -> 0)(1) < (1 / 2) { 1 } else { 2 };\n"),
        pairs(&[
            (
                "r = if (v60 -> 0)(1) < (1r / 2) { 1 } else { 2 };",
                "the literal is then exactly 1, a rat"
            ),
            (
                "r = if (v60 -> 0)(1) < (1.0f64 / 2) { 1 } else { 2 };",
                "the literal is then the f64 1.0"
            ),
        ])
    );
}

/// A decimal literal that nothing fixes is no error: it takes `f64`, and so does an operation
/// on literals alone with a decimal among its operands, with no warning and no menu (DESIGN.md
/// step L1.26b, author decision 2026-11-12). These lines each listed a menu before.
#[test]
fn an_unfixed_decimal_takes_f64_with_no_menu() {
    for (src, want) in [
        ("y = 0.5;\n", "0.5"),
        ("y = 0.5 * 2 + 1;\n", "2.0"),
        ("y = 1 == 1.0;\n", "true"),
        ("y = 1 + 2 < 0.5;\n", "false"),
        // `0.5` reaches `1 + 2`, an operation on literals alone, which takes its carrier.
        ("y = (1 + 2) * 0.5;\n", "1.5"),
        ("y = (1 + 2) * 0.5 ^ 2;\n", "0.75"),
        ("y = (1 + 2) * (3 + 0.5);\n", "10.5"),
    ] {
        assert_eq!(value(src, "y"), want, "{src}");
        assert!(l01_16_checked(src).info.warnings.is_empty(), "{src}");
    }
}

/// A power whose exponent is an `int` lists `rat` as well, by the arrow (rat, int) of `^`:
/// an integer literal, or an operation on integer literals alone, which the `rat` fix leaves
/// as it is (plan row LIT-rat-int-op-exponent). One whose exponent is no `int`, as `2^-1`
/// makes it, does not, as `^` has no arrow (rat, rat).
#[test]
fn a_power_lists_rat_only_with_an_int_exponent() {
    assert_eq!(
        checked("y = (2 ^ 3) / 4;\n"),
        pairs(&[
            ("y = (2r ^ 3) / 4;", "y is (2r ^ 3) / 4"),
            ("y = (2.0 ^ 3) / 4;", "y is 2.0"),
            ("y = (f64(2) ^ 3) / 4;", "y is 2.0"),
        ])
    );
    assert_eq!(
        checked("y = (2 ^ (1 + 2)) / 4;\n"),
        pairs(&[
            ("y = (2r ^ (1 + 2)) / 4;", "y is (2r ^ (1 + 2)) / 4"),
            ("y = (2.0 ^ (1.0 + 2)) / 4;", "y is 2.0"),
            ("y = (f64(2) ^ (f64(1) + 2)) / 4;", "y is 2.0"),
        ])
    );
    let fixes = checked("y = (2 ^ (3 - 2^-1)) / 4;\n");
    assert!(fixes.iter().all(|(l, _)| !l.contains('r')), "{fixes:?}");
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
        pairs(&[("f(s: String) = s == \"1\";", "compares the text")])
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
        pairs(&[
            ("y = f(-2.5);", "the literal is then exactly -2.5, a rat"),
            ("y = f(-2.5r);", "the literal is then exactly -2.5, a rat"),
        ])
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
            ("half = 1r / 2;", "half is 1r/2r"),
            ("half = 1.0 / 2;", "half is 0.5"),
            ("half = f64(1) / 2;", "half is 0.5"),
        ])
    );
    assert_eq!(
        checked("y = 1 / 2;    /* a note */\n"),
        pairs(&[
            ("y = 1r / 2;", "y is 1r/2r"),
            ("y = 1.0 / 2;", "y is 0.5"),
            ("y = f64(1) / 2;", "y is 0.5"),
        ])
    );
    // A comment between the tokens of the line stays.
    assert_eq!(
        checked("y = 1 /* half */ / 2; // done\n"),
        pairs(&[
            ("y = 1r /* half */ / 2;", "y is 1r/2r"),
            ("y = 1.0 /* half */ / 2;", "y is 0.5"),
            ("y = f64(1) /* half */ / 2;", "y is 0.5"),
        ])
    );
    // A `//` in a string is not a comment.
    assert_eq!(
        checked("y = 1 / 2; s = \"a // b\"; // c\n"),
        pairs(&[
            ("y = 1r / 2; s = \"a // b\";", "y is 1r/2r"),
            ("y = 1.0 / 2; s = \"a // b\";", "y is 0.5"),
            ("y = f64(1) / 2; s = \"a // b\";", "y is 0.5"),
        ])
    );
    // A block comment that the line opens and a later line closes is kept whole: the text
    // after the edit does not lex on its own.
    assert_eq!(
        fixes("y = 1 / 2; /* a note\n   that goes on */\n"),
        pairs(&[
            ("y = 1r / 2; /* a note", "y is 1r/2r"),
            ("y = 1.0 / 2; /* a note", "y is 0.5"),
            ("y = f64(1) / 2; /* a note", "y is 0.5"),
        ])
    );
}

/// A fix that gives a power of literals the carrier `rat` names the value the binder then
/// holds by the operation as the fix writes it, and does not compute it: `3r^200000` has
/// 95,425 digits, and the note is as long as the text (DESIGN.md sec:diagnostics, "The value a
/// fix names"; MSG-fixnote-huge-value). At `f64` the value, of fixed size, is named, and so is
/// a value at `rat` with no `^`. The same holds for a pair of a tuple.
#[test]
fn a_value_at_rat_reached_through_a_power_is_named_by_the_operation() {
    assert_eq!(
        type_errors("x = 3^200000 / 2;\n"),
        [concat!(
            "Nothing gives the integer literals a carrier, and `/` has none at `int`: ",
            "`x = 3^200000 / 2`. Try `x = 3r^200000 / 2` instead.\n",
            "  fixes, each checked here:\n",
            "    x = 3r^200000 / 2;        x is 3r^200000 / 2\n",
            "    x = 3.0^200000 / 2;       x is inf\n",
            "    x = f64(3)^200000 / 2;    x is inf [3^200000 / 2]",
        )]
    );
    // The contrast: with no `^` the value is named at `rat` too.
    assert_eq!(
        checked("x = (3 + 1) / 2;\n"),
        pairs(&[
            ("x = (3r + 1) / 2;", "x is 2r"),
            ("x = (3.0 + 1) / 2;", "x is 2.0"),
            ("x = (f64(3) + 1) / 2;", "x is 2.0"),
        ])
    );
    assert_eq!(
        checked("x = (3^2 + 1) / 2;\n"),
        pairs(&[
            ("x = (3r^2 + 1) / 2;", "x is (3r^2 + 1) / 2"),
            ("x = (3.0^2 + 1) / 2;", "x is 5.0"),
            ("x = (f64(3)^2 + 1) / 2;", "x is 5.0"),
        ])
    );
    // A pair of a tuple is named as the fix writes it where it holds a `^` at `rat`.
    assert_eq!(
        fixes("y = (3^20 / 2, 1);\n"),
        pairs(&[
            ("y = (3r^20 / 2, 1);", "y[0] is 3r^20 / 2"),
            ("y = (3.0^20 / 2, 1);", "y[0] is 1743392200.5"),
            ("y = (f64(3)^20 / 2, 1);", "y[0] is 1743392200.5"),
        ])
    );
    for fix in ["y = (3r^20 / 2, 1);\n", "y = (3.0^20 / 2, 1);\n"] {
        assert_eq!(type_errors(fix), Vec::<String>::new(), "{fix}");
    }
    assert_eq!(value("y = (3r^20 / 2, 1);\n", "y"), "(3486784401r/2r, 1)");
    // DESIGN.md: `y = (3^20 / 2, 1) == (1, 2);` "has `y = (3r^20 / 2, 1) == (1, 2);    y is
    // (3r^20 / 2, 1) == (1, 2)`": the first pair takes `rat`, the second stays at `int`, and
    // the `rat` pair holds a `^`, so the comparison is named as written. The fixes at `f64`, of
    // fixed size, name the value (row LIT-tuple-compare-power-menu).
    assert_eq!(
        checked("y = (3^20 / 2, 1) == (1, 2);\n"),
        pairs(&[
            (
                "y = (3r^20 / 2, 1) == (1, 2);",
                "y is (3r^20 / 2, 1) == (1, 2)"
            ),
            ("y = (3.0^20 / 2, 1) == (1, 2);", "y is false"),
            ("y = (f64(3)^20 / 2, 1) == (1, 2);", "y is false"),
        ])
    );
    for fix in [
        "y = (3r^20 / 2, 1) == (1, 2);\n",
        "y = (3.0^20 / 2, 1) == (1, 2);\n",
        "y = (f64(3)^20 / 2, 1) == (1, 2);\n",
    ] {
        assert_eq!(value(fix, "y"), "false", "{fix}");
    }
    // DESIGN.md: a pair at `int` is named the same way, in `y = (3^2 + 1, 1 / 2) == (10, 1 /
    // 2);`: the two `1 / 2` meet at `==`, so one rejection, whose fixes write the pair's first
    // literal and name `y` by the comparison as written, the pair at `int` holding a `^` (row
    // LIT-tuple-compare-names-literal). Each fix makes the line check, `y` then `true`.
    let src = "y = (3^2 + 1, 1 / 2) == (10, 1 / 2);\n";
    let fixed = [
        "y = (3^2 + 1, 1r / 2) == (10, 1 / 2);",
        "y = (3^2 + 1, 1.0 / 2) == (10, 1 / 2);",
        "y = (3^2 + 1, f64(1) / 2) == (10, 1 / 2);",
    ];
    let named: Vec<String> = (fixed.iter())
        .map(|f| {
            format!(
                "y is {}",
                f.trim_start_matches("y = ").trim_end_matches(';')
            )
        })
        .collect();
    let expected: Vec<(&str, &str)> = fixed
        .iter()
        .copied()
        .zip(named.iter().map(String::as_str))
        .collect();
    assert_eq!(checked(src), pairs(&expected));
    for fix in fixed {
        assert_eq!(value(&format!("{fix}\n"), "y"), "true", "{fix}");
    }
    // The note is on one line: a line break or a comment between two tokens is one space.
    assert_eq!(
        fixes("x = (3^20 // three\n    + 1) / 2;\n"),
        pairs(&[
            ("x = (3r^20", "x is (3r^20 + 1) / 2"),
            ("x = (3.0^20", "x is 1743392201.0"),
            ("x = (f64(3)^20", "x is 1743392201.0"),
        ])
    );
}

#[test]
fn an_exponent_folded_past_f64_lists_the_nearest_whatever_its_text() {
    // An exponent folded from integer literals is a literal whose text may be a power form,
    // `3^100`, shorter than its digits (`Rat::integer_text`); the nearest `f64` is read from
    // its value, so the fix is offered as for digits. The values are 3^40, 3^100 and 5*3^100
    // by `bc`, and their nearest `f64` by glibc's `strtod`.
    assert_eq!(
        checked("f() = 0.5f64 ^ (3^40);\n"),
        pairs(&[(
            "f() = 0.5f64 ^ 12157665459056928768;",
            "the literal is then 12157665459056929000.0, the nearer f64 by ties to even"
        )])
    );
    let near = |src: &str| (checked(src).into_iter().map(|(line, _)| line)).collect::<Vec<_>>();
    assert_eq!(
        near("f() = 0.5f64 ^ (3^100);\n"),
        ["f() = 0.5f64 ^ 515377520732011324194596268868618440852459487232;"]
    );
    assert_eq!(
        near("f() = 0.5f64 ^ (5 * 3^100);\n"),
        ["f() = 0.5f64 ^ 2576887603660056783232258173556455595840307724288;"]
    );
    assert_eq!(
        near("f() = 0.5f64 ^ (0 - 3^100);\n"),
        ["f() = 0.5f64 ^ -515377520732011324194596268868618440852459487232;"]
    );
    // Past the range of `f64` there is no nearest, and no fix.
    let errors = type_errors("f() = 0.5f64 ^ (3^(2^20));\n");
    assert_eq!(
        errors,
        ["No `f64` equals the literal `3^1048576`. [(3^(2^20))]"]
    );
}

#[test]
fn an_exponent_with_a_coefficient_is_quoted_in_parentheses() {
    // TEST-exponent-literal-coefficient-parens: an exponent literal folded to a power form with
    // a coefficient, `3*2^1100`, is quoted in parentheses (walk.rs, at `contains('*')`), so
    // that the text pasted back after `^` parses as one exponent: `x ^ 3*2^1100` would read as
    // `(x ^ 3) * 2^1100`. 3^30, held as its digits 205891132094649, prints as its power (the
    // printer finds it, `Rat::integer_text`, KEPT-power-form-print), so the form has two powers
    // and a `*`; 2^20 = 1048576.
    for (src, lit) in [
        ("(3 * 2^1100)", "(3*2^1100)"),
        ("(3^30 * 2^1100)", "(2^1100*3^30)"),
        ("(3 * 2^(2^20))", "(3*2^1048576)"),
    ] {
        let text = format!("f() = 0.5f64 ^ {src};\n");
        assert_eq!(
            type_errors(&text),
            [format!("No `f64` equals the literal `{lit}`. [{src}]")],
            "{text}"
        );
        // The quoted text pasted back is the same literal.
        let text = format!("f() = 0.5f64 ^ {lit};\n");
        assert_eq!(
            type_errors(&text),
            [format!("No `f64` equals the literal `{lit}`. [{lit}]")],
            "{text}"
        );
    }
}
