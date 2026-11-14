//! A repair is offered only when the checker accepts the repaired application, so applying
//! the offered repair makes the program check.

use super::rejected;
use zedc::run::load;

/// The program `src` with the text `at` wrapped in `word(…)`.
fn wrapped(src: &str, at: &str, word: &str) -> String {
    assert_eq!(src.matches(at).count(), 1, "{at}");
    src.replace(at, &format!("{word}({at})"))
}

#[test]
fn the_offered_repair_applied_makes_the_program_check() {
    let cases = [
        (
            "main(m: MainArgs) {
  n = int(m.stdin[0]) else 0;
  m.stdout <- \"count: \" ++ n * 2;
}
",
            "n * 2",
            "String",
        ),
        (
            "price(positional cents: int) = cents * 100;
main(m: MainArgs) {
  m.stdout <- String(price(2.5));
}
",
            "2.5",
            "",
        ),
    ];
    for (src, at, word) in cases {
        let out = rejected(src);
        if word.is_empty() {
            assert!(!out.contains("repair:"), "{out}");
            continue;
        }
        let offered = format!("repair: wrap this in `{word}(…)`; the checker accepts that");
        assert!(out.contains(&offered), "{out}");
        let fixed = wrapped(src, at, word);
        load(fixed.as_bytes()).unwrap_or_else(|e| panic!("{fixed}\n{e}"));
    }
}

#[test]
fn a_conversion_that_can_fail_is_not_offered_where_its_failure_is_not_taken() {
    // `int(m.stdin[0])` is `int | #invalid | …`, and `discount` takes no `#invalid`.
    let src = "discount(price: int, tier) = if tier == #gold { price * 8 } else { price * 10 };
main(m: MainArgs) {
  p = discount(price: m.stdin[0], tier: #gold);
  m.stdout <- String(p);
}
";
    let out = rejected(src);
    assert!(!out.contains("repair: wrap this in `int"), "{out}");
    let tried = wrapped(src, "m.stdin[0]", "int");
    assert!(load(tried.as_bytes()).is_err());
    // `int("12")` always converts (item CAST-literal-exact), so the repair writes the `int` it
    // gives, `12`, in place of the cast (item REPAIR-literal-cast).
    let src = src.replace("m.stdin[0]", "\"12\"");
    let out = rejected(&src);
    assert!(
        out.contains("repair: write `12`; the checker accepts that"),
        "{out}"
    );
    assert!(!out.contains("int(\"12\")"), "{out}");
    let fixed = src.replace("\"12\"", "12");
    load(fixed.as_bytes()).unwrap_or_else(|e| panic!("{fixed}\n{e}"));
}

/// The repair the headline of `out` ends with, as in "Try `r` instead".
fn tried(out: &str) -> Option<&str> {
    let first = out.lines().next()?;
    first
        .strip_suffix("` instead.")?
        .rsplit_once("Try `")
        .map(|(_, r)| r)
}

#[test]
fn a_cast_that_cannot_fail_on_a_literal_is_written_as_the_literal_it_gives() {
    // A `main`, so that `load` checks the program; the error is in `f`.
    const MAIN: &str = "main(m: MainArgs) {\n  m.stdout <- \"a\";\n}\n";
    // (declarations before, the rejected expression, the repair its headline ends with). Each
    // repair is applied in place of the expression and must check.
    let cases = [
        ("f(positional n: int) = ", "n * \"8\"", Some("n * 8")),
        ("f(positional n: int) = ", "n * \"-12\"", Some("n * -12")),
        ("f(positional n: int) = ", "n + \"-0\"", Some("n + 0")),
        (
            "f(positional n: int) = ",
            "max(n, \"8\")",
            Some("max(n, 8)"),
        ),
        (
            "g(price: int) = price - 1;\nf() = ",
            "g(price: \"12\")",
            Some("g(price: 12)"),
        ),
        ("f() = ", "sqrt(\"2\")", Some("sqrt(2.0)")),
        ("f(positional x: f64) = ", "x * \"0.5\"", Some("x * 0.5")),
        (
            "f(positional x: f64) = ",
            "x * \"1e300\"",
            Some("x * 1.0e300"),
        ),
        // A `rat` is written with its point where that is no longer than the exponent form.
        ("f(positional r: rat) = ", "r * \"0.5\"", Some("r * 0.5r")),
        ("f(positional r: rat) = ", "r * \"0.05\"", Some("r * 0.05r")),
        ("f(positional r: rat) = ", "r * \"12.5\"", Some("r * 12.5r")),
        ("f(positional r: rat) = ", "r * \"1000\"", Some("r * 1e3r")),
        (
            "f(positional r: rat) = ",
            "r * \"-0.0001\"",
            Some("r * -1e-4r"),
        ),
        // `1/3` has no literal of its own, so the cast stays.
        (
            "f(positional r: rat) = ",
            "r * \"1/3\"",
            Some("r * rat(\"1/3\")"),
        ),
        // Text the cast rejects: the cast can fail, so no repair is offered.
        ("f(positional n: int) = ", "n * \"x8\"", None),
        ("f(positional n: int) = ", "n * \"1_000\"", None),
    ];
    for (before, expr, want) in cases {
        let out = rejected(&format!("{before}{expr};\n{MAIN}"));
        assert_eq!(tried(&out), want, "{out}");
        if let Some(fix) = want {
            let fixed = format!("{before}{fix};\n{MAIN}");
            load(fixed.as_bytes()).unwrap_or_else(|e| panic!("{fixed}\n{e}"));
        }
    }
}

/// The first repair the headline of `out` offers, as in "Try `r` to compare the numbers
/// instead".
fn first_tried(out: &str) -> Option<&str> {
    let (_, rest) = out.lines().next()?.rsplit_once("Try `")?;
    rest.split_once('`').map(|(r, _)| r)
}

#[test]
fn a_comparison_with_a_literal_is_repaired_by_the_literal_before_a_cast_of_the_other_side() {
    // Row REPAIR-compare-order. Casting the other operand to `String` would compare text,
    // which orders "10" before "8", so the literal the cast gives comes first, in both orders
    // of the operands, for the orderings and for `==` and `!=`.
    const MAIN: &str = "main(m: MainArgs) {\n  m.stdout <- \"a\";\n}\n";
    // (declarations before, the rejected expression, the first repair of its headline, and
    // whether that repair is the whole expression, applied and checked in its place).
    let cases = [
        ("f(positional n: int) = ", "n < \"8\"", Some("n < 8"), true),
        ("f(positional n: int) = ", "\"8\" < n", Some("8 < n"), true),
        (
            "f(positional n: int) = ",
            "n <= \"8\"",
            Some("n <= 8"),
            true,
        ),
        ("f(positional n: int) = ", "\"8\" > n", Some("8 > n"), true),
        (
            "f(positional n: int) = ",
            "n >= \"-12\"",
            Some("n >= -12"),
            true,
        ),
        (
            "f(positional x: f64) = ",
            "x < \"8\"",
            Some("x < 8.0"),
            true,
        ),
        (
            "f(positional x: f64) = ",
            "\"0.5\" < x",
            Some("0.5 < x"),
            true,
        ),
        // `1/3` has no literal of its own, so the cast of the literal stays, still first.
        (
            "f(positional r: rat) = ",
            "r < \"1/3\"",
            Some("r < rat(\"1/3\")"),
            true,
        ),
        // Text no number cast takes: only the cast of the other side is left.
        (
            "f(positional n: int) = ",
            "n < \"x8\"",
            Some("String(n) < \"x8\""),
            true,
        ),
        (
            "f(positional n: int) = ",
            "n == \"8\"",
            Some("n == 8"),
            true,
        ),
        (
            "f(positional n: int) = ",
            "\"8\" == n",
            Some("8 == n"),
            true,
        ),
        (
            "f(positional n: int) = ",
            "n != \"8\"",
            Some("n != 8"),
            true,
        ),
        (
            "f(positional n: int) = ",
            "\"8\" != n",
            Some("8 != n"),
            true,
        ),
        (
            "f(positional x: f64) = ",
            "x == \"0.5\"",
            Some("x == 0.5"),
            true,
        ),
        (
            "f(positional r: rat) = ",
            "r == \"0.5\"",
            Some("r == 0.5r"),
            true,
        ),
        // `1/3` has no literal of its own: the cast kept around the literal, as for `<`, in
        // both orders of the operands, for `==` and `!=` (row REPAIR-eq-kept-cast).
        (
            "f(positional r: rat) = ",
            "r == \"1/3\"",
            Some("r == rat(\"1/3\")"),
            true,
        ),
        (
            "f(positional r: rat) = ",
            "\"1/3\" == r",
            Some("rat(\"1/3\") == r"),
            true,
        ),
        (
            "f(positional r: rat) = ",
            "r != \"1/3\"",
            Some("r != rat(\"1/3\")"),
            true,
        ),
        (
            "f(positional r: rat) = ",
            "\"1/3\" != r",
            Some("rat(\"1/3\") != r"),
            true,
        ),
        // An operand with no name: the cast in place of the literal operand.
        (
            "f(positional r: rat) = ",
            "r + 1r == \"1/3\"",
            Some("rat(\"1/3\")"),
            false,
        ),
        // `1/3` is no `int`, so `int("1/3")` can fail, and no repair writes it: only the
        // comparison's one answer is left.
        (
            "f(positional n: int) = ",
            "n == \"1/3\"",
            Some("false"),
            false,
        ),
        // A literal of another number type: its literal before the cast of the name.
        ("f(positional n: int) = ", "n == 1r", Some("n == 1"), true),
        // An operand with no name: the literal in place of the literal operand.
        (
            "f(positional n: int) = ",
            "n + 1 == \"8\"",
            Some("8"),
            false,
        ),
        // Text no cast to a number writes as a literal: the comparison's one answer.
        (
            "f(positional n: int) = ",
            "n == \"x8\"",
            Some("false"),
            false,
        ),
        (
            "f(positional n: int) = ",
            "\"x8\" != n",
            Some("true"),
            false,
        ),
        // A text holding a backtick is named by its side, as a code span cannot hold it.
        (
            "f(positional n: int) = ",
            "n == \"a`b\"",
            Some("false"),
            false,
        ),
    ];
    for (before, expr, want, whole) in cases {
        let out = rejected(&format!("{before}{expr};\n{MAIN}"));
        assert_eq!(first_tried(&out), want, "{out}");
        if let Some(fix) = want.filter(|_| whole) {
            let fixed = format!("{before}{fix};\n{MAIN}");
            load(fixed.as_bytes()).unwrap_or_else(|e| panic!("{fixed}\n{e}"));
        }
    }
}

#[test]
fn a_comparison_of_an_f64_with_a_number_no_f64_writes_offers_only_its_answer() {
    // Row REPAIR-both-sides-cast. No finite `f64` is `1/3` or `1/10`, and NaN and the
    // infinities are no `rat`, so every comparison of the numbers, `rat(x) == rat("1/3")`
    // included, is always `false`: no repair keeps the meaning, and `rat(x)` could not be
    // offered anyway, as it gives `#invalid` at NaN and the infinities. The headline is the
    // answer alone, in both orders of the operands, for `==` and `!=`, and for a text, a
    // cast of a text and a `rat` literal.
    const MAIN: &str = "main(m: MainArgs) {\n  m.stdout <- \"a\";\n}\n";
    let cases = [
        (
            "x == rat(\"1/3\")",
            "No value is both `f64` and `rat`: `x : f64 == rat(\"1/3\") : rat` is always \
             `false`. Try `false` instead.",
        ),
        (
            "rat(\"1/3\") == x",
            "No value is both `rat` and `f64`: `rat(\"1/3\") : rat == x : f64` is always \
             `false`. Try `false` instead.",
        ),
        (
            "x != rat(\"1/3\")",
            "No value is both `f64` and `rat`: `x : f64 != rat(\"1/3\") : rat` is always \
             `true`. Try `true` instead.",
        ),
        (
            "x == \"1/3\"",
            "No value is both `f64` and `String`: `x : f64 == \"1/3\" : String` is always \
             `false`. Try `false` instead.",
        ),
        (
            "\"1/3\" != x",
            "No value is both `String` and `f64`: `\"1/3\" : String != x : f64` is always \
             `true`. Try `true` instead.",
        ),
        (
            "x == rat(\"0.1\")",
            "No value is both `f64` and `rat`: `x : f64 == rat(\"0.1\") : rat` is always \
             `false`. Try `false` instead.",
        ),
        (
            "x == 0.1r",
            "No value is both `f64` and `rat`: `x : f64 == 0.1r : rat` is always `false`. \
             Try `false` instead.",
        ),
    ];
    for (expr, want) in cases {
        let out = rejected(&format!("f(positional x: f64) = {expr};\n{MAIN}"));
        let first = out.lines().next().unwrap_or("");
        assert!(first.ends_with(want), "{out}");
        assert!(
            !out.contains("rat(x)") && !out.contains("f64(rat"),
            "no cast of `x` and no cast around the cast: {out}"
        );
    }
}

#[test]
fn a_comparison_with_a_cast_of_a_literal_is_repaired_by_the_literal_its_value_has() {
    // Row REPAIR-both-sides-cast. An operand that is a number cast of a literal is one
    // number; where a literal of the other side's type writes it exactly, that literal in
    // its place keeps the comparison's meaning and comes first, as for a text operand. Where
    // none does, no cast is wrapped around the cast.
    const MAIN: &str = "main(m: MainArgs) {\n  m.stdout <- \"a\";\n}\n";
    let cases = [
        ("f(positional x: f64) = ", "x == rat(\"1/2\")", "x == 0.5"),
        ("f(positional x: f64) = ", "rat(\"1/2\") != x", "0.5 != x"),
        ("f(positional x: f64) = ", "x == rat(-2)", "x == -2.0"),
        ("f(positional x: f64) = ", "x == rat(0.5r)", "x == 0.5"),
        ("f(positional x: f64) = ", "x == int(\"3\")", "x == 3.0"),
        ("f(positional n: int) = ", "n == rat(\"8\")", "n == 8"),
        ("f(positional n: int) = ", "rat(\"8\") == n", "8 == n"),
        ("f(positional n: int) = ", "n == f64(-3)", "n == -3"),
        ("f(positional r: rat) = ", "r == f64(\"0.5\")", "r == 0.5r"),
        // No `int` is `1/3`: the cast of the name, `rat(n)`, cannot fail and is offered.
        (
            "f(positional n: int) = ",
            "n == rat(\"1/3\")",
            "rat(n) == rat(\"1/3\")",
        ),
        // No `int` is `2.5`, and `f64(n)` can lose digits: the answer alone.
        ("f(positional n: int) = ", "n == f64(2.5f64)", "false"),
    ];
    for (before, expr, want) in cases {
        let out = rejected(&format!("{before}{expr};\n{MAIN}"));
        assert_eq!(first_tried(&out), Some(want), "{out}");
        assert!(
            !out.contains("rat(rat") && !out.contains("f64(rat"),
            "{out}"
        );
        if want != "false" {
            let fixed = format!("{before}{want};\n{MAIN}");
            load(fixed.as_bytes()).unwrap_or_else(|e| panic!("{fixed}\n{e}"));
        }
    }
}

#[test]
fn an_ordering_with_a_text_written_as_a_number_offers_no_comparison_of_texts() {
    // Row REPAIR-string-compare-offer. `String(x) < "1/3"` compares the two texts character by
    // character, not the numbers, so it would change what the program means: it is never
    // offered where the text reads as a number, whichever side the text is on, for each
    // ordering. For `x : f64` no repair keeps the meaning: no `f64` literal is `1/3`, `rat(x)`
    // gives `#invalid` at NaN and the infinities, and `f64("1/3")` rounds. The headline then
    // ends with no repair.
    const MAIN: &str = "main(m: MainArgs) {\n  m.stdout <- \"a\";\n}\n";
    for op in ["<", "<=", ">", ">="] {
        for text in ["\"1/3\"", "\"1e999\"", "\"-2/7\"", "\"14/6\""] {
            for expr in [format!("x {op} {text}"), format!("{text} {op} x")] {
                let out = rejected(&format!("f(positional x: f64) = {expr};\n{MAIN}"));
                assert_eq!(first_tried(&out), None, "{expr}\n{out}");
                assert!(!out.contains("String("), "{expr}\n{out}");
            }
        }
    }
    // Where a literal keeps the meaning, it is offered alone, with no comparison of texts after
    // it in the menu.
    let cases = [
        ("f(positional n: int) = ", "n < \"8\"", Some("n < 8")),
        ("f(positional n: int) = ", "\"8\" >= n", Some("8 >= n")),
        ("f(positional x: f64) = ", "x <= \"0.5\"", Some("x <= 0.5")),
        ("f(positional x: f64) = ", "\"-0\" > x", Some("-0.0 > x")),
        (
            "f(positional r: rat) = ",
            "r < \"1/3\"",
            Some("r < rat(\"1/3\")"),
        ),
        (
            "f(positional r: rat) = ",
            "\"1/3\" > r",
            Some("rat(\"1/3\") > r"),
        ),
        // No `int` is `1/3` and `n` has no cast that keeps it and meets the text: no repair.
        ("f(positional n: int) = ", "n < \"1/3\"", None),
        ("f(positional n: int) = ", "\"1/3\" <= n", None),
    ];
    for (before, expr, want) in cases {
        let out = rejected(&format!("{before}{expr};\n{MAIN}"));
        assert_eq!(first_tried(&out), want, "{out}");
        assert!(!out.contains("String("), "{out}");
        if let Some(fix) = want {
            let fixed = format!("{before}{fix};\n{MAIN}");
            load(fixed.as_bytes()).unwrap_or_else(|e| panic!("{fixed}\n{e}"));
        }
    }
    // A text no number cast reads is compared as text, so the cast of the other side to text
    // keeps the program's meaning and stays offered, in both orders.
    for (expr, want) in [
        ("x < \"x8\"", "String(x) < \"x8\""),
        ("\"x8\" >= x", "\"x8\" >= String(x)"),
    ] {
        let out = rejected(&format!("f(positional x: f64) = {expr};\n{MAIN}"));
        assert_eq!(first_tried(&out), Some(want), "{out}");
    }
}
