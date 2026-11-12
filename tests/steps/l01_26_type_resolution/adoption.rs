//! A bare numeric literal is generic (DESIGN.md sec:domains, L1.26a, L1.26b): it takes the
//! carrier of its use, exactly or not at all. An integer literal that nothing fixes is an
//! `int`; a decimal literal is never an `int`, and one that nothing fixes is rejected with a
//! menu of the suffixed forms, as is a `/` of integer literals. A literal with a suffix, such
//! as `1r` or `0.5f64`, keeps its own carrier, and a bare one beside it takes that carrier.

use super::{info, menu, tried, type_errors};
use zed_kernel::{F64, Value};
use zed_tests::step_helpers::l01_16_elaboration::value;

/// The values the literals of `text` adopt, sorted by position.
fn adopted(text: &str) -> Vec<Value> {
    let (i, _) = info(text);
    let mut v: Vec<_> = i.adopt.into_iter().collect();
    v.sort_by_key(|(s, _)| s.start);
    v.into_iter().map(|(_, x)| x).collect()
}

/// The rejection of the decimal literal `d` that nothing gives a carrier, whose fixes are
/// `fixes`, each a corrected line and what the program then holds.
fn unfixed(d: &str, fixes: &[(&str, &str)]) -> String {
    format!(
        "Nothing gives the literal `{d}` a carrier{}{} [{d}]",
        tried(fixes),
        menu(fixes)
    )
}

/// The rejection of the decimal literal `d` where `int` is expected, with the one fix `line`,
/// which writes the integer literal `int`.
fn decimal_at_int(d: &str, line: &str, int: &str) -> String {
    let fixes = [(line, &*format!("the literal is then the int {int}"))];
    format!(
        "A decimal literal is never an `int`, even with an integer value: the literal `{d}`{}{} [{d}]",
        tried(&fixes),
        menu(&fixes)
    )
}

#[test]
fn an_integer_literal_beside_a_float_takes_its_carrier() {
    // `1 + taxRate` with `taxRate: f64` is the case generic literals are for.
    let gross = "gross(positional net: f64, positional taxRate: f64) = net * (1 + taxRate);\n";
    assert!(type_errors(gross).is_empty());
    assert_eq!(
        value(&format!("{gross}y = gross(200.0, 0.25);\n"), "y"),
        "250.0"
    );
    assert_eq!(
        adopted(gross),
        [Value::Float(F64::new(1.0))],
        "`1` takes `f64` from `taxRate`"
    );
}

#[test]
fn a_power_with_a_decimal_that_nothing_fixes_is_rejected_with_f64_alone() {
    // `^` has no arrow at `rat`, so the menu offers `f64` alone.
    assert_eq!(
        type_errors("root2 = 2^0.5;\n"),
        [unfixed(
            "0.5",
            &[("root2 = 2^0.5f64;", "root2 is 1.4142135623730951")]
        )]
    );
    assert_eq!(
        type_errors("x = 0.5^2;\n"),
        [unfixed("0.5", &[("x = 0.5f64^2;", "x is 0.25")])]
    );
    assert_eq!(
        type_errors("q = (3/2)^2;\n"),
        [{
            let fixes = [
                ("q = (3.0f64/2)^2;", "q is 2.25"),
                ("q = (f64(3)/2)^2;", "q is 2.25"),
            ];
            format!(
                "Nothing gives the integer literals a carrier, `/` has none at `int`, and `^` none \
                 at `rat`: `q = (3/2)^2`{}{} [(3/2)]",
                tried(&fixes),
                menu(&fixes)
            )
        }]
    );
    // Each repair checks: the bare `2` takes `f64` from the suffixed decimal.
    assert_eq!(value("root2 = 2^0.5f64;\n", "root2"), "1.4142135623730951");
    assert_eq!(value("x = 0.5f64^2;\n", "x"), "0.25");
    assert_eq!(value("q = (f64(3)/2)^2;\n", "q"), "2.25");
    assert_eq!(value("q = (3.0f64/2)^2;\n", "q"), "2.25");
    // An integer power of integer literals is an `int`.
    assert_eq!(value("p = 2^3;\n", "p"), "8");
}

#[test]
fn a_slash_among_operations_on_literals_is_rejected_once_at_the_literal_that_fixes_it() {
    // At the top level an operation on two literals that meets no carrier is an `int`, as
    // `1 + 2` is in `(1 + 2) / 3`. The value is rejected once, at its `/`, and each fix
    // writes the first literal of the value with a carrier, the suffixed forms before the
    // cast; an operation on literals alone takes the carrier of what it meets, so it reaches
    // the rest, a `/` of two literals and the base and literal exponent of a `^` among them,
    // and every fix checks. DESIGN.md sec:diagnostics, "A `/` of integer literals": "the menu
    // writes the carrier at the first literal of the value":
    //   q = (1.0f64 + 2) / (3 + 4);    q is 0.42857142857142855
    //   q = (1r + 2) / (3 + 4);        q is 3r/7r
    //   q = (f64(1) + 2) / (3 + 4);    q is 0.42857142857142855
    // Each headline quotes the binding, the value being the whole of it.
    let why = "Nothing gives the integer literals a carrier, and `/` has none at `int`";
    let pow = "Nothing gives the integer literals a carrier, `/` has none at `int`, and `^` none \
               at `rat`";
    let slash = |why: &str| why.to_string();
    let cases = [
        (
            "y = (1 + 2) / 3;\n",
            slash(why),
            vec![
                ("y = (1.0f64 + 2) / 3;", "y is 1.0"),
                ("y = (1r + 2) / 3;", "y is 1r"),
                ("y = (f64(1) + 2) / 3;", "y is 1.0"),
            ],
            "(1 + 2) / 3",
        ),
        (
            "y = 7 / (1 + 2);\n",
            slash(why),
            vec![
                ("y = 7.0f64 / (1 + 2);", "y is 2.3333333333333335"),
                ("y = 7r / (1 + 2);", "y is 7r/3r"),
                ("y = f64(7) / (1 + 2);", "y is 2.3333333333333335"),
            ],
            "7 / (1 + 2)",
        ),
        (
            "y = -(1 + 2) / 3;\n",
            slash(why),
            vec![
                ("y = -(1.0f64 + 2) / 3;", "y is -1.0"),
                ("y = -(1r + 2) / 3;", "y is -1r"),
                ("y = -(f64(1) + 2) / 3;", "y is -1.0"),
            ],
            "-(1 + 2) / 3",
        ),
        (
            "y = 1 + 7 / 2;\n",
            slash(why),
            vec![
                // The carrier of `1` reaches `7 / 2`, which meets it at the `+`.
                ("y = 1.0f64 + 7 / 2;", "y is 4.5"),
                ("y = 1r + 7 / 2;", "y is 9r/2r"),
                ("y = f64(1) + 7 / 2;", "y is 4.5"),
            ],
            "7 / 2",
        ),
        // A literal in another base is offered in a cast alone, at `f64` and then `rat`.
        (
            "y = 0xFF / 2;\n",
            slash(why),
            vec![
                ("y = f64(0xFF) / 2;", "y is 127.5"),
                ("y = rat(0xFF) / 2;", "y is 255r/2r"),
            ],
            "0xFF / 2",
        ),
        (
            "y = 0xFF / 2 ^ 2;\n",
            slash(pow),
            // `2 ^ 2` meets `f64(0xFF)` at the `/` and takes its carrier, so only `0xFF` is
            // written, and in a cast alone.
            vec![("y = f64(0xFF) / 2 ^ 2;", "y is 63.75")],
            "0xFF / 2 ^ 2",
        ),
        (
            "y = 1 + 2 ^ 2 / 3;\n",
            slash(pow),
            vec![
                ("y = 1.0f64 + 2 ^ 2 / 3;", "y is 2.333333333333333"),
                ("y = f64(1) + 2 ^ 2 / 3;", "y is 2.333333333333333"),
            ],
            "2 ^ 2 / 3",
        ),
        // One carrier reaches both `/` of two literals: they meet at the outer `/`.
        (
            "y = (1 / 2) / (3 / 4);\n",
            slash(why),
            vec![
                ("y = (1.0f64 / 2) / (3 / 4);", "y is 0.6666666666666666"),
                ("y = (1r / 2) / (3 / 4);", "y is 2r/3r"),
                ("y = (f64(1) / 2) / (3 / 4);", "y is 0.6666666666666666"),
            ],
            "(1 / 2) / (3 / 4)",
        ),
        (
            "y = (1 + 2) / (3 + 4) + 7 / 2;\n",
            slash(why),
            vec![
                (
                    "y = (1.0f64 + 2) / (3 + 4) + 7 / 2;",
                    "y is 3.9285714285714284",
                ),
                ("y = (1r + 2) / (3 + 4) + 7 / 2;", "y is 55r/14r"),
                (
                    "y = (f64(1) + 2) / (3 + 4) + 7 / 2;",
                    "y is 3.9285714285714284",
                ),
            ],
            "(1 + 2) / (3 + 4)",
        ),
        // DESIGN's example: the suffix on the first literal alone reaches both sums.
        (
            "y = (1 + 2) / (3 + 4);\n",
            slash(why),
            vec![
                ("y = (1.0f64 + 2) / (3 + 4);", "y is 0.42857142857142855"),
                ("y = (1r + 2) / (3 + 4);", "y is 3r/7r"),
                ("y = (f64(1) + 2) / (3 + 4);", "y is 0.42857142857142855"),
            ],
            "(1 + 2) / (3 + 4)",
        ),
    ];
    for (src, text, fixes, at) in &cases {
        assert_eq!(
            type_errors(src),
            [format!(
                "{text}: `{}`{}{} [{at}]",
                src.trim_end().trim_end_matches(';'),
                tried(fixes),
                menu(fixes)
            )],
            "{src}"
        );
        // Each fix checks, and the binder holds the value it names.
        for (line, holds) in fixes {
            let y = holds.strip_prefix("y is ").unwrap();
            assert_eq!(value(&format!("{line}\n"), "y"), y, "{line}");
        }
    }
    // The suffix on the decimal reaches the operation on literals beside it, which takes the
    // carrier it meets (DESIGN.md step L1.26b: "`y = 0.5f64 * (1 + 2)` is `1.5`").
    assert_eq!(
        type_errors("y = 0.5 * (1 + 2);\n"),
        [unfixed(
            "0.5",
            &[
                ("y = 0.5f64 * (1 + 2);", "y is 1.5"),
                ("y = 0.5r * (1 + 2);", "y is 3r/2r"),
            ]
        )]
    );
    assert_eq!(
        type_errors("y = 2 * 0.5;\n"),
        [unfixed(
            "0.5",
            &[
                ("y = 2 * 0.5f64;", "y is 1.0"),
                ("y = 2 * 0.5r;", "y is 1r")
            ]
        )]
    );
    // The suffix on the decimal reaches the `/` of two integer literals beside it too: an
    // operation on literals alone is an `int` only where nothing at all gives it a carrier.
    assert_eq!(
        type_errors("y = 0.5 * (7 / 2);\n"),
        [unfixed(
            "0.5",
            &[
                ("y = 0.5f64 * (7 / 2);", "y is 1.75"),
                ("y = 0.5r * (7 / 2);", "y is 7r/4r"),
            ]
        )]
    );
    assert_eq!(value("y = 0.5f64 * (7 / 2);\n", "y"), "1.75");
    assert_eq!(value("y = 0.5r * (7 / 2);\n", "y"), "7r/4r");
    assert_eq!(value("y = 0.5f64 * (1 + 2);\n", "y"), "1.5");
    assert_eq!(value("y = 0.5r * (1 + 2);\n", "y"), "3r/2r");
    assert_eq!(value("y = 2 * 0.5f64;\n", "y"), "1.0");
    assert_eq!(value("y = 2 * 0.5r;\n", "y"), "1r");
}

#[test]
fn a_literal_argument_takes_its_parameter_carrier() {
    let quarter = "quarter(positional x: f64) = x / 4;\n";
    assert_eq!(value(&format!("{quarter}y = quarter(2);\n"), "y"), "0.5");
    let f = "f(positional x: f64) = x;\n";
    assert_eq!(value(&format!("{f}y = f(4);\n"), "y"), "4.0");
    assert_eq!(
        adopted(&format!("{f}y = f(4);\n")),
        [Value::Float(F64::new(4.0))]
    );
    // Within a body the literal leaves the carrier open: `x / 2` takes `f64` or `rat`, the
    // carriers `/` has.
    let half = "half(x) = x / 2;\n";
    assert!(type_errors(half).is_empty());
    assert_eq!(value(&format!("{half}y = half(x: 3.0f64);\n"), "y"), "1.5");
    assert_eq!(value(&format!("{half}y = half(x: 3r);\n"), "y"), "3r/2r");
}

#[test]
fn an_integer_literal_that_cannot_take_a_carrier_exactly_is_an_error() {
    // 2^53 + 1 has no f64, so the literal is rejected, not rounded.
    let f = "f(positional x: f64) = x;\n";
    assert_eq!(
        type_errors(&format!("{f}y = f(9007199254740993);\n")),
        [format!(
            "No `f64` equals the literal `9007199254740993`. Try `y = f(9007199254740992)` \
             instead.{} [9007199254740993]",
            menu(&[(
                "y = f(9007199254740992);",
                "the literal is then 9007199254740992.0, the nearer f64 by ties to even"
            )])
        )]
    );
    assert_eq!(
        value(&format!("{f}y = f(9007199254740992);\n"), "y"),
        "9007199254740992.0"
    );
}

#[test]
fn a_decimal_literal_never_becomes_an_int() {
    assert_eq!(
        type_errors("f(positional x: int) = x;\ny = f(2.0);\n"),
        [decimal_at_int("2.0", "y = f(2);", "2")]
    );
    assert_eq!(
        type_errors("x = 7 div 2.0;\n"),
        [decimal_at_int("2.0", "x = 7 div 2;", "2")]
    );
    // Each fix checks.
    assert_eq!(value("f(positional x: int) = x;\ny = f(2);\n", "y"), "2");
    assert_eq!(value("x = 7 div 2;\n", "x"), "3");
}

#[test]
fn a_bare_literal_beside_a_suffixed_one_takes_its_carrier() {
    assert!(type_errors("x = 1r + 1;\n").is_empty());
    assert_eq!(value("x = 1r + 1;\n", "x"), "2r");
    assert_eq!(
        adopted("x = 1r + 1;\n"),
        [Value::rat(zed_kernel::Rat::decimal("1").unwrap().unwrap())]
    );
    assert!(adopted("x = 1r + 2r;\n").is_empty());
}

#[test]
fn equality_takes_two_values_of_one_carrier() {
    // A divisor that cannot be zero adds no `#divByZero`, so the quotient passes as a rat.
    assert!(type_errors("f(positional x: rat) = x;\ny = f(3r/2r);\n").is_empty());
    // A divisor that may be zero adds `#divByZero`, a loose atom, which passes through `f`.
    assert!(
        type_errors(
            "f(positional x: int) = x;\nwhole(positional v: int) = v;\ny = f(7 div whole(0));\n"
        )
        .is_empty()
    );
    assert_eq!(
        value(
            "f(positional x: int) = x;\nwhole(positional v: int) = v;\ny = f(7 div whole(0));\n",
            "y"
        ),
        "#divByZero"
    );
    // `1 == 1.0` fixes neither literal: the decimal is rejected with its menu.
    assert_eq!(
        type_errors("y = 1 == 1.0;\n"),
        [unfixed(
            "1.0",
            &[
                ("y = 1 == 1.0f64;", "y is true"),
                ("y = 1 == 1.0r;", "y is true")
            ]
        )]
    );
    assert_eq!(value("y = 1 == 1.0f64;\n", "y"), "true");
    // Beside a rat a decimal takes `rat`, exactly.
    assert_eq!(value("y = 1.5 == 3r/2r;\n", "y"), "true");
    assert_eq!(value("y = 1 == 1r;\n", "y"), "true");
    assert_eq!(value("y = 1 == 1;\n", "y"), "true");
}

#[test]
fn a_test_row_at_a_decimal_needs_a_carrier() {
    // `x * 2` leaves `double` generic, so a row's decimal argument is fixed by nothing.
    let rows = |arg: &str| format!("double(x) = x * 2\ntest {{\n  3 -> 6,\n  {arg} -> 3.0,\n}}\n");
    assert_eq!(
        type_errors(&rows("1.5")),
        [unfixed(
            "1.5",
            &[
                ("1.5f64 -> 3.0,", "the literal is then the f64 1.5"),
                ("1.5r -> 3.0,", "the literal is then exactly 1.5, a rat"),
            ]
        )]
    );
    assert!(type_errors(&rows("1.5f64")).is_empty());
    assert!(type_errors(&rows("1.5r")).is_empty());
}

#[test]
fn a_decimal_at_rat_is_exact() {
    let price = "price(positional p: rat) = p;\n";
    assert_eq!(value(&format!("{price}x = price(0.1);\n"), "x"), "1r/10r");
    assert_eq!(value("x = 1r + 0.1;\n", "x"), "11r/10r");
    // Exact as a rat, so neither rounds: beyond the f64 range is no error there.
    assert_eq!(type_errors("x = 1r + 1e-400;\n"), Vec::<String>::new());
    assert_eq!(type_errors("x = 1r + 1e400r;\n"), Vec::<String>::new());
}

#[test]
fn a_decimal_literal_at_f64_rounds_to_the_nearest() {
    // `0.1` has no exact f64; at `f64` a decimal literal rounds to the nearest.
    let f = "f(positional x: f64) = x;\n";
    assert_eq!(value(&format!("{f}y = f(0.1);\n"), "y"), "0.1");
    assert_eq!(
        value(&format!("{f}y = f(9007199254740992.0);\n"), "y"),
        "9007199254740992.0"
    );
}
