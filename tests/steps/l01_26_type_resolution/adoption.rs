//! A bare numeric literal is generic (DESIGN.md sec:domains, L1.26a, L1.26b): it takes the
//! carrier of its use, exactly or not at all. An integer literal that nothing fixes is an
//! `int`; a decimal literal is never an `int`, and one that nothing fixes is rejected with a
//! menu of the suffixed forms, as is a `/` of integer literals. A literal with a suffix, such
//! as `1r` or `0.5f64`, keeps its own carrier, and a bare one beside it takes that carrier.

use super::{info, menu, type_errors};
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
        "the literal `{d}` is a decimal, and nothing here gives it a carrier; a decimal literal \
         takes the carrier of its use, never `int`, and Zed does not choose one for it{} [{d}]",
        menu(fixes)
    )
}

/// The rejection of the decimal literal `d` where `int` is expected, with the one fix `line`,
/// which writes the integer literal `int`.
fn decimal_at_int(d: &str, line: &str, int: &str) -> String {
    format!(
        "the literal `{d}` is a decimal, and `int` is expected here; a decimal literal is never \
         an `int`, even when its value is an integer{} [{d}]",
        menu(&[(line, &format!("the literal is then the int {int}"))])
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
        [format!(
            "the `/` in the value of `q` divides integer literals, and nothing here gives them a \
             carrier; `/` has no arrow at `int`, `^` has none at `rat`, and Zed does not choose \
             `f64` for it{} [(3/2)]",
            menu(&[
                ("q = (f64(3)/2)^2;", "q is 2.25"),
                ("q = (3.0f64/2)^2;", "q is 2.25"),
            ])
        )]
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
    // writes with a carrier the literals whose carrier reaches every operation of the value.
    let why = "nothing here gives them a carrier; `/` has no arrow at `int`, and Zed does not \
               choose `f64` or `rat` for it";
    let pow = "nothing here gives them a carrier; `/` has no arrow at `int`, `^` has none at \
               `rat`, and Zed does not choose `f64` for it";
    let slash =
        |why: &str| format!("the `/` in the value of `y` divides integer literals, and {why}");
    let cases = [
        (
            "y = (1 + 2) / 3;\n",
            slash(why),
            vec![
                ("y = (f64(1) + 2) / 3;", "y is 1.0"),
                ("y = (1.0f64 + 2) / 3;", "y is 1.0"),
                ("y = (1r + 2) / 3;", "y is 1r"),
            ],
            "(1 + 2) / 3",
        ),
        (
            "y = 7 / (1 + 2);\n",
            slash(why),
            vec![
                ("y = 7 / (f64(1) + 2);", "y is 2.3333333333333335"),
                ("y = 7 / (1.0f64 + 2);", "y is 2.3333333333333335"),
                ("y = 7 / (1r + 2);", "y is 7r/3r"),
            ],
            "7 / (1 + 2)",
        ),
        (
            "y = -(1 + 2) / 3;\n",
            slash(why),
            vec![
                ("y = -(f64(1) + 2) / 3;", "y is -1.0"),
                ("y = -(1.0f64 + 2) / 3;", "y is -1.0"),
                ("y = -(1r + 2) / 3;", "y is -1r"),
            ],
            "-(1 + 2) / 3",
        ),
        (
            "y = 1 + 7 / 2;\n",
            slash(why),
            vec![
                ("y = 1 + f64(7) / 2;", "y is 4.5"),
                ("y = 1 + 7.0f64 / 2;", "y is 4.5"),
                ("y = 1 + 7r / 2;", "y is 9r/2r"),
            ],
            "7 / 2",
        ),
        // A literal in another base is offered in a cast alone; `^` gives its base's carrier.
        (
            "y = 0xFF / 2;\n",
            format!("`y = 0xFF / 2` divides two integer literals, and {why}"),
            vec![
                ("y = f64(0xFF) / 2;", "y is 127.5"),
                ("y = rat(0xFF) / 2;", "y is 255r/2r"),
            ],
            "0xFF / 2",
        ),
        (
            "y = 0xFF / 2 ^ 2;\n",
            slash(pow),
            vec![
                ("y = 0xFF / f64(2) ^ 2;", "y is 63.75"),
                ("y = 0xFF / 2.0f64 ^ 2;", "y is 63.75"),
            ],
            "0xFF / 2 ^ 2",
        ),
        // No one literal reaches both operations on literals, so each fix writes two.
        (
            "y = (1 + 2) / (3 + 4);\n",
            slash(why),
            vec![
                (
                    "y = (f64(1) + 2) / (f64(3) + 4);",
                    "y is 0.42857142857142855",
                ),
                (
                    "y = (1.0f64 + 2) / (3.0f64 + 4);",
                    "y is 0.42857142857142855",
                ),
                ("y = (1r + 2) / (3r + 4);", "y is 3r/7r"),
            ],
            "(1 + 2) / (3 + 4)",
        ),
    ];
    for (src, text, fixes, at) in &cases {
        assert_eq!(
            type_errors(src),
            [format!("{text}{} [{at}]", menu(fixes))],
            "{src}"
        );
        // Each fix checks, and the binder holds the value it names.
        for (line, holds) in fixes {
            let y = holds.strip_prefix("y is ").unwrap();
            assert_eq!(value(&format!("{line}\n"), "y"), y, "{line}");
        }
    }
    // A decimal whose suffix would not reach the operation on literals beside it gets fixes
    // that give the carrier to a literal of that operation; one whose suffix would reach
    // the rest gets the suffixed forms.
    assert_eq!(
        type_errors("y = 0.5 * (1 + 2);\n"),
        [unfixed(
            "0.5",
            &[
                ("y = 0.5 * (1.0f64 + 2);", "y is 1.5"),
                ("y = 0.5 * (1r + 2);", "y is 3r/2r"),
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
    assert_eq!(value("y = 0.5 * (1.0f64 + 2);\n", "y"), "1.5");
    assert_eq!(value("y = 0.5 * (1r + 2);\n", "y"), "3r/2r");
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
            "the literal `9007199254740993` has no exact `f64`, and `f64` is expected here; an \
             integer literal takes a carrier only where it is exact{} [9007199254740993]",
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
