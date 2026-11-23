//! A `/` or a `^` of literals alone, and a component of a tuple that is an operation on
//! literals alone, takes the carrier of what it meets, as `+`, `-` and `*` of literals do.
//! DESIGN.md sec:diagnostics, "A `/` of integer literals": "Neither side is typed on its own
//! as an `int` before it meets the `/`: an operation on literals alone is an `int` only where
//! nothing at all gives it a carrier." Step L1.26a: "An operation on literals alone, as
//! `2 + 1` or `-1`, is a literal too and takes the carrier of what it meets".

use super::fixes::{checked, pairs};
use zed_tests::step_helpers::l01_16_elaboration::value;
use zed_tests::step_helpers::l01_26_type_resolution::{sig, type_errors};

/// The value of `y` in `src`, which the checker accepts.
fn y(src: &str) -> String {
    assert_eq!(type_errors(src), Vec::<String>::new(), "{src}");
    value(src, "y")
}

/// The first line of the one rejection of `src`, without the ` [text]` the helper adds.
fn first(src: &str) -> String {
    let errors = type_errors(src);
    assert_eq!(errors.len(), 1, "{src}: {errors:?}");
    let message = errors[0].rsplit_once(" [").unwrap().0;
    message.lines().next().unwrap().to_string()
}

#[test]
fn a_division_of_literals_takes_the_carrier_it_meets() {
    // "an operation on literals alone is an `int` only where nothing at all gives it a
    // carrier": `7 / 2` meets `1.0f64` under `+`, so it is an `f64`, the carrier on the left
    // or on the right.
    assert_eq!(y("y = 1.0f64 + 7 / 2;\n"), "4.5");
    assert_eq!(y("y = 7 / 2 + 1.0f64;\n"), "4.5");
    assert_eq!(y("y = (1 + 2) / (3 + 4) + 1.0f64;\n"), "1.4285714285714286");
    assert_eq!(y("y = 1.0f64 + (1 + 2) / (3 + 4);\n"), "1.4285714285714286");
    // A `rat` reaches it the same way, and a name of one carrier as a literal does.
    assert_eq!(y("y = 1r + 7 / 2;\n"), "9r/2r");
    assert_eq!(y("y = (1 + 2) / (3 + 4) - 1r;\n"), "-4r/7r");
    assert_eq!(y("x = 0.5f64;\ny = x * (7 / 2);\n"), "1.75");
    // A `/` nested in a `/`, and a `-` of one.
    assert_eq!(y("y = 1.0f64 + (7 / 2) / (1 / 4);\n"), "15.0");
    assert_eq!(y("y = (1 / 2) / (1 / 4) * 1r;\n"), "2r");
    assert_eq!(y("y = -(7 / 2) + 1.0f64;\n"), "-2.5");
    // A comparison gives its other side's carrier too.
    assert_eq!(y("y = 7 / 2 == 3.5f64;\n"), "true");
    assert_eq!(y("y = 4.0f64 > 7 / 2;\n"), "true");
    // A `+` of a decimal and an integer literal meets the carrier the same way.
    assert_eq!(y("y = 1.0f64 + (2 + 0.5);\n"), "3.5");
}

#[test]
fn a_power_of_literals_takes_the_carrier_it_meets() {
    // DESIGN.md sec:lexical, the operator table's row for `^`: "`^` takes the integer or the
    // floating-point power by the types of its operands". `2 ^ 3` meets `1.0f64`, so both its
    // literals are `f64`.
    assert_eq!(y("y = 1.0f64 + 2 ^ 3;\n"), "9.0");
    assert_eq!(y("y = 2 ^ 3 * 0.5f64;\n"), "4.0");
    // At `f64` a negative exponent is a power like any other.
    assert_eq!(y("y = 1.0f64 + 2 ^ -1;\n"), "1.5");
    assert_eq!(y("y = (2 ^ 3) / (1 + 1) + 0.5f64;\n"), "4.5");
    // With nothing to give a carrier, `^` of integer literals is the `int` power.
    assert_eq!(y("y = 1 + 2 ^ 3;\n"), "9");
    assert_eq!(y("y = 2 ^ 3;\n"), "8");
}

#[test]
fn where_nothing_gives_a_carrier_the_menu_writes_the_first_literal() {
    // "A `/` of integer literals": "the menu writes the carrier at the first literal of the
    // value". The carrier written at `1` reaches the `/` through the `+`.
    let src = "y = 1 + 7 / 2;\n";
    assert_eq!(
        first(src),
        "Nothing gives the integer literals a carrier, and `/` has none at `int`: `y = 1 + 7 / 2`. \
         Try `y = 1r + 7 / 2` instead."
    );
    assert_eq!(
        checked(src),
        pairs(&[
            ("y = 1r + 7 / 2;", "y is 9r/2r"),
            ("y = 1.0 + 7 / 2;", "y is 4.5"),
            ("y = f64(1) + 7 / 2;", "y is 4.5"),
        ])
    );
    // A decimal gives its carrier to the `/` it meets: `f64` where nothing fixes it (author
    // decision 2026-11-12), or the carrier of its suffix.
    assert_eq!(y("y = 0.5 * (7 / 2);\n"), "1.75");
    assert_eq!(y("y = 0.5f64 * (7 / 2);\n"), "1.75");
    assert_eq!(y("y = 0.5r * (7 / 2);\n"), "7r/4r");
    // A `^` whose exponent is an integer literal takes `rat` too, by its arrow (rat, int): the
    // exponent keeps `int` while the base takes `rat` (POW-rat-literal-ops).
    assert_eq!(
        checked("y = 2 ^ 3 / 2;\n"),
        pairs(&[
            ("y = 2r ^ 3 / 2;", "y is 2r ^ 3 / 2"),
            ("y = 2.0 ^ 3 / 2;", "y is 4.0"),
            ("y = f64(2) ^ 3 / 2;", "y is 4.0"),
        ])
    );
    assert_eq!(
        checked("y = 1 + 2 ^ 3 / 2;\n"),
        pairs(&[
            ("y = 1r + 2 ^ 3 / 2;", "y is 1r + 2 ^ 3 / 2"),
            ("y = 1.0 + 2 ^ 3 / 2;", "y is 5.0"),
            ("y = f64(1) + 2 ^ 3 / 2;", "y is 5.0"),
        ])
    );
}

#[test]
fn a_tuple_comparison_gives_a_component_its_carrier() {
    // Step L1.26a: "two tuples compare component by component, each pair under this rule",
    // and "An operation on literals alone [...] takes the carrier of what it meets": in
    // `(1 + 2, 0) == (3.0f64, 0)`, `1 + 2` meets `3.0f64`.
    assert_eq!(y("y = (1 + 2, 0) == (3.0f64, 0);\n"), "true");
    assert_eq!(y("y = (3.0f64, 0) == (1 + 2, 0);\n"), "true");
    assert_eq!(y("y = (1 + 2, 0) != (3.0f64, 0);\n"), "false");
    assert_eq!(y("y = (7 / 2, 0) == (3.5f64, 0);\n"), "true");
    assert_eq!(y("y = (2 ^ 2, 0) == (4.0f64, 0);\n"), "true");
    assert_eq!(y("y = (0, (1 + 2, 1)) == (0, (3r, 1));\n"), "true");
    assert_eq!(y("x = 3.0f64;\ny = (1 + 2, 0) == (x, 0);\n"), "true");
    // With nothing to give a carrier the component is an `int`.
    assert_eq!(y("y = (1 + 2, 0) == (3, 0);\n"), "true");
}

#[test]
fn a_tuple_menu_names_the_value_where_a_pair_is_an_operation() {
    // A decimal in a tuple comparison is an `f64` where nothing fixes it (author decision
    // 2026-11-12), and gives its carrier to the operation in the other component.
    assert_eq!(y("y = (1 + 2, 0.5) == (3.0f64, 1);\n"), "false");
    assert_eq!(y("y = (1 + 2, 0.5) == (3r, 0.5);\n"), "true");
    assert_eq!(y("y = (1 + 0.5, 0) == (2.5, 0);\n"), "false");
    // DESIGN.md step L1.26b: an operation on literals alone with a decimal among its operands
    // takes `f64` where nothing fixes its carrier, and `1 == 1.0` is `true`; step L1.26a: an
    // operation on literals alone "takes the carrier of what it meets". So `2 + 1` meets the
    // `f64` `1 + 0.5` and `y` is `false`. This zedc keeps `2 + 1` at `int` and rejects the
    // comparison as always `false`, as it does `y = 1 + 0.5 == 2 + 1;` and `2^0.5 == 1 + 1`
    // (`top_body_agree::a_comparison_of_an_f64_with_an_int_is_rejected_in_every_place`); row
    // LIT-f64-op-meets-int-op.
    assert_eq!(
        type_errors("y = (1 + 0.5, 0) == (2 + 1, 0);\n"),
        [
            "No value is both `f64` and `int`: component `[0]` of the left operand compared by \
             `==` with component `[0]` of the right operand is always `false`. Try `false` \
             instead. [(1 + 0.5, 0) == (2 + 1, 0)]"
        ]
    );
    // sec:diagnostics, "The value a fix names": the binder is named "where the binder's value
    // is the literal, or an operation on literals alone", as `y = (3^2 + 1, 1 / 2) == (10, 1 /
    // 2);` has `y is (3r^2 + 1, 1 / 2) == (10, 1 / 2)`: one rejection, whose every fix names
    // `y`. `1 + 2` takes the carrier of `3.0f64` in its pair, and the `/` of integer literals
    // in the other pair has none; the one pair that holds a `/` is the one the fix writes in
    // (plan rows LIT-tuple-compare-names-literal, LIT-tuple-compare-power-menu).
    let fixes = [
        "y = (1 + 2, 1r / 2) == (3.0f64, 1);",
        "y = (1 + 2, 1.0 / 2) == (3.0f64, 1);",
        "y = (1 + 2, f64(1) / 2) == (3.0f64, 1);",
    ];
    assert_eq!(
        checked("y = (1 + 2, 1 / 2) == (3.0f64, 1);\n"),
        fixes.map(|f| (f.to_string(), "y is false".to_string()))
    );
    for fix in fixes {
        assert_eq!(y(&format!("{fix}\n")), "false", "{fix}");
    }
    // A `/` in each component of one pair: the fix writes the first, and the second meets
    // its carrier, the `f64` of `1.0` too (DESIGN.md step L1.26b); one rejection.
    let fixes = [
        "y = (1 + 2, 1r / 2) == (3r, 1 / 2);",
        "y = (1 + 2, 1.0 / 2) == (3r, 1 / 2);",
        "y = (1 + 2, f64(1) / 2) == (3r, 1 / 2);",
    ];
    assert_eq!(
        checked("y = (1 + 2, 1 / 2) == (3r, 1 / 2);\n"),
        fixes.map(|f| (f.to_string(), "y is true".to_string()))
    );
    for fix in fixes {
        assert_eq!(y(&format!("{fix}\n")), "true", "{fix}");
    }
    // One rejection, the `1`, where the comparison of `f64` with `int` was rejected too: the
    // `/` has no carrier, so neither side is an `f64`.
    let fixes = [
        "y = (1r + 1 / 2, 0) == (2 + 1, 0);",
        "y = (1.0 + 1 / 2, 0) == (2 + 1, 0);",
        "y = (f64(1) + 1 / 2, 0) == (2 + 1, 0);",
    ];
    let errors = type_errors("y = (1 + 1 / 2, 0) == (2 + 1, 0);\n");
    assert_eq!(errors.len(), 1, "{errors:?}");
    for fix in fixes {
        assert!(
            errors[0]
                .lines()
                .any(|l| l.trim_start().starts_with(fix) && l.contains("  y is false")),
            "{fix}: {errors:?}"
        );
    }
    assert_eq!(y(&format!("{}\n", fixes[0])), "false");
    assert_eq!(y(&format!("{}\n", fixes[2])), "false");
    // The menu names `false` for the `1.0` fix, the value DESIGN gives, but this zedc keeps
    // `2 + 1` at `int` beside the `f64` `1.0 + 1 / 2` and rejects that fix, as it rejects
    // `y = 1.0 + 1 / 2 == 2 + 1;`, whose own menu lists it too; row LIT-f64-op-meets-int-op,
    // whose fix makes this `false`.
    assert!(
        type_errors(&format!("{}\n", fixes[1]))[0].starts_with("No value is both `f64` and `int`"),
        "{}",
        fixes[1]
    );
}

#[test]
fn a_menu_writes_the_exponent_of_a_power_that_its_carrier_does_not_reach() {
    // "the menu writes the carrier at the first literal of the value": the carrier of `2`
    // reaches the `/` and the base of `^`, but not its exponent, since `^` has no arrow that
    // takes an `f64` and an `int`, so the exponent's first literal is written too. At `rat`
    // the exponent, an operation on integer literals alone, keeps `int` as one integer literal
    // does, and is left as it is (plan row LIT-rat-int-op-exponent).
    let src = "y = 2 ^ (1 + 1) / 2;\n";
    assert_eq!(
        checked(src),
        pairs(&[
            ("y = 2r ^ (1 + 1) / 2;", "y is 2r ^ (1 + 1) / 2"),
            ("y = 2.0 ^ (1.0 + 1) / 2;", "y is 2.0"),
            ("y = f64(2) ^ (f64(1) + 1) / 2;", "y is 2.0"),
        ])
    );
    assert_eq!(y("y = 2.0 ^ (1.0 + 1) / 2;\n"), "2.0");
    assert_eq!(y("y = 2r ^ (1 + 1) / 2;\n"), "2r");
    assert_eq!(y("y = f64(2) ^ (f64(1) + 1) / 2;\n"), "2.0");
    // A literal exponent takes the carrier `f64` of the base it meets, and keeps `int` under a
    // base at `rat`, so only the first literal of the value is written: `2 ^ 2` meets
    // `f64(0xFF)` or `rat(0xFF)` under `/`.
    assert_eq!(
        checked("y = 0xFF / 2 ^ 2;\n"),
        pairs(&[
            ("y = rat(0xFF) / 2 ^ 2;", "y is rat(0xFF) / 2 ^ 2"),
            ("y = f64(0xFF) / 2 ^ 2;", "y is 63.75"),
        ])
    );
    assert_eq!(y("y = f64(0xFF) / 2 ^ 2;\n"), "63.75");
    assert_eq!(y("y = rat(0xFF) / 2 ^ 2;\n"), "255r/4r");
}

/// Item NUM-huge-div: in a body, the literals of `2 ^ 2 ^ 100 / 3` used to take `f64` as the
/// literal of a float-only word does, so it gave `inf` and `2 ^ 2 ^ 100 / 2 ^ (2 ^ 100 - 1)`
/// gave `nan`. DESIGN.md sec:domains: "an operation on literals alone ... takes the carrier of
/// what it meets", and nothing gives these one, so each is rejected, as at the top level, with
/// the carrier written at its first literal. An exponent that is an operation on integer
/// literals alone is an `int` as one integer literal is (DESIGN.md sec:lexical; plan row
/// LIT-rat-int-op-exponent), so `^` keeps `rat` and the `rat` fix is offered beside `f64`. An
/// exponent whose value is no exact `f64`, as `2 ^ 100 - 1`, removes `f64` as that value
/// written as one literal does, and `f32` too, since a literal base takes no `f32` through
/// `f32 ^ int` (DESIGN.md L1.17; plan row LIT-f32-inexact-exponent): the exact `rat` fix alone
/// is offered. The headline names no carriers, and the menu lists `rat` first (author
/// decision 2026-11-12).
#[test]
fn a_division_of_literal_powers_in_a_body_is_rejected_and_not_read_at_f64() {
    for (body, fix) in [
        ("2 ^ (1 + 1) / 3", "2r ^ (1 + 1) / 3"),
        ("2 ^ 2 ^ 10 / 3", "2r ^ 2 ^ 10 / 3"),
        ("2 ^ 2 ^ 100 / 3", "2r ^ 2 ^ 100 / 3"),
        (
            "2 ^ 2 ^ 100 / 2 ^ (2 ^ 100 - 1)",
            "2r ^ 2 ^ 100 / 2 ^ (2 ^ 100 - 1)",
        ),
        (
            "2 ^ 2 ^ 100 / 2 ^ 1267650600228229401496703205375",
            "2r ^ 2 ^ 100 / 2 ^ 1267650600228229401496703205375",
        ),
    ] {
        let src = format!("h(positional c: bool) = {body};\n");
        assert_eq!(
            first(&src),
            format!(
                "Nothing gives the literal `2` a carrier. \
                 Try `h(positional c: bool) = {fix}` instead."
            ),
            "{src}"
        );
    }
    // Where the exponent's value is no exact `f64`, the `rat` fix alone is offered.
    for (body, n) in [
        ("2 ^ (1 + 1) / 3", 2),
        ("2 ^ 2 ^ 100 / 3", 2),
        ("2 ^ 2 ^ 100 / 2 ^ (2 ^ 100 - 1)", 1),
        ("2 ^ 2 ^ 100 / 2 ^ 1267650600228229401496703205375", 1),
    ] {
        let src = format!("h(positional c: bool) = {body};\n");
        assert_eq!(super::fixes::fixes(&src).len(), n, "{src}");
    }
    // The `rat` fix is exact: `2r`, where the `f64` arithmetic gives `nan`.
    let at = |body: &str| y(&format!("h(positional c: bool) = {body};\ny = h(true);\n"));
    assert_eq!(at("2r ^ 2 ^ 100 / 2 ^ (2 ^ 100 - 1)"), "2r");
    assert_eq!(at("2r ^ (1 + 1) / 3"), "4r/3r");
    // A word that takes float formats alone still gives its literals `f64` (`sqrt(2)`), with
    // an operation on them as its argument, and a decimal literal still does.
    assert_eq!(at("sqrt(2)"), "1.4142135623730951");
    assert_eq!(at("sqrt(2 ^ (1 + 1) / 3)"), "1.1547005383792515");
    assert_eq!(at("2 ^ -1.0 / 3"), "0.16666666666666666");
    // The fix the menu offers is the `f64` arithmetic it names.
    assert_eq!(at("2.0f64 ^ (1 + 1) / 3"), "1.3333333333333333");
    // With nothing to divide, the power is the `int` one.
    assert_eq!(at("2 ^ (1 + 1)"), "4");
}

/// Row LIT-menu-rat-tower: at the top level the menu of a quotient of literal powers whose
/// exponent is itself a power offers the exact `rat` fix first, its value kept unbuilt as a
/// power, then the `f64` ones, whose value is `inf`. Before, it offered the `f64` fix alone.
#[test]
fn a_quotient_of_a_literal_power_tower_is_offered_the_rat_fix_first() {
    assert_eq!(
        checked("y = 2^2^100 / 3;\n"),
        pairs(&[
            ("y = 2r^2^100 / 3;", "y is 2r^2^100 / 3"),
            ("y = 2.0^2.0^100 / 3;", "y is inf"),
            ("y = f64(2)^f64(2)^100 / 3;", "y is inf"),
        ])
    );
    assert_eq!(
        checked("y = 2^(2^62) / 3;\n"),
        pairs(&[
            ("y = 2r^(2^62) / 3;", "y is 2r^(2^62) / 3"),
            ("y = 2.0^(2.0^62) / 3;", "y is inf"),
            ("y = f64(2)^(f64(2)^62) / 3;", "y is inf"),
        ])
    );
}

/// Item NUM-huge-div: at `rat` a power is kept as its prime's exponent, so the quotient of two
/// powers of `2r` whose exponents are past any memory is divided in that form and is exact:
/// `2r`. A power of a base that is no zero is no zero whatever its `int` exponent, so a `/` by
/// one gives no `#divByZero` where the exponent is an operation, as `2 ^ 62 - 1` is.
#[test]
fn a_quotient_of_rat_powers_is_exact_in_the_power_form() {
    for body in [
        "2r ^ (2 ^ 62) / 2r ^ (2 ^ 62 - 1)",
        "2r ^ 2 ^ 100 / 2r ^ (2 ^ 100 - 1)",
        "1r / 2r ^ (1 + 1)",
        "1r / (-3r) ^ (2 - 3)",
    ] {
        let src = format!("h(positional c: bool) = {body};\n");
        assert_eq!(sig(&src, "h"), "bool -> rat", "{body}");
    }
    // A base that may be zero still may give `#divByZero`.
    assert_eq!(
        sig("h(positional c: bool) = 1r / 0r ^ (1 + 1);\n", "h"),
        "bool -> rat | #divByZero"
    );
    assert_eq!(y("y = 2r ^ (2 ^ 62) / 2r ^ (2 ^ 62 - 1);\n"), "2r");
    assert_eq!(
        y("h(positional c: bool) = 2r ^ (2 ^ 62) / 2r ^ (2 ^ 62 - 1);\ny = h(true);\n"),
        "2r"
    );
    assert_eq!(y("y = 2r ^ (2 ^ 62) > 2r ^ (2 ^ 62 - 1);\n"), "true");
    assert_eq!(y("y = 1r / 2r ^ (1 + 1);\n"), "1r/4r");
    assert_eq!(y("y = 1r / (-3r) ^ (2 - 3);\n"), "-3r");
}
