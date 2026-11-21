//! A bare numeric literal is generic (DESIGN.md sec:domains, L1.26a, L1.26b): it takes the
//! carrier of its use, exactly or not at all. An integer literal that nothing fixes is an
//! `int`; a decimal literal is never an `int`, and one that nothing fixes is the `f64` it
//! writes (step L1.26b, author decision 2026-11-12). A `/` of integer literals alone that
//! nothing fixes is rejected with a menu, the exact `rat` fixes first. A literal with a suffix,
//! such as `1r` or `0.5f64`, keeps its own carrier, and a bare one beside it takes that carrier.

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

/// The rejection of the literal `d` that nothing gives a carrier, whose fixes are
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

/// The value of `name` that a fix's note names: the value written, or, where the note names a
/// `rat` value reached through a `^` by the operation as the fix writes it (DESIGN.md
/// sec:diagnostics, "The value a fix names"), the value of that operation.
fn named(name: &str, holds: &str) -> String {
    match holds.contains('^') {
        true => value(&format!("{name} = {holds};\n"), name),
        false => holds.to_string(),
    }
}

/// The fix `line` of a menu checks, and `name` then holds `holds`.
fn fix_holds(name: &str, line: &str, holds: &str) {
    let text = format!("{line}\n");
    assert_eq!(type_errors(&text), Vec::<String>::new(), "{line}");
    assert_eq!(value(&text, name), holds, "{line}");
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
fn a_power_with_a_decimal_that_nothing_fixes_takes_f64() {
    // A decimal exponent leaves the float formats alone, so it takes `f64`, as in a body
    // (POW-top-body-agree). A decimal base with an integer exponent may be a `rat` too, and
    // takes `f64` all the same, since a use that leaves a decimal more than one carrier fixes
    // nothing (step L1.26b, author decision 2026-11-12).
    assert_eq!(type_errors("root2 = 2^0.5;\n"), Vec::<String>::new());
    assert_eq!(value("root2 = 2^0.5;\n", "root2"), "1.4142135623730951");
    assert_eq!(type_errors("x = 0.5^2;\n"), Vec::<String>::new());
    assert_eq!(value("x = 0.5^2;\n", "x"), "0.25");
    // The suffixed forms give the same values: the bare `2` takes `f64` from the decimal.
    assert_eq!(value("root2 = 2^0.5f64;\n", "root2"), "1.4142135623730951");
    assert_eq!(value("x = 0.5f64^2;\n", "x"), "0.25");
    // An integer power of integer literals is an `int`.
    assert_eq!(value("p = 2^3;\n", "p"), "8");
}

/// A `/` of integer literals under a `^` whose exponent is an integer literal: the value is
/// refused at `/`, which has no arrow at `int`, and the menu offers the exact `rat` power
/// first, since `^` takes (rat, int) and the exponent keeps `int` (POW-rat-literal-ops), then
/// `f64`: the literal at each carrier, then the cast (sec:diagnostics, `half = 1 / 2`). DESIGN
/// also lists the binding declared at each carrier, which this zedc does not compile, so it
/// is left out (row LIT-declared-fix-call-arg).
#[test]
fn a_power_of_a_division_of_integer_literals_is_offered_the_exact_rat_power() {
    let why = "Nothing gives the integer literals a carrier, and `/` has none at `int`";
    for (src, fixes) in [
        (
            "q = (3/2)^2;",
            [
                ("q = (3r/2)^2;", "q is (3r/2)^2"),
                ("q = (3.0/2)^2;", "q is 2.25"),
                ("q = (f64(3)/2)^2;", "q is 2.25"),
            ],
        ),
        (
            "q = (3/2)^-2;",
            [
                ("q = (3r/2)^-2;", "q is (3r/2)^-2"),
                ("q = (3.0/2)^-2;", "q is 0.4444444444444444"),
                ("q = (f64(3)/2)^-2;", "q is 0.4444444444444444"),
            ],
        ),
    ] {
        let value_text = src.trim_end_matches(';');
        assert_eq!(
            type_errors(&format!("{src}\n")),
            [format!(
                "{why}: `{value_text}`{}{} [(3/2)]",
                tried(&fixes),
                menu(&fixes)
            )],
            "{src}"
        );
        for (line, holds) in fixes {
            let q = holds.strip_prefix("q is ").unwrap();
            fix_holds("q", line, &named("q", q));
        }
    }
    // An exponent that is an operation on integer literals alone is an `int` at `rat` as one
    // integer literal is, and keeps `int` under the `rat` base (DESIGN.md sec:lexical; plan row
    // LIT-rat-int-op-exponent), so the menu offers the exact `rat` power too, with the
    // exponent left as it is: `^` has no arrow (rat, rat).
    let fixes = [
        ("q = (3r/2)^(1+1);", "q is (3r/2)^(1+1)"),
        ("q = (3.0/2)^(1.0+1);", "q is 2.25"),
        ("q = (f64(3)/2)^(f64(1)+1);", "q is 2.25"),
    ];
    assert_eq!(
        type_errors("q = (3/2)^(1+1);\n"),
        [format!(
            "{why}: `q = (3/2)^(1+1)`{}{} [(3/2)]",
            tried(&fixes),
            menu(&fixes)
        )]
    );
    for (line, holds) in fixes {
        let q = holds.strip_prefix("q is ").unwrap();
        fix_holds("q", line, &named("q", q));
    }
    assert_eq!(value("q = (3r/2)^(1+1);\n", "q"), named("q", "9r/4r"));
    // An exponent that is no `int`, as its `2^-1` makes it, would be a `rat` at `rat`, and
    // `^` has no arrow (rat, rat), so there the menu offers `f64` alone.
    let fixes = [
        ("q = (3.0/2)^(1.0-2^-1);", "q is 1.224744871391589"),
        ("q = (f64(3)/2)^(f64(1)-2^-1);", "q is 1.224744871391589"),
    ];
    assert_eq!(
        type_errors("q = (3/2)^(1-2^-1);\n"),
        [format!(
            "Nothing gives the integer literals a carrier, `/` has none at `int`, and `^` none \
             at `rat` with this exponent: `q = (3/2)^(1-2^-1)`{}{} [(3/2)]",
            tried(&fixes),
            menu(&fixes)
        )]
    );
    for (line, holds) in fixes {
        let q = holds.strip_prefix("q is ").unwrap();
        fix_holds("q", line, &named("q", q));
    }
}

#[test]
fn a_slash_among_operations_on_literals_is_rejected_once_at_the_literal_that_fixes_it() {
    // At the top level an operation on two literals that meets no carrier is an `int`, as
    // `1 + 2` is in `(1 + 2) / 3`. The value is rejected once, at its `/`, and the menu is
    // DESIGN's for `half = 1 / 2` (sec:diagnostics; step L1.26b, author decision 2026-11-12):
    // the exact fix first, the first literal of the value written at `rat`, then the literal
    // written as a decimal, then the cast; DESIGN's declared bindings are left out, as this
    // zedc does not compile them (row LIT-declared-fix-call-arg). An operation on literals alone
    // takes the carrier of what it meets, so the written carrier reaches the rest, a `/` of two
    // literals and the base and literal exponent of a `^` among them (an integer exponent keeps
    // `int` under a base at `rat`), and every fix checks. Each headline quotes the binding, the
    // value being the whole of it.
    let why = "Nothing gives the integer literals a carrier, and `/` has none at `int`";
    let pow = "Nothing gives the integer literals a carrier, `/` has none at `int`, and `^` none \
               at `rat` with this exponent";
    let slash = |why: &str| why.to_string();
    let cases = [
        (
            "y = (1 + 2) / 3;\n",
            slash(why),
            vec![
                ("y = (1r + 2) / 3;", "y is 1r"),
                ("y = (1.0 + 2) / 3;", "y is 1.0"),
                ("y = (f64(1) + 2) / 3;", "y is 1.0"),
            ],
            "(1 + 2) / 3",
        ),
        (
            "y = 7 / (1 + 2);\n",
            slash(why),
            vec![
                ("y = 7r / (1 + 2);", "y is 7r/3r"),
                ("y = 7.0 / (1 + 2);", "y is 2.3333333333333335"),
                ("y = f64(7) / (1 + 2);", "y is 2.3333333333333335"),
            ],
            "7 / (1 + 2)",
        ),
        (
            "y = -(1 + 2) / 3;\n",
            slash(why),
            vec![
                ("y = -(1r + 2) / 3;", "y is -1r"),
                ("y = -(1.0 + 2) / 3;", "y is -1.0"),
                ("y = -(f64(1) + 2) / 3;", "y is -1.0"),
            ],
            "-(1 + 2) / 3",
        ),
        (
            "y = 1 + 7 / 2;\n",
            slash(why),
            vec![
                // The carrier of `1` reaches `7 / 2`, which meets it at the `+`.
                ("y = 1r + 7 / 2;", "y is 9r/2r"),
                ("y = 1.0 + 7 / 2;", "y is 4.5"),
                ("y = f64(1) + 7 / 2;", "y is 4.5"),
            ],
            "7 / 2",
        ),
        // A literal in another base is offered in a cast, at `rat` and then at `f64`, each
        // followed by the declaration at that carrier.
        (
            "y = 0xFF / 2;\n",
            slash(why),
            vec![
                ("y = rat(0xFF) / 2;", "y is 255r/2r"),
                ("y = f64(0xFF) / 2;", "y is 127.5"),
            ],
            "0xFF / 2",
        ),
        (
            "y = 0xFF / 2 ^ 2;\n",
            slash(why),
            // `2 ^ 2` meets `f64(0xFF)` or `rat(0xFF)` at the `/` and takes its carrier, its
            // exponent `int` under `rat`, so only `0xFF` is written, and in a cast alone.
            vec![
                ("y = rat(0xFF) / 2 ^ 2;", "y is rat(0xFF) / 2 ^ 2"),
                ("y = f64(0xFF) / 2 ^ 2;", "y is 63.75"),
            ],
            "0xFF / 2 ^ 2",
        ),
        (
            "y = 1 + 2 ^ 2 / 3;\n",
            slash(why),
            vec![
                ("y = 1r + 2 ^ 2 / 3;", "y is 1r + 2 ^ 2 / 3"),
                ("y = 1.0 + 2 ^ 2 / 3;", "y is 2.333333333333333"),
                ("y = f64(1) + 2 ^ 2 / 3;", "y is 2.333333333333333"),
            ],
            "2 ^ 2 / 3",
        ),
        // An exponent that is an operation on integer literals alone keeps `int` under a base
        // at `rat`, as one integer literal does (plan row LIT-rat-int-op-exponent), so the
        // `rat` fix leaves it as it is; at `f64` it is written too, since `^` has no arrow
        // (f64, int).
        (
            "y = 2 ^ (1 + 1) / 3;\n",
            slash(why),
            vec![
                ("y = 2r ^ (1 + 1) / 3;", "y is 2r ^ (1 + 1) / 3"),
                ("y = 2.0 ^ (1.0 + 1) / 3;", "y is 1.3333333333333333"),
                ("y = f64(2) ^ (f64(1) + 1) / 3;", "y is 1.3333333333333333"),
            ],
            "2 ^ (1 + 1) / 3",
        ),
        // An exponent that is no `int`, as its `2^-1` makes it, takes the base's carrier, and
        // `^` has no arrow (rat, rat), so the menu offers `f64` alone.
        (
            "y = 2 ^ (1 - 2^-1) / 3;\n",
            slash(pow),
            vec![
                ("y = 2.0 ^ (1.0 - 2^-1) / 3;", "y is 0.47140452079103173"),
                (
                    "y = f64(2) ^ (f64(1) - 2^-1) / 3;",
                    "y is 0.47140452079103173",
                ),
            ],
            "2 ^ (1 - 2^-1) / 3",
        ),
        // One carrier reaches both `/` of two literals: they meet at the outer `/`.
        (
            "y = (1 / 2) / (3 / 4);\n",
            slash(why),
            vec![
                ("y = (1r / 2) / (3 / 4);", "y is 2r/3r"),
                ("y = (1.0 / 2) / (3 / 4);", "y is 0.6666666666666666"),
                ("y = (f64(1) / 2) / (3 / 4);", "y is 0.6666666666666666"),
            ],
            "(1 / 2) / (3 / 4)",
        ),
        (
            "y = (1 + 2) / (3 + 4) + 7 / 2;\n",
            slash(why),
            vec![
                ("y = (1r + 2) / (3 + 4) + 7 / 2;", "y is 55r/14r"),
                (
                    "y = (1.0 + 2) / (3 + 4) + 7 / 2;",
                    "y is 3.9285714285714284",
                ),
                (
                    "y = (f64(1) + 2) / (3 + 4) + 7 / 2;",
                    "y is 3.9285714285714284",
                ),
            ],
            "(1 + 2) / (3 + 4)",
        ),
        // DESIGN's example: the carrier written on the first literal alone reaches both sums.
        (
            "y = (1 + 2) / (3 + 4);\n",
            slash(why),
            vec![
                ("y = (1r + 2) / (3 + 4);", "y is 3r/7r"),
                ("y = (1.0 + 2) / (3 + 4);", "y is 0.42857142857142855"),
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
            fix_holds("y", line, &named("y", y));
        }
    }
    // A decimal beside an operation on literals is the `f64` it writes, and the operation takes
    // that carrier (DESIGN.md step L1.26b: "`y = 0.5 * 2` the `f64` `1.0`"), a `/` of two
    // integer literals among them: an operation on literals alone is an `int` only where
    // nothing at all gives it a carrier.
    for (src, y) in [
        ("y = 0.5 * (1 + 2);\n", "1.5"),
        ("y = 2 * 0.5;\n", "1.0"),
        ("y = 0.5 * (7 / 2);\n", "1.75"),
    ] {
        assert_eq!(type_errors(src), Vec::<String>::new(), "{src}");
        assert_eq!(value(src, "y"), y, "{src}");
    }
    // The suffixed forms give those values, and the exact ones at `rat`.
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
    // `1 == 1.0` fixes neither literal, so the decimal is the `f64` it writes and `1` takes
    // `f64` beside it (step L1.26b: "`1 == 1.0` is `true`").
    assert_eq!(type_errors("y = 1 == 1.0;\n"), Vec::<String>::new());
    assert_eq!(value("y = 1 == 1.0;\n", "y"), "true");
    assert_eq!(value("y = 1 == 1.0f64;\n", "y"), "true");
    // A `/` of integer literals there is still rejected, with the exact fixes first.
    let fixes = [
        ("y = 1r == 1 / 2;", "y is false"),
        ("y = 1.0 == 1 / 2;", "y is false"),
        ("y = f64(1) == 1 / 2;", "y is false"),
    ];
    assert_eq!(
        type_errors("y = 1 == 1 / 2;\n"),
        [format!(
            "Nothing gives the integer literals a carrier, and `/` has none at `int`: \
             `y = 1 == 1 / 2`{}{} [1 / 2]",
            tried(&fixes),
            menu(&fixes)
        )]
    );
    for (line, _) in fixes {
        fix_holds("y", line, "false");
    }
    // Beside a rat a decimal takes `rat`, exactly.
    assert_eq!(value("y = 1.5 == 3r/2r;\n", "y"), "true");
    assert_eq!(value("y = 1 == 1r;\n", "y"), "true");
    assert_eq!(value("y = 1 == 1;\n", "y"), "true");
}

#[test]
fn a_test_row_at_a_decimal_takes_f64_and_one_at_a_slash_needs_a_carrier() {
    // `x * 2` leaves `double` generic, so a row's decimal argument is fixed by nothing and is
    // the `f64` it writes (step L1.26b, author decision 2026-11-12).
    let rows = |arg: &str| format!("double(x) = x * 2\ntest {{\n  3 -> 6,\n  {arg} -> 3.0,\n}}\n");
    assert!(type_errors(&rows("1.5")).is_empty());
    assert!(type_errors(&rows("1.5f64")).is_empty());
    assert!(type_errors(&rows("1.5r")).is_empty());
    // A row whose argument is a `/` of integer literals is rejected, the exact fix first.
    let rows = |arg: &str| format!("double(x) = x * 2\ntest {{\n  3 -> 6,\n  {arg} -> 1,\n}}\n");
    assert_eq!(
        type_errors(&rows("1 / 2")),
        [unfixed(
            "1",
            &[
                ("1r / 2 -> 1,", "the literal is then exactly 1, a rat"),
                ("1.0f64 / 2 -> 1,", "the literal is then the f64 1.0"),
            ]
        )]
    );
    assert!(type_errors(&rows("1r / 2")).is_empty());
    assert!(type_errors(&rows("1.0f64 / 2")).is_empty());
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
