//! A plain numeric literal adopts no carrier (DESIGN.md sec:domains, L1.26): `1` is always an
//! int and `0.1` always an f64, whatever is expected, since Zed converts no value implicitly.
//! Where the expected type does not hold the literal's carrier, it is rejected with a menu of
//! the forms to write that the type holds. Only a generic literal `kn` takes its carrier from
//! its use, exactly or not at all; a decorated literal such as `1r` keeps its own.

use super::{info, type_errors};
use zed_kernel::{F64, Value};
use zed_tests::step_helpers::l01_16_elaboration::value;

/// The values the literals of `text` adopt, sorted by position.
fn adopted(text: &str) -> Vec<Value> {
    let (i, _) = info(text);
    let mut v: Vec<_> = i.adopt.into_iter().collect();
    v.sort_by_key(|(s, _)| s.start);
    v.into_iter().map(|(_, x)| x).collect()
}

#[test]
fn an_integer_literal_beside_a_float_is_rejected_with_its_menu() {
    // `1 + taxRate` with `taxRate: f64` is the case the menu is for.
    assert_eq!(
        type_errors("gross(positional net: f64, positional taxRate: f64) = net * (1 + taxRate);\n"),
        [
            "`1` is an int where `f64` is expected; a literal takes no other carrier; write `1.0` \
          or `1n` [1]"
        ]
    );
    assert_eq!(
        value(
            "gross(positional net: f64, positional taxRate: f64) = net * (1.0 + taxRate);\n\
             y = gross(200.0, 0.25);\n",
            "y"
        ),
        "250.0"
    );
    assert_eq!(
        value(
            "gross(positional net: f64, positional taxRate: f64) = net * (1n + taxRate);\n\
             y = gross(200.0, 0.25);\n",
            "y"
        ),
        "250.0"
    );
    // Of two literals of two carriers the integer is rejected: `2 ** 0.5` is no `2.0 ** 0.5`.
    assert_eq!(
        type_errors("root2 = 2 ** 0.5;\n"),
        [
            "`2` is an int where `f64` is expected; a literal takes no other carrier; write `2.0` \
          or `2n` [2]"
        ]
    );
    assert_eq!(
        value("root2 = 2.0 ** 0.5;\n", "root2"),
        "1.4142135623730951"
    );
    assert!(adopted("root2 = 2.0 ** 0.5;\n").is_empty());
}

#[test]
fn a_literal_argument_keeps_its_carrier() {
    // `quarter` takes an f64, and `2` is an int: the call is rejected, not converted.
    let quarter = "quarter(positional x: f64) = x / 4.0;\n";
    assert_eq!(
        type_errors(&format!("{quarter}y = quarter(2);\n")),
        [
            "`2` is an int where `f64` is expected; a literal takes no other carrier; write `2.0` \
          or `2n` [2]"
        ]
    );
    assert_eq!(value(&format!("{quarter}y = quarter(2.0);\n"), "y"), "0.5");
    assert_eq!(value(&format!("{quarter}y = quarter(2n);\n"), "y"), "0.5");
    // Within a body too: `x / 2` leaves `x` int, which `/` does not take.
    assert_eq!(
        type_errors("half(x) = x / 2;\n"),
        ["`/` does not take (int, int) [x / 2]"]
    );
    assert_eq!(value("half(x) = x / 2.0;\ny = half(x: 3.0);\n", "y"), "1.5");
}

#[test]
fn a_generic_literal_that_cannot_take_a_carrier_exactly_is_an_error() {
    // 2^53 + 1 has no f64: the plain literal is an int, and the generic one is no f64.
    let f = "f(positional x: f64) = x;\n";
    assert_eq!(
        type_errors(&format!("{f}y = f(9007199254740993);\n")),
        [
            "`9007199254740993` is an int where `f64` is expected; a literal takes no other \
          carrier [9007199254740993]"
        ]
    );
    assert_eq!(
        type_errors(&format!("{f}y = f(9007199254740993n);\n")),
        ["`9007199254740993n` is not an f64 [9007199254740993n]"]
    );
    assert_eq!(
        value(&format!("{f}y = f(9007199254740992n);\n"), "y"),
        "9007199254740992.0"
    );
}

#[test]
fn a_float_literal_never_becomes_an_int() {
    assert_eq!(
        type_errors("f(positional x: int) = x;\ny = f(2.0);\n"),
        ["`2.0` is an f64 where `int` is expected; a literal takes no other carrier [2.0]"]
    );
    assert_eq!(
        type_errors("x = 7 div 2.0;\n"),
        ["`2.0` is an f64 where `int` is expected; a literal takes no other carrier [2.0]"]
    );
}

#[test]
fn a_decorated_literal_keeps_its_carrier_and_a_plain_one_beside_it_is_rejected() {
    assert_eq!(
        type_errors("x = 1r + 1;\n"),
        [
            "`1` is an int where `rat` is expected; a literal takes no other carrier; write `1r` \
          or `1n` [1]"
        ]
    );
    assert!(adopted("x = 1r + 2r;\n").is_empty());
    assert_eq!(value("x = 1r + 1r;\n", "x"), "2r");
    assert_eq!(value("x = 1r + 1n;\n", "x"), "2r");
    assert_eq!(
        adopted("x = 1r + 1n;\n"),
        [Value::rat(zed_kernel::Rat::decimal("1").unwrap().unwrap())]
    );
}

#[test]
fn equality_takes_two_values_of_one_carrier() {
    // A divisor that cannot be zero adds no `#divByZero`, so the quotient passes as a rat.
    assert!(type_errors("f(positional x: rat) = x;\ny = f(3r/2r);\n").is_empty());
    // A divisor that may be zero adds `#divByZero`, a loose atom, which passes through `f`.
    assert!(type_errors("f(positional x: int) = x;\ny = f(7 div 0);\n").is_empty());
    assert_eq!(
        value("f(positional x: int) = x;\ny = f(7 div 0);\n", "y"),
        "#divByZero"
    );
    // `1 == 1.0` compares an int and an f64, which no carrier holds both of.
    assert_eq!(
        type_errors("y = 1 == 1.0;\n"),
        [
            "`1` is an int where `f64` is expected; a literal takes no other carrier; write `1.0` \
          or `1n` [1]"
        ]
    );
    // Of an f64 and a rat, the decimal is rejected.
    assert_eq!(
        type_errors("y = 1.5 == 3r/2r;\n"),
        [
            "`1.5` is an f64 where `rat` is expected; a literal takes no other carrier; write \
          `1.5r` [1.5]"
        ]
    );
    assert_eq!(value("y = 1.5r == 3r/2r;\n", "y"), "true");
    assert_eq!(value("y = 1n == 1r;\n", "y"), "true");
    assert_eq!(value("y = 1n == 1.0;\n", "y"), "true");
}

#[test]
fn a_body_with_a_plain_literal_takes_its_carrier() {
    // `x * 2` leaves `x` int, so a test row at a float is rejected at its argument and at its
    // expected result; the generic literal keeps every carrier.
    assert_eq!(
        type_errors("double(x) = x * 2\ntest {\n  3 -> 6,\n  1.5 -> 3.0,\n}\n"),
        [
            "`1.5` is an f64 where `int` is expected; a literal takes no other carrier [1.5]",
            "`3.0` is an f64 where `int` is expected; a literal takes no other carrier [3.0]"
        ]
    );
    assert!(type_errors("double(x) = x * 2n\ntest {\n  3 -> 6,\n  1.5 -> 3.0,\n}\n").is_empty());
}

#[test]
fn a_decimal_at_rat_is_rejected_and_its_r_form_is_exact() {
    let price = "price(positional p: rat) = p;\n";
    assert_eq!(
        type_errors(&format!("{price}x = price(0.1);\n")),
        [
            "`0.1` is an f64 where `rat` is expected; a literal takes no other carrier; write \
          `0.1r` [0.1]"
        ]
    );
    assert_eq!(value(&format!("{price}x = price(0.1r);\n"), "x"), "1r/10r");
    assert_eq!(value("x = 1r + 0.1r;\n", "x"), "11r/10r");
    // Exact as a rat, so neither rounds: beyond the f64 range is no error there.
    assert_eq!(type_errors("x = 1r + 1e-400r;\n"), Vec::<String>::new());
    assert_eq!(type_errors("x = 1r + 1e400r;\n"), Vec::<String>::new());
}

#[test]
fn a_float_literal_at_f64_rounds_to_the_nearest() {
    // `0.1` has no exact f64; a float literal rounds to the nearest.
    assert_eq!(
        value("f(positional x: f64) = x;\ny = f(0.1);\n", "y"),
        "0.1"
    );
    assert!(adopted("f(positional x: f64) = x;\ny = f(0.1);\n").is_empty());
    assert_eq!(
        value(
            "f(positional x: f64) = x;\ny = f(9007199254740992.0);\n",
            "y"
        ),
        "9007199254740992.0"
    );
    assert_eq!(
        adopted("f(positional x: f64) = x;\ny = f(4n);\n"),
        [Value::Float(F64::new(4.0))]
    );
}
