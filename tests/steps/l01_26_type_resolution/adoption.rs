//! A bare numeric literal adopts the carrier its context expects, exactly or not at all: an
//! integer literal adopts int, f64 or rat; a float literal adopts f64 or rat, never int; a
//! decorated literal such as `1r` keeps its own carrier.

use super::{info, type_errors};
use crate::l01_16_elaboration::value;
use zed_kernel::{F64, Value};

/// The values the literals of `text` adopt, sorted by position.
fn adopted(text: &str) -> Vec<Value> {
    let (i, _) = info(text);
    let mut v: Vec<_> = i.adopt.into_iter().collect();
    v.sort_by_key(|(s, _)| s.start);
    v.into_iter().map(|(_, x)| x).collect()
}

#[test]
fn an_integer_literal_adopts_the_other_operands_carrier() {
    assert_eq!(adopted("x = 0.1 + 1;\n"), [Value::Float(F64::new(1.0))]);
    assert_eq!(adopted("x = 2 ** 0.5;\n"), [Value::Float(F64::new(2.0))]);
    assert_eq!(value("x = 0.1 + 1;\n", "x"), "1.1");
    assert_eq!(value("x = 1r / 4r + 1;\n", "x"), "5r/4r");
}

#[test]
fn a_literal_adopts_a_parameters_carrier() {
    assert_eq!(
        value("f(positional x: f64) = x / 4.0;\ny = f(2);\n", "y"),
        "0.5"
    );
    // Within the body too: `2` is an f64 in `half`.
    assert_eq!(value("half(x) = x / 2;\ny = half(x: 3.0);\n", "y"), "1.5");
}

#[test]
fn a_literal_that_cannot_adopt_exactly_is_an_error() {
    assert_eq!(
        type_errors("f(positional x: f64) = x;\ny = f(9007199254740993);\n"),
        ["`9007199254740993` is not an f64 [9007199254740993]"]
    );
}

#[test]
fn a_float_literal_never_adopts_int() {
    assert_eq!(
        type_errors("f(positional x: int) = x;\ny = f(2.0);\n"),
        ["`f` does not take (2.0) [f(2.0)]"]
    );
    assert_eq!(
        type_errors("x = 7 div 2.0;\n"),
        ["`div` does not take (7, 2.0) [7 div 2.0]"]
    );
}

#[test]
fn a_decorated_literal_keeps_its_carrier() {
    // The integer literal adopts rat; `1r` itself adopts nothing.
    assert_eq!(adopted("x = 1r + 1;\n").len(), 1);
    assert!(adopted("x = 1r + 2r;\n").is_empty());
    assert_eq!(value("x = 1r + 1;\n", "x"), "2r");
    assert_eq!(value("y = 0.1 + 1r;\n", "y"), "11r/10r");
}

#[test]
fn equality_compares_across_carriers() {
    // A divisor that cannot be zero adds no `#divByZero`, so the quotient passes as a rat.
    assert!(type_errors("f(positional x: rat) = x;\ny = f(3r/2r);\n").is_empty());
    assert_eq!(
        type_errors("f(positional x: int) = x;\ny = f(7 div 0);\n"),
        ["`f` does not take (#divByZero) [f(7 div 0)]"]
    );
    assert_eq!(value("y = 1 == 1r;\n", "y"), "true");
    assert_eq!(value("y = 1.5 == 3r/2r;\n", "y"), "true");
}

#[test]
fn a_body_keeps_the_arrows_with_the_fewest_adoptions() {
    // `x * 2` checks at int with no adoption, so the f64 and rat arrows, which adopt `2`,
    // are not kept, and a test row at a float is an error.
    assert_eq!(
        type_errors("f(positional x) = x * 2\ntest {\n  3 -> 6,\n  1.5 -> 3.0,\n}\n"),
        ["`f` does not take (1.5) [1.5]"]
    );
}
