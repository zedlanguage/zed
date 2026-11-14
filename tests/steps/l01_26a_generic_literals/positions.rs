//! Completeness of steps L1.26a and L1.26b by syntactic position (row TEST-complete-literals,
//! author P189): a literal takes the carrier of its use wherever it stands, in a lambda body,
//! a local function, a block, a tuple component, an `else` default, a string hole, a nest of
//! operations or calls, a comparison, a negation and a nest of `if`s. Each expected type and
//! value is the one DESIGN.md L1.26a and L1.26b give; COMPLETENESS.md lists the cases.

use zed_tests::step_helpers::l01_16_elaboration::value;
use zed_tests::step_helpers::l01_26_type_resolution::{info, sig, type_errors};

use super::{T, T_NO_INT};

/// `src` is accepted, and each `(name, value)` evaluates to that value.
fn values(src: &str, want: &[(&str, &str)]) {
    assert_eq!(type_errors(src), Vec::<String>::new(), "{src}");
    for (name, v) in want {
        assert_eq!(value(src, name), *v, "{src}\n`{name}`");
    }
}

/// `src` is rejected with one message, which holds each of `parts`.
fn rejected(src: &str, parts: &[&str]) {
    let errors = type_errors(src);
    assert_eq!(errors.len(), 1, "{src}\n{errors:?}");
    for p in parts {
        assert!(errors[0].contains(p), "{src}\n{:?} lacks {p:?}", errors[0]);
    }
}

const AP: &str = "ap(positional f, positional x) = f(x);\n";

#[test]
fn a_literal_in_a_lambda_body_takes_the_carrier_of_the_lambdas_argument() {
    // The lambda's parameter is a class like a function's (L1.26a), so its body's `1` takes
    // the carrier of each argument, and its `0.5` takes every carrier but `int`.
    values(
        &format!(
            "{AP}a = ap(y -> y + 1, 2.5f64);\nb = ap(y -> y + 1, 1r);\nc = ap(y -> y + 1, 2);\n\
             d = ap(y -> y * 0.5, 3r);\ne = ap(y -> y * 0.5, 3.0f64);\n"
        ),
        &[
            ("a", "3.5"),
            ("b", "2r"),
            ("c", "3"),
            ("d", "3r/2r"),
            ("e", "1.5"),
        ],
    );
    // A decimal is never an `int` (L1.26b): no arrow of the lambda takes `3`.
    rejected(
        &format!("{AP}a = ap(y -> y * 0.5, 3);\n"),
        &["`f` does not take (3)"],
    );
}

#[test]
fn a_lambda_bound_to_a_name_is_generic_over_the_carriers_its_literal_takes() {
    let src = "half = y -> y * 0.5;\n";
    assert_eq!(
        info(src)
            .0
            .tops
            .get("half")
            .map(ToString::to_string)
            .as_deref(),
        Some("(T) -> T for T in f32 | f64 | rat")
    );
    // Passed twice through a higher-order function, the literal takes `rat` each time.
    values(
        "twice(positional f, positional x) = f(f(x));\na = twice(y -> y * 0.5, 3r);\n",
        &[("a", "3r/4r")],
    );
    // A lambda called where it is written.
    let src = "f(x) = (z -> z + 1)(x);\na = f(x: 2.5f64);\n";
    assert_eq!(sig(src, "f"), T);
    values(src, &[("a", "3.5")]);
}

#[test]
fn a_lambda_body_of_literals_alone_keeps_its_literals() {
    // A body that does not use its parameter returns the literal itself, a tuple of the
    // argument and a literal keeps the literal's value, and an `if` whose other branch is the
    // parameter gives the literal the parameter's carrier.
    values(
        &format!(
            "{AP}a = ap(y -> 1, 2.5f64);\nb = ap(y -> if y > 0 {{ y }} else {{ 0 }}, -2.5f64);\n"
        ),
        &[("a", "1"), ("b", "0.0")],
    );
}

#[test]
fn a_literal_in_a_local_function_or_a_block_takes_the_carrier_of_the_parameter() {
    let src = "f(x) = { g(positional y) = y + 1; g(x) };\na = f(x: 2.5f64);\nb = f(x: 2);\n";
    assert_eq!(sig(src, "f"), T);
    values(src, &[("a", "3.5"), ("b", "3")]);
    let src = "f(x) = { y = x + 1; y * 2 };\na = f(x: 2.5f64);\n";
    assert_eq!(sig(src, "f"), T);
    values(src, &[("a", "7.0")]);
}

#[test]
fn an_integer_literal_bound_to_a_local_name_alone_is_an_int() {
    // DESIGN.md L1.26a: an integer literal bound to a name alone, `y = 1`, is an `int`, so
    // `x + k` fixes `x` to `int` and a call at `f64` is rejected.
    let src = "f(positional x) = { k = 1; x + k };\na = f(2);\n";
    assert_eq!(sig(src, "f"), "(int) -> int");
    values(src, &[("a", "3")]);
    assert!(
        !type_errors("f(positional x) = { k = 1; x + k };\na = f(2.5f64);\n").is_empty(),
        "an f64 argument beside an int name"
    );
}

#[test]
fn a_literal_returned_in_a_tuple_beside_a_parameter_keeps_its_value() {
    assert_eq!(sig("f(x) = (x, 1);\n", "f"), "(x: T) -> (T, 1)");
    assert_eq!(sig("f(x) = (x, 2.5);\n", "f"), "(x: T) -> (T, 2.5)");
}

#[test]
fn a_literal_default_of_else_takes_the_carrier_of_the_other_side() {
    // `div` takes `int` alone, so its `else 0` is an `int`, and the default is used where the
    // divisor is zero.
    let src = "f(x: int, d: int) = x div d else 0;\na = f(x: 7, d: 0);\nb = f(x: 7, d: 2);\n";
    assert_eq!(sig(src, "f"), "(x: int, d: int) -> int");
    values(src, &[("a", "0"), ("b", "3")]);
    // Beside a `rat` the default is a literal of the union, `0 | rat` (L1.26a: one literal
    // branch beside a carrier is fixed as it would be alone, and the union rule applies).
    assert_eq!(
        sig("g(x: rat, d: rat) = x / d else 0;\n", "g"),
        "(x: rat, d: rat) -> 0 | rat"
    );
    assert_eq!(
        sig("g(x: rat, d: rat) = x / d else 0.5;\n", "g"),
        "(x: rat, d: rat) -> 0.5 | rat"
    );
}

#[test]
fn a_literal_in_a_string_hole_takes_a_carrier_as_it_would_alone() {
    // An integer literal alone is an `int`; a decimal alone has no carrier and is rejected
    // with the menu of L1.26b; a hole of a parameter's operation is generic.
    values(
        "a = \"${1 + 2}\";\nb = \"${0.5f64}\";\n",
        &[("a", "\"3\""), ("b", "\"0.5\"")],
    );
    rejected(
        "a = \"${0.5}\";\n",
        &["a = \"${0.5f64}\";", "a = \"${0.5r}\";"],
    );
    assert_eq!(
        sig("f(positional x) = \"${x + 1}\";\n", "f"),
        "(T) -> String for T in int | f32 | f64 | rat"
    );
}

#[test]
fn literals_nested_in_operations_and_calls_take_the_carrier_of_the_outermost_use() {
    let src = "f(x) = x + (1 + (2 + 3));\na = f(x: 0.5f64);\n";
    assert_eq!(sig(src, "f"), T);
    values(src, &[("a", "6.5")]);
    // `1 / 2` of literals alone beside a class takes its carrier, never `int` (L1.26a).
    assert_eq!(sig("f(x) = x * (1 / 2);\n", "f"), T_NO_INT);
    values(
        &format!("{}a = inc(x: inc(x: 2.5f64));\n", super::INC),
        &[("a", "4.5")],
    );
}

#[test]
fn a_nest_of_ifs_of_literals_is_the_union_of_their_values() {
    assert_eq!(
        sig(
            "f(positional a: bool, positional b: bool) = if a { 1 } else if b { 2 } else { 3 };\n",
            "f"
        ),
        "(bool, bool) -> 1 | 2 | 3"
    );
}

#[test]
fn a_literal_compared_with_a_parameter_takes_its_carrier() {
    assert_eq!(
        sig("pos(x) = x > 0;\n", "pos"),
        "(x: T) -> bool for T in int | f32 | f64 | rat"
    );
    assert_eq!(
        sig("f(x) = x + 1 > 2;\n", "f"),
        "(x: T) -> bool for T in int | f32 | f64 | rat"
    );
    assert_eq!(
        sig("f(x) = x + 1 == 2;\n", "f"),
        "(x: T) -> bool for T in int | f32 | f64 | rat"
    );
    values(
        "pos(x) = x > 0;\na = pos(x: -0.5f64);\nb = pos(x: 1r);\n",
        &[("a", "false"), ("b", "true")],
    );
}

#[test]
fn a_negated_literal_takes_the_carrier_of_its_use() {
    let src = "f(x) = x * -0.5;\na = f(x: 3r);\n";
    assert_eq!(sig(src, "f"), T_NO_INT);
    values(src, &[("a", "-3r/2r")]);
    let src = "f(x) = -(-x + 1);\na = f(x: 2.5f64);\n";
    assert_eq!(sig(src, "f"), T);
    values(src, &[("a", "1.5")]);
}

const AP_INT: &str = "ap(f: (x: int) -> int) = f(x: 1);\n";

#[test]
fn a_lambda_in_a_slot_of_a_declared_function_type_gives_its_literal_that_slots_carrier() {
    // L1.26 rule 4: the lambda's parameter takes the slot's parameter type, so its literal
    // takes that carrier: `2` an `int`, `0.5` an `f64` at an `f64` slot, `3` a `rat`.
    values(
        &format!(
            "{AP_INT}a = ap(f: x -> x * 2);\nb = ap(f: (x, y = 2) -> x + y);\nc = ap(f: (x: int | f64) -> 2);\n"
        ),
        &[("a", "2"), ("b", "3"), ("c", "2")],
    );
    values(
        "ap(f: (x: f64) -> f64) = f(x: 1.5f64);\na = ap(f: x -> x * 0.5);\n",
        &[("a", "0.75")],
    );
    values(
        "ap(f: (x: rat) -> rat) = f(x: 1);\na = ap(f: x -> x / 3);\n",
        &[("a", "1r/3r")],
    );
    // A decimal is never an `int` (L1.26b), in a lambda body as anywhere.
    rejected(
        &format!("{AP_INT}a = ap(f: x -> x * 0.5);\n"),
        &["A decimal literal is never an `int`: `x : int * 0.5`."],
    );
    // A parameter the slot does not pass needs a default; a parameter narrower than the
    // slot's is rejected.
    rejected(
        &format!("{AP_INT}a = ap(f: (x, y) -> x + y);\n"),
        &["the lambda's parameter `y` is not a parameter of `(x: int) -> int`"],
    );
    let errors = type_errors(&format!("{AP_INT}a = ap(f: (x: f64) -> x);\n"));
    assert!(
        errors
            .iter()
            .any(|e| e
                .contains("the lambda's parameter `x` is f64, and `(x: int) -> int` passes int")),
        "{errors:?}"
    );
}
