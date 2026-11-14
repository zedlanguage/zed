//! An operation on generic literals alone, as `2 + 0` in `x * (2 + 0)`, takes its carrier by
//! one `match` on what gives the literals theirs and is built once per carrier inside it, so
//! the build stage folds each arm to a constant (STAGE-generic-fold, COMPLEXITY.md F85).
//! Each value is checked against the same body at a parameter of the carrier written out.

use zed_tests::step_helpers::l01_16_elaboration::{checked, elab, term, value};

/// The value of `f` of `body` at the argument `arg`, `f`'s parameters generic, and at `ty`,
/// each parameter declared of that type.
fn both(params: &[&str], body: &str, arg: &str, ty: &str) -> (String, String) {
    let generic: Vec<String> = params.iter().map(|p| format!("positional {p}")).collect();
    let typed: Vec<String> = params
        .iter()
        .map(|p| format!("positional {p}: {ty}"))
        .collect();
    let src = |ps: &[String]| format!("f({}) = {body};\ny = f({arg});\n", ps.join(", "));
    (value(&src(&generic), "y"), value(&src(&typed), "y"))
}

#[test]
fn an_operation_on_literals_alone_is_one_match_on_the_carrier() {
    assert_eq!(
        term("f(positional x) = x * (2 + 0);\n", "f"),
        "x -> (x * match x { is f64 -> (2.0 + 0.0), is rat -> (2r + 0r), \
         is f32 -> (2.0f32 + 0.0f32), _ -> (2 + 0) })"
    );
}

#[test]
fn nested_and_negated_operations_on_literals_are_one_match() {
    for body in [
        "x + (1 + 2) * 3",
        "x * -(2 + 1)",
        "x - (1 - 2 - 3 - 4)",
        "x * (2 + -(1 + 1))",
        "x * (1180591620717411303424 + 0)",
    ] {
        let t = term(&format!("f(positional x) = {body};\n"), "f");
        assert_eq!(t.matches("match").count(), 1, "{body}: {t}");
    }
}

#[test]
fn operations_on_literals_give_each_carrier_s_value() {
    let bodies = [
        "x * (2 + 0)",
        "x + (1 + 2) * 3",
        "x * -(2 + 1)",
        "x - (1 - 2 - 3 - 4)",
        "x + (1 / 2 + 3)",
        "x + 3 * (1 / 2)",
        "(x > 0) == (1 < 2)",
        "x * (1180591620717411303424 + 0)",
        "x * (2 + -(1 + 1))",
        // One `match` since STAGE-generic-fold-div ([`FOLDED`]).
        "x * (1.5 + 1)",
        "x * (1 + 1.5)",
        "x * ((2 + 1) ^ 2)",
        "x * ((2 + 1) ^ 2 + 1)",
        "x * (1.5 ^ 2 + 1)",
        "x * (1 / 2 + 1.5)",
        "x * ((1 / 2) ^ 2 + 1)",
        "x * (1 / 1180591620717411303424 + 1)",
        "x == 1 / 2 + 1",
        "x * (1 ^ 1180591620717411303424 + 1)",
        // Still a `let` and a `match` per literal ([`NOT_FOLDED`]).
        "x * (1 / (2 + 1) + 1)",
        "x * (2 ^ -1 + 1)",
        "x * (1.5 ^ -1 + 1)",
        "x * ((1 + 1.5) + 0)",
        "x * (1 / 2 + 2 ^ 2 + 1)",
    ];
    let args = [
        ("1", "int"),
        ("1.5f64", "f64"),
        ("3r", "rat"),
        ("1.5f32", "f32"),
    ];
    for body in bodies {
        for (arg, ty) in args {
            // `/` and a decimal take no `int`, and `int ^ -1` is refused.
            if ty == "int" && (body.contains('/') || body.contains('.') || body.contains("^ -")) {
                continue;
            }
            let (generic, typed) = both(&["x"], body, arg, ty);
            assert_eq!(generic, typed, "{body} at {arg}");
        }
    }
}

/// Operations on literals alone with `/`, a decimal or `^` whose carrier is known in every
/// arm, so the literal that follows takes it there and the whole is one `match` (plan row
/// STAGE-generic-fold-div): `/` keeps the carrier of each arm `is c` and gives a `rat` from two
/// `int`s, `^` with a whole-number exponent keeps the base's, and a literal following a decimal
/// takes the decimal's arms, its own value where it lists no value at their carrier.
const FOLDED: [&str; 12] = [
    "x + (1 / 2 + 3)",
    "x + 3 * (1 / 2)",
    "x * (1.5 + 1)",
    "x * (1 + 1.5)",
    "x * ((2 + 1) ^ 2)",
    "x * ((2 + 1) ^ 2 + 1)",
    "x * (1.5 ^ 2 + 1)",
    "x * (1 / 2 + 1.5)",
    "x * ((1 / 2) ^ 2 + 1)",
    "x == 1 / 2 + 1",
    "x * (1 / 1180591620717411303424 + 1)",
    "x * (1 ^ 1180591620717411303424 + 1)",
];

/// Operations whose carrier is not known in every arm, so the literal that follows takes the
/// old path, a `let` and a `match` on its value, and keeps the value: a divisor that is an
/// operation, which elaboration does not evaluate; a zero divisor, which gives `#divByZero` at
/// `rat`; a negative exponent, refused at `int`; an exponent not a whole number; a sum of a
/// decimal and an integer, or of a quotient and an integer power, whose last arm, at `int`,
/// gives no value of a carrier (plan row STAGE-generic-fold-int-arm).
const NOT_FOLDED: [&str; 7] = [
    "x * (1 / (2 + 1) + 1)",
    "x * (1 / 0 + 1)",
    "x * (2 ^ -1 + 1)",
    "x * (1.5 ^ -1 + 1)",
    "x * ((2 + 1) ^ 0.5 + 1)",
    "x * ((1 + 1.5) + 0)",
    "x * (1 / 2 + 2 ^ 2 + 1)",
];

#[test]
fn a_quotient_a_decimal_or_a_power_among_literals_is_one_match() {
    for body in FOLDED {
        let t = term(&format!("f(positional x) = {body};\n"), "f");
        assert_eq!(t.matches("match").count(), 1, "{body}: {t}");
    }
    for body in NOT_FOLDED {
        let t = term(&format!("f(positional x) = {body};\n"), "f");
        assert_eq!(t.matches("match").count(), 2, "{body}: {t}");
    }
    // At `int`, `1 / 2` is a `rat`, and `3` follows it there as `3r`.
    assert_eq!(
        term("f(positional x) = x + (1 / 2 + 3);\n", "f"),
        "x -> (x + match x { is f64 -> ((1.0 / 2.0) + 3.0), is rat -> ((1r / 2r) + 3r), \
         is f32 -> ((1.0f32 / 2.0f32) + 3.0f32), _ -> ((1 / 2) + 3r) })"
    );
    // `1` lists `f64`, `rat` and `f32`; the decimal's arms are `rat`, `f32` and its own `f64`.
    assert_eq!(
        term("f(positional x) = x * (1.5 + 1);\n", "f"),
        "x -> (x * match x { is rat -> (3r/2r + 1r), is f32 -> (1.5f32 + 1.0f32), \
         _ -> (1.5 + 1.0) })"
    );
    // The exponent lists `f64` and `f32`, and keeps its own `2` at `rat` and `int`.
    assert_eq!(
        term("f(positional x) = x * ((2 + 1) ^ 2);\n", "f"),
        "x -> (x * match x { is f64 -> ((2.0 + 1.0)^2.0), is rat -> ((2r + 1r)^2), \
         is f32 -> ((2.0f32 + 1.0f32)^2.0f32), _ -> ((2 + 1)^2) })"
    );
}

#[test]
fn a_zero_divisor_keeps_the_value_of_the_old_path() {
    // The same text at `f64` and at `rat`, generic and declared. At `f64` the value is `inf`
    // until plan row POW-domains makes float `x / 0.0` `#divByZero`.
    for (arg, ty) in [("1.5f64", "f64"), ("3r", "rat"), ("1.5f32", "f32")] {
        let (generic, typed) = both(&["x"], "x * (1 / 0 + 1)", arg, ty);
        assert_eq!(generic, typed, "at {arg}");
    }
}

#[test]
fn a_literal_following_another_takes_its_carrier_in_the_last_arm() {
    // `/` takes no `int`, so the checker gives `1` the value `1.0` at a value of another
    // carrier, as at the `int` 2 here; `2` follows `1` and takes `2.0` there too, not its own
    // `2`, which would give `/` an `f64` and an `int`.
    assert_eq!(
        term("g(positional x) = x == 1 / 2;\n", "g"),
        "x -> (x == match x { is f64 -> (1.0 / 2.0), is rat -> (1r / 2r), \
         is f32 -> (1.0f32 / 2.0f32), _ -> (1.0 / 2.0) })"
    );
    let text = "g(positional x) = x == 4 / 2;\nt = (g(2), g(2.0f64), g(2r), g(3));\n";
    assert_eq!(value(text, "t"), "(false, true, true, false)");
}
#[test]
fn literals_of_two_parameters_are_split_on_each_alone() {
    // A tuple: a sum of the two products would join `x` and `y` in one class.
    let body = "(x * (1 + 1), y * (2 + 3))";
    for (arg, ty) in [
        ("1, 2", "int"),
        ("1.5f64, 2.0f64", "f64"),
        ("1r, 2r", "rat"),
    ] {
        let (generic, typed) = both(&["x", "y"], body, arg, ty);
        assert_eq!(generic, typed, "{body} at {arg}");
    }
    let t = term(&format!("f(positional x, positional y) = {body};\n"), "f");
    assert_eq!(t.matches("match x").count(), 1, "{t}");
    assert_eq!(t.matches("match y").count(), 1, "{t}");
}

/// A function of one parameter times `n` literals added: `x * (1 + 1 + … + 1)`, the text
/// `bench/operations.rs` measures.
pub(super) fn chain(n: usize) -> String {
    format!("f(positional x) = x * ({});\n", vec!["1"; n].join(" + "))
}

#[test]
fn an_operation_on_several_literals_is_one_match() {
    let t = term(&chain(4), "f");
    assert_eq!(t.matches("match").count(), 1, "{t}");
    assert_eq!(checked(&chain(4)).elab(), elab(&chain(4)).unwrap());
    let (generic, typed) = both(&["x"], "x * (1 + 1 + 1 + 1)", "1.5f64", "f64");
    assert_eq!(generic, typed);
}

/// A function of one parameter times a sum of `n` terms, each a quotient, a decimal, a power or
/// an integer in turn: `x * (1 / 2 + 1.5 + (1 / 2) ^ 2 + 1 + 1 / 2 + …)`, the text
/// `bench/operations.rs` measures for STAGE-generic-fold-div. The power is of a quotient: `2 ^ 2`
/// is an `int` in the last arm, where `1 / 2` is a `rat`, and a literal following their sum
/// takes the old path (plan row STAGE-generic-fold-int-arm).
pub(super) fn mixed_chain(n: usize) -> String {
    let terms = ["1 / 2", "1.5", "(1 / 2) ^ 2", "1"];
    let sum: Vec<&str> = (0..n).map(|i| terms[i % terms.len()]).collect();
    format!("f(positional x) = x * ({});\n", sum.join(" + "))
}

#[test]
fn a_sum_of_quotients_decimals_and_powers_is_one_match() {
    let t = term(&mixed_chain(8), "f");
    assert_eq!(t.matches("match").count(), 1, "{t}");
    assert_eq!(
        checked(&mixed_chain(8)).elab(),
        elab(&mixed_chain(8)).unwrap()
    );
    let body = "x * (1 / 2 + 1.5 + (1 / 2) ^ 2 + 1 + 1 / 2 + 1.5 + (1 / 2) ^ 2 + 1)";
    assert!(mixed_chain(8).contains(body));
    for (arg, ty) in [("1.5f64", "f64"), ("3r", "rat"), ("1.5f32", "f32")] {
        let (generic, typed) = both(&["x"], body, arg, ty);
        assert_eq!(generic, typed, "at {arg}");
    }
}
