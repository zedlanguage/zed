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
        // Not one `match`: a decimal's arms and an exponent's carriers differ from the
        // other operand's, and the operation keeps the `let` of `follow`.
        "x * (1.5 + 1)",
        "x * ((2 + 1) ^ 2)",
    ];
    let args = [
        ("1", "int"),
        ("1.5f64", "f64"),
        ("3r", "rat"),
        ("1.5f32", "f32"),
    ];
    for body in bodies {
        for (arg, ty) in args {
            if ty == "int" && (body.contains('/') || body.contains('.')) {
                continue;
            }
            let (generic, typed) = both(&["x"], body, arg, ty);
            assert_eq!(generic, typed, "{body} at {arg}");
        }
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
