//! An operation on generic literals alone, as `2 + 0` in `x * (2 + 0)`, takes its carrier by
//! one `match` on what gives the literals theirs and is built once per carrier inside it, so
//! the build stage folds each arm to a constant (STAGE-generic-fold, COMPLEXITY.md F85).
//! Each value is checked against the same body at a parameter of the carrier written out.

use zed_tests::scaling;

use zed_tests::step_helpers::l01_16_elaboration::{checked, elab, term, value};

/// The value of `f` of `body` at the argument `arg`, `f`'s parameters generic, and at `ty`,
/// each parameter declared of that type.
fn both(params: &[&str], body: &str, arg: &str, ty: &str) -> (String, String) {
    let generic: Vec<String> = params.iter().map(|p| format!("positional {p}")).collect();
    let typed: Vec<String> = params.iter().map(|p| format!("positional {p}: {ty}")).collect();
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
    for body in ["x + (1 + 2) * 3", "x * -(2 + 1)", "x - (1 - 2 - 3 - 4)"] {
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
    ];
    let args = [("1", "int"), ("1.5f64", "f64"), ("3r", "rat"), ("1.5f32", "f32")];
    for body in bodies {
        for (arg, ty) in args {
            if ty == "int" && body.contains('/') {
                continue;
            }
            let (generic, typed) = both(&["x"], body, arg, ty);
            assert_eq!(generic, typed, "{body} at {arg}");
        }
    }
}

#[test]
fn literals_of_two_parameters_are_split_on_each_alone() {
    let body = "x * (1 + 1) + y * (2 + 3)";
    for (arg, ty) in [("1, 2", "int"), ("1.5f64, 2.0f64", "f64"), ("1r, 2r", "rat")] {
        let (generic, typed) = both(&["x", "y"], body, arg, ty);
        assert_eq!(generic, typed, "{body} at {arg}");
    }
    let t = term(&format!("f(positional x, positional y) = {body};\n"), "f");
    assert_eq!(t.matches("match x").count(), 1, "{t}");
    assert_eq!(t.matches("match y").count(), 1, "{t}");
}

/// A function of one parameter times `n` literals added: `x * (1 + 1 + … + 1)`.
fn chain(n: usize) -> String {
    format!("f(positional x) = x * ({});\n", vec!["1"; n].join(" + "))
}

#[test]
fn an_operation_on_many_literals_elaborates_in_linear_time() {
    std::thread::Builder::new()
        .stack_size(1 << 29)
        .spawn(|| {
            assert_eq!(term(&chain(3), "f").matches("match").count(), 1);
            let n = 1000;
            let units = [checked(&chain(n)), checked(&chain(scaling::FACTOR * n))];
            assert_eq!(units[0].elab(), elab(&chain(n)).unwrap());
            scaling::check("elaborating an operation on n generic literals", n, |m| {
                units[usize::from(m != n)].elab();
            });
        })
        .unwrap()
        .join()
        .unwrap();
}
