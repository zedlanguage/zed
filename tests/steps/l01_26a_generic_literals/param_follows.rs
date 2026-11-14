//! In a function body, an operation on literals alone compared by `==` or `!=` with a
//! parameter follows the parameter's carrier at each call, as a bare literal does (DESIGN.md
//! L1.26a: under `==` a literal "follows the class without removing carriers from it", and an
//! operation on literals alone "is a literal too and takes the carrier of what it meets"; plan
//! row LIT-generic-class-follows). `g(positional x) = x == 1 + 1` gave `false` for
//! `g(2.0f64)`, since `1 + 1` took `int` where the function ended, while
//! `g(x: f64) = x == 1 + 1` gave `true`.

use zed_tests::step_helpers::l01_19_whole_file_ports::run;
use zed_tests::step_helpers::l01_26_type_resolution::type_errors;

/// The program defining `def` and printing `calls`, each a call written in Zed, on one line.
fn program(def: &str, calls: &[&str]) -> String {
    let shown: Vec<String> = calls.iter().map(|c| format!("${{{c}}}")).collect();
    format!(
        "{def}\nmain(args: MainArgs) -> int = {{ args.stdout <- \"{}\"; 0 }};\n",
        shown.join(" ")
    )
}

/// Checks and runs the program of `def` and `calls`, and returns what it prints.
fn prints(name: &str, def: &str, calls: &[&str]) -> String {
    let src = program(def, calls);
    assert_eq!(type_errors(&src), Vec::<String>::new(), "{src}");
    let out = run(name, &src, "", &[]);
    assert_eq!((out.status, out.stderr.as_str()), (0, ""), "{src}");
    out.stdout
}

#[test]
fn an_operation_on_literals_takes_the_carrier_of_the_parameter_it_is_compared_with() {
    // f64, f32, rat and int arguments, and the same line with the parameter's type written.
    let def = "g(positional x) = x == 1 + 1;\nh(x: f64) = x == 1 + 1;";
    let calls = ["g(2.0f64)", "g(2.0f32)", "g(2r)", "g(2)", "h(x: 2.0f64)"];
    let out = prints("l01_26a_param_follows_sum", def, &calls);
    assert_eq!(out, "true true true true true\n");
    // Another value at each carrier.
    let calls = ["g(3.0f64)", "g(2.5f32)", "g(5r/2r)", "g(3)"];
    let out = prints("l01_26a_param_follows_sum_other", def, &calls);
    assert_eq!(out, "false false false false\n");
}

#[test]
fn the_operation_follows_on_either_side_and_under_not_equal() {
    let calls = ["g(2.0f64)", "g(2.0f32)", "g(2r)", "g(2)", "g(3.0f64)"];
    for (i, def) in [
        "g(positional x) = 1 + 1 == x;",
        "g(positional x) = !(x != 1 + 1);",
        "g(positional x) = !(1 + 1 != x);",
        "g(positional x) = x == -(1 + 1) * -1;",
    ]
    .into_iter()
    .enumerate()
    {
        let out = prints(&format!("l01_26a_param_follows_side_{i}"), def, &calls);
        assert_eq!(out, "true true true true false\n", "{def}");
    }
    // A `/` of integer literals removes `int` (L1.26a), so at an `int` the quotient is not
    // read and the comparison is false, though `4 / 2` is a whole number.
    let def = "g(positional x) = x == 4 / 2;";
    let out = prints("l01_26a_param_follows_quotient", def, &calls);
    assert_eq!(out, "true true true false false\n");
}

#[test]
fn an_operation_no_int_holds_is_false_at_an_int_as_a_bare_decimal_literal_is() {
    // `1 / 2` and `0.5 + 0.5 - 0.5` hold no `int`: at an `int` argument, or a value of no
    // number, the comparison is false, as `x == 0.5` is.
    let calls = [
        "g(0.5f64)",
        "g(0.5f32)",
        "g(1r/2r)",
        "g(2)",
        "g(0)",
        "g(\"a\")",
    ];
    for (i, def) in [
        "g(positional x) = x == 0.5;",
        "g(positional x) = x == 1 / 2;",
        "g(positional x) = x == 0.5 + 0.5 - 0.5;",
        "g(positional x) = 1 / 2 == x;",
    ]
    .into_iter()
    .enumerate()
    {
        let out = prints(&format!("l01_26a_param_follows_no_int_{i}"), def, &calls);
        assert_eq!(out, "true true true false false false\n", "{def}");
    }
    // A float format alone: `2^0.5` at each float format, and false at `rat` and `int`.
    let def = "g(positional x) = x == 2^0.5;";
    let calls = ["g(2.0f64^0.5)", "g(2.0f32^0.5)", "g(1r)", "g(1)"];
    let out = prints("l01_26a_param_follows_float", def, &calls);
    assert_eq!(out, "true true false false\n");
}

#[test]
fn a_value_of_no_number_compares_unequal() {
    let def = "g(positional x) = x == 1 + 1;";
    let calls = ["g(\"2\")", "g(true)", "g(2)"];
    let out = prints("l01_26a_param_follows_no_number", def, &calls);
    assert_eq!(out, "false false true\n");
}

#[test]
fn components_and_several_parameters_follow_each_their_own() {
    let def = "g(positional p) = p[0] == 1 + 1;";
    let calls = [
        "g((2.0f64, 1))",
        "g((2r, \"a\"))",
        "g((2, 1))",
        "g((3.0f32, 1))",
    ];
    let out = prints("l01_26a_param_follows_component", def, &calls);
    assert_eq!(out, "true true true false\n");
    let def = "g(positional x, positional y) = x == 1 + 1 && y == 3 * 2;";
    let calls = ["g(2.0f64, 6r)", "g(2, 6.0f32)", "g(2r, 7)"];
    let out = prints("l01_26a_param_follows_two", def, &calls);
    assert_eq!(out, "true true false\n");
}

#[test]
fn an_integer_sum_past_two_to_the_53_compares_as_with_the_type_written() {
    // At `f64`, `9007199254740992 + 1` rounds to `9007199254740992.0`, as it does where the
    // parameter is declared `f64`; at `int` and `rat` it is exact.
    let def = "g(positional x) = x == 9007199254740992 + 1;\n\
               h(x: f64) = x == 9007199254740992 + 1;";
    let calls = [
        "g(9007199254740992.0f64)",
        "h(x: 9007199254740992.0f64)",
        "g(9007199254740993)",
        "g(9007199254740992)",
        "g(9007199254740993r)",
    ];
    let out = prints("l01_26a_param_follows_big", def, &calls);
    assert_eq!(out, "true true true false true\n");
}

#[test]
fn an_operation_with_a_need_of_its_own_keeps_its_carrier() {
    // The base of `2^-1` needs a carrier other than `int`; nothing at a call gives the base
    // the parameter's carrier, so it is read at `int` and rejected, with the repair checked.
    let src = program("g(positional x) = x == 2^-1;", &["g(0.5f64)"]);
    let errs = type_errors(&src);
    assert!(
        errs.iter()
            .any(|e| e.contains("Int power with a negative exponent: `2 : int ^ -1 : int`.")),
        "{src}{errs:#?}"
    );
    let def = "g(positional x) = x == 2.0f64^-1;";
    let out = prints("l01_26a_param_follows_power_repair", def, &["g(0.5f64)"]);
    assert_eq!(out, "true\n");
}

/// A body of `n` comparisons of the parameter `x` with operations on literals alone:
/// `g(positional x) = { c0 = x == 0 + 1; …; c0 };` (plan row LIT-generic-class-follows).
pub(super) fn comparisons(n: usize) -> String {
    let lines: String = (0..n)
        .map(|i| format!("c{i} = x == {i} + {}; ", i % 7))
        .collect();
    format!("g(positional x) = {{ {lines}c0 }};\n")
}

#[test]
fn comparisons_of_a_parameter_with_operations_on_literals_check() {
    // A small instance of the benchmark
    // `bench::param_follows::comparisons_with_a_parameter_are_checked_in_linear_time`.
    assert_eq!(type_errors(&comparisons(4)), Vec::<String>::new());
}
