//! Completeness of steps L1.26a and L1.26b by the features a literal meets (row
//! TEST-complete-literals, author P189): atoms and `else`, casts, declared parameters and
//! declared unions, the forms of a number (bases, separators, exponents), signs, zero and the
//! bounds of `int` and `f32`, literals of two carriers in one expression, comparisons, `^`, and
//! a program run through its ports. Each expected type and value is the one DESIGN.md L1.26a,
//! L1.26b, sec:domains and the operator table give; COMPLETENESS.md lists the cases.

use zed_tests::step_helpers::l01_16_elaboration::{errors, value};
use zed_tests::step_helpers::l01_19_whole_file_ports::run;
use zed_tests::step_helpers::l01_26_type_resolution::{info, sig, type_errors};

use super::{T, T_NO_INT};

/// `src` is accepted, and each `(name, value)` evaluates to that value.
fn values(src: &str, want: &[(&str, &str)]) {
    assert_eq!(type_errors(src), Vec::<String>::new(), "{src}");
    for (name, v) in want {
        assert_eq!(value(src, name), *v, "{src}\n`{name}`");
    }
}

/// The type the checker gives the top-level name `name` of the accepted `src`.
fn top(src: &str, name: &str) -> String {
    let (i, _) = info(src);
    let errors: Vec<&str> = i.errors.iter().map(|e| e.message.as_str()).collect();
    assert!(errors.is_empty(), "{src}\nerrors: {errors:?}");
    i.tops.get(name).expect("a type for the name").to_string()
}

/// `src` is rejected with one message, which holds each of `parts`.
fn rejected(src: &str, parts: &[&str]) {
    let errors = type_errors(src);
    assert_eq!(errors.len(), 1, "{src}\n{errors:?}");
    for p in parts {
        assert!(errors[0].contains(p), "{src}\n{:?} lacks {p:?}", errors[0]);
    }
}

#[test]
fn a_literal_beside_an_operation_that_may_give_an_atom_keeps_the_atom() {
    assert_eq!(
        sig("f(x: int, d: int) = x div d + 1;\n", "f"),
        "(x: int, d: int) -> int | #divByZero"
    );
    // `/` by the literal `0` takes every carrier but `int` and gives `#divByZero` at `rat`.
    let src = "f(x) = x / 0;\na = f(x: 7r);\n";
    assert_eq!(
        sig(src, "f"),
        "(x: T) -> T | #divByZero for T in f32 | f64 | rat"
    );
    values(src, &[("a", "#divByZero")]);
    // An `int` `div` by the literal `0` gives only an atom, which is an error (always-atom).
    assert!(!type_errors("f(x: int) = x div 0;\n").is_empty());
    // An `if` branch that is an atom beside a literal: the union of both.
    let src = "f(positional c: bool) = if c { 1 } else { #none };\na = f(false);\n";
    assert_eq!(sig(src, "f"), "(bool) -> 1 | #none");
    values(src, &[("a", "#none")]);
    // An atom operand gives the atom whatever the literal.
    assert_eq!(
        sig("f(positional x) = x + #none;\n", "f"),
        "(T) -> #none for T in int | f32 | f64 | rat"
    );
}

#[test]
fn a_literal_cast_takes_the_carrier_the_cast_names() {
    values(
        "a = f64(1);\nb = rat(1) / 2;\nc = f64(1) / 2;\n",
        &[("a", "1.0"), ("b", "1r/2r"), ("c", "0.5")],
    );
}

#[test]
fn a_literal_argument_of_a_declared_parameter_is_read_at_its_carrier() {
    values(
        "r(x: rat) = x;\na = r(x: 1);\nb = r(x: 0.1);\nc = r(x: 0.5);\n\
         d(x: f64) = x;\ne = d(x: 0.5);\n",
        &[("a", "1r"), ("b", "1r/10r"), ("c", "1r/2r"), ("e", "0.5")],
    );
    // A decimal is never an `int`.
    assert_eq!(
        type_errors("i(x: int) = x;\na = i(x: 0.5);\n"),
        ["A decimal literal is never an `int`: the literal `0.5`. [0.5]"]
    );
}

#[test]
fn a_literal_argument_of_a_declared_union_takes_its_one_numeric_carrier() {
    // L1.26: a literal at a declared type takes the one numeric carrier of the type it can
    // take, in a tuple component too; beside two numeric carriers it is rejected with the menu
    // of each.
    values(
        "p(x: String | f64) = x;\na = p(x: 1);\n\
         q(x: (f64, f64) | (String, f64)) = x;\nb = q(x: (1, 2));\n\
         s(x: int | f64) = x;\nc = s(x: 1);\n",
        &[("a", "1.0"), ("b", "(1.0, 2.0)"), ("c", "1")],
    );
    rejected("p(x: f64 | rat) = x;\na = p(x: 1);\n", &["1r", "1.0f64"]);
    rejected(
        "p(x: f64 | rat) = x;\na = p(x: 0.5);\n",
        &["0.5r", "0.5f64"],
    );
}

#[test]
fn a_literal_out_of_the_range_of_a_float_is_rejected_with_the_rounding_it_would_take() {
    // sec:domains: a decimal that rounds to infinity or to zero in its format is rejected
    // with that rounding named and the exact `rat` offered.
    let e = errors("d(x: f64) = x;\ny = d(x: 1e-400);\n");
    assert!(
        e.iter().any(|m| m.contains(
            "`1e-400` is not zero, and it lies nearer to zero than to the least positive f64, \
             5.0e-324, so as an f64 it rounds to zero. Write `1e-400r` for the exact rational"
        )),
        "{e:?}"
    );
    let e = errors("y = 1e39f32;\n");
    assert!(
        e.iter().any(|m| m.contains(
            "`1e39` is larger than the largest f32, 3.4028235e38, so as an f32 it rounds to \
             infinity. Write `1e39r` for the exact rational"
        )),
        "{e:?}"
    );
    let e = errors("y = 1e-50f32;\n");
    assert!(
        e.iter().any(|m| m.contains(
            "`1e-50` is not zero, and it lies nearer to zero than to the least positive f32, \
             1.0e-45, so as an f32 it rounds to zero."
        )),
        "{e:?}"
    );
}

#[test]
fn a_decimal_past_the_range_of_f32_leaves_f32_out_of_a_class() {
    // L1.26b: a decimal keeps only the carriers it fits. The largest f32 keeps `f32`; a value
    // below the least positive f32 and one past the largest do not.
    assert_eq!(sig("f(x) = x + 3.4028235e38;\n", "f"), T_NO_INT);
    assert_eq!(
        sig("f(x) = x + 1e-46;\n", "f"),
        "(x: T) -> T for T in f64 | rat"
    );
    assert_eq!(
        sig("f(x) = x + 1e39;\n", "f"),
        "(x: T) -> T for T in f64 | rat"
    );
}

#[test]
fn the_forms_of_a_number_are_one_literal_each() {
    // Bases, separators and exponents (sec:lexical) change the spelling, not the use.
    let src = "f(x) = x + 0x10 + 0b1 + 0o7 + 1_0;\na = f(x: 2.5f64);\nb = f(x: 1);\n";
    assert_eq!(sig(src, "f"), T);
    values(src, &[("a", "36.5"), ("b", "35")]);
    let src = "f(x) = x * 1.5e2;\ng(x) = x * 2.5e-1;\na = f(x: 2r);\nb = g(x: 2r);\n";
    assert_eq!(sig(src, "f"), T_NO_INT);
    values(src, &[("a", "300r"), ("b", "1r/2r")]);
}

#[test]
fn signs_zero_and_the_bounds_of_i64_keep_their_exact_values() {
    // `int` is unbounded (sec:domains): one past each bound of i64 is an exact `int`.
    values(
        "a = 0 - 1;\nb = 9223372036854775807 + 1;\nc = -9223372036854775808 - 1;\n",
        &[
            ("a", "-1"),
            ("b", "9223372036854775808"),
            ("c", "-9223372036854775809"),
        ],
    );
    assert_eq!(top("a = -0;\n", "a"), "0");
    // The literal `0` takes `f64` with the sign rules of IEEE 754: `-2.5 * 0` is `-0.0`, and
    // `-0.0 + 0.0` is `0.0`.
    values(
        "f(x) = x * 0;\ng(x) = x + 0.0;\na = f(x: -2.5f64);\nb = g(x: -0.0f64);\n",
        &[("a", "-0.0"), ("b", "0.0")],
    );
}

#[test]
fn literals_of_two_carriers_meet_only_where_one_takes_the_other() {
    // An unsuffixed literal takes the carrier of the suffixed one beside it.
    values(
        "a = (1, 2.5f64)[0] + 1;\nb = 1 + 0.5 + 1r;\n",
        &[("a", "2"), ("b", "5r/2r")],
    );
    let src = "f(x, y) = x + y + 1;\na = f(x: 1r, y: 2r);\nb = f(x: 1.5f64, y: 2.0f64);\n";
    values(src, &[("a", "4r"), ("b", "4.5")]);
    assert_eq!(
        sig("f(x, y) = x + y + 0.5;\n", "f"),
        "(x: T, y: T) -> T for T in f32 | f64 | rat"
    );
    // Two suffixed literals, or two values, of different carriers have no common carrier.
    rejected("a = 1r == 1.0f64;\n", &["The suffix makes the literal"]);
    assert!(!type_errors("f(x: f64, y: rat) = x + 1 == y + 1;\n").is_empty());
    // Two literals compared alone take a carrier together.
    values(
        "a = 1 == 1;\nb = 0.5f64 == 1;\n",
        &[("a", "true"), ("b", "false")],
    );
}

#[test]
fn a_literal_compared_with_a_value_that_holds_no_number_is_offered_the_values_it_may_mean() {
    // LIT-eq-kind: no number equals a `String`, a `bool` or a tuple, so the literal is
    // rejected with a menu of the values of the other operand's type it may mean.
    rejected("f(x: String) = x == 1;\n", &["x == \"1\""]);
    rejected("f(x: bool) = x == 1;\n", &["true", "false"]);
    rejected("f(x: (int, int)) = x == 1;\n", &["x[0]", "x[1]"]);
    rejected("f(x: String) = 1 != x;\n", &["\"1\" != x"]);
    // An atom is a value of the other operand's type.
    assert_eq!(
        type_errors("f(x: String | #none) = x == #none;\n"),
        Vec::<String>::new()
    );
}

#[test]
fn an_operator_that_takes_no_number_rejects_a_literal() {
    for src in [
        "f(x: bool) = x && 1;\n",
        "f(x: bool) = !x + 1;\n",
        "f(x: String) = x ++ 1;\n",
    ] {
        assert!(!type_errors(src).is_empty(), "{src}");
    }
}

#[test]
fn a_literal_branch_beside_a_branch_of_another_type_keeps_both() {
    let g = "g(positional c: bool) = ";
    for (body, want) in [
        ("if c { 1 } else { \"s\" }", "(bool) -> 1 | \"s\""),
        ("if c { 1 } else { true }", "(bool) -> 1 | true"),
        ("if c { -1 } else { 0x10 }", "(bool) -> -1 | 16"),
        ("if c { 1.50 } else { 1e2 }", "(bool) -> 1.5 | 100.0"),
        ("if c { 1 } else { 1 }", "(bool) -> 1"),
    ] {
        assert_eq!(sig(&format!("{g}{body};\n"), "g"), want, "{body}");
    }
    // A declared `int` beside a decimal branch: the union `2.5 | int`, to which `+ 1` gives
    // no carrier for both.
    assert_eq!(
        sig("g(c: bool, x: int) = if c { x } else { 2.5 };\n", "g"),
        "(c: bool, x: int) -> 2.5 | int"
    );
    assert!(!type_errors("g(c: bool, x: int) = (if c { x } else { 2.5 }) + 1;\n").is_empty());
    assert_eq!(
        sig("g(c: bool, x: f64) = if c { x } else { 1 };\n", "g"),
        "(c: bool, x: f64) -> 1 | f64"
    );
}

#[test]
fn a_literal_branch_at_a_declared_parameter_is_read_at_its_carrier() {
    // L1.26a: "`h(if b { r } else { 0.1 })` with `h(positional z: rat)` is `1r/10r` where `b`
    // is false", here with `r` a parameter; and two literal branches read at `rat` and `f64`.
    values(
        "h(positional z: rat) = z;\nk(positional y: rat) = h(if false { y } else { 0.1 });\n\
         a = k(1r);\nb = h(if false { 1 } else { 0.1 });\nc = h(if false { 1r } else { 0.1r });\n\
         d(positional z: f64) = z;\ne = d(if false { 1.0f64 } else { 0.1 });\n",
        &[
            ("a", "1r/10r"),
            ("b", "1r/10r"),
            ("c", "1r/10r"),
            ("e", "0.1"),
        ],
    );
}

#[test]
fn a_power_takes_the_integer_or_the_float_power_by_its_operands() {
    // The operator table: `^` takes the integer or the floating-point power; a `rat` base
    // takes an `int` exponent of either sign and gives the exact `rat`; `0r^-1` is
    // `#divByZero`; `-x^2` is `-(x^2)`; `^` is right-associative; an int power with a
    // negative exponent is rejected.
    let src = "f(positional x: rat) = x ^ 2;\na = f(3r/2r);\n";
    assert_eq!(sig(src, "f"), "(rat) -> rat");
    values(src, &[("a", "9r/4r")]);
    values(
        "a = (2r/3r)^-2;\nb = -2^2;\nc = 2^3^2;\nd = 0r^-1;\n",
        &[
            ("a", "9r/4r"),
            ("b", "-4"),
            ("c", "512"),
            ("d", "#divByZero"),
        ],
    );
    assert_eq!(top("a = 0r^-1;\n", "a"), "rat | #divByZero");
    rejected("a = 2^-1;\n", &["Int power with a negative exponent"]);
    // A literal exponent beside a class: `x ^ 2` is the integer power, defined at `int` and
    // the floats; `x ^ 2.0` the float power alone.
    assert_eq!(
        sig("f(positional x) = x ^ 2;\n", "f"),
        "(T) -> T for T in int | f32 | f64"
    );
    let src = "f(positional x) = x ^ 2.0;\na = f(1.5f64);\n";
    assert_eq!(sig(src, "f"), "(T) -> T for T in f32 | f64");
    values(src, &[("a", "2.25")]);
    assert_eq!(
        sig("f(positional x, positional k: int) = x ^ k;\n", "f"),
        "(T, int) -> T | #divByZero for T in int | f32 | rat"
    );
}

#[test]
fn a_rat_literal_folds_with_integer_and_decimal_literals_at_a_rat_parameter() {
    values(
        "h(positional z: rat) = z;\na = h(1 + 2r);\nb = h(2r * 0.5 + 1);\nc = h((2r/3r)^-2);\n",
        &[("a", "3r"), ("b", "2r"), ("c", "9r/4r")],
    );
    // At `f64` the `2r` has no carrier in common with the parameter.
    rejected(
        "h(positional z: f64) = z;\na = h(1 + 2r);\n",
        &["`h` does not take (rat)"],
    );
}

#[test]
fn a_literal_cast_compared_with_a_value_of_another_type_is_always_false() {
    // The cast of a literal is named as written in the message.
    rejected(
        "f(x: String) = x == rat(\"1/3\");\n",
        &["`x : String == rat(\"1/3\") : rat` is always `false`"],
    );
    rejected(
        "f(x: bool) = f64(\"1.5\") == x;\n",
        &["`f64(\"1.5\") : f64 == x : bool` is always `false`"],
    );
}

#[test]
fn an_integer_literal_with_no_exact_float_is_rejected_at_that_float() {
    // sec:domains: an integer literal is that integer exactly; 2^24 + 1 is no `f32`, and
    // 2^53 + 1 is no `f64`, whose fix is the nearer `f64` by ties to even.
    rejected(
        "h(positional z: f32) = z;\na = h(16777217);\n",
        &["No `f32` equals the literal `16777217`."],
    );
    rejected(
        "h(positional z: f64) = z;\na = h(9007199254740993);\n",
        &[
            "No `f64` equals the literal `9007199254740993`.",
            "a = h(9007199254740992)",
        ],
    );
    values(
        "h(positional z: f32) = z;\na = h(0.1);\nb = h(0.5);\n",
        &[("a", "0.1f32"), ("b", "0.5f32")],
    );
}

#[test]
fn a_literal_in_a_program_run_through_its_ports_takes_its_carrier() {
    // The whole path, `main` and its standard output: a `rat` power in a string hole.
    let src = "main(m: MainArgs) {\n    m.stdout <- \"${(2r/3r)^-2} ${1 + 0.5f64}\";\n}\n";
    let out = run("lit_ports", src, "", &[]);
    assert_eq!(out.status, 0, "{}", out.stderr);
    assert_eq!(out.stdout, "9r/4r 1.5\n");
}

#[test]
fn a_rat_literal_in_an_operation_on_literals_at_a_rat_parameter_keeps_its_exact_value() {
    values(
        "h(positional z: rat) = z;\na = h(1 + 0.5r);\nb = h(0.5r * 2);\n",
        &[("a", "3r/2r"), ("b", "1r")],
    );
}

#[test]
fn a_lambda_needs_a_parameter_for_each_argument_passed_by_position() {
    rejected(
        "ap(f: (int, int) -> int) = f(1, 2);\na = ap(f: x -> x);\n",
        &["the lambda takes 1 parameter, and `(int, int) -> int` passes 2 by position"],
    );
    rejected(
        "ap(f: (int, int) -> int) = f(1, 2);\na = ap(f: (x, y, z) -> x);\n",
        &["the lambda's parameter `z` is not a parameter of `(int, int) -> int`"],
    );
}

#[test]
fn several_literal_arguments_a_call_refuses_are_one_error_that_counts_them() {
    // sec:diagnostics, row "Numeric literal at a carrier that cannot take it": one error at
    // the first literal, whose headline counts them; by position or by name, the same literal
    // twice or two different ones.
    for src in [
        "g(positional a: int, positional b: int) = a;\ny = g(0.5, 0.25);\n",
        "g(positional a: int, positional b: int) = a;\ny = g(0.5, 0.5);\n",
        "g(a: int, b: int) = a;\ny = g(a: 0.5, b: 0.5);\n",
    ] {
        rejected(
            src,
            &["2 arguments of `g` are literals at carriers they cannot take. [0.5]"],
        );
    }
}
