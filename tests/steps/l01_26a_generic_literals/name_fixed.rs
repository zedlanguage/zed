//! A name in a body bound to an operation on literals alone fixes its carrier where it is bound
//! (QUESTIONS A63, item LIT-name-int-fixed), as one outside every function does: `b = 2^62` is
//! an `int`, and `q = 1.5 + 1` is rejected at its binding. Until this item, the class of the
//! literals resolved only at the function's end, so a later use gave the name its carrier:
//! `b = 2^2000; c = b + 0.5f64` printed `inf`, `b = 2^62; c = b + 0.5f64` printed
//! `4611686018427388000.0`, and `q = 1.5 + 1; z = q * 2.0f64` printed `5.0`. A class that holds a
//! parameter is not fixed: a call gives it its carrier.

use zed_tests::step_helpers::l01_16_elaboration::value;
use zed_tests::step_helpers::l01_26_type_resolution::{info, sig, type_errors};

/// `main` with the lines `body`, each indented, and the one error its check gives: the error's
/// line, counted from 1, and its message.
fn one_error(body: &[&str]) -> (usize, String) {
    let mut src = String::from("main(m: MainArgs) {\n");
    for line in body {
        src += &format!("    {line}\n");
    }
    src += "}\n";
    let (i, _) = info(&src);
    assert_eq!(i.errors.len(), 1, "{src}: {:?}", i.errors);
    let e = &i.errors[0];
    let line = src[..e.span.start].matches('\n').count() + 1;
    (line, e.message.clone())
}

#[test]
fn an_int_name_meets_an_f64_and_is_rejected_at_the_use() {
    // The first two programs of the item: `b` is an `int`, so `+` meets an `int` and an `f64`, and
    // `f64(b)` would round `b` (2^2000 and 2^62 are past 2^53): no fix is offered, as outside
    // every function.
    for b in ["2^2000", "2^62"] {
        let (line, m) = one_error(&[
            &format!("b = {b};"),
            "c = b + 0.5f64;",
            "m.stdout <- String(c);",
        ]);
        assert_eq!(line, 3, "{m}");
        assert!(
            m.starts_with("The suffix makes the literal `0.5f64` an `f64`, never `int`."),
            "{m}"
        );
        assert!(m.contains("No fix is offered"), "{m}");
    }
    // Within ±2^53 the cast is exact, and it is the fix.
    let (line, m) = one_error(&["b = 2^3;", "c = b + 0.5f64;", "m.stdout <- String(c);"]);
    assert_eq!(line, 3, "{m}");
    assert!(m.contains("Try `c = f64(b) + 0.5f64` instead."), "{m}");
}

#[test]
fn a_decimal_operation_is_rejected_at_its_binding() {
    // The third program of the item: once, at the binding, with the fixes written as the
    // binding, and not again at the use or at the function's end.
    let (line, _) = one_error(&["q = 1.5 + 1;", "z = q * 2.0f64;", "m.stdout <- String(z);"]);
    assert_eq!(line, 2);
    let errors = type_errors(
        "main(m: MainArgs) {\n    q = 1.5 + 1;\n    z = q * 2.0f64;\n    m.stdout <- String(z);\n}\n",
    );
    let m = &errors[0];
    for (fix, v) in [
        ("q = 1.5f64 + 1;", "q is 2.5"),
        ("q = 1.5r + 1;", "q is 5r/2r"),
    ] {
        let line = m.lines().find(|l| l.trim_start().starts_with(fix));
        assert!(line.is_some_and(|l| l.contains(v)), "{m}");
    }
}

#[test]
fn a_body_and_the_top_level_give_the_same_error() {
    for (top, body) in [
        (
            "b = 2^62;\nc = b + 0.5f64;\n",
            "b = 2^62; c = b + 0.5f64; return c;",
        ),
        (
            "q = 1.5 + 1;\nz = q * 2.0f64;\n",
            "q = 1.5 + 1; z = q * 2.0f64; return z;",
        ),
    ] {
        let top = type_errors(top);
        let body = type_errors(&format!("f() {{ {body} }}\n"));
        assert_eq!((top.len(), body.len()), (1, 1), "{top:?} {body:?}");
        let headline = |e: &str| e.split(['.', ':']).next().unwrap_or_default().to_owned();
        assert_eq!(headline(&top[0]), headline(&body[0]), "{top:?} {body:?}");
    }
}

#[test]
fn a_name_reached_through_a_tuple_or_a_chain_is_fixed_too() {
    // A component of a tuple, and a name bound to another plus a literal: each was read at the
    // carrier of its last use.
    let (line, m) = one_error(&[
        "t = (2^62, 1);",
        "c = t[0] + 0.5f64;",
        "m.stdout <- String(c);",
    ]);
    assert_eq!(line, 3, "{m}");
    let (line, m) = one_error(&[
        "b0 = 2^3;",
        "b1 = b0 + 1;",
        "c = b1 + 0.5f64;",
        "m.stdout <- String(c);",
    ]);
    assert_eq!(line, 4, "{m}");
    assert!(m.contains("Try `c = f64(b1) + 0.5f64` instead."), "{m}");
    // Two targets: `b` is an `int`.
    let (line, m) = one_error(&[
        "a, b = (0.5f64, 1);",
        "c = b + 0.5f64;",
        "m.stdout <- String((a, c));",
    ]);
    assert_eq!(line, 3, "{m}");
}

#[test]
fn a_name_used_as_an_int_keeps_its_value() {
    for (body, v) in [
        ("b = 2^62; return b + 1;", "4611686018427387905"),
        ("b = 2^3; b1 = b + 1; return b1 * b1;", "81"),
        ("t = (2^62, 1); return t[0] - t[1];", "4611686018427387903"),
        ("q = 1.5f64 + 1; return q * 2.0f64;", "5.0"),
    ] {
        let src = format!("f() {{ {body} }}\ny = f();\n");
        assert_eq!(type_errors(&src), Vec::<String>::new(), "{src}");
        assert_eq!(value(&src, "y"), v, "{src}");
    }
    assert_eq!(sig("f() { b = 2^62; return b; }\n", "f"), "() -> int");
}

#[test]
fn a_class_of_a_parameter_is_left_to_the_call() {
    // `y` holds `x`: a call gives the class its carrier.
    assert_eq!(
        sig("f(x) { y = x + 1; return y; }\n", "f"),
        "(x: T) -> T for T in int | f32 | f64 | rat"
    );
    // `b = 2` is an `int`, as outside every function, so `x` is one too.
    assert_eq!(
        sig("f(x) { b = 2; return x * b; }\n", "f"),
        "(x: int) -> int"
    );
    assert_eq!(sig("b = 2;\nf(x) = x * b;\n", "f"), "(x: int) -> int");
}

/// A body of `n` names, each bound to the last plus `2^3`, an operation on literals alone and so
/// a class of its own at each binding, from `2^3`, returning the last.
pub(super) fn chain(n: usize) -> String {
    let mut src = String::from("f() {\n    b0 = 2^3;\n");
    for i in 1..n {
        src += &format!("    b{i} = b{} + 2^3;\n", i - 1);
    }
    src + &format!("    return b{};\n}}\n", n - 1)
}

/// A body binding a tuple of `n` parts `1.5 + 1`, rejected at the binding in one error that
/// names each part, as outside every function.
pub(super) fn decimals(n: usize) -> String {
    let parts: Vec<&str> = vec!["1.5 + 1"; n];
    format!(
        "f() {{\n    t = ({});\n    return t;\n}}\n",
        parts.join(", ")
    )
}


#[test]
fn a_chain_of_bindings_of_literals_is_an_int() {
    // A small instance of the benchmark
    // `bench::name_fixed::bindings_of_literals_check_in_linear_time`.
    assert_eq!(sig(&chain(3), "f"), "() -> int");
}

#[test]
fn rejected_parts_of_a_binding_are_one_error() {
    // A small instance of the benchmark
    // `bench::name_fixed::rejected_parts_of_a_binding_check_in_linear_time`.
    let errors = type_errors(&decimals(3));
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(
        errors[0].starts_with("3 parts of the value of `t`"),
        "{errors:?}"
    );
}
