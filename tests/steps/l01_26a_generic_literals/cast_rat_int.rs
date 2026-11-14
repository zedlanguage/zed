//! `rat` of an operation on integer literals alone (item CAST-rat-int). In a body, a name bound
//! to such an operation, `b = 2^64 + 13`, took the type of the literals' class, which only
//! resolved at the function's end, and `rat(b)` took the `#invalid` of the `f64`, `f32` and
//! `String` arrows of `rat` from it, so `String(rat(b) ^ (2^64))` asked for an `else`. A cast
//! keeps an atom only where its operand can give it (QUESTIONS A36), and `rat` of an int never
//! gives one. A name bound to integer literals alone is an `int` where it is bound (QUESTIONS
//! A63, item LIT-name-int-fixed), in a body as outside every function, so `rat(b)` gives `rat`,
//! and a use that would take another carrier from `b` is rejected at the use, before the cast or
//! after it. `rat` of a `String` or an `f64` keeps `#invalid`, and so does `rat` of a parameter,
//! which may be any value of its carrier.

use zed_tests::step_helpers::l01_16_elaboration::value;
use zed_tests::step_helpers::l01_26_type_resolution::{info, sig, type_errors};

/// The signature of `f` in `src`, which checks with no error.
fn sig_f(src: &str) -> String {
    assert_eq!(type_errors(src), Vec::<String>::new(), "{src}");
    sig(src, "f")
}

#[test]
fn rat_of_an_operation_on_integer_literals_in_a_body_has_no_atom() {
    // The case of the item, then the same operand written in place, and smaller and negative
    // values, all of which were `rat | #invalid`.
    for (body, v) in [
        ("b = 2^64 + 13; return rat(b);", "18446744073709551629r"),
        ("return rat(2^64 + 13);", "18446744073709551629r"),
        ("b = 2^3; b1 = b + 1; return rat(b1);", "9r"),
        (
            "b = -(2^70) * 3 - 1; return rat(b);",
            "-3541774862152233910273r",
        ),
        ("b = 2^3; return rat(b) + rat(b + 1);", "17r"),
    ] {
        let src = format!("f() {{ {body} }}\ny = f();\n");
        let t = sig_f(&src);
        assert!(!t.contains('#'), "{src}: {t}");
        assert_eq!(value(&src, "y"), v, "{src}");
    }
}

#[test]
fn the_program_of_the_item_needs_no_else() {
    let src = "main(m: MainArgs) {\n    b = 2^64 + 13;\n    m.stdout <- String(rat(b) ^ 2);\n}\n";
    assert_eq!(type_errors(src), Vec::<String>::new(), "{src}");
}

#[test]
fn rat_of_a_string_an_f64_or_a_parameter_keeps_invalid() {
    for (src, ty) in [
        ("f(s: String) = rat(s);\n", "(s: String) -> rat | #invalid"),
        ("f(x: f64) = rat(x);\n", "(x: f64) -> rat | #invalid"),
        (
            "f(x: f32) { y = x + 1; return rat(y); }\n",
            "(x: f32) -> rat | #invalid",
        ),
    ] {
        assert_eq!(sig_f(src), ty, "{src}");
    }
    // A parameter with no type may be a float, a NaN among its values, even with a literal
    // beside it: the class is the parameter's, not one of literals alone.
    let t = sig_f("f(x) { y = x + 1; return rat(y); }\n");
    assert!(t.contains("#invalid"), "{t}");
}

#[test]
fn a_decimal_literal_is_still_given_no_carrier_by_rat() {
    // `rat` takes every carrier, so it fixes none for a decimal literal, as `rat(1.5)`.
    for body in [
        "return rat(1.5);",
        "return rat(1.5 + 1);",
        "b = 1.5 + 1; return rat(b);",
    ] {
        let src = format!("f() {{ {body} }}\n");
        let errors = type_errors(&src);
        assert_eq!(errors.len(), 1, "{src}: {errors:?}");
        assert!(errors[0].contains("a carrier"), "{src}: {errors:?}");
    }
}

#[test]
fn a_use_that_takes_another_carrier_from_the_operand_is_rejected_at_the_use() {
    // `b` is an `int` where it is bound (QUESTIONS A63), so a use that would take another
    // carrier from it is rejected as it is with `b: int`, with a cast of `b` as the fix, whether
    // it comes after the cast or before it. The headlines are pinned in
    // `the_headline_prints_a_bound_name_as_its_type`.
    for body in [
        "b = 2^3; y = rat(b); c = b + 0.5f64; return (y, c);",
        "b = 2^3; y = rat(b); c = b + 1r; return (y, c);",
        "b = 2^3; y = rat(b); c = b + 0.5; return (y, c);",
        "b = 2^3; c = b + 0.5; y = rat(b); return (y, c);",
    ] {
        let src = format!("f() {{ {body} }}\n");
        let errors = type_errors(&src);
        assert_eq!(errors.len(), 1, "{src}: {errors:?}");
        assert!(errors[0].contains("(b) + "), "{src}: {errors:?}");
    }
    // Before the cast: the error is at the use, never at the cast, which reads an `int`.
    for (use_, cast, fix) in [
        (
            "c = b + 0.5f64;",
            "m.stdout <- String(rat(b)) else \"${c}\";",
            "Try `c = f64(b) + 0.5f64` instead.",
        ),
        // `c = b + 1` is not offered: it makes `rat(b) + c` add an int to a rat
        // (REPAIR-past-binding).
        (
            "c = b + 1r;",
            "m.stdout <- String(rat(b) + c);",
            "Try `c = rat(b) + 1r` instead.",
        ),
    ] {
        let src = format!("main(m: MainArgs) {{\n    b = 2^3;\n    {use_}\n    {cast}\n}}\n");
        let (i, _) = info(&src);
        assert_eq!(i.errors.len(), 1, "{src}");
        let e = &i.errors[0];
        let line = src.find(use_).expect("the use");
        assert!(
            (line..line + use_.len()).contains(&e.span.start),
            "{src}: {}",
            e.message
        );
        assert!(e.message.contains(fix), "{src}: {}", e.message);
    }
}

#[test]
fn the_headline_prints_a_bound_name_as_its_type() {
    // Item MSG-literal-class-headline: `b` in a body was a class of the literals `2` and `3`
    // until the function's end, and the headline of `+` printed it as its first literal:
    // "`+` does not take (2, 0.5f64)". Since LIT-name-int-fixed (dba724818) `b` is an `int`
    // where it is bound, and every headline shows it as `int`, a type the program could write,
    // never as `2`.
    for (body, headline) in [
        (
            "b = 2^3; y = rat(b); c = b + 0.5f64; return (y, c);",
            "The suffix makes the literal `0.5f64` an `f64`, never `int`. Try `f() { b = 2^3; \
             y = rat(b); c = f64(b) + 0.5f64; return (y, c); }` instead.",
        ),
        (
            "b = 2^3; y = rat(b); c = b + 1r; return (y, c);",
            "The suffix makes the literal `1r` a `rat`, never `int`. Try `f() { b = 2^3; \
             y = rat(b); c = b + 1; return (y, c); }` instead.",
        ),
        (
            "b = 2^3; c = b + 0.5; y = rat(b); return (y, c);",
            "A decimal literal is never an `int`: `b : int + 0.5`. Try `f() { b = 2^3; \
             c = rat(b) + 0.5; y = rat(b); return (y, c); }` instead.",
        ),
        (
            "b = 2^3; y = rat(b); c = b + \"a\"; return (y, c);",
            "`+` does not take (int, \"a\"): no arrow of `+` takes these types.",
        ),
        (
            "b = 2 + 13; c = b < \"a\"; return c;",
            "`<` does not take (int, \"a\"): no arrow of `<` takes these types. \
             Try `String(b) < \"a\"` instead.",
        ),
    ] {
        let src = format!("f() {{ {body} }}\n");
        let (i, _) = info(&src);
        assert_eq!(i.errors.len(), 1, "{src}: {:?}", i.errors);
        let m = &i.errors[0].message;
        assert_eq!(m.lines().next(), Some(headline), "{src}: {m}");
    }
}

/// A body of `n` names, each bound to the last plus `1` from `2^3`, so one class of `n + 1`
/// literals, and `n` casts of the last, summed.
pub(super) fn many(n: usize) -> String {
    let mut src = String::from("f() {\n    b0 = 2^3;\n");
    for i in 1..n {
        src += &format!("    b{i} = b{} + 1;\n", i - 1);
    }
    src += "    return 0r";
    for _ in 0..n {
        src += &format!(" + rat(b{})", n - 1);
    }
    src + ";\n}\n"
}

#[test]
fn casts_of_a_name_of_literals_keep_no_atom() {
    // A small instance of the benchmark `bench::cast_rat_int`.
    assert!(!sig_f(&many(3)).contains('#'));
}
