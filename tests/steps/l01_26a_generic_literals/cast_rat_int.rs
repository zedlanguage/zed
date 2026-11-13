//! `rat` of an operation on integer literals alone (item CAST-rat-int). In a body, a name bound
//! to such an operation, `b = 2^64 + 13`, has the type of the literals' class until the class
//! resolves, and `rat(b)` took the `#invalid` of the `f64`, `f32` and `String` arrows of `rat`
//! from it, so `String(rat(b) ^ (2^64))` asked for an `else`. A cast keeps an atom only where its
//! operand can give it (QUESTIONS A36), and `rat` of an int never gives one: the cast now takes
//! the class at `int`, the carrier a name bound to integer literals alone has where it is bound
//! (QUESTIONS A63), and gives `rat`. A use that takes `int` from the class is then rejected,
//! whether it comes before the cast or after it. `rat` of a `String` or an `f64` keeps
//! `#invalid`, and so does `rat` of a parameter, which may be any value of its carrier. A name
//! bound at the top level is already an `int` where it is read, so only bodies had the defect.

use zed_tests::scaling;
use zed_tests::step_helpers::l01_16_elaboration::value;
use zed_tests::step_helpers::l01_26_type_resolution::{Resolved, info, sig, type_errors};

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
        // `0.5` before the cast joins the class, which then holds a decimal; after it, `0.5` is
        // rejected beside an `int` (below).
        "b = 2^3; c = b + 0.5; y = rat(b); return (y, c);",
    ] {
        let src = format!("f() {{ {body} }}\n");
        let errors = type_errors(&src);
        assert_eq!(errors.len(), 1, "{src}: {errors:?}");
        assert!(errors[0].contains("a carrier"), "{src}: {errors:?}");
    }
}

#[test]
fn a_use_that_takes_int_from_the_operand_is_rejected_before_or_after_the_cast() {
    // After the cast: the use is rejected as it is with `b: int`, with a cast of `b` as
    // the fix. (The headline of `+` prints `b` as its first literal, `2`: MSG-wide-value-notes.)
    for body in [
        "b = 2^3; y = rat(b); c = b + 0.5f64; return (y, c);",
        "b = 2^3; y = rat(b); c = b + 1r; return (y, c);",
        "b = 2^3; y = rat(b); c = b + 0.5; return (y, c);",
    ] {
        let src = format!("f() {{ {body} }}\n");
        let errors = type_errors(&src);
        assert_eq!(errors.len(), 1, "{src}: {errors:?}");
        assert!(errors[0].contains("(b) + "), "{src}: {errors:?}");
    }
    // Before it, where the use takes `int` from the class first: the cast is rejected, naming
    // the use.
    for (use_, cast) in [
        (
            "c = b + 0.5f64;",
            "m.stdout <- String(rat(b)) else \"${c}\";",
        ),
        ("c = b + 1r;", "m.stdout <- String(rat(b) + c);"),
    ] {
        let src = format!("main(m: MainArgs) {{\n    b = 2^3;\n    {use_}\n    {cast}\n}}\n");
        let (i, _) = info(&src);
        assert_eq!(i.errors.len(), 1, "{src}");
        let e = &i.errors[0];
        assert!(
            e.message.starts_with(
                "`rat(b)` reads `b`, an operation on integer literals alone, as an `int`, but \
                 another use takes `int` from it"
            ),
            "{src}: {}",
            e.message
        );
        // A note shows the use that took `int`, on its line.
        let line = src.find(use_).expect("the use");
        assert!(
            (e.notes.iter())
                .any(|n| (line..line + use_.len()).contains(&n.span.start)
                    && n.text.contains("takes")),
            "{src}: {:?}",
            e.notes
        );
    }
}

/// A body of `n` names, each bound to the last plus `1` from `2^3`, so one class of `n + 1`
/// literals, and `n` casts of the last, summed.
fn many(n: usize) -> String {
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
fn casts_of_a_name_of_many_literals_check_in_linear_time() {
    // Each cast reads the class's flags and restricts its mask once: no walk of its literals.
    scaling::on_a_thread(1 << 28, || {
        assert!(!sig_f(&many(3)).contains('#'));
        let n = 200;
        let units = scaling::inputs(n, |m| Resolved::new(&many(m)));
        scaling::check(
            "checking n casts `rat(b)` of a name of n literals",
            n,
            |m| {
                units[&m].check();
            },
        );
    });
}
