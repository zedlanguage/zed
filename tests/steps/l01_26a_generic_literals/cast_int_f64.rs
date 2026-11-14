//! `int` and `f64` of an operation on integer literals in a body (item CAST-int-f64-lit-class).
//! A cast keeps an atom only where its operand can give it (QUESTIONS A36): `int` of an int
//! gives none, and `f64` of an int gives `#inexact` only past 2^53 and `#overflow` only past
//! the largest finite `f64`. A name bound to integer literals alone is an `int` where it is
//! bound (QUESTIONS A63), so `int(b)` with `b = 2^64 + 13` is an `int`, and `f64(b)` with
//! `b = 2^3 + 1` an `f64`, and neither asks for an `else`.

use zed_tests::step_helpers::l01_16_elaboration::value;
use zed_tests::step_helpers::l01_19_whole_file_ports::run;
use zed_tests::step_helpers::l01_26_type_resolution::{sig, type_errors};

/// The signature of `f` in `src`, which checks with no error.
fn sig_f(src: &str) -> String {
    assert_eq!(type_errors(src), Vec::<String>::new(), "{src}");
    sig(src, "f")
}

#[test]
fn the_programs_of_the_item_need_no_else() {
    for (name, body, out) in [
        (
            "l01_26a_cast_int",
            "b = 2^64 + 13;\n    m.stdout <- String(int(b));",
            "18446744073709551629\n",
        ),
        (
            "l01_26a_cast_f64",
            "b = 2^3 + 1;\n    m.stdout <- String(f64(b));",
            "9.0\n",
        ),
    ] {
        let src = format!("main(m: MainArgs) {{\n    {body}\n}}\n");
        assert_eq!(type_errors(&src), Vec::<String>::new(), "{src}");
        // `2^64` passes a machine word, of which `zedc run` warns on stderr; the run succeeds.
        let r = run(name, &src, "", &[]);
        assert_eq!(r.status, 0, "{src}: {}", r.stderr);
        assert!(!r.stderr.contains("else"), "{src}: {}", r.stderr);
        assert_eq!(r.stdout, out, "{src}");
    }
}

#[test]
fn int_of_an_operation_on_integer_literals_has_no_atom() {
    for (body, v) in [
        ("b = 2^64 + 13; return int(b);", "18446744073709551629"),
        ("return int(2^64 + 13);", "18446744073709551629"),
        ("b = -(2^70) - 1; return int(b);", "-1180591620717411303425"),
        ("b = 2^3; b1 = b + 1; return int(b1);", "9"),
    ] {
        let src = format!("f() {{ {body} }}\ny = f();\n");
        assert_eq!(sig_f(&src), "() -> int", "{src}");
        assert_eq!(value(&src, "y"), v, "{src}");
    }
}

#[test]
fn f64_of_an_operation_on_integer_literals_keeps_only_the_atoms_its_value_gives() {
    for (body, ty, v) in [
        // Within ±2^53 every int is exact in f64.
        ("b = 2^3 + 1; return f64(b);", "() -> f64", "9.0"),
        ("return f64(2^3 + 1);", "() -> f64", "9.0"),
        (
            "b = 2^53; return f64(b);",
            "() -> f64",
            "9007199254740992.0",
        ),
        (
            "b = -(2^53); return f64(b);",
            "() -> f64",
            "-9007199254740992.0",
        ),
        // Past 2^53 it may be inexact, but below the largest finite f64 it never overflows.
        (
            "b = 2^53 + 1; return f64(b);",
            "() -> f64 | #inexact",
            "#inexact",
        ),
        (
            "b = 2^1000; return f64(b);",
            "() -> f64 | #inexact",
            "1.0715086071862673e301",
        ),
    ] {
        let src = format!("f() {{ {body} }}\ny = f();\n");
        assert_eq!(sig_f(&src), ty, "{src}");
        assert_eq!(value(&src, "y"), v, "{src}");
    }
    // `f32` likewise, at its own bounds: 2^24 is exact, 2^24 + 1 is not.
    for (body, ty, v) in [
        ("return f32(2^24);", "() -> f32", "16777216.0f32"),
        (
            "b = 2^24 + 1; return f32(b);",
            "() -> f32 | #inexact",
            "#inexact",
        ),
    ] {
        let src = format!("f() {{ {body} }}\ny = f();\n");
        assert_eq!(sig_f(&src), ty, "{src}");
        assert_eq!(value(&src, "y"), v, "{src}");
    }
    // Past the largest finite f64 the cast overflows: `2^2000` keeps `#overflow`.
    let src = "f() { b = 2^2000; return f64(b); }\ny = f();\n";
    assert!(sig_f(src).contains("#overflow"), "{src}");
    assert_eq!(value(src, "y"), "#overflow");
}

#[test]
fn f64_of_2_to_53_plus_1_still_asks_for_an_else() {
    let src = "main(m: MainArgs) {\n    b = 2^53 + 1;\n    m.stdout <- String(f64(b));\n}\n";
    let errors = type_errors(src);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(errors[0].contains("#inexact"), "{errors:?}");
    let src =
        "main(m: MainArgs) {\n    b = 2^53 + 1;\n    m.stdout <- String(f64(b)) else \"\";\n}\n";
    assert_eq!(type_errors(src), Vec::<String>::new(), "{src}");
}

#[test]
fn a_cast_of_a_parameter_keeps_its_atoms() {
    // A parameter may be any value of its carrier, a NaN or an infinity among them.
    assert_eq!(
        sig_f("f(x: f64) = int(x);\n"),
        "(x: f64) -> int | #inexact | #invalid"
    );
    assert_eq!(
        sig_f("f(x: int) = f64(x);\n"),
        "(x: int) -> f64 | #inexact | #overflow"
    );
}

/// A body of `n` names, each bound to the last plus `1` from `2^3`, `n` casts of the last to
/// `int` and to `f64`, and `n` casts of operations on integer literals written in place,
/// `int(2^3 + i)` and `f64(2^3 + i)`, each its own class taken at `int` by the cast.
pub(super) fn many(n: usize) -> String {
    let mut src = String::from("f() {\n    b0 = 2^3;\n");
    for i in 1..n {
        src += &format!("    b{i} = b{} + 1;\n", i - 1);
    }
    src += "    return (0";
    for i in 0..n {
        src += &format!(" + int(b{}) + int(2^3 + {i})", n - 1);
    }
    src += ", 0.0f64";
    for i in 0..n {
        src += &format!(" + f64(b{}) + f64(2^3 + {i})", n - 1);
    }
    src + ");\n}\n"
}

#[test]
fn casts_of_names_and_operations_on_literals_keep_no_atom() {
    // A small instance of the benchmark `bench::cast_int_f64`.
    assert!(!sig_f(&many(3)).contains('#'));
}
