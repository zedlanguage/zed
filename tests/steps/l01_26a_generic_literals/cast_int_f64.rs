//! `int` and `f64` of an operation on integer literals in a body (item CAST-int-f64-lit-class).
//! A cast keeps an atom only where its operand can give it (QUESTIONS A36): `int` of an int
//! gives none, and a cast to a float format gives none, rounding to nearest, ties to even (step
//! L1.18). A name bound to integer literals alone is an `int` where it is
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
fn f64_of_an_operation_on_integer_literals_rounds_with_no_atom() {
    for (body, v) in [
        // Within ±2^53 every int is exact in f64.
        ("b = 2^3 + 1; return f64(b);", "9.0"),
        ("return f64(2^3 + 1);", "9.0"),
        ("b = 2^53; return f64(b);", "9007199254740992.0"),
        ("b = -(2^53); return f64(b);", "-9007199254740992.0"),
        // Past 2^53 it rounds to nearest, ties to even, and past the largest finite f64 it is
        // the infinity of its sign (step L1.18).
        ("b = 2^53 + 1; return f64(b);", "9007199254740992.0"),
        ("b = 2^53 + 3; return f64(b);", "9007199254740996.0"),
        ("b = 2^1000; return f64(b);", "1.0715086071862673e301"),
        ("b = 2^2000; return f64(b);", "inf"),
        ("b = -(2^2000); return f64(b);", "-inf"),
    ] {
        let src = format!("f() {{ {body} }}\ny = f();\n");
        assert_eq!(sig_f(&src), "() -> f64", "{src}");
        assert_eq!(value(&src, "y"), v, "{src}");
    }
    // `f32` likewise, at its own bounds: 2^24 is exact, 2^24 + 1 rounds to it.
    for (body, v) in [
        ("return f32(2^24);", "16777216.0f32"),
        ("b = 2^24 + 1; return f32(b);", "16777216.0f32"),
        ("b = 2^24 + 3; return f32(b);", "16777220.0f32"),
    ] {
        let src = format!("f() {{ {body} }}\ny = f();\n");
        assert_eq!(sig_f(&src), "() -> f32", "{src}");
        assert_eq!(value(&src, "y"), v, "{src}");
    }
}

#[test]
fn f64_of_2_to_53_plus_1_needs_no_else() {
    let src = "main(m: MainArgs) {\n    b = 2^53 + 1;\n    m.stdout <- String(f64(b));\n}\n";
    assert_eq!(type_errors(src), Vec::<String>::new(), "{src}");
    let r = run("l01_26a_cast_f64_round", src, "", &[]);
    assert_eq!(r.status, 0, "{src}: {}", r.stderr);
    assert_eq!(r.stdout, "9007199254740992.0\n", "{src}");
}

#[test]
fn a_cast_of_a_parameter_keeps_only_the_atoms_it_may_give() {
    // A parameter may be any value of its carrier, a NaN or an infinity among them: `int` of
    // an `f64` is not proved whole and is rejected, and `f64` of an `int` rounds.
    let errors = type_errors("f(x: f64) = int(x);\n");
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(
        errors[0].starts_with("No `int` equals the value: `int(x)`. Try `round(x)` instead."),
        "{}",
        errors[0]
    );
    assert_eq!(sig_f("f(x: int) = f64(x);\n"), "(x: int) -> f64");
}

/// The menu of "No `int` equals the value" (DESIGN.md sec:corner_cases, "Casts are domain
/// proofs", and step L1.18): `int(7r/2r)` and `int(2.5f64)` are rejected with the rounding
/// functions offered, each with the value it gives, and each fix checks as written and gives
/// that value; `int(x)` with a parameter `x: f64` is offered the same words, each of which
/// checks, with the type `int | #NaN | #overflow` (a NaN or an infinity has no whole number).
#[test]
fn the_menu_of_an_int_cast_not_proved_whole_offers_each_rounding_and_each_checks() {
    use super::fixes::fixes;
    // Each word, its `ties:` argument, and the value it gives on 3.5 and on 2.5.
    let words = [
        ("round", "", ["4", "2"]),
        ("round", ", ties: #away", ["4", "3"]),
        ("floor", "", ["3", "2"]),
        ("ceil", "", ["4", "3"]),
        ("trunc", "", ["3", "2"]),
        ("awayFromZero", "", ["4", "3"]),
    ];
    for (i, lit) in ["7r/2r", "2.5f64"].into_iter().enumerate() {
        let src = format!("k = int({lit});\n");
        let got = fixes(&src);
        let expected: Vec<(String, &str)> = (words.iter())
            .map(|(w, ties, v)| (format!("k = {w}({lit}{ties});"), v[i]))
            .collect();
        assert_eq!(got.len(), expected.len(), "{src}: {got:?}");
        for ((line, holds), (want_line, v)) in got.iter().zip(&expected) {
            assert_eq!(line, want_line, "{src}");
            assert!(holds.starts_with(&format!("k is {v}")), "{line}: {holds}");
            let fixed = format!("{line}\n");
            assert_eq!(type_errors(&fixed), Vec::<String>::new(), "{line}");
            assert_eq!(value(&fixed, "k"), *v, "{line}");
        }
    }
    let got = fixes("f(positional x: f64) = int(x);\n");
    let words: Vec<&str> = got.iter().map(|(l, _)| l.as_str()).collect();
    assert_eq!(
        words,
        [
            "f(positional x: f64) = round(x);",
            "f(positional x: f64) = round(x, ties: #away);",
            "f(positional x: f64) = floor(x);",
            "f(positional x: f64) = ceil(x);",
            "f(positional x: f64) = trunc(x);",
            "f(positional x: f64) = awayFromZero(x);",
        ]
    );
    for (line, _) in &got {
        let fixed = format!("{line}\n");
        assert_eq!(sig_f(&fixed), "f64 -> int | #NaN | #overflow", "{line}");
    }
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
