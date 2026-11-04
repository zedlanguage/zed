//! What the checker states of the four words: each takes the kind it reads and gives that kind
//! or its failure atom, and a `codePoint` is an int in `0 ..= 1114111`, so a bit word may read
//! it, as a lexer encoding a scalar does.

use super::{accepted, rejected, x};

#[test]
fn an_argument_of_another_kind_is_rejected() {
    for (src, msg) in [
        (
            "x = codePoint(3);\n",
            "`codePoint` takes (String) -> int | #notScalar",
        ),
        (
            "x = scalar(\"a\");\n",
            "`scalar` takes (int) -> String | #notScalar",
        ),
        ("x = utf8(1);\n", "`utf8` takes (String) -> (int ->? int)"),
        (
            "x = fromUtf8(\"x\");\n",
            "`fromUtf8` takes ((int ->? int)) -> String | #badUtf8",
        ),
    ] {
        let out = rejected(src);
        assert!(out.contains("does not take"), "{src}: {out}");
        assert!(out.contains(msg), "{src}: {out}");
    }
}

#[test]
fn the_bytes_are_not_a_number() {
    let out = rejected("x = utf8(\"a\") + 1;\n");
    assert!(
        out.contains("this call of `utf8` gives (int ->? int)"),
        "{out}"
    );
}

#[test]
fn a_failure_must_be_handled_before_a_string_is_written() {
    let src = "main(stdin: Lines) -> (stdout: Lines) {\n  stdout <- scalar(65);\n}\n";
    let out = rejected(src);
    assert!(out.contains("String | #notScalar"), "{out}");
    assert!(accepted(
        "main(stdin: Lines) -> (stdout: Lines) {\n  stdout <- scalar(65) else \"?\";\n}\n"
    ));
}

#[test]
fn a_code_point_is_in_the_domain_of_the_bit_words() {
    // The UTF-8 encoding of a scalar, the way a lexer writes it.
    let src = "c = codePoint(\"€\");\n\
               lead = bitOr(224, shr(c, 12)) else 0;\n\
               mid = bitOr(128, bitAnd(shr(c, 6), 63)) else 0;\n\
               low = bitOr(128, bitAnd(\"€\".codePoint, 63)) else 0;\n\
               wide = rotl(\"€\".codePoint(), 1, width: 21) else 0;\n";
    let v = |n| crate::l01_16_elaboration::value(src, n);
    assert!(accepted(src));
    assert_eq!(
        (v("lead"), v("mid"), v("low")),
        ("226".into(), "130".into(), "172".into())
    );
    assert_eq!(v("wide"), "16728");
    assert_eq!(x("utf8(\"€\")"), "{1 -> 226, 2 -> 130, 3 -> 172}");
}

#[test]
fn a_code_point_is_not_wider_than_21_digits_but_may_be_wider_than_20() {
    assert!(accepted("x = bitNot(codePoint(\"a\"), width: 21);\n"));
    let out = rejected("x = bitNot(codePoint(\"a\"), width: 20);\n");
    assert!(out.contains("`bitNot` takes `x`"), "{out}");
}

#[test]
fn a_local_function_named_code_point_is_not_the_word() {
    // The receiver forms resolve to the user's `codePoint`, whose value is -1.
    for call in ["\"a\".codePoint", "\"a\".codePoint()"] {
        let src = format!("codePoint(s) = -1;\nx = bitAnd({call}, 1);\n");
        let out = rejected(&src);
        assert!(
            out.contains("`bitAnd` takes `a` in int[0..]"),
            "{src}: {out}"
        );
        assert!(out.contains("this `a` is -1"), "{src}: {out}");
    }
}

#[test]
fn a_code_point_returned_by_a_function_is_read_as_any_int() {
    // COMPLEXITY.md C28: only a call of `codePoint` written as the operand, or bound to a
    // name by `=`, is known to lie in `0 ..= 1114111`; through a function's result it is any int.
    let out = rejected("f(s) = codePoint(s);\nx = bitAnd(f(s: \"a\"), 1);\n");
    assert!(
        out.contains("`bitAnd` takes `a` in int[0..], and this `a` is int"),
        "{out}"
    );
    assert!(accepted(
        "c = codePoint(\"a\");\nx = bitAnd(c, 1) else 0;\n"
    ));
}
