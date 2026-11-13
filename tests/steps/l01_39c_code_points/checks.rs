//! What the checker states of the four words: each takes the kind it reads and gives that kind
//! or its failure atom, and a `codePoint` is an int in `0 ..= 1114111`, so a bit word may read
//! it, as a lexer encoding a scalar does.

use super::{PASS, accepted, rejected, x};

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
        ("x = utf8(1);\n", "`utf8` takes (String) -> int ->? int"),
        (
            "x = fromUtf8(\"x\");\n",
            "`fromUtf8` takes (int ->? int) -> String | #badUtf8",
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
        out.contains("this call of `utf8` gives int ->? int"),
        "{out}"
    );
}

#[test]
fn a_failure_must_be_handled_before_a_string_is_written() {
    // `whole` passes its int on, so `scalar` is judged on a value known only when the program
    // runs and may give `#notScalar`.
    let src = |push: &str| format!("{PASS}main(m: MainArgs) {{\n  m.stdout <- {push};\n}}\n");
    let out = rejected(&src("scalar(whole(65))"));
    assert!(out.contains("String | #notScalar"), "{out}");
    assert!(accepted(&src("scalar(whole(65)) else \"?\"")));
    // On a literal the checker lists only the atoms its value gives (DESIGN sec:failure): 65 is
    // a scalar value, so `scalar(65)` is a `String` and needs no handling, and 55296, a
    // surrogate, always fails, which is rejected.
    assert!(accepted(&src("scalar(65)")));
    let out = rejected(&src("scalar(55296) else \"?\""));
    assert!(out.contains("always fails"), "{out}");
}

#[test]
fn a_code_point_is_in_the_domain_of_the_bit_words() {
    // The UTF-8 encoding of a scalar, the way a lexer writes it.
    let src = "c = codePoint(\"€\");\n\
               lead = bitOr(224, shr(c, 12)) else 0;\n\
               mid = bitOr(128, bitAnd(shr(c, 6), 63)) else 0;\n\
               low = bitOr(128, bitAnd(\"€\".codePoint, 63)) else 0;\n\
               wide = rotl(\"€\".codePoint(), 1, width: 21) else 0;\n";
    let v = |n| zed_tests::step_helpers::l01_16_elaboration::value(src, n);
    assert!(accepted(src));
    assert_eq!(
        (v("lead"), v("mid"), v("low")),
        ("226".into(), "130".into(), "172".into())
    );
    assert_eq!(v("wide"), "16728");
    assert_eq!(x("utf8(\"€\")"), "{0 -> 226, 1 -> 130, 2 -> 172}");
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
        assert!(
            out.contains(&format!("`bitAnd({call} : -1, 1)`.\n")),
            "{src}: {out}"
        );
    }
}

#[test]
fn a_code_point_returned_by_a_function_is_read_as_any_int() {
    // COMPLEXITY.md C28: only a call of `codePoint` written as the operand, or bound to a
    // name by `=`, is known to lie in `0 ..= 1114111`; through a function's result it is any int.
    let out = rejected("f(s) = codePoint(s);\nx = bitAnd(f(s: \"a\"), 1);\n");
    assert!(
        out.contains(
            "`bitAnd` takes `a` in int[0..]: `bitAnd(f(s: \"a\") : int, 1)`. Try \
             `a2 = f(s: \"a\"); if a2 >= 0 { bitAnd(a2, 1) } else { … }` instead.\n"
        ),
        "{out}"
    );
    assert!(accepted(
        "c = codePoint(\"a\");\nx = bitAnd(c, 1) else 0;\n"
    ));
}

/// A word whose literal operand is never a scalar always fails, which the checker rejects
/// (row "Operation that always fails"); the same word on a parameter keeps its atom.
#[test]
fn a_literal_that_is_never_a_scalar_is_rejected() {
    for (src, written) in [
        ("x = codePoint(\"ab\");\n", "\"ab\""),
        ("x = codePoint(\"\") else -1;\n", "\"\""),
        ("x = scalar(55296);\n", "55296"),
    ] {
        let out = rejected(src);
        assert!(
            out.contains(&format!("its operand `{written}` gives `#notScalar`")),
            "{src}: {out}"
        );
    }
    assert!(accepted("f(s: String) = codePoint(s);\n"));
}
