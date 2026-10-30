//! The call rules: positional arguments first, then named ones, then an optional `...`; `x:`
//! supplies the variable `x`; no argument is named twice.

use zedc::lex::lex;
use zedc::parse::{TOP, parse};

use super::ast;

#[test]
fn positional_then_named_then_curry() {
    let cases = [
        ("clamp(5, 0, 8)", "(call clamp 5 0 8)"),
        (
            "greet(\"Al\", punct: \"?\")",
            "(call greet (str \"Al\") (punct: (str \"?\")))",
        ),
        (
            "join(b, on: #orderId, kind: #left)",
            "(call join b (on: #orderId) (kind: #left))",
        ),
        ("Point(x:, y:)", "(call Point (x: x) (y: y))"),
        ("Point(x: 0.0, ...)", "(call Point (x: 0.0) ...)"),
        ("greet(\"Ann\", ...)", "(call greet (str \"Ann\") ...)"),
        (
            "Vec3(z: 1.0, x: 0.0, y: 0.0,)",
            "(call Vec3 (z: 1.0) (x: 0.0) (y: 0.0))",
        ),
        ("now()", "(call now)"),
    ];
    for (text, want) in cases {
        assert_eq!(ast(text).unwrap().to_string(), want, "{text}");
    }
}

#[test]
fn a_shorthand_argument_is_the_name_at_its_own_place() {
    let text = "Point(x:, y: 2.0)";
    let e = ast(text).unwrap();
    let zedc::ast::ExprKind::Call { named, .. } = &e.kind else {
        panic!("{e}")
    };
    assert_eq!(&text[named[0].1.span.start..named[0].1.span.end], "x");
}

#[test]
fn misordered_arguments_do_not_parse() {
    // DESIGN.md: `greet(name: "Al")` and `greet(punct: "?", "Al")` are errors; the first is a
    // type error (L1.16), the second a syntax error, as is `...` anywhere but last.
    for text in [
        "greet(punct: \"?\", \"Al\")",
        "f(..., x: 1)",
        "f(x: 1, ..., y: 2)",
        "f(...)",
    ] {
        let tokens = lex(text).unwrap();
        assert!(parse(text, &tokens, "Expr", TOP).is_err(), "{text}");
    }
}

#[test]
fn an_argument_named_twice_is_an_error_at_the_second() {
    let text = "Rect(w: 3, h: 4, w: 5)";
    let err = ast(text).unwrap_err();
    assert_eq!(&text[err.span.start..err.span.end], "w");
    assert_eq!(err.span.start, 17);
    assert_eq!(err.message, "the argument `w` is named twice");
    let [first] = &err.notes[..] else {
        panic!("one note: {:?}", err.notes)
    };
    assert_eq!(first.text, "the first argument named `w`");
    assert_eq!(first.span.start, 5);
}

#[test]
fn a_form_of_a_later_layer_names_that_layer() {
    let cases = [
        ("data::len", "this form (Suffix) is built from layer L3"),
        ("rows*.price", "this form (Suffix) is built from layer L6"),
        (
            "sort(desc score)",
            "this form (PosArg) is built from layer L5",
        ),
    ];
    for (text, want) in cases {
        assert_eq!(ast(text).unwrap_err().message, want, "{text}");
    }
}
