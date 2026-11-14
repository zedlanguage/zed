//! The one-tuple (QUESTIONS A21; DESIGN.md sec:grammar `TupleExpr` and `TuplePat`, step L1.10):
//! `(e,)` is the tuple of one component and `(p,)` the pattern that matches it, while `(e)` is
//! only `e` in parentheses and `(p)` is no pattern. Each parses, evaluates, and prints back as
//! written, so the formatter keeps the comma that makes it a tuple.

use super::{check, sx};
use zed_kernel::term::build::var;
use zed_kernel::{Evaluator, Pattern, Shared, Term, World};
use zed_tests::step_helpers::l01_13_formatter::{build, fmt};
use zed_tests::step_helpers::l01_16_elaboration::{elab, value, with_prelude};
use zedc::format::format;
use zedc::lex::lex;
use zedc::parse::{TOP, parse};

#[test]
fn a_trailing_comma_makes_a_one_tuple() {
    // In the s-expressions a tuple pattern is its components in parentheses, so `(a)` is `(a,)`.
    check(&[
        ("(1,)", "(tuple 1)"),
        ("((1,),)", "(tuple (tuple 1))"),
        ("((1),)", "(tuple 1)"),
        ("((1,))", "(tuple 1)"),
        ("(1)", "1"),
        ("(\"one\",).len", "(. (tuple (str \"one\")) len)"),
        ("match v { (a,) -> a }", "(match v (-> (a) a))"),
        (
            "match v { ((a,),) -> a, (_,) -> 0, (a, b) -> b }",
            "(match v (-> ((a)) a) (-> (_) 0) (-> (a, b) b))",
        ),
    ]);
}

#[test]
fn a_one_tuple_evaluates_to_a_tuple_of_one() {
    assert_eq!(value("x = (1,);\n", "x"), "(1,)");
    assert_eq!(value("x = ((1,),);\n", "x"), "((1,),)");
    assert_eq!(value("x = ((1),);\n", "x"), "(1,)");
    assert_eq!(value("x = (1);\n", "x"), "1");
    assert_eq!(value("x = (1,) == (1,);\n", "x"), "true");
    assert_eq!(value("x = (1,) == (2,);\n", "x"), "false");
}

/// The surface `match` is elaborated from step L2.4, so until then the arm `(a,) -> a` is run
/// as the kernel arm it elaborates to: the one-tuple pattern binds the one component, and does
/// not match a tuple of two.
#[test]
fn the_one_tuple_pattern_matches_a_tuple_of_one() {
    let run = |of: &str| {
        let u = elab(&format!("v = {of};\n")).unwrap();
        let m = Term::Match(
            Shared::new(u.get("v").unwrap()),
            vec![
                (Pattern::Tuple(vec![Pattern::Bind("a".into())]), var("a")),
                (Pattern::Bind("w".into()), var("w")),
            ],
        );
        let printed = m.to_string();
        let got = Evaluator::new(World::new()).run(&with_prelude(m));
        (printed, got.map(|v| v.to_string()))
    };
    let (printed, got) = run("(5,)");
    assert!(printed.contains("(a,) -> a"), "{printed}");
    assert_eq!(got.unwrap(), "5");
    assert_eq!(run("((\"deep\",),)").1.unwrap(), "(\"deep\",)");
    assert_eq!(run("(5, 6)").1.unwrap(), "(5, 6)");
}

#[test]
fn a_one_tuple_prints_back_as_written() {
    for text in [
        "x = (1,);\n",
        "x = ((1,),);\n",
        "x = (1, (2,));\n",
        "x = match v {\n  (a,) -> a,\n};\n",
        "x = match v {\n  ((a,),) -> a,\n  (_,) -> 0,\n};\n",
        "f(p) = (p.name,);\n",
        "g(x) {\n  a = x;\n  (a,)\n}\n",
    ] {
        assert_eq!(fmt(text), text);
    }
    // A group loses its parentheses; a one-tuple keeps its comma.
    assert_eq!(fmt("x = ((1),);\n"), "x = (1,);\n");
    assert_eq!(fmt("x = ((1,));\n"), "x = (1,);\n");
    // A block's one export is written last, the one-tuple still a one-tuple.
    assert_eq!(
        fmt("g(x) { a = x; return (a,); b = 1; }\n"),
        "g(x) {\n  a = x;\n  b = 1;\n  (a,)\n}\n"
    );
}

#[test]
fn an_empty_tuple_and_a_parenthesized_pattern_are_rejected() {
    assert_eq!(sx("(,)"), "syntax");
    assert_eq!(sx("(1,,)"), "syntax");
    assert_eq!(sx("match v { (a) -> a }"), "syntax");
    assert_eq!(sx("match v { ((a),) -> a }"), "syntax");
    // The parse of `(a)` as a pattern stops at its `)`, where a `,` would make it a one-tuple.
    let text = "match v { (a) -> a }";
    let tokens = lex(text).unwrap();
    let e = parse(text, &tokens, "Expr", TOP).unwrap_err();
    assert_eq!(&text[e.span.start..e.span.end], ")");
    assert!(e.expected.iter().any(|x| x == "','"), "{:?}", e.expected);
}

/// `x = ((…(1,)…),);`, a one-tuple nested `n` deep.
pub(super) fn nested(n: usize) -> String {
    format!("x = {}1{};\n", "(".repeat(n), ",)".repeat(n))
}

/// Parses `text` and checks that it prints back as written.
pub(super) fn prints_back(text: &str) {
    let (tokens, stmts) = build(text).unwrap();
    assert_eq!(&format(text, &tokens, &stmts), text);
}

/// Evaluates `text`, a one-tuple nested `n` deep, and checks the length of the printed value.
pub(super) fn evaluates(text: &str, n: usize) {
    assert_eq!(value(text, "x").len(), 1 + 3 * n);
}

/// A one-tuple nested a few deep prints back as written and evaluates to a value of its depth;
/// `bench/one_tuples.rs` holds the timing.
#[test]
fn nested_one_tuples_print_back_and_evaluate_at_small_depths() {
    for n in [1, 2, 9] {
        prints_back(&nested(n));
        evaluates(&nested(n), n);
    }
    assert_eq!(value(&nested(2), "x"), "((1,),)");
}
