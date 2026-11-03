//! The bounds clause `t for X in t1 | … | tn` (DESIGN.md sec:type_language, step L1.26): `X`
//! is a type variable in scope in `t`, its bound is resolved outside it, and the function type
//! that holds every use of `X` takes one carrier of the bound for it at each call.

use super::{info, sig, type_errors};
use crate::l01_10_lambdas_types_else_tuples::sx;
use crate::l01_13_formatter::fmt;
use crate::l01_16_elaboration::value;
use zedc::ast::unit;
use zedc::check::read::parse_type;
use zedc::lex::lex_fence;
use zedc::parse::{TOP, parse};
use zedc::resolve::resolve;

/// The resolution errors of the unit `text`, each `message [text]`, each note after it as
/// `; note [text]`.
fn resolve_errors(text: &str) -> Vec<String> {
    let tokens = lex_fence(text).unwrap();
    let tree = parse(text, &tokens, "Unit", TOP).unwrap();
    let stmts = unit(text, &tokens, &tree).unwrap();
    let Err(es) = resolve(&stmts) else {
        return Vec::new();
    };
    es.iter()
        .map(|e| {
            let mut out = format!("{} [{}]", e.message, &text[e.span.start..e.span.end]);
            for n in &e.notes {
                out += &format!("; {} [{}]", n.text, &text[n.span.start..n.span.end]);
            }
            out
        })
        .collect()
}

/// A function that applies a bounded function to an int and to an f64.
const TWICE: &str =
    "twice(positional v: int, g: (x: T) -> T for T in int | f64) = g(x: g(x: v));\n";

#[test]
fn the_clause_parses_loosest() {
    let cases = [
        (
            "f is ((T) -> T for T in int)",
            "(is f (for (-> (T) T) (T int)))",
        ),
        (
            "f is ((T, U) -> T for T in int | f64, U in String)",
            "(is f (for (-> (T U) T) (T (| int f64)) (U String)))",
        ),
        // The clause binds looser than the arrow, and the bound is a union of carriers.
        (
            "f is (T -> T -> T for T in int | rat)",
            "(is f (for (-> (T) (-> (T) T)) (T (| int rat))))",
        ),
        // A clause inside another, in a parameter's parentheses.
        (
            "f is (((T) -> T for T in int) -> U for U in bool)",
            "(is f (for (-> ((for (-> (T) T) (T int))) U) (U bool)))",
        ),
        // `is` takes a union, so an unparenthesized clause does not parse.
        ("f is (T) -> T for T in int", "syntax"),
        ("f is ((T) -> T for T int)", "syntax"),
    ];
    let wrong: Vec<String> = cases
        .iter()
        .filter_map(|&(text, want)| {
            let got = sx(text);
            (got != want).then(|| format!("{text}\n  got  {got}\n  want {want}"))
        })
        .collect();
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

#[test]
fn a_variable_bounded_twice_in_one_clause_is_an_error() {
    let text = "f is ((T) -> T for T in int, T in f64)";
    assert!(sx(text).starts_with("error: "), "{}", sx(text));
    assert!(
        sx(text).contains("the type variable `T` is bounded twice"),
        "{}",
        sx(text)
    );
}

#[test]
fn the_formatter_writes_the_clause_and_parenthesizes_it_inside_tighter_forms() {
    for text in [
        TWICE,
        "f(g: (T, U) -> T for T in int | f64, U in String) = 0;\n",
        "f(g: (T -> T for T in int) -> U for U in bool) = 0;\n",
        "f(g: (T -> T for T in int, int)) = 0;\n",
        "f(g: (T -> T for T in rat,)) = 0;\n",
        "y = 1 is (T -> T for T in int) | int;\n",
    ] {
        assert_eq!(fmt(text), text);
    }
    // Parentheses the grammar needs stay; others go.
    assert_eq!(
        fmt("f(g: (((T) -> T) for T in int)) = 0;\n"),
        "f(g: T -> T for T in int) = 0;\n"
    );
}

#[test]
fn a_bounded_function_type_is_checked_at_each_call() {
    let neg = format!("{TWICE}neg(x) = -x;\ny = twice(3, g: neg);\n");
    assert!(type_errors(&neg).is_empty(), "{:?}", type_errors(&neg));
    assert_eq!(value(&neg, "y"), "3");
    // One carrier, and several variables.
    let one = "h(g: (x: T) -> T for T in rat) = 0;\n";
    assert!(type_errors(one).is_empty(), "{:?}", type_errors(one));
    let two = "h(g: (a: T, b: U) -> T for T in int | f64, U in String) = g(a: 2, b: \"s\");\n";
    assert!(type_errors(two).is_empty(), "{:?}", type_errors(two));
}

#[test]
fn a_call_outside_the_bound_is_an_error() {
    let errors = type_errors("h(g: (x: T) -> T for T in int | f64) = g(x: \"s\");\n");
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(errors[0].ends_with("[g(x: \"s\")]"), "{errors:?}");
    let errors = type_errors("h(g: (a: T, b: U) -> T for T in int, U in bool) = g(a: 2, b: 3);\n");
    assert_eq!(errors.len(), 1, "{errors:?}");
}

#[test]
fn the_signature_holds_the_bound() {
    assert_eq!(
        sig(TWICE, "twice"),
        "(int, g: ((x: T) -> T for T in int | f64)) -> int"
    );
}

#[test]
fn an_unbounded_name_is_an_error() {
    assert_eq!(
        resolve_errors("f(g: (T) -> U for T in int) = 0;\n"),
        ["the type `U` is not defined [U]"]
    );
}

#[test]
fn a_bound_on_a_variable_the_type_does_not_hold_is_an_error() {
    assert_eq!(
        resolve_errors("f(g: (T) -> T for T in int, U in f64) = 0;\n"),
        [
            "the bound names `U`, which the type before `for` does not hold [U]; \
             the type [(T) -> T]"
        ]
    );
}

#[test]
fn a_repeated_variable_is_an_error() {
    assert_eq!(
        resolve_errors("f(g: ((T) -> T for T in int) -> T for T in f64) = 0;\n"),
        ["the type variable `T` is bounded twice [T]; the first bound of `T` [T]"]
    );
}

#[test]
fn a_bound_that_is_no_union_of_carriers_is_an_error() {
    let cases = [
        (
            "f(g: (T) -> T for T in #a) = 0;\n",
            "the bound of `T` is not a union of carriers: `#a` is an atom, no carrier; \
             the carriers are int, f64, rat, String, bool [#a]",
        ),
        (
            "f(g: (T) -> T for T in int | (int, int)) = 0;\n",
            "the bound of `T` is not a union of carriers: this type is no carrier; \
             the carriers are int, f64, rat, String, bool [(int, int)]",
        ),
        (
            "f(g: (T) -> T for T in Lines) = 0;\n",
            "the bound of `T` is not a union of carriers: `Lines` is no carrier; \
             the carriers are int, f64, rat, String, bool [Lines]",
        ),
        // A bound is read outside its clause, so a variable of the same clause is no name there.
        (
            "f(g: (T, U) -> T for T in int, U in T) = 0;\n",
            "the bound of `U` is not a union of carriers: `T` is no carrier; \
             the carriers are int, f64, rat, String, bool [T]",
        ),
        (
            "f(g: ((U) -> U for U in T) -> T for T in int) = 0;\n",
            "the bound of `U` is not a union of carriers: `T` is a type variable; \
             the carriers are int, f64, rat, String, bool [T]",
        ),
    ];
    for (text, want) in cases {
        let got = resolve_errors(text);
        assert_eq!(got.len(), 1, "{text}: {got:?}");
        assert!(got[0].starts_with(want), "{text}: {got:?}");
    }
}

#[test]
fn a_variable_outside_one_function_type_is_an_error() {
    let outside = resolve_errors("f(x: T for T in int) = x;\n");
    assert_eq!(outside.len(), 1, "{outside:?}");
    assert!(
        outside[0].starts_with("the bounded variable `T` stands outside a function type"),
        "{outside:?}"
    );
    let two = resolve_errors("f(g: ((T) -> T, (T) -> int) for T in int) = 0;\n");
    assert_eq!(two.len(), 1, "{two:?}");
    assert!(
        two[0].starts_with("the bounded variable `T` stands in two function types"),
        "{two:?}"
    );
}

#[test]
fn an_is_test_of_a_bounded_type_is_an_error() {
    let errors = elab_errors("f(x) = x;\ny = f is ((T) -> T for T in int);\n");
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(
        errors[0].starts_with("an `is` test cannot take a type with bounded variables (`T`)"),
        "{errors:?}"
    );
}

/// The elaboration errors of the unit `text`.
fn elab_errors(text: &str) -> Vec<String> {
    let tokens = lex_fence(text).unwrap();
    let tree = parse(text, &tokens, "Unit", TOP).unwrap();
    let stmts = unit(text, &tokens, &tree).unwrap();
    let res = resolve(&stmts).unwrap_or_else(|e| panic!("{text}: {e:?}"));
    match zedc::elab::elaborate(&stmts, &res) {
        Ok(_) => Vec::new(),
        Err(es) => es.iter().map(|e| e.message.clone()).collect(),
    }
}

#[test]
fn a_printed_bounded_type_reads_back() {
    // The printer writes each function type in parentheses, and a function-typed parameter in
    // the parameter list's own; what it writes reads back to the same type.
    for (text, want) in [
        (
            "(T) -> T for T in int | f64",
            "((T) -> T for T in int | f64)",
        ),
        (
            "(T, U) -> T for T in int, U in String | bool",
            "((T, U) -> T for T in int, U in String | bool)",
        ),
        (
            "((T) -> T for T in rat) -> int",
            "((((T) -> T for T in rat)) -> int)",
        ),
    ] {
        let printed = parse_type(text)
            .unwrap_or_else(|e| panic!("{e}"))
            .to_string();
        assert_eq!(printed, want);
        let again = parse_type(&printed).unwrap_or_else(|e| panic!("{e}"));
        assert_eq!(again.to_string(), printed);
    }
}

#[test]
fn the_checker_reads_a_one_tuple_and_a_morphism_type() {
    let one = "f(p: (int,)) = p;\n";
    assert_eq!(sig(one, "f"), "(p: (int,)) -> (int,)");
    let morphism = "f(m: int .. int -> bool) = 0;\n";
    assert!(
        type_errors(morphism).is_empty(),
        "{:?}",
        type_errors(morphism)
    );
    let (info, _) = info(morphism);
    assert_eq!(info.sigs.len(), 1);
}

#[test]
fn an_argument_must_take_every_carrier_of_the_bound() {
    // A call of `twice` may bind `T` to int or to f64, so its argument takes both.
    let shout = format!("{TWICE}shout(x) = upper(x) ++ \"!\";\ny = twice(3, g: shout);\n");
    assert_eq!(
        type_errors(&shout),
        ["`shout` is `(x: String) -> String`, not `(x: T) -> T for T in int | f64` [shout]"]
    );
    let inc = format!("{TWICE}inc(x: int) = x + 1;\ny = twice(3, g: inc);\n");
    assert_eq!(
        type_errors(&inc),
        ["`inc` is `(x: int) -> int`, not `(x: T) -> T for T in int | f64` [inc]"]
    );
    let neg = format!("{TWICE}neg(x) = -x;\ny = twice(3, g: neg);\n");
    assert!(type_errors(&neg).is_empty(), "{:?}", type_errors(&neg));
}

/// A function whose parameter `g` takes `n` arguments, each of its own bounded variable, and
/// that calls `g` once.
fn wide(n: usize) -> String {
    let ps: Vec<String> = (0..n).map(|i| format!("x{i}: T{i}")).collect();
    let bs: Vec<String> = (0..n).map(|i| format!("T{i} in int | f64")).collect();
    let args: Vec<String> = (0..n)
        .map(|i| match i % 2 {
            0 => format!("x{i}: 1"),
            _ => format!("x{i}: 1.5"),
        })
        .collect();
    format!(
        "h(g: ({}) -> T0 for {}) = g({});\n",
        ps.join(", "),
        bs.join(", "),
        args.join(", ")
    )
}

/// `n` bounds clauses nested in the parameter of a function type.
fn nested(n: usize) -> String {
    let mut t = "T0 -> T0 for T0 in int".to_string();
    for i in 1..n {
        t = format!("({t}) -> T{i} for T{i} in f64");
    }
    format!("h(g: {t}) = 0;\n")
}

#[test]
fn many_bounded_variables_scale() {
    assert!(
        type_errors(&wide(3)).is_empty(),
        "{:?}",
        type_errors(&wide(3))
    );
    zed_tests::scaling::check_order(
        "a clause of n bounds and a call of n arguments",
        800,
        1,
        |n| {
            let text = wide(n);
            let (info, _) = info(&text);
            assert!(info.errors.is_empty(), "{:?}", info.errors);
            assert_eq!(fmt(&text), text);
        },
    );
}

#[test]
fn nested_bounds_clauses_scale() {
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(|| {
            assert!(
                resolve_errors(&nested(3)).is_empty(),
                "{:?}",
                resolve_errors(&nested(3))
            );
            assert_eq!(fmt(&nested(400)), nested(400));
            // The check alone is timed: the formatter's linear work would hide a walk of each
            // clause's whole type, quadratic in the depth.
            zed_tests::scaling::check_order("n nested bounds clauses", 400, 1, |n| {
                let text = nested(n);
                let (info, _) = info(&text);
                assert!(info.errors.is_empty(), "{:?}", info.errors);
            });
        })
        .unwrap()
        .join()
        .unwrap();
}
