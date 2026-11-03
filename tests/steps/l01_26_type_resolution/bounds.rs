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
        [
            "the type `U` is not defined [U]; a type variable is bounded by the clause after its \
             type, as `for U in int | f64`; this clause does not bound `U` \
             [(T) -> U for T in int]"
        ]
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
    let mut t = "(".repeat(n - 1);
    t.push_str("T0 -> T0 for T0 in int");
    for i in 1..n {
        t.push_str(&format!(") -> T{i} for T{i} in f64"));
    }
    format!("h(g: {t}) = 0;\n")
}

/// A function that passes its argument, of `n` parameters each of its own variable bounded by
/// int and f64, where one bounded by int alone is expected.
fn passed(n: usize) -> String {
    let ps = |v: &str| -> String {
        let ps: Vec<String> = (0..n).map(|i| format!("x{i}: {v}{i}")).collect();
        ps.join(", ")
    };
    let bs = |v: &str, b: &str| -> String {
        let bs: Vec<String> = (0..n).map(|i| format!("{v}{i} in {b}")).collect();
        bs.join(", ")
    };
    format!(
        "p(g: ({}) -> T0 for {}) = 0;\nq(f: ({}) -> U0 for {}) = p(g: f);\n",
        ps("T"),
        bs("T", "int"),
        ps("U"),
        bs("U", "int | f64")
    )
}

/// The unit `text` lexed, parsed and resolved, for a test that times the check alone.
fn resolved(text: &str) -> (Vec<zedc::ast::Stmt>, zedc::resolve::Resolution) {
    let tokens = lex_fence(text).unwrap();
    let tree = parse(text, &tokens, "Unit", TOP).unwrap();
    let stmts = unit(text, &tokens, &tree).unwrap();
    let res = resolve(&stmts).unwrap_or_else(|e| panic!("{e:?}"));
    (stmts, res)
}

/// Checks `make(n)` at `n` and `8n` with `check_order`, each input lexed, parsed and resolved
/// before timing, so that the check alone is measured.
fn check_scales(what: &str, n: usize, make: impl Fn(usize) -> String) {
    let inputs: std::collections::HashMap<usize, _> = [n, zed_tests::scaling::FACTOR * n]
        .into_iter()
        .map(|n| (n, resolved(&make(n))))
        .collect();
    zed_tests::scaling::check_order(what, n, 1, |n| {
        let (stmts, res) = &inputs[&n];
        let info = zedc::check::check(stmts, res);
        assert!(info.errors.is_empty(), "{:?}", info.errors);
    });
}

#[test]
fn many_bounded_variables_scale() {
    assert!(
        type_errors(&wide(3)).is_empty(),
        "{:?}",
        type_errors(&wide(3))
    );
    assert_eq!(fmt(&wide(800)), wide(800));
    check_scales("a clause of n bounds and a call of n arguments", 800, wide);
}

#[test]
fn passing_a_function_of_many_bounded_variables_scales() {
    assert!(
        type_errors(&passed(3)).is_empty(),
        "{:?}",
        type_errors(&passed(3))
    );
    check_scales(
        "a function of n bounded variables passed as one of n",
        800,
        passed,
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
            check_scales("n nested bounds clauses", 400, nested);
        })
        .unwrap()
        .join()
        .unwrap();
}

/// `p` calls its argument on an int; `p_wide` on an int and on an f64.
const P: &str = "p(g: (x: T) -> T for T in int) = g(x: 1);\n\
                 p_wide(g: (x: T) -> T for T in int | f64) = g(x: 1.5);\n";

#[test]
fn a_bounded_function_passes_where_its_bound_holds_the_expected_one() {
    // `f` takes int and f64, so it serves where only int is asked, whatever its variable's name.
    for q in [
        "q(f: (x: T) -> T for T in int | f64) = p(g: f);\n",
        "q(f: (x: U) -> U for U in int | f64) = p(g: f);\n",
        "q(f: (x: U) -> U for U in int | f64) = p_wide(g: f);\n",
        "q(f: (x: T) -> T for T in int | f64) = p_wide(g: f);\n",
    ] {
        let text = format!("{P}{q}");
        assert!(
            type_errors(&text).is_empty(),
            "{q}: {:?}",
            type_errors(&text)
        );
    }
    let text = format!("{P}q(f: (x: U) -> U for U in int | f64) = p_wide(g: f);\n");
    assert_eq!(
        sig(&text, "q"),
        "(f: ((x: U) -> U for U in int | f64)) -> f64"
    );
}

#[test]
fn a_bounded_function_does_not_pass_where_more_carriers_are_asked() {
    // `p_wide` calls `g` on an f64, which `f` does not take.
    for q in [
        "q(f: (x: T) -> T for T in int) = p_wide(g: f);\n",
        "q(f: (x: U) -> U for U in int) = p_wide(g: f);\n",
        "q(f: (x: U) -> U for U in int | rat) = p_wide(g: f);\n",
    ] {
        let text = format!("{P}{q}");
        let errors = type_errors(&text);
        assert_eq!(errors.len(), 1, "{q}: {errors:?}");
        assert!(errors[0].ends_with("[p_wide(g: f)]"), "{q}: {errors:?}");
    }
}

#[test]
fn a_function_of_one_carrier_is_the_function_bounded_by_it() {
    let q = format!("{P}q(f: (x: int) -> int) = p(g: f);\n");
    assert!(type_errors(&q).is_empty(), "{:?}", type_errors(&q));
    let inc = format!("{P}inc(x: int) = x + 1;\ny = p(g: inc);\n");
    assert!(type_errors(&inc).is_empty(), "{:?}", type_errors(&inc));
    assert_eq!(value(&inc, "y"), "2");
    // Of two carriers, a function of one does not do; nor does one that takes both but
    // returns either, since the caller's `T` is the carrier it passed.
    let narrow = format!("{P}q(f: (x: int) -> int) = p_wide(g: f);\n");
    assert_eq!(type_errors(&narrow).len(), 1, "{:?}", type_errors(&narrow));
    let either = format!("{P}q(f: (x: int | f64) -> int | f64) = p_wide(g: f);\n");
    assert_eq!(type_errors(&either).len(), 1, "{:?}", type_errors(&either));
    let test = "t(g: (x: T) -> bool for T in int | f64) = g(x: 2);\n\
                q(f: (x: int | f64) -> bool) = t(g: f);\n";
    assert!(type_errors(test).is_empty(), "{:?}", type_errors(test));
}

#[test]
fn a_bounded_variable_only_in_the_result_gives_its_whole_bound() {
    let text = "h(g: () -> T for T in int | f64) = g();\n";
    assert!(type_errors(text).is_empty(), "{:?}", type_errors(text));
    assert_eq!(
        sig(text, "h"),
        "(g: (() -> T for T in int | f64)) -> int | f64"
    );
}

#[test]
fn printing_a_deep_function_type_scales() {
    // Each function type is written in place: building each part as a string and copying it
    // into the whole cost O(n^2) for n nested function types.
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(|| {
            let inputs: std::collections::HashMap<usize, _> = [800, 6400]
                .into_iter()
                .map(|n| {
                    let (info, names) = info(&nested(n));
                    let (_, s) = info
                        .sigs
                        .iter()
                        .find(|(id, _)| names[**id] == "h")
                        .expect("h");
                    (n, s.clone())
                })
                .collect();
            assert!(inputs[&800].to_string().ends_with(" -> 0"));
            zed_tests::scaling::check("printing n nested function types", 800, |n| {
                assert!(!inputs[&n].to_string().is_empty());
            });
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn a_bounded_variable_in_a_parameter_that_is_a_function_is_checked_at_each_carrier() {
    // `p2` gives its argument a function on the carrier its caller picks.
    let p2 = "p2(g: ((x: T) -> T) -> T for T in int | f64) = 0;\n\
              p1(g: ((x: T) -> T) -> T for T in int) = 0;\n";
    let cases = [
        // Refused for now, though sound to take: `U` occurs only under a function parameter,
        // where `fits_sig` binds no variable of the outer function (STATUS, TYPE-forms).
        (
            "q(f: ((x: U) -> U) -> U for U in int | f64) = p2(g: f);\n",
            1,
        ),
        ("q(f: ((x: int) -> int) -> int) = p1(g: f);\n", 0),
        // At f64, `f` would get a function on f64, which it does not take.
        ("q(f: ((x: int) -> int) -> int) = p2(g: f);\n", 1),
        ("q(f: ((x: U) -> U) -> U for U in int) = p2(g: f);\n", 1),
        // A generic function with no bound takes every carrier.
        ("id(x) = x;\ny = p_wide(g: id);\n", 0),
    ];
    for (q, n) in cases {
        let text = format!("{P}{p2}{q}");
        assert_eq!(type_errors(&text).len(), n, "{q}: {:?}", type_errors(&text));
    }
}

/// Functions whose bounded variable no parameter holds: no argument fixes its carrier, so
/// each returns a value of some carrier of the bound.
const R: &str = "r(g: () -> T for T in int | f64) = g();\n\
                 r2(g: (x: T) -> U for T in int, U in int | f64) = 0;\n\
                 r3(g: (x: T) -> U for T in int, U in int) = 0;\n";

#[test]
fn a_function_whose_bounded_variable_is_only_in_its_result_passes_as_itself() {
    let cases = [
        // The value has exactly the expected type.
        ("k(f: () -> T for T in int | f64) = r(g: f);\n", 0),
        (
            "k(f: (x: T) -> U for T in int, U in int | f64) = r2(g: f);\n",
            0,
        ),
        // A narrower function: int is within int | f64.
        ("k(f: (x: int) -> int) = r2(g: f);\n", 0),
        ("k(f: () -> int) = r(g: f);\n", 0),
        ("k(f: () -> T for T in f64) = r(g: f);\n", 0),
        ("y = r(g: () -> 1);\n", 0),
        ("y = r(g: () -> 1.5);\n", 0),
        // A result outside the bound, and a bound wider than the expected one.
        ("k(f: () -> String) = r(g: f);\n", 1),
        ("y = r(g: () -> \"s\");\n", 1),
        ("k(f: () -> T for T in int | rat) = r(g: f);\n", 1),
        (
            "k(f: (x: T) -> U for T in int, U in int | f64) = r3(g: f);\n",
            1,
        ),
    ];
    for (k, n) in cases {
        let text = format!("{R}{k}");
        assert_eq!(type_errors(&text).len(), n, "{k}: {:?}", type_errors(&text));
    }
    let text = format!("{R}y = r(g: () -> 1);\n");
    assert_eq!(value(&text, "y"), "1");
}

#[test]
fn a_lambda_outside_a_result_only_bound_names_the_whole_bound() {
    let errors = type_errors(&format!("{R}y = r(g: () -> \"s\");\n"));
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(
        errors[0].contains("the lambda returns \"s\"") && errors[0].contains("returns int | f64"),
        "{errors:?}"
    );
}

/// `p` and `q` both take a function of type `t` nested `n` deep, `(h: … (x: int) -> int …)
/// -> int`, each level's result its own variable bounded by int when `bounded`; `q` passes its
/// argument to `p`.
fn passed_deep(n: usize, bounded: bool) -> String {
    let mut t = String::from("(x: int) -> int");
    for i in 0..n {
        t = match bounded {
            false => format!("(h{i}: {t}) -> int"),
            true => format!("((h{i}: {t}) -> T{i} for T{i} in int)"),
        };
    }
    format!("p(g: {t}) = 0;\nq(f: {t}) = p(g: f);\n")
}

#[test]
fn passing_a_deep_function_type_as_itself_scales() {
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(|| {
            check_scales("a function type n deep passed as itself", 400, |n| {
                passed_deep(n, false)
            });
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn passing_a_deep_bounded_function_type_as_itself_scales() {
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(|| {
            let e = type_errors(&passed_deep(3, true));
            assert!(e.is_empty(), "{e:?}");
            check_scales(
                "a function type n deep, a bound at each level, passed as itself",
                400,
                |n| passed_deep(n, true),
            );
        })
        .unwrap()
        .join()
        .unwrap();
}

/// Functions with bounded variables passed where other bounded function types are expected.
const S: &str = "r(g: () -> T for T in int | f64) = g();\n\
                 need_int(x: int) = x;\n\
                 r4(g: (h: () -> T) -> int for T in int | f64) = 0;\n\
                 r5(g: (x: int) -> U for U in int | f64) = 0;\n";

#[test]
fn a_bounded_function_fits_only_where_each_carrier_it_returns_is_taken() {
    let cases = [
        // `r` returns an int or an f64, so its result is no int.
        ("z = need_int(x: r(g: () -> 1));\n", 1),
        ("k(f: () -> T for T in int | f64) = need_int(x: f());\n", 1),
        // The caller of `r4`'s argument passes `h` returning either carrier.
        ("k(f: (h: () -> int) -> int) = r4(g: f);\n", 1),
        // `f` returns the carrier it is given; `r5` asks for an int or an f64 back.
        ("k(f: (x: T) -> T for T in int | f64) = r5(g: f);\n", 0),
        ("k(f: (x: T) -> T for T in int | f64) = r(g: f);\n", 1),
        ("k(f: (x: int) -> String) = r5(g: f);\n", 1),
    ];
    for (k, n) in cases {
        let text = format!("{S}{k}");
        assert_eq!(type_errors(&text).len(), n, "{k}: {:?}", type_errors(&text));
    }
}

/// Functions whose parameter `g` has bounded variables, for lambdas passed as `g`: `t` calls
/// it on an int, `two` and `mix` on an f64 and an int.
const L: &str = "t(g: (x: T) -> bool for T in int | f64) = g(x: 2);\n\
                 two(g: (a: T, b: U) -> T for T in int | f64, U in int) = g(a: 1.5, b: 2);\n\
                 mix(g: (a: T, b: int) -> T for T in int | f64) = g(a: 1.5, b: 2);\n\
                 pz(g: (z: T) -> T for T in int) = g(z: 1);\n\
                 dbl(x) = x + x;\n";

#[test]
fn a_lambda_uses_its_bounded_parameters_as_a_declared_function_does() {
    // Each use is checked at each carrier of the bound: at int, and for `p_wide` at f64.
    let cases = [
        ("y = p(g: (x) -> x + 1);\n", "2"),
        ("y = p_wide(g: (x) -> x + x);\n", "3.0"),
        ("y = p_wide(g: (x) -> -x);\n", "-1.5"),
        ("y = p_wide(g: (x) -> x - x);\n", "0.0"),
        ("y = t(g: (x) -> x < x + x);\n", "true"),
        ("y = p_wide(g: (x) -> dbl(x: x));\n", "3.0"),
        ("y = two(g: (a, b) -> a + a);\n", "3.0"),
        // Named parameters taken in another order, and one `g` is not passed, by its default.
        ("y = two(g: (b, a) -> a);\n", "1.5"),
        ("y = p_wide(g: (x, k = 2) -> x);\n", "1.5"),
        // A parameter of a plain type beside a bounded one.
        ("y = mix(g: (a, b) -> a);\n", "1.5"),
        // Nested lambdas, the inner one using the outer one's parameter.
        ("y = p(g: (x) -> pz(g: (z) -> z + x));\n", "2"),
        (
            "y = p(g: (x) -> x + p(g: (x) -> x + p(g: (x) -> x)));\n",
            "3",
        ),
        // `(x: int) -> int` has no bounded variable: the lambda is checked against it alone.
        (
            "q(g: (x: int) -> int) = g(x: 1);\ny = q(g: (x) -> x + 1);\n",
            "2",
        ),
    ];
    for (q, v) in cases {
        let text = format!("{P}{L}{q}");
        assert!(
            type_errors(&text).is_empty(),
            "{q}: {:?}",
            type_errors(&text)
        );
        assert_eq!(value(&text, "y"), v, "{q}");
    }
    let twice = format!("{TWICE}y = twice(3, g: (x) -> -x);\n");
    assert!(type_errors(&twice).is_empty(), "{:?}", type_errors(&twice));
    assert_eq!(value(&twice, "y"), "3");
}

#[test]
fn a_lambda_whose_uses_the_bound_does_not_allow_is_an_error() {
    let cases = [
        // The literal 1 makes `x` an int, and `p_wide` passes an f64 too.
        (
            "y = p_wide(g: (x) -> x + 1);\n",
            "the lambda is `(x: int) -> int`, not `(x: T) -> T for T in int | f64` \
             [(x) -> x + 1]",
        ),
        (
            "y = p_wide(g: (x, k = 2) -> x + k);\n",
            "the lambda is `(x: int) -> int`, not `(x: T) -> T for T in int | f64` \
             [(x, k = 2) -> x + k]",
        ),
        (
            "y = p_wide(g: (x) -> upper(x));\n",
            "the lambda is `(x: String) -> String`, not `(x: T) -> T for T in int | f64` \
             [(x) -> upper(x)]",
        ),
        (
            "y = p_wide(g: (x: int) -> x);\n",
            "the lambda is `(x: int) -> int`, not `(x: T) -> T for T in int | f64` \
             [(x: int) -> x]",
        ),
        // A comparison gives a bool, not the carrier passed.
        (
            "y = p_wide(g: (x) -> x < x);\n",
            "the lambda is `(x: T) -> bool for T in int | f64 | rat | String | bool`, \
             not `(x: T) -> T for T in int | f64` [(x) -> x < x]",
        ),
        // `a` and `b` take different carriers, so `a + b` is no sum of one carrier.
        (
            "y = two(g: (a, b) -> a + b);\n",
            "the lambda is `(a: T, b: T) -> T for T in int | f64 | rat`, \
             not `(a: T, b: U) -> T for T in int | f64, U in int` [(a, b) -> a + b]",
        ),
        (
            "y = mix(g: (a, b) -> b);\n",
            "the lambda is `(a: T, b: U) -> U`, not `(a: T, b: int) -> T for T in int | f64` \
             [(a, b) -> b]",
        ),
        // The inner `p_wide` gives an f64, so `x` is an f64, and `p_wide` passes an int too.
        (
            "y = p_wide(g: (x) -> p_wide(g: (x) -> x + x) + x);\n",
            "the lambda is `(x: f64) -> f64`, not `(x: T) -> T for T in int | f64` \
             [(x) -> p_wide(g: (x) -> x + x) + x]",
        ),
    ];
    for (q, message) in cases {
        let text = format!("{P}{L}{q}");
        assert_eq!(type_errors(&text), [message], "{q}");
    }
}

#[test]
fn a_lambda_and_a_declared_function_of_the_same_body_give_the_same_result() {
    for body in [
        "x + 1",
        "x + x",
        "-x",
        "x - x",
        "x < x",
        "upper(x)",
        "dbl(x: x)",
        "x",
    ] {
        for (g, n) in [("p", "x"), ("p_wide", "x"), ("t", "x")] {
            let lambda = format!("{P}{L}y = {g}(g: ({n}) -> {body});\n");
            let named = format!("{P}{L}f({n}) = {body};\ny = {g}(g: f);\n");
            let shown = |errors: Vec<String>, what: &str, at: &str| -> Vec<String> {
                errors
                    .iter()
                    .map(|e| e.replace(what, "it").replace(at, "[]"))
                    .collect()
            };
            let from_lambda = shown(
                type_errors(&lambda),
                "the lambda",
                &format!("[({n}) -> {body}]"),
            );
            let from_named = shown(type_errors(&named), "`f`", "[f]");
            assert_eq!(from_lambda, from_named, "{g} with {body}");
            if from_lambda.is_empty() {
                assert_eq!(value(&lambda, "y"), value(&named, "y"), "{g} with {body}");
            }
        }
    }
}

/// `n` lambdas nested, each passed for a parameter bounded by int and using its own.
fn nested_lambdas(n: usize) -> String {
    let mut body = String::from("x");
    for _ in 1..n {
        body = format!("x + p(g: (x) -> {body})");
    }
    format!("{P}y = p(g: (x) -> {body});\n")
}

/// A lambda of `n` parameters, each of its own bounded variable, passed to the `h` of
/// [`wide`].
fn wide_lambda(n: usize) -> String {
    let xs: Vec<String> = (0..n).map(|i| format!("x{i}")).collect();
    format!("{}y = h(g: ({}) -> x0 + x0);\n", wide(n), xs.join(", "))
}

#[test]
fn a_lambda_of_many_bounded_parameters_scales() {
    let text = wide_lambda(3);
    assert!(type_errors(&text).is_empty(), "{:?}", type_errors(&text));
    assert_eq!(value(&text, "y"), "2");
    check_scales(
        "a lambda of n bounded parameters passed as a function of n",
        800,
        wide_lambda,
    );
}

#[test]
fn nested_lambdas_for_bounded_parameters_scale() {
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(|| {
            assert_eq!(value(&nested_lambdas(3), "y"), "3");
            check_scales(
                "n nested lambdas, each for a bounded parameter",
                400,
                nested_lambdas,
            );
        })
        .unwrap()
        .join()
        .unwrap();
}
