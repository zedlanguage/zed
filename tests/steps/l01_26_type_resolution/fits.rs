//! A function argument fits the function type its slot expects: by its parameters' names,
//! in any order; a lambda by its own names; a parameter the type leaves out only with a
//! default.

use super::{info, sig, type_errors};
use crate::l01_16_elaboration::value;
use zedc::ast::unit;
use zedc::check::Fit;
use zedc::lex::lex_fence;
use zedc::parse::{TOP, parse};
use zedc::resolve::resolve;

const APPLY: &str = "apply(f: (a: int, b: int) -> int) = f(a: 1, b: 2);\n";

fn fits(text: &str) -> Vec<Fit> {
    info(text).0.fits.into_values().collect()
}

#[test]
fn a_function_with_the_same_names_in_order_needs_no_fit() {
    let p = format!("{APPLY}sub(a, b) = a - b;\ny = apply(f: sub);\n");
    assert!(fits(&p).is_empty());
    assert_eq!(value(&p, "y"), "-1");
}

#[test]
fn a_function_with_the_names_reordered_gets_an_adapter() {
    let p = format!("{APPLY}sub(b, a) = a - b;\ny = apply(f: sub);\n");
    assert_eq!(fits(&p), [Fit::Adapter { from: vec![1, 0] }]);
    assert_eq!(value(&p, "y"), "-1");
}

#[test]
fn a_lambda_takes_its_parameters_by_name() {
    let p = format!("{APPLY}y = apply(f: (b, a) -> a - b);\n");
    assert_eq!(
        fits(&p),
        [Fit::Lambda {
            order: vec![Some(1), Some(0)],
            extra: vec![]
        }]
    );
    assert_eq!(value(&p, "y"), "-1");
}

#[test]
fn a_lambda_parameter_the_type_leaves_out_takes_its_default() {
    let p = "apply(f: (a: int) -> int) = f(a: 3);\ny = apply(f: (a, k = 10) -> a * k);\n";
    assert_eq!(value(p, "y"), "30");
}

#[test]
fn a_lambda_parameter_with_another_name_is_an_error() {
    assert_eq!(
        type_errors(&format!("{APPLY}y = apply(f: (a, s) -> a - s);\n")),
        [
            "the lambda's parameter `s` is not a parameter of `(a: int, b: int) -> int`: \
          rename it `b` [s]"
        ]
    );
}

#[test]
fn named_parameters_do_not_fit_a_positional_type() {
    assert_eq!(
        type_errors(
            "apply(f: (int, int) -> int) = f(1, 2);\nsub(a, b) = a - b;\ny = apply(f: sub);\n"
        ),
        [
            "the parameters of `sub` (a, b) do not fit `(int, int) -> int`: declare them as it \
          passes them, with `positional` where it passes by position, or pass a lambda, \
          (a, b) -> sub(a: a, b: b) [sub]"
        ]
    );
}

#[test]
fn a_lambdas_result_must_fit() {
    assert_eq!(
        type_errors("apply(f: (int) -> String) = f(1);\ny = apply(f: n -> n + 1);\n"),
        ["the lambda returns int, and `(int) -> String` returns String [n + 1]"]
    );
}

/// A slot written as an intersection of function types expects one function with an arrow for
/// each (DESIGN.md sec:type_language, "Relation to semantic subtyping" (2)): a generic `neg`
/// has both, and `half`, on `int` alone, has one.
const BOTH: &str = "both(f: ((x: int) -> int) & ((x: f64) -> f64)) = (f(x: 2), f(x: 0.5));\n";

#[test]
fn a_slot_written_as_an_intersection_of_function_types_takes_each_arrow() {
    assert_eq!(
        sig(BOTH, "both"),
        "(f: (((x: int) -> int) & ((x: f64) -> f64))) -> (int, f64)"
    );
    let neg = format!("{BOTH}neg(x) = -x;\ny = both(f: neg);\n");
    assert!(type_errors(&neg).is_empty(), "{:?}", type_errors(&neg));
    assert_eq!(value(&neg, "y"), "(-2, -0.5)");
    let half = format!("{BOTH}half(x: int) = x div 2;\ny = both(f: half);\n");
    assert_eq!(
        type_errors(&half),
        ["`half` is `(x: int) -> int`, not `((x: int) -> int) & ((x: f64) -> f64)` [half]"]
    );
    // A call through the slot that no arrow takes is refused with each arrow.
    let text = "both(f: ((x: int) -> int) & ((x: f64) -> f64)) = f(x: \"a\");\n";
    assert_eq!(
        type_errors(text),
        ["`f` does not take (\"a\") [f(x: \"a\")]"]
    );
}

#[test]
fn an_intersection_of_function_types_with_different_parameters_is_an_error() {
    let text = "both(f: ((x: int) -> int) & ((y: f64) -> f64)) = f(x: 2);\n";
    assert_eq!(
        resolve_errors(text),
        [
            "the arrows of an intersection of function types share one parameter list, but one \
             takes (x) and another (y) [((x: int) -> int) & ((y: f64) -> f64)]"
        ]
    );
}

/// The messages `resolve` gives `text`, each with the text it is at.
fn resolve_errors(text: &str) -> Vec<String> {
    let tokens = lex_fence(text).unwrap();
    let tree = parse(text, &tokens, "Unit", TOP).unwrap();
    let stmts = unit(text, &tokens, &tree).unwrap();
    resolve(&stmts)
        .expect_err("refused")
        .into_iter()
        .map(|e| format!("{} [{}]", e.message, &text[e.span.start..e.span.end]))
        .collect()
}

/// A slot written as an overload in parentheses and one more arrow expects all three arrows.
#[test]
fn a_slot_written_with_an_overload_in_parentheses_takes_every_arrow() {
    let text = "three(f: (((x: int) -> int) & ((x: f64) -> f64)) & ((x: rat) -> rat)) = \
                f(x: 1);\n";
    assert_eq!(
        sig(text, "three"),
        "(f: (((x: int) -> int) & ((x: f64) -> f64) & ((x: rat) -> rat))) -> int"
    );
    let half = format!("{text}half(x: int) = x div 2;\ny = three(f: half);\n");
    assert_eq!(
        type_errors(&half),
        [
            "`half` is `(x: int) -> int`, not `((x: int) -> int) & ((x: f64) -> f64) & \
             ((x: rat) -> rat)` [half]"
        ]
    );
    let text = "three(f: (((x: int) -> int) & ((x: f64) -> f64)) & ((y: rat) -> rat)) = \
                f(x: 1);\n";
    assert_eq!(
        resolve_errors(text),
        [
            "the arrows of an intersection of function types share one parameter list, but one \
             takes (x) and another (y) [(((x: int) -> int) & ((x: f64) -> f64)) & ((y: rat) -> \
             rat)]"
        ]
    );
}

/// Two arrows of a slot that bound one name by different carriers are no type, so the bound
/// of neither is lost.
#[test]
fn a_slot_whose_arrows_bound_one_variable_differently_is_an_error() {
    let text = "p(f: (((x: T) -> T) for T in int) & (((x: T) -> T) for T in f64)) = f(x: 1);\n";
    assert_eq!(
        resolve_errors(text),
        [
            "the type variable `T` is bounded by int on one arrow of an intersection of function \
             types and by f64 on another, but the arrows of one function share its bounds \
             [(((x: T) -> T) for T in int) & (((x: T) -> T) for T in f64)]"
        ]
    );
}

/// An overload whose arrows cover a slot's parameter only together:
/// `((x: int) -> String) & ((x: bool) -> String)` passed where `(x: int | bool) -> String` is
/// expected. Rule 6 (DESIGN.md sec:type_resolution) types an application region by region, so
/// a call of the slot at `int | bool` reaches, at each value, an arrow that gives `String`
/// (`check::ty::covered`).
#[test]
fn an_overload_that_covers_a_slots_parameter_only_together_fits() {
    let text = "p(f: (x: int | bool) -> String) = f(x: 1);\n\
                q(g: ((x: int) -> String) & ((x: bool) -> String)) = p(f: g);\n";
    assert_eq!(type_errors(text), Vec::<String>::new());
    // Run through: `show` takes both, `q` passes it on as two arrows, `p` calls it at `int`.
    let run = format!("{text}show(x: int | bool) = \"shown\";\ny = q(g: show);\n");
    assert_eq!(type_errors(&run), Vec::<String>::new());
    assert_eq!(value(&run, "y"), "\"shown\"");
    // With parameters passed by position, whose names are not compared, alike.
    let text = "p(f: (positional x: int | bool) -> String) = f(1);\n\
                q(g: ((positional y: int) -> String) & ((positional z: bool) -> String)) = \
                p(f: g);\n";
    assert_eq!(type_errors(text), Vec::<String>::new());
    // Three arrows, two of which cover the slot's parameter together.
    let text = "p(f: (x: int | bool) -> String) = f(x: 1);\n\
                q(g: ((x: int) -> String) & ((x: String) -> int) & ((x: bool) -> String)) = \
                p(f: g);\n";
    assert_eq!(type_errors(text), Vec::<String>::new());
}

/// Arrows that cover the slot's parameter together but one of which returns outside the slot's
/// result do not fit: at `bool`, `g` gives an `int`.
#[test]
fn arrows_that_cover_together_must_each_return_within_the_slots_result() {
    let text = "p(f: (x: int | bool) -> String) = f(x: 1);\n\
                q(g: ((x: int) -> String) & ((x: bool) -> int)) = p(f: g);\n";
    assert_eq!(
        type_errors(text),
        ["`p` does not take ((((x: int) -> String) & ((x: bool) -> int))) [p(f: g)]"]
    );
    // Nor do arrows that leave part of the parameter out.
    let text = "p(f: (x: int | bool | String) -> String) = f(x: 1);\n\
                q(g: ((x: int) -> String) & ((x: bool) -> String)) = p(f: g);\n";
    assert_eq!(
        type_errors(text),
        ["`p` does not take ((((x: int) -> String) & ((x: bool) -> String))) [p(f: g)]"]
    );
}

/// Two cases rule 6 accepts that the checker rejects, each a Complexity tradeoff of
/// `check::ty::covered` (COMPLEXITY.md F82): arrows that cover a slot only by splitting two
/// parameters at once (whether a union of products covers a product is coNP-complete), and
/// arrows that overlap on the slot's parameter, each returning outside its result while the
/// intersection of their results, which rule 6 gives there, is within it (the all-subsets
/// condition of semantic subtyping, exponential in the arrows that overlap).
#[test]
fn arrows_that_cover_only_across_two_parameters_or_by_intersected_results_are_refused() {
    let text = "p(f: (x: int | bool, y: int | bool) -> String) = f(x: 1, y: 2);\n\
                q(g: ((x: int, y: int) -> String) & ((x: bool, y: bool) -> String) & \
                ((x: int, y: bool) -> String) & ((x: bool, y: int) -> String)) = p(f: g);\n";
    assert_eq!(type_errors(text).len(), 1, "{:?}", type_errors(text));
    // One parameter split, the other held by each arrow, is covered.
    let text = "p(f: (x: int | bool, y: int) -> String) = f(x: 1, y: 2);\n\
                q(g: ((x: int, y: int) -> String) & ((x: bool, y: int | bool) -> String)) = \
                p(f: g);\n";
    assert_eq!(type_errors(text), Vec::<String>::new());
    let text = "p(f: (x: int) -> String) = f(x: 1);\n\
                q(g: ((x: int) -> String | #a) & ((x: int) -> String | #b)) = p(f: g);\n";
    assert_eq!(type_errors(text).len(), 1, "{:?}", type_errors(text));
}
