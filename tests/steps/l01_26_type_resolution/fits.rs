//! A function argument fits the function type its slot expects: by its parameters' names,
//! in any order; a lambda by its own names; a parameter the type leaves out only with a
//! default.

use super::{info, sig, type_errors};
use zed_tests::step_helpers::l01_16_elaboration::{errors, value};
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
    assert_eq!(
        fits(&p),
        [Fit::Adapter {
            from: vec![1, 0],
            domain: None,
            result: None
        }]
    );
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
          rename it `b`. The lambda is passed where a function of type `(a: int, b: int) -> int` is \
          expected, and a call of it passes each named argument by its name, so each parameter \
          the lambda does not take by position must have a name of `(a: int, b: int) -> int` or \
          a default. [s]"
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
          (a, b) -> sub(a: a, b: b). [sub]"
        ]
    );
}

#[test]
fn a_lambdas_result_must_fit() {
    assert_eq!(
        type_errors("apply(f: (int) -> String) = f(1);\ny = apply(f: n -> n + 1);\n"),
        [
            "the lambda returns int, and `int -> String` returns String: the lambda is passed where a function of type `int -> String` is expected, so its result must be String. [n + 1]"
        ]
    );
}

/// A lambda in a slot whose type is a union holding one function type, or several of which only
/// one has parameters the lambda's names fit, is fitted to that function type, as in a slot of
/// that type alone (FAIL-check-lambda-into-fn-union: before, it was checked alone, with
/// positional parameters, and refused as "`p` does not take (int -> int)").
#[test]
fn a_lambda_in_a_union_slot_is_fitted_to_the_function_type_its_parameters_fit() {
    for slot in [
        "((x: int) -> int) | String",
        "((x: int) -> int) | (int, int)",
        "((x: int) -> int) | ((s: String) -> int)",
        "((s: String) -> int) | ((x: int) -> int) | #none",
    ] {
        for lambda in ["(x: int) -> x", "x -> x + 1"] {
            let p = format!("p(h: {slot}) = 0;\nq = p(h: {lambda});\n");
            assert_eq!(type_errors(&p), Vec::<String>::new(), "{p}");
        }
    }
    // Two parameters, among function types of one and of two, taken by name in the other
    // order: the fit records the order, as in a slot of that function type alone.
    let p =
        "p(h: ((x: int) -> int) | ((b: int, a: int) -> int)) = 0;\nq = p(h: (a, b) -> a - b);\n";
    assert_eq!(type_errors(p), Vec::<String>::new(), "{p}");
    assert_eq!(
        fits(p),
        [Fit::Lambda {
            order: vec![Some(1), Some(0)],
            extra: vec![]
        }]
    );
    // Fitted, the lambda's parameter and result are checked against that function type.
    assert_eq!(
        type_errors("p(h: ((x: int) -> int) | String) = 0;\nq = p(h: (x: String) -> 0);\n"),
        [
            "the lambda's parameter `x` is String, and `(x: int) -> int` passes int: the lambda is \
             called as a function of type `(x: int) -> int` is, so each parameter must take every \
             value passed to it. [x: String]"
        ]
    );
    assert_eq!(
        type_errors(
            "p(h: ((x: int) -> int) | ((s: String) -> int)) = 0;\nq = p(h: (s: String) -> s);\n"
        ),
        [
            "the lambda returns String, and `(s: String) -> int` returns int: the lambda is passed \
             where a function of type `(s: String) -> int` is expected, so its result must be \
             int. [s]"
        ]
    );
}

/// Where the lambda's names fit several function types, those its written parameter types
/// take are kept, and it is fitted to the one left: `(x: int) -> x` to `(x: int) -> int`,
/// `(x: String) -> 0` to `(x: String) -> int`. Where several are left and they give each
/// parameter one kind, the lambda is checked alone with those kinds and compared with the
/// slot: `x -> 0` is generic and fits both (FAIL-check-lambda-fn-union-same-names).
#[test]
fn a_lambda_whose_names_fit_several_function_types_of_a_union_is_chosen_by_its_written_types() {
    let slot = "((x: int) -> int) | ((x: String) -> int)";
    for lambda in [
        "(x: int) -> x",
        "(x: String) -> 0",
        "x -> 0",
        "(x: int) -> x + 1",
    ] {
        let p = format!("p(h: {slot}) = 0;\nq = p(h: {lambda});\n");
        assert_eq!(type_errors(&p), Vec::<String>::new(), "{p}");
    }
    // A written type that takes neither: checked alone, as before, and refused.
    let p = format!("p(h: {slot}) = 0;\nq = p(h: (x: f64) -> 0);\n");
    assert_eq!(type_errors(&p).len(), 1, "{p}");
    // Both left, and the result fits neither: refused. (`x -> x` is accepted: it fits
    // `(x: int) -> int`, and a union takes a function that fits one member.)
    let p = format!("p(h: {slot}) = 0;\nq = p(h: x -> \"a\");\n");
    assert_eq!(type_errors(&p).len(), 1, "{p}");
}

/// Where the lambda's names fit none of the function types, it is checked alone, with
/// positional parameters, and no function type of the slot takes it.
#[test]
fn a_lambda_whose_names_fit_no_one_function_type_of_a_union_is_refused() {
    let (slot, lambda) = ("((x: int) -> int) | ((s: String) -> int)", "(y: int) -> y");
    let p = format!("p(h: {slot}) = 0;\nq = p(h: {lambda});\n");
    assert_eq!(
        type_errors(&p),
        [format!(
            "`p` does not take (int -> int): no arrow of `p` takes these types. [p(h: {lambda})]"
        )],
        "{p}"
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
        "(f: ((x: int) -> int) & ((x: f64) -> f64)) -> (int, f64)"
    );
    let neg = format!("{BOTH}neg(x) = -x;\ny = both(f: neg);\n");
    assert!(type_errors(&neg).is_empty(), "{:?}", type_errors(&neg));
    assert_eq!(value(&neg, "y"), "(-2, -0.5)");
    let half = format!("{BOTH}half(x: int) = x div 2;\ny = both(f: half);\n");
    assert_eq!(
        type_errors(&half),
        [
            "`half` is `(x: int) -> int`, not `((x: int) -> int) & ((x: f64) -> f64)`: it is passed where a function of that type is expected, and its own type does not fit that one. [half]"
        ]
    );
    // A call through the slot that no arrow takes is refused with each arrow.
    let text = "both(f: ((x: int) -> int) & ((x: f64) -> f64)) = f(x: \"a\");\n";
    assert_eq!(
        type_errors(text),
        ["`f` does not take (\"a\"): no arrow of `f` takes these types. [f(x: \"a\")]"]
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
        "(f: ((x: int) -> int) & ((x: f64) -> f64) & ((x: rat) -> rat)) -> int"
    );
    let half = format!("{text}half(x: int) = x div 2;\ny = three(f: half);\n");
    assert_eq!(
        type_errors(&half),
        [
            "`half` is `(x: int) -> int`, not `((x: int) -> int) & ((x: f64) -> f64) & \
             ((x: rat) -> rat)`: it is passed where a function of that type is expected, and its own type does not fit that one. [half]"
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
    // Three arrows, two of which cover the slot's parameter together, and the third takes
    // `String`, which the slot does not: a domain is exact (DESIGN.md sec:type_language, `int
    // -> int` is not a subtype of `int[0..<10] -> int`), so the overload, whose domain is
    // `int | String | bool`, does not fit (FAIL-types-fn-param-exact-domain).
    let text = "p(f: (x: int | bool) -> String) = f(x: 1);\n\
                q(g: ((x: int) -> String) & ((x: String) -> int) & ((x: bool) -> String)) = \
                p(f: g);\n";
    assert_eq!(
        type_errors(text),
        [
            "`p` does not take (((x: int) -> String) & ((x: String) -> int) & ((x: bool) -> String)): no arrow of `p` takes these types. [p(f: g)]"
        ]
    );
}

/// Arrows that cover the slot's parameter together but one of which returns outside the slot's
/// result do not fit: at `bool`, `g` gives an `int`.
#[test]
fn arrows_that_cover_together_must_each_return_within_the_slots_result() {
    let text = "p(f: (x: int | bool) -> String) = f(x: 1);\n\
                q(g: ((x: int) -> String) & ((x: bool) -> int)) = p(f: g);\n";
    assert_eq!(
        type_errors(text),
        [
            "`p` does not take (((x: int) -> String) & ((x: bool) -> int)): no arrow of `p` takes these types. [p(f: g)]"
        ]
    );
    // Nor do arrows that leave part of the parameter out.
    let text = "p(f: (x: int | bool | String) -> String) = f(x: 1);\n\
                q(g: ((x: int) -> String) & ((x: bool) -> String)) = p(f: g);\n";
    assert_eq!(
        type_errors(text),
        [
            "`p` does not take (((x: int) -> String) & ((x: bool) -> String)): no arrow of `p` takes these types. [p(f: g)]"
        ]
    );
}

/// Case (1) of `check::ty::covered` (COMPLEXITY.md F82): arrows that cover a slot only by
/// splitting two parameters at once are refused, with the reason, since whether a union of
/// products covers a product is coNP-complete. One parameter split, the other held by each
/// arrow, is covered.
#[test]
fn arrows_that_cover_only_across_two_parameters_are_refused_with_the_reason() {
    let text = "p(f: (x: int | bool, y: int | bool) -> String) = f(x: 1, y: 2);\n\
                q(g: ((x: int, y: int) -> String) & ((x: bool, y: bool) -> String) & \
                ((x: int, y: bool) -> String) & ((x: bool, y: int) -> String)) = p(f: g);\n";
    assert_eq!(
        type_errors(text),
        [
            "`p` does not take (((x: int, y: int) -> String) & ((x: bool, y: bool) -> String) & ((x: int, y: bool) -> String) & ((x: bool, y: int) -> String)): at `(x: Part1, y: Part1) -> String`, the arrow `(x: int, y: int) -> String` takes a part of more than one parameter, and arrows are combined only when they differ at one parameter: telling whether arrows that each split several parameters cover them all can take time exponential in the number of parameters, so the checker does not try; to repair it, write the arrows so that they differ at one parameter.\n  Part1 stands for a part written more than once:\n    type Part1 = int | bool; [p(f: g)]"
        ]
    );
    // Each arrow holds `y` at the slot's `int`: an arrow at `y: int | bool` would take `bool`,
    // which the slot does not, and a domain is exact (FAIL-types-fn-param-exact-domain).
    let text = "p(f: (x: int | bool, y: int) -> String) = f(x: 1, y: 2);\n\
                q(g: ((x: int, y: int) -> String) & ((x: bool, y: int) -> String)) = \
                p(f: g);\n";
    assert_eq!(type_errors(text), Vec::<String>::new());
}

/// Case (2): a parameter type that binds nothing takes part in a cover: a function type, read
/// as a variable of its own, alike. An arrow whose parameter type holds a type variable of its
/// own, at any depth, takes no part, with the reason: `(x: (T,)) -> String for T in int | f64`
/// does not take `(bool,)`, and a union with the other arrows' types would bind `T` to `bool`
/// with no check of its bound. Alone, it fits where its bound holds and not elsewhere.
#[test]
fn a_function_type_takes_part_in_a_cover_and_a_type_variable_does_not() {
    let text = "p(f: (x: int | ((y: int) -> int)) -> String) = f(x: 1);\n\
                q(g: ((x: int) -> String) & ((x: (y: int) -> int) -> String)) = p(f: g);\n";
    assert_eq!(type_errors(text), Vec::<String>::new());
    let run = format!("{text}show(x: int | ((y: int) -> int)) = \"shown\";\nz = q(g: show);\n");
    assert_eq!(value(&run, "z"), "\"shown\"");
    // Near miss: the function arrow returns outside the slot's result.
    let text = "p(f: (x: int | ((y: int) -> int)) -> String) = f(x: 1);\n\
                q(g: ((x: int) -> String) & ((x: (y: int) -> int) -> int)) = p(f: g);\n";
    assert_eq!(type_errors(text).len(), 1, "{:?}", type_errors(text));
    let text = "p(f: (x: int | (bool,)) -> String) = f(x: 1);\n\
                q(g: ((x: int) -> String) & ((x: (T,)) -> String for T in int | f64)) = \
                p(f: g);\n";
    assert_eq!(
        type_errors(text),
        [
            "`p` does not take (((x: int) -> String) & ((x: (T,)) -> String) for T in int | f64): at `(x: int | (bool,)) -> String`, the arrow `(x: (T,)) -> String for T in int | f64` would take part of `x` only by binding its type variable there, and arrows that cover a parameter together bind no variable: which part each takes is a choice per arrow, and fixing a bounded variable to each carrier of its bound multiplies the arrows by the product of the bounds. [p(f: g)]"
        ]
    );
    let text = "p(f: (x: (bool,)) -> String) = 0;\n\
                q(g: (x: (T,)) -> String for T in int | f64) = p(f: g);\n";
    assert_eq!(type_errors(text).len(), 1, "{:?}", type_errors(text));
    let text = "p(f: (x: (int,)) -> String) = 0;\n\
                q(g: (x: (T,)) -> String for T in int | f64) = p(f: g);\n";
    assert_eq!(type_errors(text), Vec::<String>::new());
}

/// Case (3): where several arrows take one value, rule 6 gives the intersection of their
/// results. Arrows that each take all of the slot's parameters, or all that the arrows within
/// its result leave of one parameter, are intersected; `String | #a` and `String | #b` meet in
/// `String`.
#[test]
fn arrows_whose_results_only_intersect_within_the_slots_fit() {
    let g = "q(g: ((x: int) -> String | #a) & ((x: int) -> String | #b)) = p(f: g);\n";
    for slot in ["String", "String | #a | #b"] {
        let text = format!("p(f: (x: int) -> {slot}) = f(x: 1);\n{g}");
        assert_eq!(type_errors(&text), Vec::<String>::new(), "{slot}");
    }
    // An arrow within takes `bool`, and the two outside both take what it leaves, `int`.
    let text = "p(f: (x: int | bool) -> String) = f(x: 1);\n\
                q(g: ((x: bool) -> String) & ((x: int | bool) -> String | #a) & \
                ((x: int) -> String | #b)) = p(f: g);\n";
    assert_eq!(type_errors(text), Vec::<String>::new());
    // Near miss: the intersection `String | #c` is not within `String | #a`.
    let text = "p(f: (x: int) -> String | #a) = f(x: 1);\n\
                q(g: ((x: int) -> String | #a | #c) & ((x: int) -> String | #b | #c)) = \
                p(f: g);\n";
    assert_eq!(
        type_errors(text),
        [
            "`p` does not take (((x: int) -> String | #a | #c) & ((x: int) -> String | #b | #c)): at `(x: int) -> String | #a`, the arrows `(x: int) -> String | #a | #c`, `(x: int) -> String | #b | #c` each take all of it, and the intersection of their results, `String | #c`, is not within `String | #a`.\n  Part1 stands for a part written more than once:\n    type Part1 = String | #a; [p(f: g)]"
        ]
    );
}

/// The rest of case (3) is refused with the reason: no one set of the arrows outside the
/// slot's result takes every value. `String` is the intersection at `int` from the first two
/// arrows and at `bool` from the first and the third; finding the values each set of arrows
/// shares is as hard as Orthogonal Vectors.
#[test]
fn arrows_whose_results_intersect_within_only_on_different_sets_are_refused_with_the_reason() {
    let text = "p(f: (x: int | bool) -> String) = f(x: 1);\n\
                q(g: ((x: int | bool) -> String | #a) & ((x: int) -> String | #b) & \
                ((x: bool) -> String | #c)) = p(f: g);\n";
    assert_eq!(
        type_errors(text),
        [
            "`p` does not take (((x: int | bool) -> String | #a) & ((x: int) -> String | #b) & ((x: bool) -> String | #c)): at `(x: int | bool) -> String`, the arrows `(x: int | bool) -> String | #a`, `(x: int) -> String | #b`, `(x: bool) -> String | #c` each return outside `String`; where several take one value, the result is what their results share, and the checker works that out only for arrows that each take all that the arrows returning within `String` leave of one parameter, since finding the values each group of arrows shares takes time that grows with the product of their number; to repair it, write the arrows so that each returns within `String`. [p(f: g)]"
        ]
    );
}

/// A bounded variable is one carrier at a call (sec:type_resolution), so an arrow that takes
/// a slot only with its variable bound to values of two carriers fits only where one argument
/// fixes the variable and the arrow takes no value of it elsewhere. `add` bound to `int | f64`
/// would be called with an `int` and an `f64`; the function `g` returns would be given an `f64`
/// after `x` fixed `T` to `int`. Each was taken before, and the first failed when run.
#[test]
fn a_bounded_variable_bound_to_two_carriers_fits_only_at_one_place() {
    let text = "p(f: (x: int | f64, y: int | f64) -> int | f64) = f(x: 1, y: 1.5);\n\
                add(x, y) = x + y;\nz = p(f: add);\n";
    assert_eq!(
        type_errors(text),
        [
            "`add` is `(x: T, y: T) -> T for T in int | f32 | f64 | rat`, not `(x: Part1, y: Part1) -> Part1`: at `(x: Part1, y: Part1) -> Part1`, the arrow `(x: T, y: T) -> T for T in int | f32 | f64 | rat` takes it only with `T` bound to `Part1`, values of more than one carrier, but a call fixes `T` to one carrier, and `T` stands at 2 places the arguments give, which could be given values of two carriers.\n  Part1 stands for a part written more than once:\n    type Part1 = int | f64; [add]"
        ]
    );
    let text = "p(f: (x: int | f64) -> ((y: int | f64) -> int)) = f(x: 1)(y: 1.5);\n\
                q(g: (x: T) -> ((y: T) -> int) for T in int | f64) = p(f: g);\n";
    assert_eq!(
        type_errors(text),
        [
            "`p` does not take ((x: T) -> (y: T) -> int for T in int | f64): at `(x: Part1) -> (y: Part1) -> int`, the arrow `(x: T) -> (y: T) -> int for T in int | f64` takes it only with `T` bound to `Part1`, values of more than one carrier, but a call fixes `T` to one carrier, and `T` stands where the arrow takes values of it inside a function type, which need not be of the carrier its argument fixes.\n  Part1 stands for a part written more than once:\n    type Part1 = int | f64; [p(f: g)]"
        ]
    );
    // Near miss: one place, the result's alike, so each value takes the arrow at its carrier.
    let text = "p(f: (x: int | f64) -> int | f64) = f(x: 1);\ninc(x) = x + 1;\nz = p(f: inc);\n";
    assert_eq!(type_errors(text), Vec::<String>::new());
    assert_eq!(value(text, "z"), "2");
}

/// Case (4): an overload whose arrows overlap, `h(x: int | bool) = "a"; h(x: int) = 3`, is
/// refused where an arrow is expected, by elaboration, since choosing among overloads arrives
/// at step L2: by
/// the order of sec:type_resolution `int` is the more specific, so `h` at `int` gives `3`, and the
/// type L2 gives the name is `((x: bool) -> String) & ((x: int) -> int)`. That type is refused
/// where `(x: int | bool) -> String` is expected, and fits where `String | int` is.
#[test]
fn an_overload_whose_arrows_overlap_is_checked_by_the_arrows_it_names() {
    for result in ["String", "String | int"] {
        let text = format!(
            "p(f: (x: int | bool) -> {result}) = f(x: 1);\nh(x: int | bool) = \"a\";\n\
             h(x: int) = 3;\nz = p(f: h);\n"
        );
        assert_eq!(
            errors(&text),
            [
                "`h` names 2 definitions, and this version of zedc does not yet choose among definitions that share a name. Give each of them a name of its own. [h]"
            ],
            "{result}"
        );
    }
    let text = "p(f: (x: int | bool) -> String) = f(x: 1);\n\
                q(g: ((x: bool) -> String) & ((x: int) -> int)) = p(f: g);\n";
    assert_eq!(
        type_errors(text),
        [
            "`p` does not take (((x: bool) -> String) & ((x: int) -> int)): no arrow of `p` takes these types. [p(f: g)]"
        ]
    );
    let text = "p(f: (x: int | bool) -> String | int) = f(x: 1);\n\
                q(g: ((x: bool) -> String) & ((x: int) -> int)) = p(f: g);\n";
    assert_eq!(type_errors(text), Vec::<String>::new());
}

/// Case (3) with results that hold a function or a variable: a function is in no other
/// result that holds none, so `String | ((y: int) -> int)` and `String | #a` meet in `String`;
/// and `U | #a` and `U | #b`, at each carrier the caller picks for `U`, meet in `U`; `U` is left
/// out where each of its carriers is missing from another result. Each fits as rule 6 of
/// sec:type_resolution gives, and a near miss does not.
#[test]
fn results_that_hold_a_function_or_a_variable_are_intersected() {
    let text = "p(f: (x: int) -> String) = f(x: 1);\n\
                q(g: ((x: int) -> String | #a) & ((x: int) -> String | ((y: int) -> int))) = \
                p(f: g);\n";
    assert_eq!(type_errors(text), Vec::<String>::new());
    let text = "p(f: (x: U) -> U for U in int | f64) = f(x: 1);\n\
                q(g: ((x: T) -> T | #a for T in int | f64) & ((x: T) -> T | #b for T in int | \
                f64)) = p(f: g);\n";
    assert_eq!(type_errors(text), Vec::<String>::new());
    // Near misses: both results hold a function, which may be in both; `#a` is in both.
    let text = "p(f: (x: int) -> String) = f(x: 1);\n\
                q(g: ((x: int) -> String | #a | ((y: int) -> int)) & ((x: int) -> String | \
                ((y: int) -> int))) = p(f: g);\n";
    assert_eq!(
        type_errors(text),
        [
            "`p` does not take (((x: int) -> String | ((y: int) -> int) | #a) & ((x: int) -> String | ((y: int) -> int))): at `(x: int) -> String`, the arrows `(x: int) -> String | ((y: int) -> int) | #a`, `(x: int) -> String | ((y: int) -> int)` each take all of it, and the intersection of their results, as the checker builds it (a function in one result is left out where another holds no function, and a variable bounded by carriers where each carrier of its bound is missing from some other result; a result that holds the unknown is left out unless every result holds it; every other piece that holds a function, a variable or the unknown is kept whole), is not within `String`. [p(f: g)]"
        ]
    );
    let text = "p(f: (x: U) -> U for U in int | f64) = f(x: 1);\n\
                q(g: ((x: T) -> T | #a for T in int | f64) & ((x: T) -> T | #a for T in int | \
                f64)) = p(f: g);\n";
    assert_eq!(type_errors(text).len(), 1, "{:?}", type_errors(text));
    // `U` is one carrier at a call: at `int` the third result holds none, at `f64` the second,
    // so `U` is in no value all three share, though no one result misses both carriers.
    let text = "p(f: (x: U) -> String for U in int | f64) = f(x: 1);\n\
                q(g: ((x: T) -> T | #a for T in int | f64) & ((x: int | f64) -> int | String) & \
                ((x: int | f64) -> f64 | String)) = p(f: g);\n";
    assert_eq!(type_errors(text), Vec::<String>::new());
    // Near miss: the second result holds `f64` too, so at `f64` all three hold `U`.
    let text = "p(f: (x: U) -> String for U in int | f64) = f(x: 1);\n\
                q(g: ((x: T) -> T | #a for T in int | f64) & ((x: int | f64) -> int | f64 | \
                String) & ((x: int | f64) -> f64 | String)) = p(f: g);\n";
    assert_eq!(type_errors(text).len(), 1, "{:?}", type_errors(text));
    // A tuple that holds a variable is not intersected value by value (DESIGN's example): the
    // results meet only on `String`, and the fit is refused with how the checker built it.
    let text = "p(f: (x: U) -> String for U in int | f64) = f(x: 1);\n\
                q(g: ((x: T) -> (T,) | String for T in int | f64) & ((x: int | f64) -> (bool,) | \
                String)) = p(f: g);\n";
    let errors = type_errors(text);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(errors[0].contains("as the checker builds it"), "{errors:?}");
}

/// Case (3) with a result that holds `_`, which is every value (A92), so it leaves the
/// intersection of the other results as it is: at `int`, `#s | #a` and `#s | #b` meet in `#s`
/// beside `_` (FAIL-kernel-print-seed-12530893063770583521). The expected type guarantees
/// `int` and permits every key the overload takes. A program cannot yet write `_`, so the
/// types are read as the checker reads type text. A near miss: `#a` is in both other results.
#[test]
fn a_result_that_holds_the_unknown_leaves_the_intersection_as_it_is() {
    use zedc::check::read::parse_type;
    let want = parse_type("(int -> #s) & ((int | f64 | bool | #c) ->? _)").unwrap();
    let given =
        parse_type("((int | f64) -> #s | #a) & ((int | bool) -> #s | #b) & ((int | #c) -> _)")
            .unwrap();
    assert!(given.subtype(&want), "{given} | {}", given.refused(&want));
    let near =
        parse_type("((int | f64) -> #s | #a) & ((int | bool) -> #s | #a) & ((int | #c) -> _)")
            .unwrap();
    assert!(!near.subtype(&want), "{near}");
    assert!(
        near.refused(&want).contains("is not within `#s`"),
        "{}",
        near.refused(&want)
    );
}

/// A partial arrow that takes all of an exact arrow's keys bounds its answers there: a
/// function of `(int ->? #b) & (int -> #b | #c)` answers at each `int` within `#b`, the
/// partial arrow's value type, and within `#b | #c`, so within `#b`
/// (FAIL-types-cover-partial-arrows-left-out). Before, the cover took the exact arrows alone
/// and refused it, its message saying "the intersection of their results, `#b`, is not within
/// `#b`". A near miss: `#c` is in both results, so the partial arrow narrows nothing.
#[test]
fn a_partial_arrow_narrows_the_answers_an_exact_arrow_guarantees() {
    use zedc::check::read::parse_type;
    let given = parse_type("(int ->? #b) & (int -> #b | #c)").unwrap();
    let want = parse_type("int -> #b").unwrap();
    assert!(given.subtype(&want), "{}", given.refused(&want));
    assert!(want.subtype(&given), "{}", want.refused(&given));
    let near = parse_type("(int ->? #b | #c) & (int -> #b | #c)").unwrap();
    assert!(!near.subtype(&want), "{near}");
}

/// A partial arrow's value type is kept apart from its lookup type (author P350, way (a)): a
/// map may store `#notFound` as a value (DESIGN.md sec:corner_cases), so at keys an exact arrow
/// guarantees, `int ->? #b` answers `#b` and `int ->? #b | #notFound` may answer a stored
/// `#notFound` (FAIL-types-partial-arrow-value-type). Before, a partial arrow kept only its
/// lookup `V | #notFound`, and the two read as one type.
#[test]
fn a_partial_arrow_keeps_its_value_type_apart_from_its_lookup_type() {
    use zedc::check::read::parse_type;
    let same = |a: &str, b: &str| {
        let (x, y) = (parse_type(a).unwrap(), parse_type(b).unwrap());
        x.subtype(&y) && y.subtype(&x)
    };
    assert!(same("(int ->? #b) & (int -> _)", "int -> #b"));
    assert!(same(
        "(int ->? #b | #notFound) & (int -> _)",
        "int -> #b | #notFound"
    ));
    assert!(!same("int ->? #b", "int ->? #b | #notFound"));
    // The narrower value type fits the wider, and not the other way.
    let (narrow, wide) = (
        parse_type("int ->? #b").unwrap(),
        parse_type("int ->? #b | #notFound").unwrap(),
    );
    assert!(narrow.subtype(&wide), "{}", narrow.refused(&wide));
    assert!(!wide.subtype(&narrow));
    // Each prints as it reads.
    assert_eq!(wide.to_string(), "int ->? #b | #notFound");
    assert_eq!(narrow.to_string(), "int ->? #b");
}

/// A message names a variable of the expected function type by its name there, not as `_`,
/// the type of every value: in the result it names, and in what a variable is bound to.
#[test]
fn a_refused_cover_names_the_expected_types_variables() {
    let text = "p(f: (x: U) -> U for U in int | f64) = f(x: 1);\n\
                q(g: ((x: int | f64) -> int | f64 | #a) & ((x: int | f64) -> int | f64 | #b)) = \
                p(f: g);\n";
    assert_eq!(
        type_errors(text),
        [
            "`p` does not take (((x: Part1) -> int | f64 | #a) & ((x: Part1) -> int | f64 | #b)): at `(x: U) -> U for U in int | f64`, the arrows `(x: Part1) -> int | f64 | #a`, `(x: Part1) -> int | f64 | #b` each take all of it, and the intersection of their results, `Part1`, is not within `U`.\n  Part1 stands for a part written more than once:\n    type Part1 = int | f64; [p(f: g)]"
        ]
    );
    let text = "p(f: (x: U, y: int | f64) -> U for U in int | f64) = 0;\n\
                q(g: (x: T, y: T) -> T for T in int | f64) = p(f: g);\n";
    assert_eq!(
        type_errors(text),
        [
            "`p` does not take ((x: T, y: T) -> T for T in int | f64): at `(x: U, y: int | f64) -> U for U in int | f64`, the arrow `(x: T, y: T) -> T for T in int | f64` takes it only with `T` bound to `int | f64 | U`, values of more than one carrier, but a call fixes `T` to one carrier, and `T` stands at 2 places the arguments give, which could be given values of two carriers. [p(f: g)]"
        ]
    );
}

/// A signature built from parts, as the checker builds one: one named parameter `x0` of type
/// `param`, returning `result`, owning the variables `own`.
fn sig_of(
    own: &[zedc::check::ty::Ty],
    param: zedc::check::ty::Ty,
    result: zedc::check::ty::Ty,
) -> zedc::check::ty::Sig {
    use zedc::check::ty::{Arrow, Facts, SParam, Sig};
    let mut s = Sig {
        params: vec![SParam {
            name: "x0".into(),
            positional: false,
            default: None,
            range: None,
        }],
        arrows: vec![Arrow {
            params: vec![param],
            result,
            partial: false,
            stores_not_found: false,
        }],
        bounds: Default::default(),
        data: false,
        dense: zedc::check::ty::Dense::No,
        keys: None,
        word: None,
        needs: Vec::new(),
        own: own.iter().filter_map(|v| v.vars.first().cloned()).collect(),
        held: Default::default(),
        named: 0,
        hull: None,
        facts: Facts::default(),
    };
    s.note_held();
    s
}

/// `(x0: (T,)) -> (T,)` fits a copy of itself in which `T` is a union of one-element tuples,
/// `(x0: ((X0,),) | ((X1,),)) -> ((X0,) | (X1,),)`, as it does where `T` is a union of
/// values: `T` takes `(X0,) | (X1,)`, and the result `((X0,) | (X1,),)` is the copy's
/// (DESIGN sec:type_resolution: a type variable stands for every type, and a tuple type for
/// its set of tuples). A copy whose result leaves out the last member does not fit.
/// Before (FAIL-types-singleton-tuple-union-match), the result's `(X1,)` was taken by the
/// shape `(X0,)`, the first in written order, by binding `X0` to `X1`, so the result was held
/// only by binding a variable, and the copy did not fit for two members or more.
#[test]
fn a_variable_of_one_element_tuples_fits_its_copy() {
    use zedc::check::ty::{Ty, fits_sig};
    let one = |t: &Ty| Ty::tuple(vec![t.clone()]);
    let t = Ty::var("T".into());
    let s = sig_of(std::slice::from_ref(&t), one(&t), one(&t));
    let lits = (0..3).map(|i| Ty::lit(&zed_kernel::Value::int((i as i64).into())));
    let vars = (0..3).map(|i| Ty::var(format!("X{i}").into()));
    for (label, leaves) in [
        ("values", lits.collect::<Vec<_>>()),
        ("variables", vars.collect()),
    ] {
        for n in 1..=3 {
            for owned in [false, true] {
                for wrap in [false, true] {
                    let xs = &leaves[..n];
                    let member = |x: &Ty| if wrap { one(x) } else { x.clone() };
                    let param =
                        Ty::union_all(&xs.iter().map(|x| one(&member(x))).collect::<Vec<_>>());
                    let own = if owned && label == "variables" {
                        xs
                    } else {
                        &[][..]
                    };
                    let all = Ty::union_all(&xs.iter().map(member).collect::<Vec<_>>());
                    let q = sig_of(own, param.clone(), one(&all));
                    let case = format!("{label}, {n} members, owned {owned}, one-element {wrap}");
                    assert!(fits_sig(&s, &q), "{case}");
                    if n >= 2 {
                        let less =
                            Ty::union_all(&xs[..n - 1].iter().map(member).collect::<Vec<_>>());
                        assert!(!fits_sig(&s, &sig_of(own, param, one(&less))), "{case}");
                    }
                }
            }
        }
    }
}

#[test]
fn a_joined_one_element_tuple_fits_split_shapes_for_every_bound() {
    use std::collections::BTreeMap;
    use zedc::check::ty::{Arrow, Carrier, EVERY, Facts, SParam, Sig, Ty, fits_sig};
    let mk = |bound: Option<u8>, param: Ty| {
        let own = ["X0", "X1"];
        let mut s = Sig {
            params: vec![SParam {
                name: "x0".into(),
                positional: false,
                default: None,
                range: None,
            }],
            arrows: vec![Arrow {
                params: vec![param],
                result: Ty::carrier(Carrier::Int),
                partial: false,
                stores_not_found: false,
            }],
            bounds: own
                .iter()
                .filter_map(|v| bound.map(|m| ((*v).into(), m)))
                .collect::<BTreeMap<_, _>>(),
            data: false,
            dense: zedc::check::ty::Dense::No,
            keys: None,
            word: None,
            needs: Vec::new(),
            own: own.iter().map(|v| (*v).into()).collect(),
            held: Default::default(),
            named: 0,
            hull: None,
            facts: Facts::default(),
        };
        s.note_held();
        s
    };
    let one = |t: &Ty| Ty::tuple(vec![t.clone()]);
    let (x0, x1) = (Ty::var("X0".into()), Ty::var("X1".into()));
    let joined = one(&x0.union(&x1));
    let split = one(&x0).union(&one(&x1));
    for bound in [None, Some(1u8), Some(EVERY)] {
        // `q`'s parameter must be within `s`'s.
        assert!(
            fits_sig(&mk(bound, split.clone()), &mk(bound, joined.clone())),
            "{bound:?}"
        );
        assert!(
            fits_sig(&mk(bound, joined.clone()), &mk(bound, split.clone())),
            "{bound:?}"
        );
    }
}

/// The signature `(x0: param) -> result` whose own variables are `{p}0` to `{p}{count - 1}`, each
/// bounded by `bound` if given.
pub(super) fn own_sig(
    p: &str,
    count: usize,
    bound: Option<u8>,
    param: zedc::check::ty::Ty,
    result: zedc::check::ty::Ty,
) -> zedc::check::ty::Sig {
    use zedc::check::ty::{Arrow, Facts, SParam, Sig};
    let names: Vec<String> = (0..count).map(|i| format!("{p}{i}")).collect();
    let mut s = Sig {
        params: vec![SParam {
            name: "x0".into(),
            positional: false,
            default: None,
            range: None,
        }],
        arrows: vec![Arrow {
            params: vec![param],
            result,
            partial: false,
            stores_not_found: false,
        }],
        bounds: (names.iter())
            .filter_map(|v| bound.map(|m| (v.as_str().into(), m)))
            .collect(),
        data: false,
        dense: zedc::check::ty::Dense::No,
        keys: None,
        word: None,
        needs: Vec::new(),
        own: names.iter().map(|v| v.as_str().into()).collect(),
        held: Default::default(),
        named: 0,
        hull: None,
        facts: Facts::default(),
    };
    s.note_held();
    s
}

/// A tuple with a component of several pieces holds what the tuples with one piece each there
/// hold, so the checker gives it the verdict it gives them written as a union: true where each
/// is held, and refused where that union is refused. In one component, in one of two, and in
/// both.
#[test]
fn a_joined_tuple_gets_the_verdict_of_its_split_union() {
    use zedc::check::ty::{Carrier, EVERY, Ty, fits_sig, why_unfit};
    let int = Ty::carrier(Carrier::Int);
    let (x, y) = (
        |i: usize| Ty::var(format!("X{i}").into()),
        |i: usize| Ty::var(format!("Y{i}").into()),
    );
    let tup = Ty::tuple;
    let union = |ts: Vec<Ty>| ts.into_iter().reduce(|a, b| a.union(&b)).unwrap();
    // The verdict, and whether a reason is given with it (a refusal, or a cover not tried).
    let verdict = |s: Ty, q: Ty, bound| {
        let (s, q) = (
            own_sig("X", 8, bound, s, int.clone()),
            own_sig("Y", 8, bound, q, int.clone()),
        );
        (fits_sig(&s, &q), why_unfit(&s, &q).is_some())
    };
    for bound in [None, Some(1u8), Some(EVERY)] {
        for n in 2..6 {
            let split = |v: &dyn Fn(usize) -> Ty| union((0..n).map(|i| tup(vec![v(i)])).collect());
            let joined = tup(vec![union((0..n).map(y).collect())]);
            let written = verdict(split(&x), split(&y), bound);
            assert_eq!(verdict(split(&x), joined, bound), written, "{n} {bound:?}");
            // Each variable takes one renamed variable, for any count of shapes.
            assert_eq!(written, (true, false), "{n} {bound:?}");
        }
        // A second component that one shape holds whole.
        let joined = tup(vec![y(0).union(&y(1)), int.clone()]);
        let split = union(vec![
            tup(vec![x(0), int.clone()]),
            tup(vec![x(1), int.clone()]),
        ]);
        assert_eq!(verdict(split, joined, bound), (true, false), "{bound:?}");
        // Two components of two pieces each: split at the first, then at the second.
        let four = |v: &dyn Fn(usize) -> Ty| {
            union(
                [(0, 2), (0, 3), (1, 2), (1, 3)]
                    .map(|(i, j)| tup(vec![v(i), v(j)]))
                    .to_vec(),
            )
        };
        let half = |v: &dyn Fn(usize) -> Ty| {
            union((0..2).map(|i| tup(vec![v(i), v(2).union(&v(3))])).collect())
        };
        let joined = tup(vec![y(0).union(&y(1)), y(2).union(&y(3))]);
        assert_eq!(
            verdict(half(&x), joined.clone(), bound),
            (true, false),
            "{bound:?}"
        );
        let written = verdict(four(&x), four(&y), bound);
        assert_eq!(verdict(four(&x), joined, bound), written, "{bound:?}");
        assert_eq!(verdict(four(&x), half(&y), bound), written, "{bound:?}");
    }
}

/// Split, each piece is still checked: `(Y0 | Y1, int)` is not in `(X0, String) | (X1,
/// String)`; and the bindings the split pieces give are those the
/// result is read with, so `(Y0 | Y1,)` returned where `(X0,) | (X1,)` is fits, and `(Y0,)`
/// does not.
#[test]
fn a_joined_tuple_split_checks_each_piece_and_keeps_its_bindings() {
    use zedc::check::ty::{Carrier, EVERY, Ty, fits_sig};
    let (int, string) = (Ty::carrier(Carrier::Int), Ty::carrier(Carrier::Str));
    let (x, y) = (
        |i: usize| Ty::var(format!("X{i}").into()),
        |i: usize| Ty::var(format!("Y{i}").into()),
    );
    let one = |t: Ty| Ty::tuple(vec![t]);
    for bound in [None, Some(EVERY)] {
        let s = own_sig(
            "X",
            8,
            bound,
            Ty::tuple(vec![x(0), string.clone()]).union(&Ty::tuple(vec![x(1), string.clone()])),
            int.clone(),
        );
        let q = own_sig(
            "Y",
            8,
            bound,
            Ty::tuple(vec![y(0).union(&y(1)), int.clone()]),
            int.clone(),
        );
        assert!(!fits_sig(&s, &q), "{bound:?}");
    }
    let split = one(x(0)).union(&one(x(1)));
    let s = own_sig("X", 8, Some(EVERY), split.clone(), split);
    let joined = one(y(0).union(&y(1)));
    assert!(fits_sig(
        &s,
        &own_sig("Y", 8, Some(EVERY), joined.clone(), joined.clone())
    ));
    assert!(!fits_sig(
        &s,
        &own_sig("Y", 8, Some(EVERY), joined, one(y(0)))
    ));
}

#[test]
fn three_shapes_of_bounded_variables_fit_themselves_renamed() {
    use zedc::check::ty::{Carrier, EVERY, Ty, fits_sig};
    let int = Ty::carrier(Carrier::Int);
    let union = |ts: Vec<Ty>| ts.into_iter().reduce(|a, b| a.union(&b)).unwrap();
    for n in 2..6 {
        let split = |p: &str| {
            union(
                (0..n)
                    .map(|i| Ty::tuple(vec![Ty::var(format!("{p}{i}").into())]))
                    .collect(),
            )
        };
        for bound in [None, Some(1u8), Some(EVERY)] {
            let s = own_sig("X", 8, bound, split("X"), int.clone());
            let q = own_sig("Y", 8, bound, split("Y"), int.clone());
            assert!(fits_sig(&s, &q), "{n} shapes, {bound:?}");
        }
    }
}

/// The signatures `(x0: shapes) -> int`, `(x0: written) -> int` and `(x0: joined) -> int` for
/// n tuples, each of k components and a last component `i`, every own variable bounded to
/// several carriers. Component j of tuple i is two variables, `X_a | X_b`, except at the places
/// `alone`, where each shape has one of the two, every choice of them a shape, so the tuple
/// has 2^|alone| shapes. `written` is the same rows of the variables `Y`, and `joined` the one
/// row of `Y_a | Y_b` at every component, which the shapes hold only split at `alone`. With
/// `missing`, the last shape of each tuple is left out of `shapes`, so `joined` does not fit.
pub(super) fn k_joined_rows(
    n: usize,
    k: usize,
    alone: &[usize],
    missing: bool,
) -> [zedc::check::ty::Sig; 3] {
    use zed_kernel::Value;
    use zedc::check::ty::{Carrier, EVERY, Ty};
    let key = |i: usize| Ty::lit(&Value::int((i as i64).into()));
    let var = |p: &str, i: usize, j: usize, s: usize| {
        Ty::var(format!("{p}{}", (i * k + j) * 2 + s).into())
    };
    let union = |ts: Vec<Ty>| ts.into_iter().reduce(|a, b| a.union(&b)).unwrap();
    // The row of tuple `i` of the variables `p`: the shape `pick` (bit b the variable at the
    // place `alone[b]`), or the joined row.
    let row = |p: &str, i: usize, pick: Option<usize>| {
        let mut cs: Vec<Ty> = (0..k)
            .map(|j| match (pick, alone.iter().position(|&a| a == j)) {
                (Some(bits), Some(b)) => var(p, i, j, (bits >> b) & 1),
                _ => var(p, i, j, 0).union(&var(p, i, j, 1)),
            })
            .collect();
        cs.push(key(i));
        Ty::tuple(cs)
    };
    let m = 1usize << alone.len();
    let rows = |p: &str, m: usize| {
        let picks = (0..n).flat_map(|i| (0..m).map(move |b| (i, b)));
        union(picks.map(|(i, b)| row(p, i, Some(b))).collect())
    };
    let shapes = rows("X", if missing { m - 1 } else { m });
    let joined = union((0..n).map(|i| row("Y", i, None)).collect());
    let int = Ty::carrier(Carrier::Int);
    let c = 2 * k * n;
    [
        own_sig("X", c, Some(EVERY), shapes, int.clone()),
        own_sig("Y", c, Some(EVERY), rows("Y", m), int.clone()),
        own_sig("Y", c, Some(EVERY), joined, int),
    ]
}

/// A row of k joined components fits shapes that hold it only split at the components they
/// differ on, at one or several of them, as the same rows written out do, and fits no longer
/// once a shape is missing (PERF-types-joined-split-many-components). Benchmark:
/// `bench::fits::k_joined_components_split_where_the_shapes_differ_scales`.
#[test]
fn k_joined_components_fit_shapes_that_differ_on_some_of_them() {
    use zedc::check::ty::fits_sig;
    for k in 2..=4 {
        for alone in [vec![k - 1], vec![0], vec![0, k - 1], (0..k).collect()] {
            let [s, written, joined] = k_joined_rows(3, k, &alone, false);
            assert!(fits_sig(&s, &written), "{k} {alone:?}: written out");
            assert!(fits_sig(&s, &joined), "{k} {alone:?}: joined");
            let [s, written, joined] = k_joined_rows(3, k, &alone, true);
            assert!(
                !fits_sig(&s, &written),
                "{k} {alone:?}: written out, one missing"
            );
            assert!(!fits_sig(&s, &joined), "{k} {alone:?}: joined, one missing");
        }
    }
}

/// TEST-read-fit-span-cross-file: `Ck::read_by` (zedc-check) keys the writer of a
/// [`Fit::Read`] by a span, and a span names no file. Two units of one package whose
/// `Read` fits sit at one span, written by constructs at different spans, are each checked by
/// a checker of their own: the package loads, both units compile, and the debug assertion of
/// `Ck::put_read`, which a second writer at one span fails
/// (`a_read_fit_from_a_second_construct_is_caught` in zedc-check), does not fire. Were the
/// two units ever checked into one `Ck`, this package would fail that assertion here.
#[test]
fn two_units_with_read_fits_at_one_span_are_checked_apart() {
    use std::collections::HashMap;
    use std::sync::Arc;
    use zedc::lex::Span;
    use zedc::query::Db;
    use zedc::unit::{Memory, load};

    // `g(b, x)`, of type `1 | f64`, is read at `f64` by the `+` beside `x` (L1.26a, as in
    // l01_26a call_union_at_f64.rs), at one span in both texts; the `+` starts one byte
    // earlier in `b`, at its `(`.
    const G: &str = "g(positional c: bool, positional x: f64) = if c { x } else { 1 };\n";
    let a = format!("{G}k(positional b: bool, positional x: f64) =  x + g(b, x);\n");
    let b = format!("{G}k(positional b: bool, positional x: f64) = (x)+ g(b, x);\n");
    let start = a.rfind("g(b, x)").expect("the call");
    assert_eq!(b.rfind("g(b, x)"), Some(start));
    let at = Span {
        start,
        end: start + "g(b, x)".len(),
    };
    // The writers differ: the `+` of `a` starts at `x`, the `+` of `b` one byte earlier, at
    // `(`, as the parser gives their spans; so a second writer at the `Read` fit's span in one
    // `Ck` would be a different construct, which `put_read`'s assertion would catch.
    let plus_start = |text: &str| {
        let tokens = lex_fence(text).unwrap();
        let tree = parse(text, &tokens, "Unit", TOP).unwrap();
        let stmts = unit(text, &tokens, &tree).unwrap();
        let k = stmts
            .iter()
            .find_map(|s| match &s.kind {
                zedc::ast::StmtKind::Function(f) if f.name == "k" => Some(&f.body),
                _ => None,
            })
            .expect("k");
        match &k.kind {
            zedc::ast::ExprKind::Binary(zedc::ast::BinaryOp::Add, _, _) => k.span.start,
            other => panic!("k's body is not a `+`: {other:?}"),
        }
    };
    assert_eq!(plus_start(&a), a.rfind("x +").expect("x"));
    assert_eq!(plus_start(&b), b.rfind("(x)").expect("(x)"));
    assert_eq!(plus_start(&b) + 1, plus_start(&a));
    for text in [&a, &b] {
        let fits = info(text).0.fits;
        assert_eq!(
            fits.get(&at),
            Some(&Fit::Read(zedc::check::ty::Carrier::F64)),
            "{text}{fits:?}"
        );
    }
    let files: HashMap<String, Arc<str>> = [("a.zed", &a), ("b.zed", &b)]
        .into_iter()
        .map(|(f, t)| (f.to_string(), Arc::from(t.as_str())))
        .collect();
    let mut db = Db::new();
    let p = load(&mut db, &Memory(files), &["a", "b"]);
    let problems = p.report(std::path::Path::new(""));
    assert!(problems.is_empty(), "{problems:#?}");
    for text in [&a, &b] {
        assert!(db.front(text).is_ok(), "{text}");
    }
}

/// `(x0: (X0 | X1,) | (X2,) | (X4 | X5,)) -> int` fits itself renamed `Y`, every variable
/// bounded to several carriers, and so do the same shapes of k = 3 and 10 components with one
/// variable at the places whose bit is set in the shape's number and two at the others
/// (`bench::fits::shapes_at_different_sets_of_places` at n = 3 and 4). The first row binds
/// `X0` to `Y0` and `X1` to `Y1` alone, so the first shape holds no other row: each later row
/// passes it and is held by its own shape. Before (FAIL-types-joined-shape-first) `(Y2,)` and
/// `(Y4 | Y5,)` both failed the first shape, and the second was refused. Controls: with the
/// last shape missing, the rows are not held.
#[test]
fn shapes_after_a_shape_of_two_bound_variables_at_every_place_hold_their_rows() {
    use zedc::check::ty::{Carrier, EVERY, Ty, fits_sig, why_unfit};
    for k in [1usize, 3, 10] {
        for n in [3usize, 4] {
            let var = |p: &str, r: usize, j: usize, s: usize| {
                Ty::var(format!("{p}{}", (r * k + j) * 2 + s).into())
            };
            let row = |p: &str, r: usize| {
                Ty::tuple(
                    (0..k)
                        .map(|j| match (r >> j) & 1 {
                            1 => var(p, r, j, 0),
                            _ => var(p, r, j, 0).union(&var(p, r, j, 1)),
                        })
                        .collect(),
                )
            };
            let rows = |p: &str, n: usize| {
                (0..n)
                    .map(|r| row(p, r))
                    .reduce(|a, b| a.union(&b))
                    .expect("one row at least")
            };
            let int = Ty::carrier(Carrier::Int);
            let c = 2 * k * n;
            let s = own_sig("X", c, Some(EVERY), rows("X", n), int.clone());
            let q = own_sig("Y", c, Some(EVERY), rows("Y", n), int.clone());
            assert_eq!(why_unfit(&s, &q), None, "k {k}, n {n}: {q} in {s}");
            assert!(fits_sig(&s, &q), "k {k}, n {n}: {q} in {s}");
            let fewer = own_sig("X", c, Some(EVERY), rows("X", n - 1), int);
            assert!(!fits_sig(&fewer, &q), "k {k}, n {n}: {q} in {fewer}");
        }
    }
}
