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
          rename it `b`. The lambda is passed where a function of type `(a: int, b: int) -> int` is \
          expected, and a call of it passes each named argument by its name, so each parameter \
          the lambda does not take by position must have a name of `(a: int, b: int) -> int` or \
          a default [s]"
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
        [
            "the lambda returns int, and `(int) -> String` returns String: the lambda is passed where a function of type `(int) -> String` is expected, so its result must be String [n + 1]"
        ]
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
            "`half` is `(x: int) -> int`, not `((x: int) -> int) & ((x: f64) -> f64)`: it is passed where a function of that type is expected, and its own type does not fit that one [half]"
        ]
    );
    // A call through the slot that no arrow takes is refused with each arrow.
    let text = "both(f: ((x: int) -> int) & ((x: f64) -> f64)) = f(x: \"a\");\n";
    assert_eq!(
        type_errors(text),
        ["`f` does not take (\"a\"): no arrow of `f` takes these types [f(x: \"a\")]"]
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
             ((x: rat) -> rat)`: it is passed where a function of that type is expected, and its own type does not fit that one [half]"
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
        [
            "`p` does not take (((x: int) -> String) & ((x: bool) -> int)): no arrow of `p` takes these types [p(f: g)]"
        ]
    );
    // Nor do arrows that leave part of the parameter out.
    let text = "p(f: (x: int | bool | String) -> String) = f(x: 1);\n\
                q(g: ((x: int) -> String) & ((x: bool) -> String)) = p(f: g);\n";
    assert_eq!(
        type_errors(text),
        [
            "`p` does not take (((x: int) -> String) & ((x: bool) -> String)): no arrow of `p` takes these types [p(f: g)]"
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
            "`p` does not take (((x: int, y: int) -> String) & ((x: bool, y: bool) -> String) & ((x: int, y: bool) -> String) & ((x: bool, y: int) -> String)): at `(x: T1, y: T1) -> String`, the arrow `(x: int, y: int) -> String` takes a part of more than one parameter, and arrows are combined only when they differ at one parameter: telling whether arrows that each split several parameters cover them all can take time exponential in the number of parameters, so the checker does not try; to repair it, write the arrows so that they differ at one parameter\n  T1 stands for a part written more than once:\n    type T1 = int | bool; [p(f: g)]"
        ]
    );
    let text = "p(f: (x: int | bool, y: int) -> String) = f(x: 1, y: 2);\n\
                q(g: ((x: int, y: int) -> String) & ((x: bool, y: int | bool) -> String)) = \
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
            "`p` does not take (((x: int) -> String) & ((x: (T,)) -> String) for T in int | f64): at `(x: int | (bool,)) -> String`, the arrow `(x: (T,)) -> String for T in int | f64` would take part of `x` only by binding its type variable there, and arrows that cover a parameter together bind no variable: which part each takes is a choice per arrow, and fixing a bounded variable to each carrier of its bound multiplies the arrows by the product of the bounds [p(f: g)]"
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
            "`p` does not take (((x: int) -> String | #a | #c) & ((x: int) -> String | #b | #c)): at `(x: int) -> String | #a`, the arrows `(x: int) -> String | #a | #c`, `(x: int) -> String | #b | #c` each take all of it, and the intersection of their results, `String | #c`, is not within `String | #a`\n  T1 stands for a part written more than once:\n    type T1 = String | #a; [p(f: g)]"
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
            "`p` does not take (((x: int | bool) -> String | #a) & ((x: int) -> String | #b) & ((x: bool) -> String | #c)): at `(x: int | bool) -> String`, the arrows `(x: int | bool) -> String | #a`, `(x: int) -> String | #b`, `(x: bool) -> String | #c` each return outside `String`; where several take one value, the result is what their results share, and the checker works that out only for arrows that each take all that the arrows returning within `String` leave of one parameter, since finding the values each group of arrows shares takes time that grows with the product of their number; to repair it, write the arrows so that each returns within `String` [p(f: g)]"
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
            "`add` is `(x: T, y: T) -> T for T in int | f64 | rat`, not `(x: T1, y: T1) -> T1`: at `(x: T1, y: T1) -> T1`, the arrow `(x: T, y: T) -> T for T in int | f64 | rat` takes it only with `T` bound to `int | f64`, values of more than one carrier, but a call fixes `T` to one carrier, and `T` stands at 2 places the arguments give, which could be given values of two carriers\n  T1 stands for a part written more than once:\n    type T1 = int | f64; [add]"
        ]
    );
    let text = "p(f: (x: int | f64) -> ((y: int | f64) -> int)) = f(x: 1)(y: 1.5);\n\
                q(g: (x: T) -> ((y: T) -> int) for T in int | f64) = p(f: g);\n";
    assert_eq!(
        type_errors(text),
        [
            "`p` does not take ((x: T) -> (y: T) -> int for T in int | f64): at `(x: T1) -> (y: T1) -> int`, the arrow `(x: T) -> (y: T) -> int for T in int | f64` takes it only with `T` bound to `int | f64`, values of more than one carrier, but a call fixes `T` to one carrier, and `T` stands where the arrow takes values of it inside a function type, which need not be of the carrier its argument fixes\n  T1 stands for a part written more than once:\n    type T1 = int | f64; [p(f: g)]"
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
            "`p` does not take (((x: bool) -> String) & ((x: int) -> int)): no arrow of `p` takes these types [p(f: g)]"
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
            "`p` does not take (((x: int) -> String | ((y: int) -> int) | #a) & ((x: int) -> String | ((y: int) -> int))): at `(x: int) -> String`, the arrows `(x: int) -> String | ((y: int) -> int) | #a`, `(x: int) -> String | ((y: int) -> int)` each take all of it, and the intersection of their results, as the checker builds it (a function in one result is left out where another holds no function, and a variable bounded by carriers where each carrier of its bound is missing from some other result; every other piece that holds a function, a variable or the unknown is kept whole), is not within `String` [p(f: g)]"
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
            "`p` does not take (((x: T1) -> int | f64 | #a) & ((x: T1) -> int | f64 | #b)): at `(x: U) -> U for U in int | f64`, the arrows `(x: int | f64) -> int | f64 | #a`, `(x: int | f64) -> int | f64 | #b` each take all of it, and the intersection of their results, `int | f64`, is not within `U`\n  T1 stands for a part written more than once:\n    type T1 = int | f64; [p(f: g)]"
        ]
    );
    let text = "p(f: (x: U, y: int | f64) -> U for U in int | f64) = 0;\n\
                q(g: (x: T, y: T) -> T for T in int | f64) = p(f: g);\n";
    assert_eq!(
        type_errors(text),
        [
            "`p` does not take ((x: T, y: T) -> T for T in int | f64): at `(x: U, y: int | f64) -> U for U in int | f64`, the arrow `(x: T, y: T) -> T for T in int | f64` takes it only with `T` bound to `int | f64 | U`, values of more than one carrier, but a call fixes `T` to one carrier, and `T` stands at 2 places the arguments give, which could be given values of two carriers [p(f: g)]"
        ]
    );
}
