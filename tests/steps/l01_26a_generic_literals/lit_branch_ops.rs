//! An operation on literals alone keeps its value as a branch of an `if`, and the result of a
//! call whose type lists literal values alone is read at the carrier of the parameter it meets
//! (DESIGN.md step L1.26a). Item LIT-branch-op-value, after LIT-branch-carrier.
//!
//! The text relied on, from step L1.26a: "where both branches are literals each keeps its own
//! value and is fixed where the result is used, so `if c { 2 } else { 1 }` is `2 | 1` and
//! `g(positional c: bool) = if c { 1 } else { 2.5 }` is `(bool) -> 1 | 2.5`, `z: f64 = if c {
//! 2 } else { 1 }` and `z: f64 = g(c)` read both branches at `f64`"; "An operation on literals
//! alone, as `2 + 1` or `-1`, is a literal too and takes the carrier of what it meets"; and
//! "an operation on literals alone keeps its value in an `if`, so `if c { 1 + 1 } else { 1.5 }`
//! is `2 | 1.5`, and one that meets no carrier is typed `int`".
//!
//! Printed unions: the author answered QUESTIONS A92 with B (2026-11-11), one fixed order with
//! numeric literals ascending, so `if c { 2 + 1 } else { 1 }` prints as `1 | 3`, not the `3 | 1`
//! of the item's note. Every union pinned here is in that order, which zedc prints today.

use zed_tests::scaling;
use zed_tests::step_helpers::l01_16_elaboration::value;
use zed_tests::step_helpers::l01_26_type_resolution::{Resolved, sig, type_errors};

const H: &str = "h(positional z: f64) = z;\n";
const G: &str = "g(positional c: bool) = if c { 2 } else { 1 };\n";

#[test]
fn an_operation_on_literals_in_an_if_keeps_its_value() {
    // Before this item zedc gave `g` the type `(bool) -> int`: the operation and the literal
    // joined one class, which nothing fixed. Order of the union: A92 answer B.
    let src = "g(positional c: bool) = if c { 2 + 1 } else { 1 };\na = g(true);\nb = g(false);\n";
    assert_eq!(type_errors(src), Vec::<String>::new());
    assert_eq!(sig(src, "g"), "(bool) -> 1 | 3");
    assert_eq!(value(src, "a"), "3");
    assert_eq!(value(src, "b"), "1");
    let both = "g(positional c: bool) = if c { 2 + 1 } else { 1 + 1 };\n";
    assert_eq!(sig(both, "g"), "(bool) -> 2 | 3");
    let negated = "g(positional c: bool) = if c { -(2 + 1) } else { 1 };\n";
    assert_eq!(sig(negated, "g"), "(bool) -> -3 | 1");
}

#[test]
fn an_operation_branch_takes_the_carrier_of_the_parameter_it_meets() {
    // Each branch is fixed where the `if` is used, the operation as `h(2 + 1)` would be.
    let src = format!(
        "{H}f(positional c: bool) = h(if c {{ 2 + 1 }} else {{ 1 + 1 }});\n\
         a = f(true);\nb = f(false);\n"
    );
    assert_eq!(type_errors(&src), Vec::<String>::new());
    assert_eq!(sig(&src, "f"), "(bool) -> f64");
    assert_eq!(value(&src, "a"), "3.0");
    assert_eq!(value(&src, "b"), "2.0");
    let rat = "h(positional z: rat) = z;\nf(positional c: bool) = h(if c { 2 + 1 } else { 1 });\n\
               a = f(true);\n";
    assert_eq!(type_errors(rat), Vec::<String>::new());
    assert_eq!(sig(rat, "f"), "(bool) -> rat");
    assert_eq!(value(rat, "a"), "3r");
    let decimal =
        format!("{H}f(positional c: bool) = h(if c {{ 2 + 1 }} else {{ 2.5 }});\na = f(true);\n");
    assert_eq!(type_errors(&decimal), Vec::<String>::new());
    assert_eq!(value(&decimal, "a"), "3.0");
}

#[test]
fn an_operation_branch_joins_the_class_of_a_generic_operand() {
    // DESIGN.md step L1.26a: "`x * (2 + 1)` is `T`"; so is `x + (if c { 2 + 1 } else { 1 })`,
    // each branch taking the carrier of `x` at run time.
    let src = "f(positional c: bool, x) = x + (if c { 2 + 1 } else { 1 });\n\
               a = f(true, x: 0.5f64);\nb = f(false, x: 1);\n";
    assert_eq!(type_errors(src), Vec::<String>::new());
    assert_eq!(sig(src, "f"), "(bool, x: T) -> T for T in int | f64 | rat");
    assert_eq!(value(src, "a"), "3.5");
    assert_eq!(value(src, "b"), "2");
    let other = "g(positional c: bool, x) = if c { 2 + 1 } else { x };\n";
    assert_eq!(
        sig(other, "g"),
        "(bool, x: T) -> T for T in int | f64 | rat"
    );
}

#[test]
fn an_operation_branch_that_nothing_fixes_is_an_int() {
    // Negative control: "one that meets no carrier is typed `int`". Added to `1`, the `if`
    // meets no carrier, so both branches are `int` and so is the sum.
    let src = "g(positional c: bool) = (if c { 2 + 1 } else { 1 }) + 1;\na = g(true);\n";
    assert_eq!(type_errors(src), Vec::<String>::new());
    assert_eq!(sig(src, "g"), "(bool) -> int");
    assert_eq!(value(src, "a"), "4");
}

#[test]
fn an_inexact_literal_in_an_operation_branch_is_its_own_error() {
    // Each literal of the operation is fixed at `f64` as it would be alone, so the one with no
    // exact `f64` is rejected, at itself, with the fix that writes its nearer `f64`.
    let src =
        format!("{H}f(positional c: bool) = h(if c {{ 9007199254740993 + 0 }} else {{ 1 }});\n");
    assert_eq!(
        type_errors(&src),
        vec![
            "No `f64` equals the literal `9007199254740993`. Try `f(positional c: bool) = \
             h(if c { 9007199254740992 + 0 } else { 1 })` instead.\n  \
             fixes, each checked here:\n    \
             f(positional c: bool) = h(if c { 9007199254740992 + 0 } else { 1 });    the \
             literal is then 9007199254740992.0, the nearer f64 by ties to even \
             [9007199254740993]"
                .to_string()
        ]
    );
}

#[test]
fn a_division_in_an_if_is_still_not_kept() {
    // Negative control: "rejected under `/`, not as its value". `1 / 2` is no `int`, and the
    // `1` beside it takes no carrier from it either.
    let src = "g(positional c: bool) = if c { 1 / 2 } else { 1 };\n";
    assert_eq!(
        type_errors(src),
        vec![
            "Nothing gives the literal `1` a carrier of `f64 \
             | rat`. Try `g(positional c: bool) = if c { 1.0f64 \
             / 2 } else { 1 }` instead.\n  \
             fixes, each checked here:\n    \
             g(positional c: bool) = if c { 1.0f64 / 2 } else { 1 };    the literal is then the \
             f64 1.0\n    \
             g(positional c: bool) = if c { 1r / 2 } else { 1 };        the literal is then \
             exactly 1, a rat [1]"
                .to_string()
        ]
    );
}

#[test]
fn a_call_of_literal_branches_is_read_at_rat() {
    // "`z: f64 = g(c)` read both branches at `f64`"; at a `rat` parameter, at `rat`.
    let src = "g(positional c: bool) = if c { 2 } else { 1 };\nh(positional z: rat) = z;\n\
               f(positional c: bool) = h(g(c));\na = f(true);\nb = f(false);\n";
    assert_eq!(type_errors(src), Vec::<String>::new());
    assert_eq!(sig(src, "f"), "(bool) -> rat");
    assert_eq!(value(src, "a"), "2r");
    assert_eq!(value(src, "b"), "1r");
}

#[test]
fn a_call_of_operation_branches_is_read_at_f64() {
    let src = format!(
        "g(positional c: bool) = if c {{ 2 + 1 }} else {{ 1 }};\n{H}\
         f(positional c: bool) = h(g(c));\na = f(true);\nb = h(g(false));\n"
    );
    assert_eq!(type_errors(&src), Vec::<String>::new());
    assert_eq!(sig(&src, "f"), "(bool) -> f64");
    assert_eq!(value(&src, "a"), "3.0");
    assert_eq!(value(&src, "b"), "1.0");
}

#[test]
fn a_call_of_an_integer_and_a_decimal_is_read_at_f64() {
    // `g` is `(bool) -> 1 | 2.5`, DESIGN's own example; at an `f64` parameter the `1` is read
    // as 1.0 and the 2.5 is the `f64` it already is.
    let src = format!(
        "g(positional c: bool) = if c {{ 1 }} else {{ 2.5 }};\n{H}\
         f(positional c: bool) = h(g(c));\na = f(true);\nb = f(false);\n"
    );
    assert_eq!(type_errors(&src), Vec::<String>::new());
    assert_eq!(sig(&src, "f"), "(bool) -> f64");
    assert_eq!(value(&src, "a"), "1.0");
    assert_eq!(value(&src, "b"), "2.5");
}

#[test]
fn a_call_of_one_literal_is_read_at_f64() {
    // `k` is `() -> 3`, one value; read as `h(3)` would be.
    let src = format!("k() = 3;\n{H}a = h(k());\n");
    assert_eq!(type_errors(&src), Vec::<String>::new());
    assert_eq!(value(&src, "a"), "3.0");
}

#[test]
fn a_call_of_an_integer_with_no_exact_f64_is_rejected() {
    // Negative control: a value is read only where the carrier holds it exactly, as a literal
    // is. Before this item the message was "`h` does not take (1 | 9007199254740993): these
    // are the types of its arguments here, and `h` has no arrow that takes them all".
    let src = format!(
        "g(positional c: bool) = if c {{ 9007199254740993 }} else {{ 1 }};\n{H}\
         f(positional c: bool) = h(g(c));\n"
    );
    assert_eq!(
        type_errors(&src),
        vec![
            "`h` does not take (1 | 9007199254740993): no `f64` equals 9007199254740993, which \
             `g(c)` may give. Make `g(c)` give a number `f64` holds exactly in its place, or \
             give this parameter of `h` a type that holds 9007199254740993, such as `int`. \
             [h(g(c))]"
                .to_string()
        ]
    );
    // At `rat` the same value is exact.
    let rat = "k() = 9007199254740993;\nh(positional z: rat) = z;\na = h(k());\n";
    assert_eq!(type_errors(rat), Vec::<String>::new());
    assert_eq!(value(rat, "a"), "9007199254740993r");
}

#[test]
fn a_call_of_a_decimal_is_not_read_at_rat() {
    // Negative control: a decimal that nothing fixes where it is written is an `f64` there,
    // and the call gives that `f64`, so it is not read at `rat`. The fix the message offers,
    // the suffix `r`, checks.
    let src = "g(positional c: bool) = if c { 1 } else { 2.5 };\nh(positional z: rat) = z;\n\
               f(positional c: bool) = h(g(c));\n";
    assert_eq!(
        type_errors(src),
        vec![
            "`h` does not take (1 | 2.5): `g(c)` may give the decimal 2.5, an `f64` where it is \
             written, and no `f64` is read as a `rat`. Write 2.5r where it is written, or give \
             this parameter of `h` the type `f64`. [h(g(c))]"
                .to_string()
        ]
    );
    let fixed = src.replace("2.5 }", "2.5r }") + "a = f(false);\n";
    assert_eq!(type_errors(&fixed), Vec::<String>::new());
    assert_eq!(value(&fixed, "a"), "5r/2r");
}

#[test]
fn a_call_is_not_read_where_the_parameter_takes_no_one_carrier() {
    // Negative controls: at `bool` nothing reads a number, and at `f64 | rat` nothing chooses
    // the carrier, so the call is checked as it is.
    let at_bool = "g(positional c: bool) = if c { 2 } else { 1 };\nh(positional z: bool) = z;\n\
                   f(positional c: bool) = h(g(c));\n";
    assert_eq!(
        type_errors(at_bool),
        vec!["`h` does not take (1 | 2): no arrow of `h` takes these types. [h(g(c))]".to_string()]
    );
    let two = "g(positional c: bool) = if c { 2 } else { 1 };\nh(positional z: f64 | rat) = z;\n\
               f(positional c: bool) = h(g(c));\n";
    assert_eq!(type_errors(two).len(), 1, "{:?}", type_errors(two));
    // At `int` the values are `int` already.
    let at_int = "g(positional c: bool) = if c { 2 } else { 1 };\nh(positional z: int) = z;\n\
                  f(positional c: bool) = h(g(c));\na = f(true);\n";
    assert_eq!(type_errors(at_int), Vec::<String>::new());
    assert_eq!(value(at_int, "a"), "2");
}

#[test]
fn a_name_and_a_call_of_a_parameter_are_not_read() {
    // Negative controls: a name is fixed where it is bound ("bound to a name alone"), so `y`
    // is not read at `f64`; and `k(x)` may give the `int` `x`, which is no literal.
    let name =
        format!("{H}f(positional c: bool) = {{ y = if c {{ 2 + 1 }} else {{ 1 }}; h(y) }};\n");
    assert_eq!(
        type_errors(&name),
        vec!["`h` does not take (1 | 3): no arrow of `h` takes these types. [h(y)]".to_string()]
    );
    let param = format!(
        "k(positional x: int) = if x == 1 {{ x }} else {{ 2 }};\n{H}\
         f(positional x: int) = h(k(x));\n"
    );
    assert_eq!(
        type_errors(&param),
        vec!["`h` does not take (int): no arrow of `h` takes these types. [h(k(x))]".to_string()]
    );
}

/// `f`, with `x` of type `t` and the body `body`, applied to `true` and to `false` with `x`
/// given `x`, as `a` and `b`.
fn at_x(t: &str, body: &str, x: &str) -> String {
    format!(
        "{G}f(positional c: bool, x: {t}) = {body};\na = f(true, x: {x});\nb = f(false, x: {x});\n"
    )
}

#[test]
fn a_call_of_literal_values_is_read_at_the_carrier_of_the_other_operand() {
    // Item LIT-op-reads-call. Before it each of these was rejected, as `x * g(c)` was with
    // "`*` does not take (f64, 1 | 2): these are the types of its arguments here, and `*` has
    // no arrow that takes them all [x * g(c)]". L1.26a: "each keeps its own value and is fixed
    // where the result is used".
    let cases = [
        ("f64", "x * g(c)", "0.5f64", "f64", "1.0", "0.5"),
        ("f64", "g(c) * x", "0.5f64", "f64", "1.0", "0.5"),
        ("rat", "x - g(c)", "0.5r", "rat", "-3r/2r", "-1r/2r"),
        ("f64", "x / g(c)", "0.5f64", "f64", "0.25", "0.5"),
        ("rat", "x / g(c)", "0.5r", "rat", "1r/4r", "1r/2r"),
        ("f64", "x * g(c) + 1", "0.5f64", "f64", "2.0", "1.5"),
        ("f64", "x < g(c)", "1.5f64", "bool", "true", "false"),
        ("f64", "x == g(c)", "2.0f64", "bool", "true", "false"),
        ("f64", "g(c) != x", "2.0f64", "bool", "false", "true"),
        ("rat", "x == g(c)", "1r", "bool", "false", "true"),
    ];
    for (t, body, x, r, a, b) in cases {
        let src = at_x(t, body, x);
        assert_eq!(type_errors(&src), Vec::<String>::new(), "{src}");
        assert_eq!(sig(&src, "f"), format!("(bool, x: {t}) -> {r}"), "{src}");
        assert_eq!(value(&src, "a"), a, "{src}");
        assert_eq!(value(&src, "b"), b, "{src}");
    }
    // At the top level.
    let top = format!("{G}x = 0.5f64;\na = x * g(true);\n");
    assert_eq!(type_errors(&top), Vec::<String>::new());
    assert_eq!(value(&top, "a"), "1.0");
    // An integer and a decimal, DESIGN's `1 | 2.5`: the `1` is read, the `2.5` is the `f64` it
    // is. Before this item: "`*` does not take (f64, 1)".
    let decimal = "g(positional c: bool) = if c { 2.5 } else { 1 };\n\
                   f(positional c: bool, x: f64) = x * g(c);\n\
                   a = f(true, x: 2.0f64);\nb = f(false, x: 2.0f64);\n";
    assert_eq!(type_errors(decimal), Vec::<String>::new());
    assert_eq!(value(decimal, "a"), "5.0");
    assert_eq!(value(decimal, "b"), "2.0");
    // Two levels of call, the values operations on literals.
    let two = "g(positional c: bool) = if c { 2 + 1 } else { 1 };\n\
               k(positional c: bool) = g(c);\n\
               f(positional c: bool, x: f64) = x * k(c);\na = f(true, x: 0.5f64);\n";
    assert_eq!(type_errors(two), Vec::<String>::new());
    assert_eq!(sig(two, "k"), "(bool) -> 1 | 3");
    assert_eq!(value(two, "a"), "1.5");
    // Through a generic function, whose two parameters share one bounded variable.
    let generic = format!(
        "{G}mul(x, y) = x * y;\nf(positional c: bool, x: f64) = mul(x: x, y: g(c));\n\
         a = f(true, x: 0.5f64);\n"
    );
    assert_eq!(type_errors(&generic), Vec::<String>::new());
    assert_eq!(sig(&generic, "f"), "(bool, x: f64) -> f64");
    assert_eq!(value(&generic, "a"), "1.0");
}

#[test]
fn a_call_of_literal_values_beside_no_one_carrier_keeps_its_own() {
    // Negative controls: beside another such call, or beside an `int`, the values are their
    // own carrier, `int`.
    let both = format!("{G}f(positional c: bool) = g(c) * g(c);\na = f(true);\n");
    assert_eq!(type_errors(&both), Vec::<String>::new());
    assert_eq!(sig(&both, "f"), "(bool) -> int");
    assert_eq!(value(&both, "a"), "4");
    let int = at_x("int", "x * g(c)", "3");
    assert_eq!(type_errors(&int), Vec::<String>::new());
    assert_eq!(sig(&int, "f"), "(bool, x: int) -> int");
    assert_eq!(value(&int, "a"), "6");
    let eq = at_x("int", "x == g(c)", "2");
    assert_eq!(type_errors(&eq), Vec::<String>::new());
    assert_eq!(value(&eq, "a"), "true");
}

#[test]
fn a_call_of_a_value_the_other_operand_cannot_hold_is_rejected() {
    // Negative controls: an integer `f64` does not hold exactly, and a decimal at `rat`, as at
    // a parameter, each with the message's menu.
    let big = "g(positional c: bool) = if c { 9007199254740993 } else { 1 };\n";
    for (op, other) in [("*", "*"), ("==", "==")] {
        let src = format!("{big}f(positional c: bool, x: f64) = x {op} g(c);\n");
        assert_eq!(
            type_errors(&src),
            vec![format!(
                "`{other}` does not take (f64, 1 | 9007199254740993): no `f64` equals \
                 9007199254740993, which `g(c)` may give. Make `g(c)` give a number `f64` holds \
                 exactly in its place, or give the other arguments of `{other}` a type that \
                 holds 9007199254740993, such as `int`. [x {op} g(c)]"
            )]
        );
    }
    let decimal = "g(positional c: bool) = if c { 2.5 } else { 1 };\n\
                   f(positional c: bool, x: rat) = x * g(c);\n";
    assert_eq!(
        type_errors(decimal),
        vec![
            "`*` does not take (rat, 1 | 2.5): `g(c)` may give the decimal 2.5, an `f64` where \
             it is written, and no `f64` is read as a `rat`. Write 2.5r where it is written, or \
             give the other arguments of `*` the type `f64`. [x * g(c)]"
                .to_string()
        ]
    );
    // The fix the message offers checks.
    let fixed = decimal.replace("2.5 }", "2.5r }") + "a = f(true, x: 2r);\n";
    assert_eq!(type_errors(&fixed), Vec::<String>::new());
    assert_eq!(value(&fixed, "a"), "5r");
}

#[test]
fn a_name_bound_to_a_call_of_literal_values_is_not_read() {
    // Item LIT-name-reads-call, held for QUESTIONS A63 ("Does a read of a name give the
    // name's literal value a carrier?"), which the author has not answered: DESIGN says two
    // things here. L1.26a reads an integer literal as an `int` where it is "bound to a name
    // alone, `y = 1`", and rejects "`y = g(c)` at the `2.5`, which nothing fixes", so the name
    // fixes the values where it is bound; step 4 of the `q` example in sec:diagnostics reads a
    // literal binder at the carrier of its use. This test pins today's result, which agrees
    // with L1.26a and with A63's recommended answer B; answer A would change it.
    let name = format!("{G}{H}f(positional c: bool) = {{ y = g(c); h(y) }};\n");
    assert_eq!(
        type_errors(&name),
        vec!["`h` does not take (1 | 2): no arrow of `h` takes these types. [h(y)]".to_string()]
    );
    // The same at an operator.
    let op = format!("{G}f(positional c: bool, x: f64) = {{ y = g(c); x * y }};\n");
    assert_eq!(
        type_errors(&op),
        vec![
            "`*` does not take (f64, 1 | 2): no arrow of `*` takes these types. [x * y]"
                .to_string()
        ]
    );
    // The call itself is read, and so is the name where its declared type fixes the values.
    let call = format!("{G}{H}f(positional c: bool) = h(g(c));\na = f(true);\n");
    assert_eq!(type_errors(&call), Vec::<String>::new());
    assert_eq!(value(&call, "a"), "2.0");
    // A binding with a declared type, `y: f64 = g(c);`, is not compiled yet; a cast fixes
    // the carrier where the name is bound.
    let cast = format!("{G}{H}f(positional c: bool) = {{ y = f64(g(c)); h(y) }};\na = f(true);\n");
    assert_eq!(type_errors(&cast), Vec::<String>::new());
    assert_eq!(value(&cast, "a"), "2.0");
    // Bound to a name alone at the top level, the same rule as in a body.
    let top = format!("{G}{H}y = g(true);\na = h(y);\n");
    assert_eq!(
        type_errors(&top),
        vec!["`h` does not take (1 | 2): no arrow of `h` takes these types. [h(y)]".to_string()]
    );
}

/// A function `k` of the parameter type `t`, and `f` passing it `arg`.
fn at_k(t: &str, arg: &str) -> String {
    format!("k(positional p: {t}) = p;\nf(positional c: bool) = k({arg});\n")
}

#[test]
fn an_if_of_literals_in_a_tuple_component_takes_the_carrier_of_the_component() {
    // Item LIT-tuple-branch-ops: an `if` of literals written as a component of a tuple is
    // read as the branches of an argument are (L1.26a: "each keeps its own value and is fixed
    // where the result is used"), at the carrier its component has. Before, each of these was
    // rejected: "`k` does not take ((1 | 3, 1.0)): these are the types of its arguments
    // here, ...".
    let cases = [
        // (parameter type, argument, signature of `f`, value of `f(true)`, of `f(false)`)
        (
            "(f64, f64)",
            "(if c { 2 + 1 } else { 1 }, 1)",
            "(f64, f64)",
            "(3.0, 1.0)",
            "(1.0, 1.0)",
        ),
        (
            "(f64, f64)",
            "(if c { 2 } else { 1 }, 1)",
            "(f64, f64)",
            "(2.0, 1.0)",
            "(1.0, 1.0)",
        ),
        (
            "(f64, f64)",
            "(1, if c { 2 * 3 } else { 1 })",
            "(f64, f64)",
            "(1.0, 6.0)",
            "(1.0, 1.0)",
        ),
        (
            "(f64, f64)",
            "(if c { 0.5 } else { 1 }, 1)",
            "(f64, f64)",
            "(0.5, 1.0)",
            "(1.0, 1.0)",
        ),
        (
            "(rat, rat)",
            "(if c { 2 + 1 } else { 1 }, 1)",
            "(rat, rat)",
            "(3r, 1r)",
            "(1r, 1r)",
        ),
        (
            "(f64, (f64, f64))",
            "(1, (if c { 2 + 1 } else { 1 }, 2))",
            "(f64, (f64, f64))",
            "(1.0, (3.0, 2.0))",
            "(1.0, (1.0, 2.0))",
        ),
        (
            "(f64, f64) | (String, f64)",
            "(if c { 2 + 1 } else { 1 }, 1)",
            "(f64, f64) | (String, f64)",
            "(3.0, 1.0)",
            "(1.0, 1.0)",
        ),
        // The operation is `f64` arithmetic on its exact literals, as alone at `f64`.
        (
            "(f64, f64)",
            "(if c { 9007199254740991 + 2 } else { 1 }, 1)",
            "(f64, f64)",
            "(9007199254740992.0, 1.0)",
            "(1.0, 1.0)",
        ),
        // Where the component is an `int`, the branches keep their own carrier.
        (
            "(int, f64)",
            "(if c { 2 + 1 } else { 1 }, 1)",
            "(int, f64)",
            "(3, 1.0)",
            "(1, 1.0)",
        ),
    ];
    for (t, arg, f, yes, no) in cases {
        let src = at_k(t, arg) + "a = f(true);\nb = f(false);\n";
        assert_eq!(type_errors(&src), Vec::<String>::new(), "{src}");
        assert_eq!(sig(&src, "f"), format!("(bool) -> {f}"), "{src}");
        assert_eq!(value(&src, "a"), yes, "{src}");
        assert_eq!(value(&src, "b"), no, "{src}");
    }
    // An `if` of more than two branches.
    let src = "k(positional p: (f64, f64)) = p;\nf(positional c: bool, d: bool) = k((if c { 2 + 1 } \
               else if d { 4 - 1 } else { 1 }, 1));\na = f(false, d: true);\nb = f(false, d: false);\n";
    assert_eq!(type_errors(src), Vec::<String>::new());
    assert_eq!(value(src, "a"), "(3.0, 1.0)");
    assert_eq!(value(src, "b"), "(1.0, 1.0)");
    // Outside every function.
    let src = "k(positional p: (f64, f64)) = p;\nc = true;\na = k((if c { 2 } else { 1 }, 1));\n";
    assert_eq!(type_errors(src), Vec::<String>::new());
    assert_eq!(value(src, "a"), "(2.0, 1.0)");
    // Where nothing fixes the carrier, the tuple keeps the branches' values.
    let src = "f(positional c: bool) = (if c { 2 + 1 } else { 1 }, 1);\na = f(true);\n";
    assert_eq!(sig(src, "f"), "(bool) -> (1 | 3, 1)");
    assert_eq!(value(src, "a"), "(3, 1)");
}

#[test]
fn an_if_of_literals_in_a_tuple_joins_the_class_of_a_generic_component() {
    // Item LIT-tuple-branch-ops: at a parameter that is a type variable, the `if` is a class
    // of its own, which each branch joins as a lone literal does, and which takes the
    // carrier of what it meets in the body.
    let pair = "sumPair(p) = p[0] + p[1];\n";
    let cases = [
        // (`f`'s parameters, argument, signature of `f`, `f`'s call, value)
        (
            ", x: f64",
            "(x, if c { 2 + 1 } else { 1 })",
            "(bool, x: f64) -> f64",
            "f(true, x: 0.5f64)",
            "3.5",
        ),
        (
            ", x: f64",
            "(x, if c { 2 } else { 1 })",
            "(bool, x: f64) -> f64",
            "f(false, x: 0.5f64)",
            "1.5",
        ),
        (
            ", x: rat",
            "(x, if c { 2 + 1 } else { 0.5 })",
            "(bool, x: rat) -> rat",
            "f(false, x: 0.5r)",
            "1r",
        ),
        (
            ", x: rat",
            "(x, if c { 2 + 1 } else { 0.5 })",
            "(bool, x: rat) -> rat",
            "f(true, x: 0.5r)",
            "7r/2r",
        ),
        (
            "",
            "(1, if c { 2 + 1 } else { 1 })",
            "(bool) -> int",
            "f(true)",
            "4",
        ),
    ];
    for (ps, arg, f, call, v) in cases {
        let src = format!("{pair}f(positional c: bool{ps}) = sumPair(p: {arg});\na = {call};\n");
        assert_eq!(type_errors(&src), Vec::<String>::new(), "{src}");
        assert_eq!(sig(&src, "f"), f, "{src}");
        assert_eq!(value(&src, "a"), v, "{src}");
    }
    // `sum` adds the components as `+` takes them: the branches adopt the `f64` of `x`.
    let src = "f(positional c: bool, x: f64) = sum((x, if c { 2 + 1 } else { 1 }));\n\
               a = f(true, x: 0.5f64);\n";
    assert_eq!(type_errors(src), Vec::<String>::new());
    assert_eq!(sig(src, "f"), "(bool, x: f64) -> f64");
    assert_eq!(value(src, "a"), "3.5");
}

#[test]
fn an_if_of_literals_in_a_tuple_takes_the_carrier_of_the_other_tuple_of_min_and_max() {
    // Item LIT-tuple-branch-ops: `min` and `max` pair the components, and the branches adopt
    // the carrier of the component they are paired with, as the `if` alone does in
    // `min(if c { 2 + 1 } else { 1 }, 0.5f64)`. Before, these were rejected: "the literal
    // `0.5f64` is an `f64` by its suffix, and `int` is expected here; ...".
    let cases = [
        (
            "min((if c { 2 + 1 } else { 1 }, 1), (0.5f64, 1.0f64))",
            "(0.5 | 1.0 | 3.0, 1.0)",
            "(0.5, 1.0)",
            "(0.5, 1.0)",
        ),
        (
            "max((0.5f64, 1.0f64), (if c { 2 + 1 } else { 1 }, 1))",
            "(0.5 | 1.0 | 3.0, 1.0)",
            "(3.0, 1.0)",
            "(1.0, 1.0)",
        ),
        (
            "max((0.5r, (1r, 2r)), (1, (if c { 2 * 3 } else { 1 }, 1)))",
            "(5e-1r | 1r, (1r | 6r, 1r | 2r))",
            "(1r, (6r, 1r))",
            // `max` orders tuples by their first differing component: `1r` beats `0.5r`.
            "(1r, (1r, 1r))",
        ),
        // Beside an `int`, the branches stay `int`.
        (
            "min((if c { 2 + 1 } else { 1 }, 1), (2, 1))",
            "(1 | 2 | 3, 1)",
            "(2, 1)",
            "(1, 1)",
        ),
    ];
    for (body, f, yes, no) in cases {
        let src = format!("f(positional c: bool) = {body};\na = f(true);\nb = f(false);\n");
        assert_eq!(type_errors(&src), Vec::<String>::new(), "{src}");
        assert_eq!(sig(&src, "f"), format!("(bool) -> {f}"), "{src}");
        assert_eq!(value(&src, "a"), yes, "{src}");
        assert_eq!(value(&src, "b"), no, "{src}");
    }
}

#[test]
fn an_inexact_literal_of_an_if_in_a_tuple_is_its_own_error() {
    // Item LIT-tuple-branch-ops: a branch literal with no exact value at its component's
    // carrier is rejected as a lone literal there is, with the fix. Before, the tuple was
    // rejected whole, "`k` does not take ((1 | 9007199254740993, 1.0))", and under `min` the
    // message named the `0.5f64` that the `int` arrow rejects, also for the `if` alone.
    let inexact = |src: &str, fixed: &str| {
        vec![format!(
            "No `f64` equals the literal `9007199254740993`. Try `{}` instead.\n  fixes, \
             each checked here:\n    {fixed}    the literal is then 9007199254740992.0, the nearer f64 by \
             ties to even [9007199254740993]",
            fixed.trim_end_matches(';')
        )]
        .into_iter()
        .map(|m| (src.to_string(), m))
        .collect::<Vec<_>>()
    };
    let cases = [
        (
            "k(positional p: (f64, f64)) = p;\n",
            "f(positional c: bool) = k((if c { 9007199254740993 } else { 1 }, 1));",
            "f(positional c: bool) = k((if c { 9007199254740992 } else { 1 }, 1));",
        ),
        (
            "",
            "f(positional c: bool) = min((if c { 9007199254740993 } else { 1 }, 1), (0.5f64, \
             1.0f64));",
            "f(positional c: bool) = min((if c { 9007199254740992 } else { 1 }, 1), (0.5f64, \
             1.0f64));",
        ),
        (
            "",
            "f(positional c: bool) = min(if c { 9007199254740993 } else { 1 }, 0.5f64);",
            "f(positional c: bool) = min(if c { 9007199254740992 } else { 1 }, 0.5f64);",
        ),
    ];
    for (k, line, fixed) in cases {
        let src = format!("{k}{line}\n");
        let want = inexact(&src, fixed);
        let got: Vec<(String, String)> = type_errors(&src)
            .into_iter()
            .map(|m| (src.clone(), m))
            .collect();
        assert_eq!(got, want);
        // The fix the message offers checks.
        let src = format!("{k}{fixed}\n");
        assert_eq!(type_errors(&src), Vec::<String>::new(), "{src}");
    }
}

#[test]
fn the_probe_programs_of_lit_branch_op_value_keep_their_results() {
    // Item TESTS-lbo-probe-cases: the programs of LIT-branch-op-value's probe that no test
    // above pins whole. A decimal with the suffix `r` beside an integer literal, read at
    // `rat` through a call.
    let src = "g(positional c: bool) = if c { 1 } else { 2.5r };\nh(positional z: rat) = z;\n\
               f(positional c: bool) = h(g(c));\na = f(false);\nb = f(true);\n";
    assert_eq!(type_errors(src), Vec::<String>::new());
    assert_eq!(sig(src, "g"), "(bool) -> 1 | 25e-1r");
    assert_eq!(sig(src, "f"), "(bool) -> rat");
    assert_eq!(value(src, "a"), "5r/2r");
    assert_eq!(value(src, "b"), "1r");
    // An operation on literals beside a decimal, read at `f64` through a call.
    let src = format!(
        "g(positional c: bool) = if c {{ 1 + 1 }} else {{ 1.5 }};\n{H}\
         f(positional c: bool) = h(g(c));\na = f(true);\nb = f(false);\n"
    );
    assert_eq!(type_errors(&src), Vec::<String>::new());
    assert_eq!(sig(&src, "f"), "(bool) -> f64");
    assert_eq!(value(&src, "a"), "2.0");
    assert_eq!(value(&src, "b"), "1.5");
    // A negated operation as a branch written at the parameter; another operator beside it.
    for (branch, v) in [("-(2 + 1)", "-3.0"), ("-(2 * 3)", "-6.0")] {
        let src = format!(
            "{H}f(positional c: bool) = h(if c {{ {branch} }} else {{ 1 }});\na = f(true);\n"
        );
        assert_eq!(type_errors(&src), Vec::<String>::new(), "{src}");
        assert_eq!(sig(&src, "f"), "(bool) -> f64", "{src}");
        assert_eq!(value(&src, "a"), v, "{src}");
    }
}

#[test]
fn an_operation_on_literals_past_two_to_the_53_differs_by_where_it_is_fixed() {
    // Item TESTS-lbo-probe-cases. Written at the `f64` parameter, `2 + 9007199254740991`
    // is `f64` addition of two literals `f64` holds exactly, 9007199254740992.0 by ties to
    // even. Returned by `g`, where nothing fixes it, it is `int` addition, the integer
    // 9007199254740993, which `f64` does not hold exactly, so the call is rejected as one of
    // the literal 9007199254740993 is.
    let inline = format!(
        "{H}f(positional c: bool) = h(if c {{ 2 + 9007199254740991 }} else {{ 1 }});\n\
         a = f(true);\n"
    );
    assert_eq!(type_errors(&inline), Vec::<String>::new());
    assert_eq!(sig(&inline, "f"), "(bool) -> f64");
    assert_eq!(value(&inline, "a"), "9007199254740992.0");
    let call = format!(
        "g(positional c: bool) = if c {{ 2 + 9007199254740991 }} else {{ 1 }};\n{H}\
         f(positional c: bool) = h(g(c));\n"
    );
    assert_eq!(sig(&call, "g"), "(bool) -> 1 | 9007199254740993");
    assert_eq!(
        type_errors(&call),
        vec![
            "`h` does not take (1 | 9007199254740993): no `f64` equals 9007199254740993, which \
             `g(c)` may give. Make `g(c)` give a number `f64` holds exactly in its place, or \
             give this parameter of `h` a type that holds 9007199254740993, such as `int`. \
             [h(g(c))]"
                .to_string()
        ]
    );
}

#[test]
fn a_call_of_literal_values_beside_a_generic_operand_is_an_int_today() {
    // Item TESTS-lbo-probe-cases pins today's result: beside a generic `x` the call is not
    // read at `x`'s carrier, so the values are `int` and fix `x` at `int`. Reading the call
    // at the class of `x`, as `x + (if c { 2 + 1 } else { 1 })` is read, is a follow-up of
    // LIT-op-reads-call, not done here.
    let src = "g(positional c: bool) = if c { 2 + 1 } else { 1 };\n\
               f(positional c: bool, x) = x + g(c);\na = f(true, x: 1);\n";
    assert_eq!(type_errors(src), Vec::<String>::new());
    assert_eq!(sig(src, "f"), "(bool, x: int) -> int");
    assert_eq!(value(src, "a"), "4");
}

#[test]
fn a_call_of_literal_values_at_a_union_of_carriers_is_rejected_whole() {
    // Item TESTS-lbo-probe-cases: the full message of the `f64 | rat` case above. Its last
    // part names `T1`, which the message never uses, for a type written once; a printer fix
    // changes this pin.
    let src = "g(positional c: bool) = if c { 2 } else { 1 };\nh(positional z: f64 | rat) = z;\n\
               f(positional c: bool) = h(g(c));\n";
    assert_eq!(
        type_errors(src),
        vec![
            "`h` does not take (1 | 2): no arrow of `h` takes these types.\n  T1 stands for a part written more than once:\n    \
             type T1 = f64 | rat; [h(g(c))]"
                .to_string()
        ]
    );
    assert_eq!(sig(src, "f"), "(bool) -> Never");
}

/// A body of `n` calls `k((if c { 2 + 1 } else { 1 }, 1))`, each `if` read at `f64`.
fn tuple_calls(n: usize) -> String {
    let mut body = String::new();
    for i in 0..n {
        body += &format!("p{i} = k((if c {{ {i} + 1 }} else {{ 1 }}, 1)); ");
    }
    format!("k(positional p: (f64, f64)) = p;\nf(positional c: bool) = {{ {body}c }};\n")
}

/// A call of a parameter of type `f64` on a nest of `n` `if`s, each branch its own operation
/// on literals: `n + 1` operations, each fixed at `f64`.
fn nest(n: usize) -> String {
    let mut body = String::new();
    for i in 0..n {
        body += &format!("if c == {i} {{ 2 * {i} + 1 }} else ");
    }
    body += &format!("{{ 2 * {n} + 1 }}");
    format!("{H}f(positional c: int) = h({body});\n")
}

/// The same nest as the body of `g`, whose result `h(g(c))` reads at `f64`.
fn through_a_call(n: usize) -> String {
    let mut body = String::new();
    for i in 0..n {
        body += &format!("if c == {i} {{ 2 * {i} + 1 }} else ");
    }
    body += &format!("{{ 2 * {n} + 1 }}");
    format!("g(positional c: int) = {body};\n{H}f(positional c: int) = h(g(c));\n")
}

/// A body of `n` products `x * g(c)`, each call read at the `f64` of `x`.
fn products(n: usize) -> String {
    let mut body = String::new();
    for i in 0..n {
        body += &format!("p{i} = x * g(c); ");
    }
    format!("{G}f(positional c: bool, x: f64) = {{ {body}x }};\n")
}

#[test]
fn scaling() {
    // Complexity tradeoff (DESIGN.md Part G): each operation is kept once as its `if` is
    // walked, read and folded once as a branch of the argument, and adopts once, O(n) in the
    // size of the nest; the call's `n + 1` values are cast once each and their singletons
    // joined in pairs, O(n log n). Joined one at a time, each union copies the type so far,
    // O(n^2).
    std::thread::Builder::new()
        .stack_size(1 << 29)
        .spawn(|| {
            assert_eq!(type_errors(&nest(3)), Vec::<String>::new());
            assert_eq!(sig(&nest(3), "f"), "(int) -> f64");
            assert_eq!(type_errors(&through_a_call(3)), Vec::<String>::new());
            assert_eq!(sig(&through_a_call(3), "g"), "(int) -> 1 | 3 | 5 | 7");
            assert_eq!(sig(&through_a_call(3), "f"), "(int) -> f64");
            let n = 250;
            let units = scaling::inputs(n, |m| Resolved::new(&nest(m)));
            scaling::check(
                "checking an `if` of n operation branches at `f64`",
                n,
                |m| {
                    units[&m].check();
                },
            );
            let units = scaling::inputs(n, |m| Resolved::new(&through_a_call(m)));
            scaling::check("reading a call of n operation branches at `f64`", n, |m| {
                units[&m].check();
            });
            // Item LIT-op-reads-call: each operator application reads its call once per
            // arrow, O(A v log v) for A arrows and v values, so n products cost O(n).
            assert_eq!(type_errors(&products(3)), Vec::<String>::new());
            let n = 1000;
            let units = scaling::inputs(n, |m| Resolved::new(&products(m)));
            scaling::check(
                "reading the calls of n products `x * g(c)` at `f64`",
                n,
                |m| {
                    units[&m].check();
                },
            );
            // Item LIT-tuple-branch-ops: each tuple's components are read once, and each `if`
            // there is walked once and adopts once, O(its size), so n calls cost O(n).
            assert_eq!(type_errors(&tuple_calls(3)), Vec::<String>::new());
            let units = scaling::inputs(n, |m| Resolved::new(&tuple_calls(m)));
            scaling::check(
                "reading the `if`s of n tuple arguments at `(f64, f64)`",
                n,
                |m| {
                    units[&m].check();
                },
            );
        })
        .unwrap()
        .join()
        .unwrap();
}
