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
            "the literal `9007199254740993` has no exact `f64`, and `f64` is expected here; an \
             integer literal takes a carrier only where it is exact\n  \
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
            "the literal `1` takes the carrier of its use, and nothing here chooses one of `f64 \
             | rat`, the carriers what it meets takes\n  \
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
            "`h` does not take (1 | 9007199254740993): `g(c)` may give the integer \
             9007199254740993, which `f64` does not hold exactly, so it cannot be read as the \
             `f64` that `h` takes here; an integer a call gives is read at `f64` only where \
             `f64` holds it exactly, as an integer literal is. Make that value one `f64` holds \
             exactly where it is written, or give this parameter of `h` a type that holds \
             9007199254740993, such as `int` [h(g(c))]"
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
            "`h` does not take (1 | 2.5): `g(c)` may give the decimal 2.5, which nothing fixes \
             where it is written, so it is an `f64` there; an `f64` is not read as the `rat` \
             that `h` takes here, since a call gives that `f64`, not the decimal written. Write \
             that decimal with the suffix `r` where it is written, as 2.5r, or give this \
             parameter of `h` the type `f64` [h(g(c))]"
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
        vec![
            "`h` does not take (1 | 2): these are the types of its arguments here, and `h` has \
             no arrow that takes them all [h(g(c))]"
                .to_string()
        ]
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
        vec![
            "`h` does not take (1 | 3): these are the types of its arguments here, and `h` has \
             no arrow that takes them all [h(y)]"
                .to_string()
        ]
    );
    let param = format!(
        "k(positional x: int) = if x == 1 {{ x }} else {{ 2 }};\n{H}\
         f(positional x: int) = h(k(x));\n"
    );
    assert_eq!(
        type_errors(&param),
        vec![
            "`h` does not take (int): these are the types of its arguments here, and `h` has \
             no arrow that takes them all [h(k(x))]"
                .to_string()
        ]
    );
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
        })
        .unwrap()
        .join()
        .unwrap();
}
