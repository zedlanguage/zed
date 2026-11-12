//! An `if` of literals is a union of literal values, each fixed where the result is used as
//! the literal would be alone; an operation on integer literals alone keeps its value in an
//! `if`; and a negated `rat` literal is a literal (DESIGN.md step L1.26a). Item
//! LIT-branch-carrier, from the findings of TESTS-L1.26-refined-divisor.

use zed_tests::scaling;
use zed_tests::step_helpers::l01_16_elaboration::value;
use zed_tests::step_helpers::l01_26_type_resolution::{Resolved, sig, type_errors};

const H: &str = "h(positional z: f64) = z;\n";

#[test]
fn literal_branches_take_f64_at_a_parameter_of_type_f64() {
    // DESIGN.md step L1.26a: "where both branches are literals each keeps its own value and
    // is fixed where the result is used", and step L1.26: "A literal at a declared type takes
    // the one numeric carrier of the type it can take". `h(2)` is accepted, so `h(if c { 2 }
    // else { 1 })` is too, each branch read at `f64`.
    let src = format!(
        "{H}f(positional c: bool) = h(if c {{ 2 }} else {{ 1 }});\n\
         a = f(true);\nb = f(false);\nc = h(if true {{ 2 }} else {{ 1 }});\n"
    );
    assert_eq!(type_errors(&src), Vec::<String>::new());
    assert_eq!(sig(&src, "f"), "(bool) -> f64");
    assert_eq!(value(&src, "a"), "2.0");
    assert_eq!(value(&src, "b"), "1.0");
    assert_eq!(value(&src, "c"), "2.0");
}

#[test]
fn nested_literal_branches_each_take_f64() {
    // Each branch of a nest of `if`s, a decimal and a negated literal among them.
    let src = format!(
        "{H}f(positional a: bool, positional b: bool) = \
         h(if a {{ 1 }} else if b {{ 2.5 }} else {{ -3 }});\n\
         x = f(true, false);\ny = f(false, true);\nz = f(false, false);\n"
    );
    assert_eq!(type_errors(&src), Vec::<String>::new());
    assert_eq!(sig(&src, "f"), "(bool, bool) -> f64");
    assert_eq!(value(&src, "x"), "1.0");
    assert_eq!(value(&src, "y"), "2.5");
    assert_eq!(value(&src, "z"), "-3.0");
}

#[test]
fn a_decimal_branch_is_still_rejected_at_int() {
    // Negative control: each branch is fixed as it would be alone, so a decimal branch at an
    // `int` parameter is rejected as `h(1.5)` is, at the decimal, and the integer branch is
    // not.
    let src = "h(positional z: int) = z;\nf(positional c: bool) = h(if c { 2 } else { 1.5 });\n";
    let errors = type_errors(src);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(
        errors[0].starts_with("the literal `1.5` is a decimal, and `int` is expected here")
            && errors[0].ends_with("[1.5]"),
        "{errors:?}"
    );
}

#[test]
fn literal_branches_take_the_carrier_of_the_dividend() {
    // The finding of TESTS-L1.26-refined-divisor: `x / (if c { 2 } else { -3 })` with `x`
    // a `rat` or an `f64`. Each branch takes the carrier of `x`, as `x / 2` does, and the
    // divisor `2 | -3` holds no zero, so the `rat` division adds no `#divByZero` (L1.26: "A
    // division, `div` or `mod` whose divisor's type holds no zero adds no `#divByZero`").
    for (x, arg, sig_, v) in [
        ("rat", "1r", "(bool, x: rat) -> rat", "-1r/3r"),
        ("f64", "1.5f64", "(bool, x: f64) -> f64", "-0.5"),
    ] {
        let src = format!(
            "f(positional c: bool, x: {x}) = x / (if c {{ 2 }} else {{ -3 }});\n\
             a = f(false, x: {arg});\n"
        );
        assert_eq!(type_errors(&src), Vec::<String>::new(), "{x}");
        assert_eq!(sig(&src, "f"), sig_);
        assert_eq!(value(&src, "a"), v);
    }
}

#[test]
fn a_zero_branch_keeps_div_by_zero() {
    // Negative control: a divisor `2 | 0` holds zero, so the `rat` division keeps
    // `#divByZero`.
    let src = "f(positional c: bool, x: rat) = x / (if c { 2 } else { 0 });\n";
    assert_eq!(type_errors(src), Vec::<String>::new());
    assert_eq!(sig(src, "f"), "(bool, x: rat) -> rat | #divByZero");
}

#[test]
fn literal_branches_join_the_class_of_a_generic_operand() {
    // DESIGN.md step L1.26a: a literal "joins the class of a parameter of the function" it
    // meets, and takes its carrier by a `match` at run time; so does each branch.
    let src = "f(positional c: bool, x) = x + (if c { 2 } else { 3 });\n\
               a = f(true, x: 0.5f64);\nb = f(false, x: 1);\n";
    assert_eq!(type_errors(src), Vec::<String>::new());
    assert_eq!(sig(src, "f"), "(bool, x: T) -> T for T in int | f64 | rat");
    assert_eq!(value(src, "a"), "2.5");
    assert_eq!(value(src, "b"), "4");
}

#[test]
fn literal_branches_with_nothing_to_fix_them_stay_int() {
    // Negative control: where no other operand gives a carrier, integer branches are `int`,
    // as an integer literal that nothing fixes is.
    let src = "f(positional c: bool) = (if c { 2 } else { 3 }) + 1;\n";
    assert_eq!(type_errors(src), Vec::<String>::new());
    assert_eq!(sig(src, "f"), "(bool) -> int");
}

#[test]
fn an_operation_on_literals_keeps_its_value_beside_a_carrier() {
    // DESIGN.md step L1.26a, beside "with `x: f64`, `if c { x } else { 1 }` is `1 | f64`":
    // "an operation on literals alone keeps its value in an `if`". At run time the operation
    // is the `int` 2, as the literal `1` is the `int` 1 in `1 | f64`.
    let src = "g(positional c: bool, x: f64) = if c { 1 + 1 } else { x };\n\
               a = g(true, x: 0.5f64);\nb = g(false, x: 0.5f64);\n";
    assert_eq!(type_errors(src), Vec::<String>::new());
    assert_eq!(sig(src, "g"), "(bool, x: f64) -> 2 | f64");
    assert_eq!(value(src, "a"), "2");
    assert_eq!(value(src, "b"), "0.5");
}

#[test]
fn an_operation_on_literals_in_an_if_has_its_value_at_run_time() {
    // Each result is compared where it is used, which fixes the `1.5`: bound alone, `b =
    // g(false)` would be rejected at the `1.5`, which nothing fixes (DESIGN.md L1.26a, "`y =
    // g(c)` is rejected at the `2.5`").
    let src = "g(positional c: bool) = if c { 1 + 1 } else { 1.5 };\n\
               a = g(true) == 2;\nb = g(false) == 1.5f64;\n";
    assert_eq!(type_errors(src), Vec::<String>::new());
    assert_eq!(value(src, "a"), "true");
    assert_eq!(value(src, "b"), "true");
    assert_eq!(
        type_errors("g(positional c: bool) = if c { 1 + 1 } else { 1.5 };\nb = g(false);\n"),
        [
            "Nothing gives the literal `1.5` a carrier; the value holds it through a call of `g`. \
             Try `g(positional c: bool) = if c { 1 + 1 } else { 1.5f64 }` instead.\n  fixes, each \
             checked here:\n    g(positional c: bool) = if c { 1 + 1 } else { 1.5f64 };    the \
             literal is then the f64 1.5\n    g(positional c: bool) = if c { 1 + 1 } else { 1.5r \
             };      the literal is then exactly 1.5, a rat [1.5]"
        ]
    );
}

#[test]
fn a_division_of_literals_in_an_if_is_not_kept_as_its_value() {
    // Negative control: DESIGN.md step L1.26a, "one that meets no carrier is typed `int`,
    // rejected under `/`, not as its value". `1 / 2` beside `1.5` is not `0.5`: the decimal
    // is read with it, and nothing fixes its carrier.
    let src = "g(positional c: bool) = if c { 1 / 2 } else { 1.5 };\n";
    let errors = type_errors(src);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(
        errors[0].starts_with("Nothing gives the literal `1.5` a carrier"),
        "{errors:?}"
    );
}

#[test]
fn an_operation_beside_an_integer_literal_takes_the_carrier_of_its_use() {
    // Negative control for the value kept: beside an integer literal the operation and the
    // literal share one class, which takes the carrier of the parameter the `if` meets.
    let src =
        format!("{H}f(positional c: bool) = h(if c {{ 1 + 1 }} else {{ 1 }});\na = f(true);\n");
    assert_eq!(type_errors(&src), Vec::<String>::new());
    assert_eq!(sig(&src, "f"), "(bool) -> f64");
    assert_eq!(value(&src, "a"), "2.0");
}

#[test]
fn a_negated_rat_literal_is_a_literal() {
    // DESIGN.md step L1.26a: "An operation on literals alone, as `2 + 1` or `-1`, is a
    // literal too"; `-3r` is the value -3 at `rat`, as `3r` is 3.
    assert_eq!(sig("f() = -3r;\n", "f"), "() -> -3r");
    assert_eq!(value("y = -3r;\n", "y"), "-3r");
}

#[test]
fn a_negated_rat_divisor_adds_no_div_by_zero() {
    // The finding of TESTS-L1.26-refined-divisor: `x / -3r` kept `#divByZero`, since `-3r`
    // was typed `rat`.
    let src = "f(positional x: rat) = x / -3r;\na = f(1r);\n";
    assert_eq!(type_errors(src), Vec::<String>::new());
    assert_eq!(sig(src, "f"), "(rat) -> rat");
    assert_eq!(value(src, "a"), "-1r/3r");
}

#[test]
fn a_negated_zero_rat_divisor_keeps_div_by_zero() {
    // Negative control: `-0r` is 0, so the division always fails.
    let src = "f(positional x: rat) = x / -0r;\n";
    assert_eq!(sig(src, "f"), "(rat) -> rat | #divByZero");
    let errors = type_errors(src);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(
        errors[0].starts_with("`/` here always fails with `#divByZero`"),
        "{errors:?}"
    );
}

/// A call of a parameter of type `f64` on a nest of `n` `if`s, each branch its own integer
/// literal: a union of `n + 1` literal values, each fixed at `f64`.
fn nest(n: usize) -> String {
    let mut body = String::new();
    for i in 0..n {
        body += &format!("if c == {i} {{ {i} }} else ");
    }
    body += &format!("{{ {n} }}");
    format!("{H}f(positional c: int) = h({body});\n")
}

#[test]
fn scaling() {
    // Complexity tradeoff (DESIGN.md Part G): the branches are read once, each adopts once,
    // and their singletons are joined in pairs, O(n log n); joined one at a time, each union
    // copies the type so far, O(n^2).
    std::thread::Builder::new()
        .stack_size(1 << 29)
        .spawn(|| {
            assert_eq!(type_errors(&nest(3)), Vec::<String>::new());
            assert_eq!(sig(&nest(3), "f"), "(int) -> f64");
            let n = 250;
            let units = scaling::inputs(n, |m| Resolved::new(&nest(m)));
            scaling::check("checking an `if` of n literal branches at `f64`", n, |m| {
                units[&m].check();
            });
        })
        .unwrap()
        .join()
        .unwrap();
}
