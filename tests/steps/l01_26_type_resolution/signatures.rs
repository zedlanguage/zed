//! A declared function's signature comes from its body: an untyped parameter is a type
//! variable, bounded by the carriers its uses take, and the error is at the use that leaves
//! it none.

use zedc::check::ty::{OTHER, Row};

use super::{sig, sig_of, type_errors};

#[test]
fn arithmetic_gives_a_variable_bounded_by_the_numeric_carriers() {
    assert_eq!(
        sig("area(w, h) = w * h;\n", "area"),
        "(w: T, h: T) -> T for T in int | f64 | rat"
    );
    assert_eq!(
        sig("neg(x) = -x;\n", "neg"),
        "(x: T) -> T for T in int | f64 | rat"
    );
}

#[test]
fn an_operator_with_one_carrier_fixes_it() {
    assert_eq!(
        sig("shout(s) = upper(s) ++ \"!\";\n", "shout"),
        "(s: String) -> String"
    );
    assert_eq!(
        sig("both(a, b) = a && b;\n", "both"),
        "(a: bool, b: bool) -> bool"
    );
    // `/` divides f64 and rat only, and the literal `2` adopts f64.
    assert_eq!(sig("half(x) = x / 2;\n", "half"), "(x: f64) -> f64");
    assert_eq!(
        sig("avg(a, b) = (a + b) / 2;\n", "avg"),
        "(a: f64, b: f64) -> f64"
    );
}

#[test]
fn comparison_checks_at_every_ordered_carrier() {
    assert_eq!(
        sig("lt(a, b) = a < b;\n", "lt"),
        "(a: T, b: T) -> bool for T in int | f64 | rat | String | bool"
    );
}

#[test]
fn a_parameter_any_value_fits_gets_a_type_variable() {
    // A variable no carriers bound is printed `_` (DESIGN.md L1.26), and is still the
    // signature's own: two such parameters are two variables.
    let s = sig_of("label(n) = \"n = ${n}\";\n", "label");
    assert_eq!(s.to_string(), "(n: _) -> String");
    assert_eq!(s.own.len(), 1);
    let s = sig_of("pair(a, b) = (a, b);\n", "pair");
    assert_eq!(s.to_string(), "(a: _, b: _) -> (_, _)");
    let [a, b] = &s.arrows[0].params[..] else {
        panic!("two parameters")
    };
    assert_eq!(s.own.len(), 2);
    assert_ne!(a, b);
    assert_eq!(
        s.arrows[0].result.tuples,
        [Row::new(vec![a.clone(), b.clone()])]
    );
    let s = sig_of("g(r) = r else 0;\n", "g");
    assert_eq!(s.to_string(), "(r: _) -> 0 | _");
    assert_eq!(s.arrows[0].result.vars, s.arrows[0].params[0].vars);
    // Only the condition is fixed; the branches stay generic, each its own variable.
    let s = sig_of(
        "pick(positional c, positional a, positional b) = if c { a } else { b };\n",
        "pick",
    );
    assert_eq!(s.to_string(), "(bool, _, _) -> _");
    let ps = &s.arrows[0].params;
    assert_ne!(ps[1], ps[2]);
    let both: std::collections::BTreeSet<_> = ps[1].vars.union(&ps[2].vars).cloned().collect();
    assert_eq!(s.arrows[0].result.vars, both);
}

#[test]
fn a_type_variable_used_as_a_tuple_gives_a_variable_each_call_binds() {
    let s = sig_of("first(p) = p[0];\n", "first");
    assert_eq!(s.to_string(), "(p: _) -> _");
    // The result is a second variable, which the need of `p[0]` gives at each call.
    let (p, r) = (&s.arrows[0].params[0].vars, &s.arrows[0].result.vars);
    assert_eq!((p.len(), r.len()), (1, 1));
    assert_ne!(p, r);
    assert_eq!(s.needs.len(), 1);
}

#[test]
fn a_declared_type_is_kept() {
    assert_eq!(
        sig("apply(positional x, f: (int) -> int) = f(x);\n", "apply"),
        "(int, f: ((int) -> int)) -> int"
    );
    assert_eq!(
        sig(
            "n(x: int | String) = if x is String { len(x) } else { x * 2 };\n",
            "n"
        ),
        "(x: int | String) -> int"
    );
}

#[test]
fn a_default_is_checked_at_its_parameters_type() {
    assert_eq!(
        sig("tax(price, rate = 0.2) = price * rate;\n", "tax"),
        "(price: f64, rate: f64) -> f64"
    );
    assert_eq!(
        sig("tax(price, rate = price / 10.0) = price * rate;\n", "tax"),
        "(price: f64, rate: f64) -> f64"
    );
}

#[test]
fn a_default_of_the_wrong_type_is_an_error() {
    assert_eq!(
        type_errors("f(a: int, b: int = a > 0) = a + b;\n"),
        ["the default of `b` is bool, not int [a > 0]"]
    );
}

#[test]
fn a_body_that_checks_at_no_type_is_reported() {
    // Wrong at every type: the error is the body's own.
    assert_eq!(
        type_errors("bad(x) = x + \"a\" * 2;\n"),
        ["`*` does not take (\"a\", 2) [\"a\" * 2]"]
    );
    // Wrong at each carrier, for a reason that depends on it: `++` makes `x` a String, and
    // the error is at the use that then finds it none.
    assert_eq!(
        type_errors("neither(x) = x ++ \"a\" + 1;\n"),
        ["`+` does not take (String, 1) [x ++ \"a\" + 1]"]
    );
}

#[test]
fn a_parameter_compared_with_a_tuple_may_be_a_tuple() {
    // `<` orders tuples of one length as well as carriers, so `x` may be `(3, 4)`: its
    // class keeps the tuple arrow, which allows only other values, and bounds its variable.
    let src = "lt(positional x) = x < (1, 2);\nmain() = lt((3, 4));\n";
    // No bounds clause can write a bound of other values, so the variable is printed `_`.
    let s = sig_of(src, "lt");
    assert_eq!(s.to_string(), "(_) -> bool");
    assert!(s.bounds.values().all(|m| m & OTHER != 0) && s.bounds.len() == 1);
    assert!(type_errors(src).is_empty(), "{:?}", type_errors(src));
}

#[test]
fn a_literal_compared_for_equality_does_not_bound_a_parameter() {
    // `==` takes any two values, so the literal follows the class and leaves it every
    // carrier: `eq1("a")` is false, not an error.
    let src = "eq1(positional x) = x == 1;\nmain() = eq1(\"a\");\n";
    let s = sig_of(src, "eq1");
    assert_eq!(s.to_string(), "(_) -> bool");
    assert!(s.bounds.is_empty());
    assert_eq!(s.own.len(), 1);
    assert!(type_errors(src).is_empty(), "{:?}", type_errors(src));
}
