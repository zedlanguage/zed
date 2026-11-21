//! Operator arrows per region: data selects an arrow, a loose atom selects none and flows
//! on, and the atoms of several operands merge into `#errs` of the set of them.

use super::x;
use zed_tests::step_helpers::l01_16_elaboration::errors;
use zed_tests::step_helpers::l01_26_type_resolution::{sig, type_errors};

#[test]
fn one_failure_flows_through_the_arithmetic() {
    assert_eq!(x("int(text(\"x\")) * 2 + 1"), "#invalid");
    assert_eq!(x("-(10 div whole(0))"), "#divByZero");
    // A term with an undefined operand is undefined, the exponent 0 included, as NaN in,
    // NaN out holds for float `^` (item FLOAT-pow-nan).
    assert_eq!(x("(10 div whole(0)) ^ 0"), "#divByZero");
}

#[test]
fn two_failures_merge_into_a_set() {
    assert_eq!(
        x("int(text(\"seven\")) + 10 div whole(0)"),
        "#errs({#divByZero, #invalid})"
    );
    assert_eq!(
        x("10 div whole(0) + int(text(\"seven\"))"),
        "#errs({#divByZero, #invalid})",
        "the set has no order to invent"
    );
    assert_eq!(
        x("int(text(\"a\")) + int(text(\"b\"))"),
        "#invalid",
        "a singleton unwraps"
    );
}

#[test]
fn a_merge_flattens_and_else_replaces_it() {
    let src = "price = int(text(\"n/a\"));\nqty = int(text(\"1.5\"));\nfee = 10 div whole(0);\n\
               total = price * qty + fee;\nshown = total else #divByZero -> 0 else #errs -> 0 else #invalid -> 0;\n";
    let v =
        |n| zed_tests::step_helpers::l01_16_elaboration::value(&format!("{}{src}", super::PASS), n);
    assert_eq!(v("total"), "#errs({#divByZero, #invalid})");
    assert_eq!(v("shown"), "0");
}

#[test]
fn an_atom_compared_with_equals_is_data() {
    assert_eq!(x("int(text(\"x\")) == int(text(\"y\"))"), "true");
    assert_eq!(x("int(text(\"x\")) != round(real(1.0f64 / 0.0))"), "true");
}

#[test]
fn euclidean_division_keeps_the_remainder_non_negative() {
    // DESIGN.md L1.18; `mod` takes only `m` in int[1..] (QUESTIONS A174), `div` any divisor.
    let cases = [
        ("7 div -2", "-3"),
        ("-7 div -2", "4"),
        ("-7 div 2", "-4"),
        ("-7 mod 2", "1"),
        ("(-1 div 4, -1 mod 4)", "(-1, 3)"),
    ];
    for (e, want) in cases {
        assert_eq!(x(e), want, "{e}");
    }
}

/// `mod` takes only `m` in int[1..] (DESIGN.md sec:domains, L1.18; QUESTIONS A174, author,
/// 2026-11-21: "make sure `m > 0` both `mod` and `floatMod`"; row MOD-positive-modulus).
#[test]
fn mod_takes_a_modulus_from_one() {
    // Proved at most 0: no test is offered.
    assert_eq!(
        errors("f(x: int) = x mod 0;\n"),
        ["`mod` takes `m` in int[1..]: `x mod 0`. [x mod 0]"]
    );
    assert_eq!(
        errors("f(x: int) = x mod -3;\n"),
        ["`mod` takes `m` in int[1..]: `x mod -3`. [x mod -3]"]
    );
    // May lie outside: the test, which checks.
    let refused = errors("f(x: int, n: int) = x mod n;\n");
    assert_eq!(refused.len(), 1, "{refused:?}");
    assert!(
        refused[0].starts_with(
            "`mod` takes `m` in int[1..]: `x mod n : int`. Try `if n > 0 { x mod n } else { … }` \
             instead."
        ),
        "{}",
        refused[0]
    );
    let repaired = "f(x: int, n: int) = if n > 0 { x mod n } else { 0 };\n";
    assert_eq!(type_errors(repaired), Vec::<String>::new());
    // In int[1..]: accepted, with no `#divByZero`.
    let ranged = "f(x: int, n: int[1..]) = x mod n;\n";
    assert_eq!(type_errors(ranged), Vec::<String>::new());
    // The residue lies in `0..<m`, so at least 0.
    assert_eq!(sig(ranged, "f"), "(x: int, n: int[1..]) -> int[0..]");
}

/// `x == m * (x div m) + x mod m` and `0 <= x mod m <= m - 1` for every `x` in `-50..=50` and
/// `m` in `1..=12` (DESIGN.md L1.18): one program per `x`, each calling the law at every `m`.
#[test]
fn div_and_mod_keep_the_euclidean_law() {
    let euclid = "euclid(x: int, m: int[1..]) = { q = x div m; r = x mod m; \
                  x == m * q + r && 0 <= r && r <= m - 1 };\n";
    for xv in -50..=50 {
        let calls: Vec<String> = (1..=12)
            .map(|m| format!("euclid(x: {xv}, m: {m})"))
            .collect();
        let src = format!("{euclid}ok = {};\n", calls.join(" && "));
        assert_eq!(
            zed_tests::step_helpers::l01_16_elaboration::value(&src, "ok"),
            "true",
            "x = {xv}"
        );
    }
}

#[test]
fn mixed_kinds_select_no_arrow() {
    assert_eq!(
        errors("x = \"a\" ++ 1;\n"),
        ["`++` does not take (\"a\", 1): no arrow of `++` takes these types. [\"a\" ++ 1]"]
    );
    // A literal keeps its kind: `1.5` is no int, and no form of it is (DESIGN.md L1.26b).
    assert_eq!(
        errors("n = 1;\nx = n + 1.5;\n"),
        [
            "A decimal literal is never an `int`: `n : int + 1.5`. Try `x = rat(n) + 1.5` \
             instead.\n  fixes, each checked here:\n    x = rat(n) + 1.5;    n is cast to rat, and \
             `+` takes two rat\n    x = f64(n) + 1.5;    n is cast to f64, exactly, since it lies within ±2^53 [1.5]"
        ]
    );
    assert_eq!(
        errors("x = 1r/2r * 2.5f64;\n"),
        [
            "The suffix makes the literal `2.5f64` an `f64`, never `rat`. Try `x = 1r/2r * 2.5` instead.\n  fixes, each checked \
             here:\n    x = 1r/2r * 2.5;     the literal is then exactly 2.5, a rat\n    \
             x = 1r/2r * 2.5r;    the literal is then exactly 2.5, a rat [2.5f64]"
        ]
    );
    // A generic literal takes the other operand's kind (step L1.26a).
    assert_eq!(x("1 + 1.0f64"), "2.0");
    assert_eq!(x("1r/2r * 2"), "1r");
}
