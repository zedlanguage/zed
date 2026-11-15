//! An infix call means the written-out call: the same value, the same overload, the same
//! errors. Each case is checked both ways and the two are compared; the value or the error is
//! also written out, so a fault that broke both ways alike is seen.

use zed_tests::step_helpers::l01_10_lambdas_types_else_tuples::sx;
use zed_tests::step_helpers::l01_16_elaboration::value;

use crate::{front, unplaced};

/// The functions the units below call.
const FNS: &str = "plus(positional a: int, positional b: int) = a + b;\n\
                   minus(positional a: int, positional b: int) = a - b;\n\
                   scale(positional p: int, positional k: int) = p * k;\n";

/// The unit `FNS` then `x = <e>;`.
fn unit(e: &str) -> String {
    format!("{FNS}x = {e};\n")
}

/// The value of `x = <infix>;` is `want`, and so is that of `x = <written>;`.
fn agrees(infix: &str, written: &str, want: &str) {
    assert_eq!(value(&unit(infix), "x"), want, "{infix}");
    assert_eq!(value(&unit(written), "x"), want, "{written}");
}

#[test]
fn an_infix_call_is_the_call() {
    agrees("3 ~plus~ 4", "plus(3, 4)", "7");
    agrees("5 ~scale~ 2", "scale(5, 2)", "10");
}

#[test]
fn a_chain_associates_to_the_left() {
    agrees("1 ~minus~ 2 ~minus~ 3", "minus(minus(1, 2), 3)", "-4");
    agrees("1 ~minus~ (2 ~minus~ 3)", "minus(1, minus(2, 3))", "2");
    agrees("2 ~plus~ 3 ~scale~ 4", "scale(plus(2, 3), 4)", "20");
}

/// Tier 6 lies between Range (tier 5) and Additive (tier 7): looser than `+`, `*`, `^` and
/// prefix operators, tighter than ranges, comparisons, `&&`, `||` and `else`.
#[test]
fn the_tier_between_range_and_additive() {
    agrees("3 ~plus~ 4 == 7", "plus(3, 4) == 7", "true");
    agrees("7 == 3 ~plus~ 4", "7 == plus(3, 4)", "true");
    agrees("3 ~plus~ 4 < 3 ~plus~ 5", "plus(3, 4) < plus(3, 5)", "true");
    agrees("(3 ~plus~ 4) * 2", "plus(3, 4) * 2", "14");
    agrees("3 ~plus~ (4 * 2)", "plus(3, 4 * 2)", "11");
    agrees("-(3 ~plus~ 4)", "-plus(3, 4)", "-7");
    agrees("(2 ~plus~ 1)^2", "plus(2, 1)^2", "9");
    assert_eq!(sx("0..<a ~f~ b"), "(..< 0 (call f a b))");
    assert_eq!(sx("a ~f~ b..<c"), "(..< (call f a b) c)");
    assert_eq!(sx("a ~f~ b == q"), "(== (call f a b) q)");
    assert_eq!(sx("a ~f~ b >< g"), "(>< (call f a b) g)");
    assert_eq!(sx("a ~f~ b else c"), "(else (call f a b) c)");
    assert_eq!(
        sx("x ~f~ y else c ~g~ d"),
        "(else (call f x y) (call g c d))"
    );
    assert_eq!(sx("a ~f~ b with { c = 1 }"), "(with (call f a b) (= c 1))");
    assert_eq!(sx("p ~f~ q && r"), "(&& (call f p q) r)");
}

/// The operands are postfix forms, or anything in parentheses.
#[test]
fn operands() {
    assert_eq!(sx("(a + b) ~f~ c"), "(call f (+ a b) c)");
    assert_eq!(sx("p.pos ~plus~ v.dir"), "(call plus (. p pos) (. v dir))");
    assert_eq!(sx("g(a)[0] ~f~ h(b)"), sx("f(g(a)[0], h(b))"));
    assert_eq!(sx("(x -> x) ~f~ b"), sx("f(x -> x, b)"));
    assert_eq!(sx("a ~f~ (b == c)"), sx("f(a, b == c)"));
}

/// A prefix `-` or `!` at the start of the right operand has one reading (orchestrator
/// decision, DESIGN a17fec3): `p ~scale~ -1` is `scale(p, -1)`.
#[test]
fn a_prefix_operator_opens_the_right_operand() {
    agrees("5 ~scale~ -1", "scale(5, -1)", "-5");
    agrees("5 ~scale~ -(-2)", "scale(5, -(-2))", "10");
    assert_eq!(sx("p ~f~ !q"), sx("f(p, !q)"));
    assert_eq!(sx("p ~f~ -(-1)"), sx("f(p, -(-1))"));
}

/// The call's own rules apply unchanged: the parameter count, the names, the types, and the
/// overloads, which this version of zedc rejects for both forms alike (it does not yet choose
/// among definitions that share a name).
#[test]
fn the_calls_rules() {
    let overloads = "f(positional n: int, positional k: int) = n + k;\n\
                     f(positional b: bool, positional k: int) = k;\n";
    for (infix, written) in [("2 ~f~ 3", "f(2, 3)"), ("true ~f~ 3", "f(true, 3)")] {
        let i = unplaced(&format!("{overloads}x = {infix};\n"));
        assert_eq!(
            i,
            unplaced(&format!("{overloads}x = {written};\n")),
            "{infix}"
        );
        assert!(
            i.contains("does not yet choose among definitions"),
            "{infix}: {i}"
        );
    }
    let errs = "neg(positional a: int) = -a;\n\
                f3(positional a: int, positional b: int, positional c: int) = a + b + c;\n\
                named(positional a: int, b: int) = a + b;\n";
    for (infix, written) in [
        ("1 ~neg~ 2", "neg(1, 2)"),
        ("1 ~f3~ 2", "f3(1, 2)"),
        ("1 ~named~ 2", "named(1, 2)"),
        ("1 ~nothere~ 2", "nothere(1, 2)"),
        ("true ~plus~ 2", "plus(true, 2)"),
    ] {
        let (i, w) = (
            format!("{FNS}{errs}x = {infix};\n"),
            format!("{FNS}{errs}x = {written};\n"),
        );
        assert_ne!(unplaced(&i), "ok", "{infix}");
        assert_eq!(unplaced(&i), unplaced(&w), "{infix}");
    }
    // The argument too many of the outer call of a chain is its right operand, `3`, at 7:22.
    let chain = format!("{FNS}{errs}x = 1 ~plus~ 2 ~neg~ 3;\n");
    let got = front(&chain);
    assert!(
        got.starts_with("7:22 this argument is one more than `neg` takes"),
        "{got}"
    );
}

/// The overloads and recursion of `l01_29_diagnostics/overload_cycles.rs`, with the inner call
/// written infix: the same verdicts.
#[test]
fn agrees_with_the_overload_cycle_cases() {
    for (infix, written) in [
        (
            "f(positional n: int, positional k: int) = n;\n\
             f(positional s: bool, positional k: int) = 1 ~f~ k;\nmain = f(true, 2);\n",
            "f(positional n: int, positional k: int) = n;\n\
             f(positional s: bool, positional k: int) = f(1, k);\nmain = f(true, 2);\n",
        ),
        (
            "f(positional n: int, positional k: int) = n ~f~ k;\n\
             f(positional s: bool, positional k: int) = 0;\nmain = 1;\n",
            "f(positional n: int, positional k: int) = f(n, k);\n\
             f(positional s: bool, positional k: int) = 0;\nmain = 1;\n",
        ),
    ] {
        assert_eq!(unplaced(infix), unplaced(written), "{infix}");
    }
}

/// An operator cannot be defined: no `operator +` and no `(+)` declaration (Q36).
#[test]
fn no_operator_definitions() {
    for decl in [
        "operator +(a: int, b: int) = a;\n",
        "(+)(a: int, b: int) = a;\n",
    ] {
        assert!(front(decl).contains("Syntax error"), "{decl}");
    }
}
