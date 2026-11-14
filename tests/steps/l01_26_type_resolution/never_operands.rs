//! An operand beside an operand of type `Never` is still checked against what the operator
//! takes (DESIGN.md L1.26, EMPTY-operand-check). The application takes place on no value, so
//! its result stays `Never` (except beside the second operand of `&&` and `||`, which is not
//! read); a value of the other operand that no arrow of the operator takes
//! is reported as it is beside an operand that has values.

use super::{sig, type_errors};

/// A function whose parameter `h` gives `Never`, with names of union types beside it: `u`
/// holds `true` beside `int`, `w` holds `int` and `f64`, and `v` holds a function beside
/// `int`.
pub(super) fn body(e: &str) -> String {
    format!(
        "f(positional h: (int) -> Never, positional n: int, positional b: bool, positional g: \
         (int) -> int, positional s: String) = {{ u = if b {{ n }} else {{ true }}; w = if b \
         {{ n }} else {{ 1.5 }}; v = if b {{ n }} else {{ g }}; {e} }};\n"
    )
}

/// The headline of the rejection of `e`, in which `op` does not take `(x, y)`.
fn refused(op: &str, x: &str, y: &str, e: &str) -> String {
    format!("`{op}` does not take ({x}, {y}): no arrow of `{op}` takes these types. [{e}]")
}

const SIG: &str = "((int) -> Never, int, bool, (int) -> int, String) -> Never";

/// [`SIG`] where the operand of type `Never` is the second of `&&` or `||`, which is not read.
const SIG_BOOL: &str = "((int) -> Never, int, bool, (int) -> int, String) -> bool";

/// Each operator form beside `h(1)`, in either order: the operand it does not take, the type
/// the message shows for it, and an operand it takes.
const FORMS: [(&str, &str, &str, &str); 19] = [
    // The operators of several arrows, beside a union that holds a value none of them takes.
    ("+", "u", "true", "w"),
    ("-", "u", "true", "w"),
    ("*", "u", "true", "w"),
    ("/", "u", "int | true", "1.5f64"),
    ("^", "u", "true", "w"),
    ("<", "v", "(int) -> int", "w"),
    (">", "v", "(int) -> int", "u"),
    ("<=", "v", "(int) -> int", "s"),
    (">=", "v", "(int) -> int", "w"),
    ("<", "g", "(int) -> int", "n"),
    // The operators of one arrow.
    ("div", "true", "true", "n"),
    ("mod", "true", "true", "n"),
    ("++", "1", "1", "s"),
    ("&&", "1", "1", "b"),
    ("||", "1", "1", "b"),
    // The prelude words of several arrows.
    ("min", "u", "true", "w"),
    ("max", "u", "true", "w"),
    // A plain value, beside a union.
    ("+", "true", "true", "1"),
    ("^", "true", "true", "n"),
];

fn applied(op: &str, x: &str, y: &str) -> String {
    match op {
        "min" | "max" => format!("{op}({x}, {y})"),
        _ => format!("{x} {op} {y}"),
    }
}

#[test]
fn an_operand_beside_never_is_checked_against_the_operator() {
    for (op, bad, shown, good) in FORMS {
        for (e, x, y) in [
            (applied(op, "h(1)", bad), "Never", shown),
            (applied(op, bad, "h(1)"), shown, "Never"),
        ] {
            let text = body(&e);
            assert_eq!(type_errors(&text), [refused(op, x, y, &e)], "{e}");
            assert_eq!(sig(&text, "f"), SIG, "{e}");
        }
        // `&&` and `||` read their second operand only where the first does not decide, so
        // `b && h(1)` is `bool` (EMPTY-call-unused, DOCS-TODO 47).
        let second = match op {
            "&&" | "||" => SIG_BOOL,
            _ => SIG,
        };
        for (e, want) in [
            (applied(op, "h(1)", good), SIG),
            (applied(op, good, "h(1)"), second),
        ] {
            let text = body(&e);
            assert_eq!(type_errors(&text), Vec::<String>::new(), "{e}");
            assert_eq!(sig(&text, "f"), want, "{e}");
        }
    }
}

/// The rejection shows the derivation of the operand's type and the arrows of the operator,
/// as it does beside an operand that has values.
#[test]
fn the_rejection_shows_its_derivation() {
    let Err(out) = zedc::run::load(body("h(1) + u").as_bytes()) else {
        panic!("accepted")
    };
    for step in [
        "`+` does not take (Never, true): no arrow of `+` takes these types.",
        "this call of `h` gives Never",
        "`u` is int | true here",
        "this block gives true",
        "`+` takes (int, int) -> int",
        "`+` takes (f64, f64) -> f64",
        "`+` takes (rat, rat) -> rat",
    ] {
        assert!(out.contains(step), "{step}\n{out}");
    }
}

/// The two cases of the item: a call of a function that recurses forever, and a call of a
/// parameter whose result is `Never`.
#[test]
fn the_cases_of_the_item() {
    let spin = "spin(positional n: int) = spin(n);\n";
    let recursion: Vec<String> = type_errors(&format!("{spin}x = spin(1) + 1;\n"));
    assert_eq!(recursion.len(), 1, "{recursion:?}");
    let errors = type_errors(&format!("{spin}x = spin(1) + true;\n"));
    assert_eq!(errors.len(), 2, "{errors:?}");
    assert!(errors.contains(&recursion[0]), "{errors:?}");
    assert!(
        errors.contains(&refused("+", "Never", "true", "spin(1) + true")),
        "{errors:?}"
    );
    let text = "f(positional h: (int) -> Never) = h(1) + true;\n";
    assert_eq!(
        type_errors(text),
        [refused("+", "Never", "true", "h(1) + true")]
    );
    assert_eq!(sig(text, "f"), "((int) -> Never) -> Never");
}

/// Beside a tuple, a comparison checks each component that is no tuple against `<`, and `min`
/// and `max` check each component against their arrows.
#[test]
fn a_tuple_beside_never_is_checked_by_component() {
    for (e, want) in [
        ("h(1) < (n, 1)", vec![]),
        ("max(h(1), (1, 2))", vec![]),
        ("min((n, w), h(1))", vec![]),
        (
            "max(h(1), (1, true))",
            vec![refused("max", "Never", "true", "max(h(1), (1, true))")],
        ),
        (
            "max((1, true), h(1))",
            vec![refused("max", "true", "Never", "max((1, true), h(1))")],
        ),
        (
            "h(1) < (n, g)",
            vec![refused("<", "Never", "(int) -> int", "h(1) < (n, g)")],
        ),
    ] {
        let text = body(e);
        assert_eq!(type_errors(&text), want, "{e}");
        assert_eq!(sig(&text, "f"), SIG, "{e}");
    }
}

/// An untyped parameter beside `Never` takes what the operator takes, as it does beside an
/// operand that has values.
#[test]
fn an_untyped_parameter_beside_never_takes_what_the_operator_takes() {
    for (e, want) in [
        (
            "h(1) + x",
            "((int) -> Never, T) -> Never for T in int | f32 | f64 | rat",
        ),
        (
            "h(1) < x",
            "((int) -> Never, T) -> Never for T in int | f32 | f64 | rat | bool | String",
        ),
        (
            "max(h(1), x)",
            "((int) -> Never, T) -> Never for T in int | f32 | f64 | rat",
        ),
        ("h(1) ++ x", "((int) -> Never, String) -> Never"),
    ] {
        let text = format!("g(positional h: (int) -> Never, positional x) = {e};\n");
        assert_eq!(type_errors(&text), Vec::<String>::new(), "{e}");
        assert_eq!(sig(&text, "g"), want, "{e}");
    }
}

/// Loose atoms pass by an operator, and leave the operand no value: the other operand is
/// still checked, and the atoms still come out.
#[test]
fn an_operand_beside_loose_atoms_is_checked() {
    let a = "f(positional n: int) = { a = if n > 0 { #a } else { #b }; u = if n > 0 { n } else \
             { true }; ";
    assert_eq!(
        type_errors(&format!("{a}a + u }};\n")),
        // The operand `a` is shown as `Never`, the type it has once its atoms pass by.
        [refused("+", "Never", "true", "a + u")]
    );
    let text = format!("{a}a + n }};\n");
    assert_eq!(type_errors(&text), Vec::<String>::new());
    assert_eq!(sig(&text, "f"), "(int) -> #a | #b");
}

/// The examples of DOCS-TODO 50 that are accepted, with their signatures, and those rejected.
#[test]
fn the_examples_of_the_guide() {
    for (text, name, want) in [
        (
            "f4(positional h: (int) -> Never, positional b: bool) = { w = if b { 1 } else \
             { 1.5f64 }; h(1) + w };\n",
            "f4",
            "((int) -> Never, bool) -> Never",
        ),
        (
            "f6(positional h: (int) -> Never, positional x) = h(1) + x;\n",
            "f6",
            "((int) -> Never, T) -> Never for T in int | f32 | f64 | rat",
        ),
        (
            "f7(positional n: int) = { a = if n > 0 { #a } else { #b }; a + n };\n",
            "f7",
            "(int) -> #a | #b",
        ),
    ] {
        assert_eq!(type_errors(text), Vec::<String>::new(), "{text}");
        assert_eq!(sig(text, name), want, "{text}");
    }
    for (text, want) in [
        (
            "f3(positional h: (int) -> Never, positional b: bool) = { u = if b { 1 } else \
             { true }; h(1) + u };\n",
            vec![refused("+", "Never", "true", "h(1) + u")],
        ),
        (
            "f5(positional h: (int) -> Never, positional g: (int) -> int) = h(1) < (1, g);\n",
            vec![refused("<", "Never", "(int) -> int", "h(1) < (1, g)")],
        ),
        (
            "f6(positional h: (int) -> Never, positional x) = h(1) + x;\nr(positional h: (int) -> Never) = f6(h, true);\n",
            vec![refused("f6", "(int) -> Never", "true", "f6(h, true)")],
        ),
    ] {
        assert_eq!(type_errors(text), want, "{text}");
    }
}

/// A chain of `n` additions beside one operand of type `Never`, each other operand a union of
/// `int` and `f64`, ending in `true`.
pub(super) fn chain_beside_never(n: usize) -> String {
    let terms: String = (0..n).map(|_| " + w").collect();
    body(&format!("h(1){terms} + true"))
}

/// `t0 = (n, w)` and `t{i+1} = (t{i}, t{i})`, the type of `t{d}` having `2^d` paths to `t0`
/// and `d + 1` rows, and `apply(t)` applied to `t{d}` and `h(1)`, of type `Never`.
pub(super) fn never_beside_shared_tuples(d: usize, apply: fn(&str) -> String) -> String {
    let mut e = String::from("t0 = (n, w); ");
    e.extend((0..d).map(|i| format!("t{} = (t{i}, t{i}); ", i + 1)));
    body(&format!("{e}{}", apply(&format!("t{d}"))))
}

/// `h(1) < t`.
pub(super) fn below(t: &str) -> String {
    format!("h(1) < {t}")
}

/// `max(h(1), t)`.
pub(super) fn max_of(t: &str) -> String {
    format!("max(h(1), {t})")
}

#[test]
fn a_chain_beside_never_is_one_error() {
    // A small instance of the benchmark `bench::never_operands::a_chain_beside_never_scales`.
    let errors = type_errors(&chain_beside_never(3));
    assert_eq!(errors.len(), 1, "{errors:?}");
}

#[test]
fn never_beside_shared_tuples_is_accepted() {
    // A small instance of the benchmarks
    // `bench::never_operands::a_comparison_of_never_with_shared_tuples_scales` and
    // `bench::never_operands::max_of_never_and_shared_tuples_scales`.
    for apply in [below as fn(&str) -> String, max_of] {
        let text = never_beside_shared_tuples(3, apply);
        assert_eq!(type_errors(&text), Vec::<String>::new(), "{text}");
    }
}
