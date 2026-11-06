//! A generic literal compared by `==` or `!=` with a parameter whose carrier is inferred
//! follows the parameter's carrier (DESIGN.md L1.26a): the elaborator writes `x == 3n` as a
//! match on `x` that gives `3.0`, `3r` or `3`. The scope reads that test as the plain `x == 3`
//! where `x` is an integer, and the preimage catalog reads it so where `x` is any integer term.
//! The value compared is found once: a chain of such tests, each comparing the `if` below with
//! a literal, costs what the plain chain costs (repair of LIT-adopt; COMPLEXITY.md row F69). A
//! plain literal follows nothing: `x == 3` makes `x` an int.

use std::sync::Arc;

use zed_kernel::Term;
use zed_kernel::types::Type;
use zed_tests::scaling;
use zedc::store::product::{Product, Scope, arms};

use super::{arm, arms_of, ints};
use zed_tests::step_helpers::l01_25_preimage_catalog::function;

/// The test of each arm, the outcome, and the integers each named parameter holds there.
fn readings(src: &str, names: &[&str]) -> Vec<String> {
    let (_, _, a) = arms_of(src);
    a.iter()
        .map(|a| {
            let held: Vec<String> = names
                .iter()
                .map(|n| format!("{n} {}", a.scope.get(n).ints()))
                .collect();
            format!("{}: {}", a.outcome, held.join(", "))
        })
        .collect()
}

#[test]
fn a_retry_counter_compared_with_a_literal_is_narrowed_to_it() {
    // `tries` is inferred: the function takes any number, and `3n` follows its carrier.
    let src = "ok(positional tries) = if tries == 3n { 10 } else { 20 };";
    let (_, body, _) = arms_of(src);
    assert!(body.to_string().contains("(is f64) -> 3.0"), "{body}");
    assert_eq!(
        readings(src, &["tries"]),
        ["true: tries [3..=3]", "false: tries [..=2, 4..]"]
    );
    // `!=` on either side.
    let src = "ok(positional slot) = if slot != 3n && 4n != slot { 10 } else { 20 };";
    assert_eq!(
        readings(src, &["slot"]),
        ["true: slot [..=2, 5..]", "false: slot [3..=4]"]
    );
}

#[test]
fn a_difference_compared_with_a_literal_is_narrowed_by_its_preimage() {
    // The value compared is a term, not a name: the preimage catalog reads the match as the
    // literal itself, and the linear relation is the plain test's.
    let src = "ok(positional a, positional b) = if a - b == 3n && a == 5n { 10 } else { 20 };";
    assert_eq!(
        readings(src, &["a", "b"]),
        ["true: a [5..=5], b [2..=2]", "false: a [..], b [..]"]
    );
    let src = "ok(positional debt) = if -debt == 3n { 10 } else { 20 };";
    assert_eq!(
        readings(src, &["debt"]),
        ["true: debt [-3..=-3]", "false: debt [..=-4, -2..]"]
    );
}

#[test]
fn at_a_float_the_test_is_not_read_as_an_integer_equality() {
    // At an `f64` the literal is `3.0`: the true arm is reached, at `3.0`, though no integer
    // is in it.
    let (ps, body) = function("ok(positional level) = if level == 3n { 10 } else { 20 };");
    let floats = Scope::new(
        ps.iter()
            .map(|p| (p.clone(), Product::of_type(Type::f64()))),
    );
    let a = arms(&body, &floats);
    let then = arm(&a, "3.0", true);
    assert!(then.reachable(), "{}", then.scope);
    assert!(arm(&a, "3.0", false).reachable());
}

/// `ok(positional n) = if (if (… n …) == 1n { n } else { n + n }) == 1n { n } else { n + n }`,
/// `d` deep; with `n: int` declared when `plain`, else `n` inferred, so each `1n` follows.
fn chain(d: usize, plain: bool) -> String {
    let inner = (0..d).fold("n".to_string(), |x, _| {
        format!("if ({x}) == 1n {{ n }} else {{ n + n }}")
    });
    let ty = if plain { ": int" } else { "" };
    format!("ok(positional n{ty}) = {inner};")
}

#[test]
fn a_chain_of_following_comparisons_costs_what_the_plain_chain_costs() {
    let d = 48;
    let (ps, follow) = function(&chain(d, false));
    assert!(follow.to_string().contains("(is f64) -> 1.0"));
    let (_, plain) = function(&chain(d, true));
    assert!(!plain.to_string().contains("is f64"));
    let scope = ints(&ps);
    let (a, b) = (arms(&follow, &scope), arms(&plain, &scope));
    assert_eq!(a.len(), b.len());
    for (x, y) in a.iter().zip(&b) {
        assert_eq!(x.scope.get("n").ints(), y.scope.get("n").ints());
    }
    // Finding each compared value again for each test around it cost 2^d; finding it once
    // per test, d times the plain chain. The terms differ by the match of each level only.
    scaling::compare(
        "the arms of a chain of 48 following comparisons against the plain chain",
        "the value compared is found once, as in the plain chain",
        3.0,
        || _ = arms(&plain, &scope),
        || _ = arms(&follow, &scope),
    );
}

/// The terms of `ok` for sizes `n` and `8 n`, built before timing.
fn sizes(n: usize, src: fn(usize) -> String) -> (Scope, [(usize, Arc<Term>); 2]) {
    let (ps, small) = function(&src(n));
    let (_, large) = function(&src(scaling::FACTOR * n));
    (
        ints(&ps),
        [(n, Arc::new(small)), (scaling::FACTOR * n, Arc::new(large))],
    )
}

fn at(terms: &[(usize, Arc<Term>); 2], k: usize) -> &Term {
    &terms.iter().find(|(n, _)| *n == k).expect("a built size").1
}

/// `if slot != 0 && slot != 1 && … { 10 } else { 20 }`, `k` tests.
fn excluded(k: usize) -> String {
    let tests: Vec<String> = (0..k).map(|i| format!("slot != {i}n")).collect();
    format!(
        "ok(positional slot) = if {} {{ 10 }} else {{ 20 }};",
        tests.join(" && ")
    )
}

/// `{ b0 = a - b == 0; …; if b(k-1) { 10 } else { 20 } }`: each binding a following test of
/// a difference, which the scope finds the value of.
fn bound(k: usize) -> String {
    let lets: String = (0..k).map(|i| format!("b{i} = a - b == {i}n; ")).collect();
    format!(
        "ok(positional a, positional b) = {{ {lets}if b{} {{ 10 }} else {{ 20 }} }};",
        k - 1
    )
}

/// `if a - b != 0 && a - b != 1 && … { 10 } else { 20 }`: following tests of a difference,
/// each read by the preimage catalog.
fn differences(k: usize) -> String {
    let tests: Vec<String> = (0..k).map(|i| format!("a - b != {i}n")).collect();
    format!(
        "ok(positional a, positional b) = if {} {{ 10 }} else {{ 20 }};",
        tests.join(" && ")
    )
}

#[test]
fn following_tests_scale() {
    for (what, n, src) in [
        (
            "a conjunction of following tests of a name",
            32,
            excluded as fn(usize) -> String,
        ),
        ("a chain of bindings of following tests", 64, bound),
        (
            "a conjunction of following tests of a difference",
            16,
            differences,
        ),
    ] {
        let (scope, terms) = sizes(n, src);
        scaling::check(what, n, |k| _ = arms(at(&terms, k), &scope));
    }
}
