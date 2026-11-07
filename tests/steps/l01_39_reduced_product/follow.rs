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

/// `ok(positional n: int, …) = if (if (… n …) == 1 { n } else { e }) == 1 { n } else { e }`,
/// `d` deep, with the parameters `ps`.
fn nested(d: usize, e: &str, ps: &str) -> String {
    let inner = (0..d).fold("n".to_string(), |x, _| {
        format!("if ({x}) == 1 {{ n }} else {{ {e} }}")
    });
    format!("ok({ps}) = {inner};")
}

/// Each sum of the chains read below: its parameters and the names whose integers are read.
const SUMS: [(&str, &str, &[&str]); 6] = [
    ("n + n", "positional n: int", &["n"]),
    ("n - n", "positional n: int", &["n"]),
    ("n + n + n", "positional n: int", &["n"]),
    ("2 * n - n", "positional n: int", &["n"]),
    ("n - 3 * n + 4", "positional n: int", &["n"]),
    ("n + m", "positional n: int, positional m: int", &["n", "m"]),
];

/// A sum of one input with itself is a line of it, so each test of the chain reads its
/// preimage exactly: the outer test holds at `n = 1` alone, at every depth. The readings are
/// those of the reading before sums of lines were summarized, at depths 1 to 12 (repair of
/// PRODUCT-nested-chain; COMPLEXITY.md row F70). A sum of two inputs is no summary, and keeps
/// its readings: from depth 2 its true arm reads every `n`; so does that of a sum with an `if`
/// among its operands from depth 4.
#[test]
fn nested_sums_keep_their_arms() {
    for (e, ps, names) in SUMS {
        for d in 1..=12 {
            let want = match (e, d) {
                ("n + m", 1) => ["true: n [1..=1], m [..]", "false: n [..=0, 2..], m [..]"],
                ("n + m", _) => ["true: n [..], m [..]", "false: n [..=0, 2..], m [..]"],
                _ => ["true: n [1..=1]", "false: n [..=0, 2..]"],
            };
            assert_eq!(readings(&nested(d, e, ps), names), want, "{e} at depth {d}");
        }
    }
    // A sum with an `if` among its operands is no summary (`Pa::plus`): from depth 4 the true
    // arm reads every `n`, as before.
    let e = "n + (if n > 0 { n } else { 0 })";
    for d in 1..=12 {
        let outer = if d < 4 { "1..=1" } else { ".." };
        let want = [
            format!("true: n [{outer}]"),
            "false: n [..=0, 2..]".to_owned(),
            "true: n [2..]".to_owned(),
            "false: n [..=0]".to_owned(),
        ];
        let src = nested(d, e, "positional n: int");
        assert_eq!(readings(&src, &["n"]), want, "{e} at depth {d}");
    }
}

fn twice(d: usize) -> String {
    nested(d, "n + n", "positional n: int")
}

fn line(d: usize) -> String {
    nested(d, "n - 3 * n + 4", "positional n: int")
}

fn two(d: usize) -> String {
    nested(d, "n + m", "positional n: int, positional m: int")
}

fn following(d: usize) -> String {
    chain(d, false)
}

/// The arms of `d` nested tests of sums cost `O(d)`: each `if` is summarized once, as a
/// function of `n` affine on each of a few intervals, where the sum `n + n` had no summary
/// and each test fell to the linear stage, `O(d^3)` (16 to 128 levels: 12 ms to 1.53 s).
#[test]
fn nested_sums_of_one_input_scale() {
    for (what, n, src) in [
        (
            "the arms of nested tests of n + n",
            16,
            twice as fn(usize) -> String,
        ),
        (
            "the arms of nested tests of n + n, following",
            16,
            following,
        ),
        ("the arms of nested tests of n - 3 * n + 4", 16, line),
        ("the arms of nested tests of n + m", 16, two),
    ] {
        let (scope, terms) = sizes(n, src);
        scaling::check(what, n, |k| _ = arms(at(&terms, k), &scope));
    }
}
