//! A generic literal compared by `==` or `!=` with a parameter whose carrier is inferred
//! follows the parameter's carrier (DESIGN.md L1.26a): the elaborator writes `x == 3n` as a
//! match on `x` that gives `3.0`, `3r` or `3`. The scope reads that test as the plain `x == 3`
//! where `x` is an integer, and the preimage catalog reads it so where `x` is any integer term.
//! The value compared is found once: a chain of such tests, each comparing the `if` below with
//! a literal, costs what the plain chain costs (repair of LIT-adopt; COMPLEXITY.md row F69). A
//! plain literal follows nothing: `x == 3` makes `x` an int.

use std::sync::Arc;

use zed_kernel::types::Type;
use zed_kernel::{Evaluator, Shared, Term, Value, World, on_stack};
use zed_tests::instances::Rng;
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
/// its readings: from depth 2 its true arm reads every `n`.
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
}

/// The value of the test of the outermost `if` of `ok`'s body at `n = x`, by the interpreter.
fn outer_test_at(body: &Term) -> impl Fn(i64) -> bool {
    fn test_of(t: &Term) -> Term {
        match t {
            Term::Let(n, e, b) => Term::Let(n.clone(), e.clone(), Shared::new(test_of(b))),
            Term::If(c, _, _) => (**c).clone(),
            _ => panic!("no `if` in {t}"),
        }
    }
    let test = test_of(body);
    move |x| {
        let t = Term::Let(
            "n".into(),
            Shared::new(Term::Lit(Value::Int(x))),
            Shared::new(test.clone()),
        );
        match on_stack(|| Evaluator::new(World::new()).run(&t)) {
            Ok(Value::Bool(b)) => b,
            v => panic!("the test at n = {x} gave {v:?}"),
        }
    }
}

/// Checks the two arms of the outermost `if` of `src` against the interpreter on
/// `-WINDOW..=WINDOW`: the true arm holds exactly the `n` where the test holds, and the false
/// arm exactly the others, so neither reads more integers than it reaches.
fn exact_on_window(src: &str) -> Result<(), String> {
    const WINDOW: i64 = 30;
    let (_, body, a) = arms_of(src);
    let holds = outer_test_at(&body);
    let (yes, no) = (&a[0], &a[1]);
    assert!(
        yes.outcome && !no.outcome,
        "{src}: the first two arms are the outer ones"
    );
    let (yes, no) = (yes.scope.get("n"), no.scope.get("n"));
    let (yes, no) = (yes.ints(), no.ints());
    for x in -WINDOW..=WINDOW {
        let h = holds(x);
        if yes.contains(x) != h || no.contains(x) != !h {
            return Err(format!(
                "{src}: at n = {x} the test gives {h}, the arms read [{yes}] and [{no}]"
            ));
        }
    }
    Ok(())
}

/// A sum with an `if` among its operands is summarized: the line `n` is added to each piece
/// of the `if` by one tag ([`Pa::plus`]), so the outer test reads its preimage exactly, `n = 1`
/// alone, at every depth, where before from depth 4 its true arm read every `n` (the sum had
/// no summary, the projection read `n` as every integer, and the linear stage refused the
/// three tied disjunctions; repair of PA-plus-if).
#[test]
fn nested_sums_with_an_if_keep_their_arms() {
    let e = "n + (if n > 0 { n } else { 0 })";
    for d in 1..=64 {
        let src = nested(d, e, "positional n: int");
        let want = [
            "true: n [1..=1]",
            "false: n [..=0, 2..]",
            "true: n [2..]",
            "false: n [..=0]",
        ];
        assert_eq!(readings(&src, &["n"]), want, "{e} at depth {d}");
        exact_on_window(&src).unwrap();
    }
    // A sum of two piecewise summaries is one, cut at the ends of both.
    for d in 1..=32 {
        exact_on_window(&ramps(d)).unwrap();
    }
}

/// A random term `if n > c { a * n + b } else { a' * n + b' }`, or with `<`.
fn random_if(rng: &mut Rng) -> String {
    let mut line = || {
        let (a, b) = (rng.int(-3, 3), rng.int(-9, 9));
        format!("{a} * n + {b}")
    };
    let (yes, no) = (line(), line());
    let op = if rng.below(2) == 0 { ">" } else { "<" };
    format!(
        "(if n {op} {} {{ {yes} }} else {{ {no} }})",
        rng.int(-12, 12)
    )
}

/// Sums and differences of two to five random `if` terms and lines of `n`, compared with a
/// random integer, read exactly on a window by the interpreter: each sum of two summaries is
/// one ([`Pa::plus`]), so the preimage of the comparison is that of the summary.
#[test]
fn random_sums_of_piecewise_terms_are_read_exactly() {
    let mut rng = Rng::new(0x5eed_0f5a_5a5a);
    for round in 0..400 {
        let mut sum = random_if(&mut rng);
        for _ in 0..1 + rng.below(4) {
            let op = if rng.below(2) == 0 { "+" } else { "-" };
            let term = if rng.below(4) == 0 {
                format!("({} * n)", rng.int(-3, 3))
            } else {
                random_if(&mut rng)
            };
            sum = format!("{sum} {op} {term}");
        }
        let cmp = rng.pick(&["==", "!=", "<", ">="]);
        let src = format!(
            "ok(positional n: int) = if {sum} {cmp} {} {{ 1 }} else {{ 2 }};",
            rng.int(-20, 20)
        );
        if let Err(e) = exact_on_window(&src) {
            panic!("round {round}: {e}");
        }
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

fn with_an_if(d: usize) -> String {
    nested(d, "n + (if n > 0 { n } else { 0 })", "positional n: int")
}

/// `if (if n > 0 { n } else { 0 }) + (if n > 1 { n } else { 0 }) + … == 1 { 1 } else { 2 }`,
/// `d` ramps: each sum adds a summary of two pieces to one of up to `d` pieces.
fn ramps(d: usize) -> String {
    let sum: Vec<String> = (0..d)
        .map(|i| format!("(if n > {i} {{ n }} else {{ 0 }})"))
        .collect();
    format!(
        "ok(positional n: int) = if {} == 1 {{ 1 }} else {{ 2 }};",
        sum.join(" + ")
    )
}

/// The arms of `d` nested tests of sums cost `O(d)`: each `if` is summarized once, as a
/// function of `n` affine on each of a few intervals, where the sum `n + n` had no summary
/// and each test fell to the linear stage, `O(d^3)` (16 to 128 levels: 12 ms to 1.53 s). A
/// sum with an `if` adds its line by one tag, and a sum of `d` ramps adds each ramp by a
/// split of the larger summary at two cuts, `O(d log d)` (16 to 128: 2.2 ms to 10.7 ms and
/// 1.3 ms to 7.0 ms, where the projection and the linear stage took 24 ms to 195 ms and 11 ms
/// to 126 ms and read every `n`).
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
        (
            "the arms of nested tests of n + (if n > 0 { n } else { 0 })",
            16,
            with_an_if,
        ),
        ("the arms of a test of a sum of d ramps", 16, ramps),
    ] {
        let (scope, terms) = sizes(n, src);
        scaling::check(what, n, |k| _ = arms(at(&terms, k), &scope));
    }
}
