//! A test of a name bound by a `let` narrows the inputs the bound value is computed from
//! (item PA-let-unsummarized-narrow). A value with a summary over one input is read through it
//! (`abs`, a `min` or `max` of two terms of one input, now among them); any other integer
//! value, such as `x div 2`, `x mod 4`, or one over two inputs, is read backward through its
//! term from the integers the test leaves the name, as a test reads a function it calls, and
//! the names that term reads are read the same way in turn (`Scope::through_terms`).
//!
//! Each body is checked against the interpreter at every point of a grid of `x` and `y`
//! (`random::trace`): every arm a run reaches holds the run's values. The narrowed ranges are
//! pinned.

use std::collections::BTreeMap;
use std::sync::Arc;

use zed_kernel::{Prim, Shared, Term, Value};
use zed_tests::scaling;
use zedc::store::product::Arm;

use super::random::trace;
use super::{arm, ints};

fn var(n: &str) -> Term {
    Term::Var(n.into())
}

fn int(n: i64) -> Term {
    Term::Lit(Value::Int(n))
}

fn prim(p: Prim, args: Vec<Term>) -> Term {
    Term::Prim(p, args)
}

fn if_(c: Term, a: Term, b: Term) -> Term {
    Term::If(Shared::new(c), Shared::new(a), Shared::new(b))
}

fn let_(x: &str, e: Term, b: Term) -> Term {
    Term::Let(x.into(), Shared::new(e), Shared::new(b))
}

/// `if <test> { 1 } else { 2 }`.
fn test(t: Term) -> Term {
    if_(t, int(1), int(2))
}

/// The arms of `body` over the integers `x` and `y`, after checking that every run over the
/// grid reaches only arms that hold it.
fn checked_arms(body: &Term) -> Vec<Arm> {
    let xy: Vec<Arc<str>> = vec!["x".into(), "y".into()];
    let arms = zedc::store::product::arms(body, &ints(&xy));
    let holds = |i: usize, v: &BTreeMap<Arc<str>, Value>| arms[i].scope.contains(v);
    let t = trace(body, &xy, &arms, &holds).unwrap_or_else(|e| panic!("{body}: {e}"));
    assert!(t.checked > 0, "{body}: no run checked");
    arms
}

/// The integers of `name` in the arm of the test printed as `guard` taken by `outcome`.
fn ints_of(arms: &[Arm], guard: &str, outcome: bool, name: &str) -> String {
    arm(arms, guard, outcome).scope.get(name).ints().to_string()
}

#[test]
fn a_test_of_an_abs_narrows_its_input() {
    // `z = abs(x); if z > 5 { 1 } else { 2 }`: `abs` has a summary, a choice on `x >= 0`.
    let body = let_(
        "z",
        prim(Prim::Abs, vec![var("x")]),
        test(prim(Prim::Gt, vec![var("z"), int(5)])),
    );
    let a = checked_arms(&body);
    assert_eq!(ints_of(&a, "(z > 5)", true, "x"), "[..=-6, 6..]");
    assert_eq!(ints_of(&a, "(z > 5)", false, "x"), "[-5..=5]");
    assert_eq!(ints_of(&a, "(z > 5)", true, "z"), "[6..]");
    assert_eq!(ints_of(&a, "(z > 5)", false, "z"), "[0..=5]");
    // The summary gives these: no binding is read through its term.
    assert_eq!(term_reads(&body).1, 0);
}

#[test]
fn a_test_of_a_div_by_a_constant_narrows_its_input() {
    // `z = x div 2; if z > 5 { 1 } else { 2 }`: no summary, read through the term.
    let body = let_(
        "z",
        prim(Prim::IntDiv, vec![var("x"), int(2)]),
        test(prim(Prim::Gt, vec![var("z"), int(5)])),
    );
    let a = checked_arms(&body);
    assert_eq!(ints_of(&a, "(z > 5)", true, "x"), "[12..]");
    assert_eq!(ints_of(&a, "(z > 5)", false, "x"), "[..=11]");
    // Each arm reads `z` through its term once.
    assert_eq!(term_reads(&body).1, 2);
}

#[test]
fn a_test_of_a_mod_by_a_constant_narrows_its_input() {
    // `if x >= 0 && x <= 9 { z = x mod 4; if z <= 1 { 1 } else { 2 } } else { 3 }`.
    let body = if_(
        prim(
            Prim::And,
            vec![
                prim(Prim::Ge, vec![var("x"), int(0)]),
                prim(Prim::Le, vec![var("x"), int(9)]),
            ],
        ),
        let_(
            "z",
            prim(Prim::Mod, vec![var("x"), int(4)]),
            test(prim(Prim::Le, vec![var("z"), int(1)])),
        ),
        int(3),
    );
    let a = checked_arms(&body);
    assert_eq!(ints_of(&a, "(z <= 1)", true, "x"), "[0..=1, 4..=5, 8..=9]");
    assert_eq!(ints_of(&a, "(z <= 1)", false, "x"), "[2..=3, 6..=7]");
    assert_eq!(term_reads(&body).1, 2);
}

#[test]
fn a_test_of_a_min_or_max_of_two_terms_of_one_input_narrows_it() {
    // `z = min(x + 1, 10 - x); if z >= 3 { 1 } else { 2 }`: a summary over `x`.
    let body = let_(
        "z",
        prim(
            Prim::Min,
            vec![
                prim(Prim::Add, vec![var("x"), int(1)]),
                prim(Prim::Sub, vec![int(10), var("x")]),
            ],
        ),
        test(prim(Prim::Ge, vec![var("z"), int(3)])),
    );
    let a = checked_arms(&body);
    assert_eq!(ints_of(&a, "(z >= 3)", true, "x"), "[2..=7]");
    assert_eq!(ints_of(&a, "(z >= 3)", false, "x"), "[..=1, 8..]");
    // The summary gives these: no binding is read through its term.
    assert_eq!(term_reads(&body).1, 0);
    // `z = max(2 * x, x + 3); if z < 5 { 1 } else { 2 }`.
    let body = let_(
        "z",
        prim(
            Prim::Max,
            vec![
                prim(Prim::Mul, vec![int(2), var("x")]),
                prim(Prim::Add, vec![var("x"), int(3)]),
            ],
        ),
        test(prim(Prim::Lt, vec![var("z"), int(5)])),
    );
    let a = checked_arms(&body);
    assert_eq!(ints_of(&a, "(z < 5)", true, "x"), "[..=1]");
    assert_eq!(ints_of(&a, "(z < 5)", false, "x"), "[2..]");
    assert_eq!(term_reads(&body).1, 0);
}

#[test]
fn a_test_of_a_value_over_two_inputs_narrows_both() {
    // `z = max(x, y); if z < 0 { 1 } else { 2 }`: no summary over one input, read through the
    // term; the true arm holds both inputs negative.
    let body = let_(
        "z",
        prim(Prim::Max, vec![var("x"), var("y")]),
        test(prim(Prim::Lt, vec![var("z"), int(0)])),
    );
    let a = checked_arms(&body);
    assert_eq!(ints_of(&a, "(z < 0)", true, "x"), "[..=-1]");
    assert_eq!(ints_of(&a, "(z < 0)", true, "y"), "[..=-1]");
    assert_eq!(ints_of(&a, "(z < 0)", false, "x"), "[..]");
    // `z = abs(x) + y; if z <= 2 { 1 } else { 2 }` under `y >= 0`: no summary.
    let body = if_(
        prim(Prim::Ge, vec![var("y"), int(0)]),
        let_(
            "z",
            prim(Prim::Add, vec![prim(Prim::Abs, vec![var("x")]), var("y")]),
            test(prim(Prim::Le, vec![var("z"), int(2)])),
        ),
        int(3),
    );
    let a = checked_arms(&body);
    assert_eq!(ints_of(&a, "(z <= 2)", true, "x"), "[-2..=2]");
    // `y <= 2` needs `abs(x) >= 0`: the summary of `abs(x)` over all of `x` must keep the
    // bound 0 at its root, which a line added to a clamp did not (`Pa::by_sign`).
    assert_eq!(ints_of(&a, "(z <= 2)", true, "y"), "[0..=2]");
}

#[test]
fn a_test_of_the_end_of_a_chain_narrows_every_link() {
    // `z1 = x div 2; z2 = z1 + 1; z3 = abs(z2 - 4); if z3 <= 1 { 1 } else { 2 }`: `z3` and
    // `z2` have summaries over `z1`, which has none and is read through its term.
    let body = let_(
        "z1",
        prim(Prim::IntDiv, vec![var("x"), int(2)]),
        let_(
            "z2",
            prim(Prim::Add, vec![var("z1"), int(1)]),
            let_(
                "z3",
                prim(Prim::Abs, vec![prim(Prim::Sub, vec![var("z2"), int(4)])]),
                test(prim(Prim::Le, vec![var("z3"), int(1)])),
            ),
        ),
    );
    let a = checked_arms(&body);
    assert_eq!(ints_of(&a, "(z3 <= 1)", true, "x"), "[4..=9]");
    assert_eq!(ints_of(&a, "(z3 <= 1)", true, "z1"), "[2..=4]");
    // `z1 = x div 2; z2 = z1 div 3; if z2 == 1 { 1 } else { 2 }`: two links read through their
    // terms, `z2` first.
    let body = let_(
        "z1",
        prim(Prim::IntDiv, vec![var("x"), int(2)]),
        let_(
            "z2",
            prim(Prim::IntDiv, vec![var("z1"), int(3)]),
            test(prim(Prim::Eq, vec![var("z2"), int(1)])),
        ),
    );
    let a = checked_arms(&body);
    assert_eq!(ints_of(&a, "(z2 == 1)", true, "x"), "[6..=11]");
    assert_eq!(ints_of(&a, "(z2 == 1)", true, "z1"), "[3..=5]");
}

/// `z1 = x div 2; z2 = z1 div 2; ...; zn = z(n-1) div 2` around `t`.
fn halvings(n: usize, mut t: Term) -> Term {
    for j in (1..=n).rev() {
        let before = if j == 1 {
            var("x")
        } else {
            var(&format!("z{}", j - 1))
        };
        t = let_(
            &format!("z{j}"),
            prim(Prim::IntDiv, vec![before, int(2)]),
            t,
        );
    }
    t
}

/// [`halvings`] around the tests `zj <= 1000 + c` for each link `j` from 1 to `n` and `c` from
/// `k - 1` down to 0, each in the `then` of the one before, `else { 2 }`, the last `{ 1 }`. A
/// test of `zj` narrows `zj`, and through its term would narrow `z(j-1)` to `..=2001 + 2c`,
/// which the tests of `z(j-1)` already gave (`..=1000`), so its `then` reads one term; its
/// `else` asks `zj >= 1001 + c` and so `z(j-1) >= 2002`, no value, which ends the reads after
/// one, or for `z1` gives `x` its range: each test reads one term in each arm.
fn nested_halvings(n: usize, k: usize) -> Term {
    let mut t = int(1);
    for j in (1..=n).rev() {
        for c in 0..k {
            let z = var(&format!("z{j}"));
            t = if_(prim(Prim::Le, vec![z, int(1000 + c as i64)]), t, int(2));
        }
    }
    halvings(n, t)
}

/// [`halvings`] around the tests `zj > c` for each link `j` from `n` down to 1 and `c` in
/// `0..k`, each in the `else` of the one before: `if zn > 0 { 1 } else if zn > 1 { 1 } ...
/// else if z1 > k - 1 { 1 } else { 2 }`.
fn else_halvings(n: usize, k: usize) -> Term {
    let mut t = int(2);
    for j in 1..=n {
        for c in (0..k).rev() {
            let z = var(&format!("z{j}"));
            t = if_(prim(Prim::Gt, vec![z, int(c as i64)]), int(1), t);
        }
    }
    halvings(n, t)
}

/// The arms of `t` over `x` and the bindings read through their terms
/// (`counts::term_reads`), on a fresh thread.
fn term_reads(t: &Term) -> (Vec<Arm>, u64) {
    let x = ints(&["x".into()]);
    scaling::on_a_thread(1 << 26, || {
        let before = zedc::store::preimage::counts::term_reads();
        let a = zedc::store::product::arms(t, &x);
        (a, zedc::store::preimage::counts::term_reads() - before)
    })
}

/// A test of a link of a chain of bindings with no summary reads only the links whose
/// integers it changes, each once: in [`nested_halvings`] each test changes one link in each
/// arm, so a chain of n links each read by k tests makes 2 n k term reads and costs O(n k).
#[test]
fn reading_chains_of_terms_scales() {
    let (a, _) = term_reads(&nested_halvings(3, 2));
    // `z1 <= 1000` gives `x <= 2001`; the tests of `z2` and `z3` leave `z1` and `z2` as they were.
    assert_eq!(ints_of(&a, "(z1 <= 1000)", true, "x"), "[..=2001]");
    assert_eq!(ints_of(&a, "(z2 <= 1000)", true, "z1"), "[..=1000]");
    assert_eq!(ints_of(&a, "(z3 <= 1000)", true, "z3"), "[..=1000]");
    assert!(!arm(&a, "(z3 <= 1001)", false).reachable());
    for n in [3, 32, 256] {
        assert_eq!(
            term_reads(&nested_halvings(n, 2)).1,
            4 * n as u64,
            "{n} links"
        );
    }
    let chains = scaling::inputs(32, |n| nested_halvings(n, 2));
    let x = ints(&["x".into()]);
    scaling::check_order(
        "a chain of n bindings `zj = z(j-1) div 2`, each read by 2 nested tests",
        32,
        1,
        |n| {
            zedc::store::product::arms(&chains[&n], &x);
        },
    );
}

/// A test that narrows every link of a chain reads every link once in each arm. In the `else`
/// chain of [`else_halvings`] at k = 2, the scope of the tests of `zj` holds `z(j+1) <= 0`, so
/// `zj <= 1` and each link below and `x` the range that gives; `zj > 0` splits `zj` into `1`
/// and `..=0`, which changes `zj`, `z(j-1)`, …, `z1` and `x` in each arm, `j` term reads an
/// arm, and `zj > 1` changes nothing. So the reads number `2 (1 + … + n) = n (n + 1)`, and
/// the arms differ from the scopes they are tested in by `Θ(n²)` names in all: the output is
/// quadratic, and the work, of order `n²`, is checked at that order. A test that reads each
/// link through its term only when it changes cannot do better, since the narrowed range of
/// each link is in the output.
#[test]
fn a_test_that_narrows_every_link_reads_every_link_once() {
    let (a, _) = term_reads(&else_halvings(3, 2));
    assert_eq!(ints_of(&a, "(z3 > 0)", true, "x"), "[8..]");
    assert_eq!(ints_of(&a, "(z2 > 0)", true, "z1"), "[2..=3]");
    assert_eq!(ints_of(&a, "(z2 > 0)", false, "x"), "[..=3]");
    assert_eq!(ints_of(&a, "(z1 > 1)", false, "x"), "[..=1]");
    for n in [3, 8, 32, 64] {
        let n64 = n as u64;
        assert_eq!(
            term_reads(&else_halvings(n, 2)).1,
            n64 * (n64 + 1),
            "{n} links"
        );
    }
    let chains = scaling::inputs(16, |n| else_halvings(n, 2));
    let x = ints(&["x".into()]);
    scaling::check_order(
        "a chain of n bindings `zj = z(j-1) div 2` under an `else` chain of 2 tests each",
        16,
        2,
        |n| {
            zedc::store::product::arms(&chains[&n], &x);
        },
    );
}
