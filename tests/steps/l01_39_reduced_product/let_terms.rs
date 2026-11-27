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

/// A congruence test on a name bound by a term with no summary narrows the term's inputs:
/// the shortcut of `Scope::atom_names` for `z mod c == r` on one name must not stop at `z`'s
/// own class (commit 68b13f979, proofs-in-comments audit).
#[test]
fn a_congruence_test_of_a_div_by_a_constant_narrows_its_input() {
    // `if x >= 0 && x <= 9 { z = x div 2; if z mod 2 == 1 { 1 } else { 2 } } else { 3 }`.
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
            prim(Prim::IntDiv, vec![var("x"), int(2)]),
            test(prim(
                Prim::Eq,
                vec![prim(Prim::Mod, vec![var("z"), int(2)]), int(1)],
            )),
        ),
        int(3),
    );
    let a = checked_arms(&body);
    assert_eq!(ints_of(&a, "((z mod 2) == 1)", true, "x"), "[2..=3, 6..=7]");
    assert_eq!(
        ints_of(&a, "((z mod 2) == 1)", false, "x"),
        "[0..=1, 4..=5, 8..=9]"
    );
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

/// The chain of [`nested_halvings`] that the benchmark `reading_chains_of_terms_scales` times:
/// `z1 <= 1000` gives `x <= 2001`, the tests of `z2` and `z3` leave `z1` and `z2` as they were,
/// and a chain of `n` links each read by 2 tests makes `4 n` term reads.
#[test]
fn a_chain_of_terms_read_by_nested_tests_reads_each_link_twice() {
    let (a, _) = term_reads(&nested_halvings(3, 2));
    assert_eq!(ints_of(&a, "(z1 <= 1000)", true, "x"), "[..=2001]");
    assert_eq!(ints_of(&a, "(z2 <= 1000)", true, "z1"), "[..=1000]");
    assert_eq!(ints_of(&a, "(z3 <= 1000)", true, "z3"), "[..=1000]");
    assert!(!arm(&a, "(z3 <= 1001)", false).reachable());
    for n in [3, 32] {
        assert_eq!(
            term_reads(&nested_halvings(n, 2)).1,
            4 * n as u64,
            "{n} links"
        );
    }
}

/// The `else` chain of [`else_halvings`] that the benchmark
/// `a_test_that_narrows_every_link_reads_every_link_once` times: the arms' ranges at 3 links,
/// and `n (n + 1)` term reads at `n` links.
#[test]
fn an_else_chain_reads_every_link_once_in_each_arm() {
    let (a, _) = term_reads(&else_halvings(3, 2));
    assert_eq!(ints_of(&a, "(z3 > 0)", true, "x"), "[8..]");
    assert_eq!(ints_of(&a, "(z2 > 0)", true, "z1"), "[2..=3]");
    assert_eq!(ints_of(&a, "(z2 > 0)", false, "x"), "[..=3]");
    assert_eq!(ints_of(&a, "(z1 > 1)", false, "x"), "[..=1]");
    for n in [3, 8] {
        let n64 = n as u64;
        assert_eq!(
            term_reads(&else_halvings(n, 2)).1,
            n64 * (n64 + 1),
            "{n} links"
        );
    }
}

/// A binding with a summary read inside a term with none (PA-let-followups part 2):
/// `w = x + 1; z = w div 2; if z == 3 { 1 } else { 2 }`. The test reads `z` through its term,
/// which gives `w` the integers `6..=7`, and `w`, summarized over `x`, must narrow `x` in turn.
#[test]
fn a_summarized_binding_read_inside_a_term_narrows_its_input() {
    let body = let_(
        "w",
        prim(Prim::Add, vec![var("x"), int(1)]),
        let_(
            "z",
            prim(Prim::IntDiv, vec![var("w"), int(2)]),
            test(prim(Prim::Eq, vec![var("z"), int(3)])),
        ),
    );
    let a = checked_arms(&body);
    assert_eq!(ints_of(&a, "(z == 3)", true, "w"), "[6..=7]");
    assert_eq!(ints_of(&a, "(z == 3)", true, "x"), "[5..=6]");
}

/// A summary of `n` pieces over `x`: the `if` chain whose piece `j` holds the inputs below
/// `10 (j + 1)` (and from `10 j`, but for the first) and is `x - (10 j + 5)` for an even `j`
/// and `(10 j + 5) - x` for an odd one, so it is 0 at `10 j + 5` and slopes up and down.
fn sawtooth(n: usize) -> Term {
    let piece = |j: usize| {
        let c = int(10 * j as i64 + 5);
        if j % 2 == 0 {
            prim(Prim::Sub, vec![var("x"), c])
        } else {
            prim(Prim::Sub, vec![c, var("x")])
        }
    };
    (0..n - 1).rev().fold(piece(n - 1), |rest, j| {
        let below = prim(Prim::Lt, vec![var("x"), int(10 * (j as i64 + 1))]);
        if_(below, piece(j), rest)
    })
}

/// One choice of [`choices`]: its name, the function of `w` and the sign of `y`.
type Choice = (&'static str, fn(Term) -> Term, i64);

/// `abs(w)`, `max(w, -w)` and `min(w, -w)`, each with the test of [`over_a_sawtooth`] that
/// bounds `y` by 2 where the choice keeps the summary's bound 0: `f(w) + y <= 2` for the first
/// two, `f(w) - y >= -2` for the third.
fn choices() -> [Choice; 3] {
    fn neg(w: Term) -> Term {
        prim(Prim::Neg, vec![w])
    }
    [
        ("abs(w) + y", |w| prim(Prim::Abs, vec![w]), 1),
        (
            "max(w, -w) + y",
            |w| prim(Prim::Max, vec![w.clone(), neg(w)]),
            1,
        ),
        (
            "min(w, -w) - y",
            |w| prim(Prim::Min, vec![w.clone(), neg(w)]),
            -1,
        ),
    ]
}

/// `if y >= 0 { w = sawtooth(n); z = f(w) + sign * y; if test { 1 } else { 2 } } else { 3 }`,
/// the test `z <= 2` for `sign` 1 and `z >= -2` for -1.
fn over_a_sawtooth(n: usize, f: fn(Term) -> Term, sign: i64) -> Term {
    let (z, t) = if sign > 0 {
        let z = prim(Prim::Add, vec![f(var("w")), var("y")]);
        (z, prim(Prim::Le, vec![var("z"), int(2)]))
    } else {
        let z = prim(Prim::Sub, vec![f(var("w")), var("y")]);
        (z, prim(Prim::Ge, vec![var("z"), int(-2)]))
    };
    if_(
        prim(Prim::Ge, vec![var("y"), int(0)]),
        let_("w", sawtooth(n), let_("z", z, test(t))),
        int(3),
    )
}

/// `abs`, `min` and `max` of a summary of several pieces keep its exact bounds at the root
/// (PA-let-followups part 3): `abs(w) >= 0`, `max(w, -w) >= 0` and `min(w, -w) <= 0` hold over
/// all of `x`, so a test of the value plus or minus `y` bounds `y` on both sides, and `x` is
/// narrowed to the inputs where `|w| <= 2`. Made as a clamp plus the summary (`Pa::plus` of two
/// summaries), the bounds were those of a line added over unbounded pieces, which are infinite,
/// and `y` was read with no upper bound.
#[test]
fn abs_min_and_max_of_a_summary_of_several_pieces_keep_exact_bounds() {
    for (name, f, sign) in choices() {
        let a = checked_arms(&over_a_sawtooth(3, f, sign));
        let guard = if sign > 0 { "(z <= 2)" } else { "(z >= -2)" };
        assert_eq!(ints_of(&a, guard, true, "y"), "[0..=2]", "{name}");
        assert_eq!(
            ints_of(&a, guard, true, "x"),
            "[3..=7, 13..=17, 23..=27]",
            "{name}"
        );
    }
}

mod bench;
