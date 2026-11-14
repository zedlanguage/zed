//! Terms nested deep (PA-let-stack): the walk of the arms (`store::product::arms`) and the
//! forward transfer it runs on each bound term (`store::product::forward`) keep the nesting of
//! `let`s, `if`s and primitives on frames on the heap, so a block of 1,500 bindings has its
//! arms on a 2 MiB thread stack. Before, both recursed on the thread's stack once per level,
//! and a block of 512 bindings overflowed the stack of a scaling run (on a 2 MiB stack the
//! walk overflowed at about 670 bindings).
//!
//! The tests here check each kind of term at depths 1 to 12 on the test thread's stack. The
//! tests at depths 1,000 to 1,500 on a 2 MiB stack, above the 200 to 670 levels at which the
//! old walk overflowed a default stack, are in `bench` (author P178: a depth that overflows a
//! default stack is an unusual size; TEST-bench-move-l0139, which also cut them from 4,000 and
//! 10,000): each level costs the checker's work on a binding or a test whatever the depth, and
//! at 100,000 bindings these tests took 324 billion instructions and up to 45 s each
//! (TEST-deep-let-size). With the walk and the transfer recursing on the thread's stack again,
//! each of those aborts with a stack overflow, at 200 to 400 levels.

use zed_kernel::{Prim, Shared, Term, Value};
use zed_tests::scaling;
use zedc::store::product::{arms, forward};

use super::ints;

fn var(x: &str) -> Term {
    Term::Var(x.into())
}

fn int(n: i64) -> Term {
    Term::Lit(Value::Int(n))
}

fn prim(p: Prim, a: Term, b: Term) -> Term {
    Term::Prim(p, vec![a, b])
}

fn if_(c: Term, a: Term, b: Term) -> Term {
    Term::If(Shared::new(c), Shared::new(a), Shared::new(b))
}

fn let_(x: &str, e: Term, b: Term) -> Term {
    Term::Let(x.into(), Shared::new(e), Shared::new(b))
}

/// `{ t1 = t0 + step(1); ...; td = t(d-1) + step(d); if td >= 2 * d { 1 } else { 2 } }`, `t0`
/// being `n`: a running total of `d` days, where `step(j)` is a fee `if n > j { 2 } else { 1 }`
/// on every `every`-th day and a deposit of 1 on the others.
fn fees(d: usize, every: usize) -> Term {
    let name = |j: usize| if j == 0 { "n".into() } else { format!("t{j}") };
    let last = if_(
        prim(Prim::Ge, var(&name(d)), int(2 * d as i64)),
        int(1),
        int(2),
    );
    (1..=d).rev().fold(last, |body, j| {
        let step = if j % every == 0 {
            if_(prim(Prim::Gt, var("n"), int(j as i64)), int(2), int(1))
        } else {
            int(1)
        };
        let_(&name(j), prim(Prim::Add, var(&name(j - 1)), step), body)
    })
}

/// The arms of [`fees`] with 12 days and a fee every third: two for each fee and two for the
/// final test, in the order written, the last fee's `2` taken only by `n > 12`. The same block
/// 1,500 days deep, on a 2 MiB stack, is `bench::a_block_of_1500_bindings_has_its_arms_on_a_2_mib_stack`.
#[test]
fn a_block_of_bindings_has_its_arms() {
    let (d, every) = (12, 3);
    let a = arms(&fees(d, every), &ints(&["n".into()]));
    assert_eq!(a.len(), 2 * (d / every) + 2);
    let fee = &a[a.len() - 4];
    assert_eq!(fee.guard, format!("(n > {d})"));
    assert!(fee.outcome);
    assert_eq!(
        fee.scope.get("n").ints().to_string(),
        format!("[{}..]", d + 1)
    );
    assert!(a.iter().all(|a| a.reachable()));
}

/// `{ a1 = 1 + 1; a2 = a1 + 1; ...; ad = a(d-1) + 1; ad }`, a block whose value is `d + 1`.
fn block(d: usize) -> Term {
    let name = |j: usize| format!("a{j}");
    (1..=d).rev().fold(var(&name(d)), |body, j| {
        let from = if j == 1 { int(1) } else { var(&name(j - 1)) };
        let_(&name(j), prim(Prim::Add, from, int(1)), body)
    })
}

/// `1 + 1 + ... + 1`, `d + 1` ones nested to the left.
fn sum(d: usize) -> Term {
    (0..d).fold(int(1), |a, _| prim(Prim::Add, a, int(1)))
}

/// `{ t = <value>; if t > d { 1 } else { 2 } }`.
fn bound_to(value: Term, d: usize) -> Term {
    let_(
        "t",
        value,
        if_(prim(Prim::Gt, var("t"), int(d as i64)), int(1), int(2)),
    )
}

/// A binding whose value is a block of 1, 2 or 5 `let`s, or a sum as deep: the forward transfer
/// finds its value, the depth plus 1, and the test after it is taken only by its true arm. The
/// same 1,500 deep, on a 2 MiB stack, is `bench::a_value_nested_1500_deep_is_found_on_a_2_mib_stack`.
#[test]
fn a_nested_value_is_found() {
    let scope = ints(&["n".into()]);
    for d in [1, 2, 5] {
        for make in [block, sum] {
            let value = make(d);
            let found = forward(&value, &mut scope.clone());
            assert_eq!(found.value(), Some(&Value::Int(d as i64 + 1)), "d = {d}");
            let a = arms(&bound_to(value, d), &scope);
            assert_eq!(a.len(), 2, "d = {d}");
            assert!(a[0].reachable() && !a[1].reachable(), "d = {d}");
        }
    }
}

/// `if n > 1 { if n > 2 { ... if n > d { 1 } else { 0 } ... } else { 0 } } else { 0 }`.
fn nested_ifs(d: usize) -> Term {
    (1..=d).rev().fold(int(1), |inner, j| {
        if_(prim(Prim::Gt, var("n"), int(j as i64)), inner, int(0))
    })
}

/// `if`s nested 1, 2 and 5 deep in their first arm: the `k`-th test's true arm holds `n > k`,
/// its false arm `n == k` (`n <= 1` for the first), the arms in the order written (the true
/// arms outside in, then the false arms inside out), and the value is 0 or 1. The same 1,000
/// deep, on a 2 MiB stack, is `bench::ifs_nested_1000_deep_have_their_arms_on_a_2_mib_stack`.
#[test]
fn nested_ifs_have_their_arms() {
    for d in [1, 2, 5] {
        let a = arms(&nested_ifs(d), &ints(&["n".into()]));
        assert_eq!(a.len(), 2 * d, "d = {d}");
        for k in 1..=d {
            assert_eq!(
                a[k - 1].scope.get("n").ints().to_string(),
                format!("[{}..]", k + 1),
                "d = {d}"
            );
            assert_eq!(
                a[2 * d - k].scope.get("n").ints().to_string(),
                if k == 1 {
                    "[..=1]".to_string()
                } else {
                    format!("[{k}..={k}]")
                },
                "d = {d}"
            );
        }
        let value = forward(&nested_ifs(d), &mut ints(&["n".into()]));
        assert_eq!(value.ints().to_string(), "[0..=1]", "d = {d}");
    }
}

/// `f(arg(1), ..., arg(d))`, each argument the block `{ t = n + j; u = t + 1; u }`: `d`
/// blocks walked one after another, each binding `t` with a summary over `n` and reading it at
/// the binding of `u`, so at most two bindings are in scope at a time.
fn blocks_in_a_call(d: usize) -> Term {
    let block = |j: usize| {
        let_(
            "t",
            prim(Prim::Add, var("n"), int(j as i64)),
            let_("u", prim(Prim::Add, var("t"), int(1)), var("u")),
        )
    };
    Term::App(Shared::new(var("f")), (1..=d).map(block).collect())
}

/// The block of [`fees`] with a fee every day, as the benchmark `the_arms_of_a_deep_block_scale`
/// builds it, at 1 to 4 days: two arms a fee and two for the final test, the last fee's `2`
/// taken only by `n > d`, every arm reachable.
#[test]
fn a_block_with_a_fee_every_day_has_its_arms() {
    for d in 1..=4 {
        let a = arms(&fees(d, 1), &ints(&["n".into()]));
        assert_eq!(a.len(), 2 * d + 2, "{d} days");
        let fee = &a[a.len() - 4];
        assert_eq!(fee.guard, format!("(n > {d})"), "{d} days");
        assert!(fee.outcome, "{d} days");
        assert!(a.iter().all(|a| a.reachable()), "{d} days");
    }
}

/// The blocks of [`blocks_in_a_call`], which the benchmark
/// `the_walk_of_blocks_one_after_another_holds_the_bytes_of_one_block` walks, hold no test, so
/// the call has no arms.
#[test]
fn blocks_one_after_another_in_a_call_have_no_arms() {
    for d in 1..=3 {
        assert!(arms(&blocks_in_a_call(d), &ints(&["n".into()])).is_empty());
    }
}

mod bench;
