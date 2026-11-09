//! Terms nested deep (PA-let-stack): the walk of the arms (`store::product::arms`) and the
//! forward transfer it runs on each bound term (`store::product::forward`) keep the nesting of
//! `let`s, `if`s and primitives on frames on the heap, so a block of 10,000 bindings has its
//! arms on a 2 MiB thread stack. Before, both recursed on the thread's stack once per level,
//! and a block of 512 bindings overflowed the stack of a scaling run (on a 2 MiB stack the
//! walk overflowed at about 670 bindings).
//!
//! The fixed depths are 10 to 25 times the depth that overflowed, and no more, because each level
//! costs the checker's work on a binding or a test whatever the depth: at 100,000 bindings
//! these tests took 324 billion instructions and up to 45 s each (TEST-deep-let-size). With
//! the walk and the transfer recursing on the thread's stack again, every test here aborts
//! with a stack overflow, at 200 to 400 levels.

use zed_kernel::{Prim, Shared, Term, Value};
use zed_tests::scaling;
use zedc::store::product::{arms, forward};

use super::ints;

/// The default stack of a test thread.
const STACK: usize = 2 << 20;

/// How deep the terms are.
const DEEP: usize = 10_000;

/// Runs `f` on a thread with a 2 MiB stack, whatever `RUST_MIN_STACK` says.
fn on_small_stack(f: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(f)
        .expect("a test thread")
        .join()
        .expect("the test passes on a 2 MiB stack");
}

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

/// The arms of [`fees`] with `DEEP` days and a fee every 100th, on a 2 MiB stack: two for
/// each fee and two for the final test, in the order written, the last fee's `2` taken only by
/// `n > DEEP`. The fee is spaced to keep the test short, not to hide a cost that grows: a
/// test costs a reduction of the scope and a copy per arm, measured at 165, 181 and 186 µs
/// with a fee on every day at 1,000, 4,000 and 12,500 days (and [`the_arms_of_a_deep_block_scale`]
/// checks that cost), and the depth of the walk is the same.
#[test]
fn a_block_of_10000_bindings_has_its_arms_on_a_2_mib_stack() {
    on_small_stack(|| {
        let every = 100;
        let a = arms(&fees(DEEP, every), &ints(&["n".into()]));
        assert_eq!(a.len(), 2 * (DEEP / every) + 2);
        let fee = &a[a.len() - 4];
        assert_eq!(fee.guard, format!("(n > {DEEP})"));
        assert!(fee.outcome);
        assert_eq!(
            fee.scope.get("n").ints().to_string(),
            format!("[{}..]", DEEP + 1)
        );
        assert!(a.iter().all(|a| a.reachable()));
    });
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

/// A binding whose value is a block of 10,000 `let`s, or a sum 10,000 deep: the forward
/// transfer finds its value, `10,001`, and the test after it is taken only by its true arm.
#[test]
fn a_value_nested_10000_deep_is_found_on_a_2_mib_stack() {
    on_small_stack(|| {
        let scope = ints(&["n".into()]);
        for make in [block, sum] {
            let value = make(DEEP);
            let found = forward(&value, &mut scope.clone());
            assert_eq!(found.value(), Some(&Value::Int(DEEP as i64 + 1)));
            let a = arms(&bound_to(value, DEEP), &scope);
            assert_eq!(a.len(), 2);
            assert!(a[0].reachable() && !a[1].reachable());
        }
    });
}

/// `if n > 1 { if n > 2 { ... if n > d { 1 } else { 0 } ... } else { 0 } } else { 0 }`.
fn nested_ifs(d: usize) -> Term {
    (1..=d).rev().fold(int(1), |inner, j| {
        if_(prim(Prim::Gt, var("n"), int(j as i64)), inner, int(0))
    })
}

/// `if`s nested 4,000 deep in their first arm, on a 2 MiB stack: the `k`-th test's true arm
/// holds `n > k`, its false arm `n == k` (`n <= 1` for the first), the arms in the order
/// written (the true arms outside in, then the false arms inside out), and the value is
/// 0 or 1. (Each test costs a reduction of the scope; the depth is 4,000, ten times the
/// depth at which the old walk overflowed, to keep the test short.)
#[test]
fn ifs_nested_4000_deep_have_their_arms_on_a_2_mib_stack() {
    on_small_stack(|| {
        let d = 4_000;
        let a = arms(&nested_ifs(d), &ints(&["n".into()]));
        assert_eq!(a.len(), 2 * d);
        for k in [1, d / 2, d] {
            assert_eq!(
                a[k - 1].scope.get("n").ints().to_string(),
                format!("[{}..]", k + 1)
            );
            assert_eq!(
                a[2 * d - k].scope.get("n").ints().to_string(),
                if k == 1 {
                    "[..=1]".to_string()
                } else {
                    format!("[{k}..={k}]")
                }
            );
        }
        let value = forward(&nested_ifs(d), &mut ints(&["n".into()]));
        assert_eq!(value.ints().to_string(), "[0..=1]");
    });
}

/// The arms of [`fees`] with a fee every day cost `O(d log d)`, at 250 and 2,000 days, on a
/// 2 MiB stack; the blocks are built before the timing.
#[test]
fn the_arms_of_a_deep_block_scale() {
    on_small_stack(|| {
        let terms = scaling::inputs(250, |d| fees(d, 1));
        let scope = ints(&["n".into()]);
        scaling::check(
            "the arms of a block of d bindings, a test in each",
            250,
            |d| _ = arms(&terms[&d], &scope),
        );
    });
}

/// The forward transfer of a block of `d` bindings and of a sum `d` deep costs `O(d)`, at
/// 1,250 and 10,000, on a 2 MiB stack; the terms are built before the timing.
#[test]
fn the_value_of_a_deep_term_scales() {
    on_small_stack(|| {
        let n = DEEP / scaling::FACTOR;
        let scope = ints(&["n".into()]);
        for (what, make) in [
            (
                "the value of a block of d bindings",
                block as fn(usize) -> Term,
            ),
            ("the value of a sum d deep", sum),
        ] {
            let terms = scaling::inputs(n, make);
            scaling::check(what, n, |d| _ = forward(&terms[&d], &mut scope.clone()));
        }
    });
}
