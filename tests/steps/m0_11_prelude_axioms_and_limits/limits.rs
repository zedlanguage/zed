//! The minimum resource limits: an evaluation within them is accepted by the reference
//! evaluator with its default settings. Each program is sized to its limit, and one step or
//! one call more is shown to cross it, so the sizes are measured and not estimated.

use zed_kernel::eval::{MIN_MEMORY, MIN_NESTED_CALLS, MIN_STEPS};
use zed_kernel::term::build::{app, if_, lam, lit, prim, var};
use zed_kernel::{Evaluator, KernelError, Prim, Term, Value, World, eval};

/// Counts the leaves of a balanced split of `n` items, as a merge sort recurses:
/// `count(n) = if n <= 1 { 1 } else { count(n div 2) + count(n - n div 2) }`, which makes
/// `2n - 1` calls, each one step.
fn count_leaves(n: i64) -> Term {
    let half = || prim(Prim::IntDiv, vec![var("n"), lit(2)]);
    let me = |arg: Term| app(var("me"), vec![var("me"), arg]);
    let body = if_(
        prim(Prim::Le, vec![var("n"), lit(1)]),
        lit(1),
        prim(
            Prim::Add,
            vec![me(half()), me(prim(Prim::Sub, vec![var("n"), half()]))],
        ),
    );
    let f = lam(&["me", "n"], body);
    app(f.clone(), vec![f, lit(n)])
}

fn with_fuel(fuel: u64, t: &Term) -> Result<Value, KernelError> {
    Evaluator::new(World::new()).with_fuel(fuel).run(t)
}

#[test]
fn ten_million_steps_are_accepted() {
    // 5,000,000 items make 9,999,999 calls; 5,000,001 make 10,000,001.
    let within = count_leaves(5_000_000);
    assert_eq!(with_fuel(MIN_STEPS, &within), Ok(Value::Int(5_000_000)));
    assert_eq!(
        with_fuel(MIN_STEPS, &count_leaves(5_000_001)),
        Err(KernelError::OutOfFuel)
    );
    // The default fuel is at least the minimum: a compile-time assertion in `zed_kernel::eval`.
}

/// A chain of `n` calls, each nested in the one before:
/// `depth(k) = if k == 1 { 1 } else { 1 + depth(k - 1) }`.
fn nested(n: i64) -> Term {
    let body = if_(
        prim(Prim::Eq, vec![var("k"), lit(1)]),
        lit(1),
        prim(
            Prim::Add,
            vec![
                lit(1),
                app(
                    var("me"),
                    vec![var("me"), prim(Prim::Sub, vec![var("k"), lit(1)])],
                ),
            ],
        ),
    );
    let f = lam(&["me", "k"], body);
    app(f.clone(), vec![f, lit(n)])
}

#[test]
fn twenty_thousand_nested_calls_are_accepted() {
    let n = MIN_NESTED_CALLS as i64;
    assert_eq!(eval(&nested(n)), Ok(Value::Int(n)));
    assert_eq!(eval(&nested(n + 1)), Err(KernelError::TooDeep));
}

#[test]
fn a_value_of_almost_a_gibibyte_is_accepted() {
    // A string doubled 29 times reaches 512 MiB; with the halves the recursion still holds,
    // the strings alive at the end total 2^30 - 1 bytes.
    let me = app(
        var("me"),
        vec![
            var("me"),
            prim(Prim::Add, vec![var("s"), var("s")]),
            prim(Prim::Sub, vec![var("k"), lit(1)]),
        ],
    );
    let body = if_(prim(Prim::Eq, vec![var("k"), lit(0)]), var("s"), me);
    let f = lam(&["me", "s", "k"], body);
    let out = eval(&app(f.clone(), vec![f, lit("z"), lit(29)])).unwrap();
    let Value::Str(s) = out else {
        panic!("{out:?}")
    };
    assert_eq!(s.len() as u64, MIN_MEMORY / 2);
    assert_eq!((1..=29).map(|k| 1u64 << k).sum::<u64>() + 1, MIN_MEMORY - 1);
}
