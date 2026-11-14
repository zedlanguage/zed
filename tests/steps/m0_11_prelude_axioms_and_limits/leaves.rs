//! The step program of `limits.rs`, which `tests/full` also runs at the limit of 10,000,000
//! steps.

use zed_kernel::term::build::{app, if_, lam, lit, prim, var};
use zed_kernel::{Evaluator, KernelError, Prim, Term, Value, World};

/// Counts the leaves of a balanced split of `n` items, as a merge sort recurses:
/// `count(n) = if n <= 1 { 1 } else { count(n div 2) + count(n - n div 2) }`, which makes
/// `2n - 1` calls, each one step.
pub fn count_leaves(n: i64) -> Term {
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

/// Evaluates `t` with `fuel` steps.
pub fn with_fuel(fuel: u64, t: &Term) -> Result<Value, KernelError> {
    Evaluator::new(World::new()).with_fuel(fuel).run(t)
}
