//! The minimum resource limits: an evaluation within them is accepted by the reference
//! evaluator with its default settings. The step program is sized to its limit, and one step
//! more is shown to cross it, so the size is measured and not estimated. Nested calls have a
//! minimum and no maximum: a chain past the minimum is accepted too. The limits at their size
//! are in `bench/limits.rs`; here the same programs run at small sizes.

use zed_kernel::term::build::{app, if_, lam, lit, prim, var};
use zed_kernel::{KernelError, Prim, Term, Value, eval};

use crate::leaves::{count_leaves, with_fuel};

/// Fuel of `2k` steps accepts the `2k - 1` calls of `k` items and refuses the `2k + 1` calls of
/// `k + 1`. The limit itself, 10,000,000 steps, takes about 14 s at each side, and
/// `tests/full/m0_11_prelude_axioms_and_limits` runs it at 5,000,000 and 5,000,001 items.
#[test]
fn the_step_past_the_fuel_is_refused() {
    for k in [1, 2, 9, 1000] {
        let fuel = 2 * k as u64;
        assert_eq!(with_fuel(fuel, &count_leaves(k)), Ok(Value::Int(k)));
        assert_eq!(
            with_fuel(fuel, &count_leaves(k + 1)),
            Err(KernelError::OutOfFuel)
        );
    }
}

/// A chain of `n` calls, each nested in the one before:
/// `depth(k) = if k == 1 { 1 } else { 1 + depth(k - 1) }`.
pub(super) fn nested(n: i64) -> Term {
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

/// `"z"` doubled `k` times by a recursion that holds each half until it returns.
pub(super) fn doubled(k: i64) -> Term {
    let me = app(
        var("me"),
        vec![
            var("me"),
            prim(Prim::Concat, vec![var("s"), var("s")]),
            prim(Prim::Sub, vec![var("k"), lit(1)]),
        ],
    );
    let body = if_(prim(Prim::Eq, vec![var("k"), lit(0)]), var("s"), me);
    let f = lam(&["me", "s", "k"], body);
    app(f.clone(), vec![f, lit("z"), lit(k)])
}

/// A chain of a few nested calls, and a string doubled a few times, are accepted; the chain
/// past the minimum of nested calls and the string of 512 MiB are in `bench/limits.rs`.
#[test]
fn a_few_nested_calls_and_a_short_doubled_string_are_accepted() {
    for n in [1, 2, 9] {
        assert_eq!(eval(&nested(n)), Ok(Value::Int(n)));
        let Ok(Value::Str(s)) = eval(&doubled(n)) else {
            panic!("a string")
        };
        assert_eq!(s.len(), 1 << n);
    }
}
