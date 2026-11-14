//! The limits of compile-time evaluation (DESIGN.md step M0.11): nested calls have a minimum,
//! 20,000, and no maximum, so a chain past the minimum is accepted too; there is no minimum of
//! steps or of memory, since no count of either may stop compile-time evaluation, so the
//! evaluator with its default settings has no fuel. Fuel is a setting a caller of the evaluator
//! may choose, and where it is set it is counted exactly. The chain at the minimum, the string of
//! 512 MiB and the run past ten million steps are in `bench/limits.rs` and
//! `tests/full/m0_11_prelude_axioms_and_limits`; here the same programs run at small sizes.

use zed_kernel::term::build::{app, if_, lam, lit, prim, var};
use zed_kernel::{Evaluator, KernelError, Prim, Term, Value, World, eval};

use crate::leaves::count_leaves;

/// Evaluates `t` with `fuel` steps.
fn with_fuel(fuel: u64, t: &Term) -> Result<Value, KernelError> {
    Evaluator::new(World::new()).with_fuel(fuel).run(t)
}

/// With no fuel, which is the evaluator's default, no count of steps stops the evaluation: the
/// programs `the_step_past_the_fuel_is_refused` stops at a fuel of `2k` steps run to the end.
#[test]
fn with_no_fuel_no_count_of_steps_stops_the_evaluation() {
    for k in [1, 2, 9, 1000, 1001] {
        assert_eq!(eval(&count_leaves(k)), Ok(Value::Int(k)));
    }
}

/// Fuel of `2k` steps accepts the `2k - 1` calls of `k` items and refuses the `2k + 1` calls of
/// `k + 1`, so the step count of `count_leaves` is measured and not estimated.
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
