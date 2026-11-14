//! The minimum resource limits: an evaluation within them is accepted by the reference
//! evaluator with its default settings. The step program is sized to its limit, and one step
//! more is shown to cross it, so the size is measured and not estimated. Nested calls have a
//! minimum and no maximum: a chain past the minimum is accepted too.

use zed_kernel::eval::{MIN_MEMORY, MIN_NESTED_CALLS};
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
    assert_eq!(eval(&nested(n + 1)), Ok(Value::Int(n + 1)));
    assert_eq!(eval(&nested(50 * n)), Ok(Value::Int(50 * n)));
}

#[test]
fn a_value_of_almost_a_gibibyte_is_accepted() {
    // A string doubled 29 times reaches 512 MiB; with the halves the recursion still holds,
    // the strings alive at the end total 2^30 - 1 bytes.
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
    let out = eval(&app(f.clone(), vec![f, lit("z"), lit(29)])).unwrap();
    let Value::Str(s) = out else {
        panic!("{out:?}")
    };
    assert_eq!(s.len() as u64, MIN_MEMORY / 2);
    assert_eq!((1..=29).map(|k| 1u64 << k).sum::<u64>() + 1, MIN_MEMORY - 1);
}
