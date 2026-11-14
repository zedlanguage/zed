//! A closure the kernel is handed is one term however many closures share it: each closure's
//! term is built once per kernel call, by its cell, on the native path (`hooks::term`) and in
//! the counting machine (`Machine::term`), so a closure captured twice at each of `d` levels
//! gives a term of `d` closures, not of `2^d` paths (COMPLEXITY.md R9, item HOOKS-term-dag).

use zed_kernel::term::build::{app, if_, lam, let_, lit, prim, var};
use zed_kernel::{Evaluator, Family, Prim, Term, Value, World};
use zed_tests::kernel::{add, fold, lt, mul};

use super::planned;
use super::scaling::counted_in;

/// `{0: x0, 1: x1}`: the two entries a fold combines.
fn pair(x0: i64, x1: i64) -> Term {
    lit(Value::Family(Family::of(
        [(0, x0), (1, x1)].map(|(k, x)| (Value::Int(k), Value::Int(x))),
    )))
}

/// A pricing rule in `d` layers of fallback: `fallback = (a, b) -> (x, y) -> if x < 0
/// { b(x, y) } else { a(x, y) }; r0 = base; r1 = fallback(r0, other(r0)); …`, then `body`
/// of the top rule. `other` gives each layer's second rule from the rule below; `|r| r`
/// gives the layer the one rule below twice.
fn layered(
    d: usize,
    base: Term,
    other: impl Fn(Term) -> Term,
    body: impl FnOnce(Term) -> Term,
) -> Term {
    let call = |f: &str| app(var(f), vec![var("x"), var("y")]);
    let fallback = lam(
        &["a", "b"],
        lam(
            &["x", "y"],
            if_(lt(var("x"), lit(0i64)), call("b"), call("a")),
        ),
    );
    let mut t = body(var(&format!("r{d}")));
    for i in (1..=d).rev() {
        let below = var(&format!("r{}", i - 1));
        let layer = app(var("fallback"), vec![below.clone(), other(below)]);
        t = let_(&format!("r{i}"), layer, t);
    }
    let_("fallback", fallback, let_("r0", base, t))
}

/// `(x, y) -> x + y`.
fn sum() -> Term {
    lam(&["x", "y"], add(var("x"), var("y")))
}

/// The fold of `{0: 1, 1: 2}` by `d` layers each holding the layer below twice.
pub(crate) fn doubled(d: usize) -> Term {
    layered(d, sum(), |r| r, |top| fold(pair(1, 2), top, None))
}

/// `t` run by the kernel, the counting machine and natively: the three values agree, and the
/// native run's counts are the machine's. Returns the value and the native kernel calls.
fn everywhere(t: &Term) -> (String, u64) {
    let k = Evaluator::new(World::new()).run(t).unwrap().to_string();
    assert_eq!(counted_in(t, World::new()), k);
    let (g, p) = planned(t);
    let o = zed_native::run(&g, &p, &mut Evaluator::new(World::new())).unwrap();
    (k, o.kernel_calls)
}

#[test]
fn sixty_layers_of_a_rule_held_twice_fold_in_one_kernel_call() {
    // A tree of every path would hold 2^60 copies of the base rule.
    assert_eq!(everywhere(&doubled(60)), ("3".into(), 1));
}

#[test]
fn layers_of_two_different_rules_keep_each_rule_its_own_term() {
    // Each layer falls back on a rule that calls the layer below and multiplies by 1, a
    // closure of its own; the entry -1 is negative, so every layer takes its second rule
    // down to the base rule, the sum.
    let other = |r: Term| {
        let (x, y) = (var("x"), var("y"));
        lam(&["x", "y"], mul(app(r, vec![x, y]), lit(1i64)))
    };
    let t = layered(40, sum(), other, |top| fold(pair(-1, 5), top, None));
    assert_eq!(everywhere(&t).0, "4");
}

#[test]
fn a_rule_used_by_two_folds_is_built_again_for_each() {
    // Two kernel calls, each with its own record of the closures built.
    let t = layered(
        30,
        sum(),
        |r| r,
        |top| {
            prim(
                Prim::Tuple,
                vec![
                    fold(pair(1, 2), top.clone(), None),
                    fold(pair(10, 20), top, None),
                ],
            )
        },
    );
    assert_eq!(everywhere(&t), ("(3, 30)".into(), 2));
}
