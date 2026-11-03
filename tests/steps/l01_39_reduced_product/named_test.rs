//! A credit rule named once with `let` and checked at each tier of an approval: tier `i`
//! approves a request of size `z` in `100..=200` when the waiting time `w` is at least `i`,
//! or, for a small request (`z` in `0..=10`), when the credit rule `t` holds, one of two
//! limits holds and the next tier approves; the last tier asks `w >= d`. The rule is a chain
//! of fallbacks on the balance `x` and the credit `y`, as long as the approval is deep. The
//! formula of the test holds the rule's formula once at each tier, shared and not copied, so
//! the arms take time near linear in `d` and not in `d²` (COMPLEXITY.md S31).

use std::collections::BTreeMap;
use std::sync::Arc;

use zed_kernel::term::build::{if_, let_, lit, prim, var};
use zed_kernel::{Prim, Term};
use zed_tests::scaling;
use zedc::store::product::{Arm, arms};

use super::ints;

fn cmp(p: Prim, n: &str, v: i64) -> Term {
    prim(p, vec![var(n), lit(v)])
}

fn ge(n: &str, v: i64) -> Term {
    cmp(Prim::Ge, n, v)
}

fn le(n: &str, v: i64) -> Term {
    cmp(Prim::Le, n, v)
}

fn all(ts: Vec<Term>) -> Term {
    ts.into_iter()
        .reduce(|a, b| prim(Prim::And, vec![a, b]))
        .expect("a part")
}

fn either(a: Term, b: Term) -> Term {
    prim(Prim::Or, vec![a, b])
}

/// The credit rule: `x >= 0 || (y >= 0 && (x >= 1 || … (x >= d)))`.
fn rule(d: usize) -> Term {
    (0..d).rev().fold(ge("x", d as i64), |inner, i| {
        either(ge("x", i as i64), all(vec![ge("y", i as i64), inner]))
    })
}

/// The approval `d` tiers deep, with `rule` at each tier.
fn approval(d: usize, rule: &dyn Fn() -> Term) -> Term {
    (0..d).rev().fold(ge("w", d as i64), |inner, i| {
        let i = i as i64;
        either(
            all(vec![ge("z", 100), le("z", 200), ge("w", i)]),
            all(vec![
                ge("z", 0),
                le("z", 10),
                rule(),
                either(ge("q", i), le("u", -i)),
                inner,
            ]),
        )
    })
}

/// `let t = rule(d) in approval(d)`, the rule named once.
fn named(d: usize) -> Term {
    let_("t", rule(d), approval(d, &|| var("t")))
}

/// The approval with the rule written out at each tier.
fn written_out(d: usize) -> Term {
    approval(d, &|| rule(d))
}

fn names() -> Vec<Arc<str>> {
    ["x", "y", "u", "q", "z", "w"].map(Into::into).into()
}

fn arms_of(test: Term) -> Vec<Arm> {
    arms(&if_(test, lit(1), lit(2)), &ints(&names()))
}

/// Each arm's reachability and the range of each name in it.
fn summary(a: &[Arm]) -> Vec<(bool, Vec<String>)> {
    a.iter()
        .map(|arm| {
            let hulls = names()
                .iter()
                .map(|n| format!("{n}={}", arm.scope.get(n).ints()))
                .collect();
            (arm.reachable(), hulls)
        })
        .collect()
}

#[test]
fn a_named_rule_at_each_tier_narrows_as_if_written_out() {
    // An approved request is large or small, and waits at least zero; a refused one is
    // anything. The rule bounds no name, since a large request approves without it.
    for d in [1, 2, 5, 30] {
        let a = summary(&arms_of(named(d)));
        assert_eq!(a, summary(&arms_of(written_out(d))), "d = {d}");
        let free = |n: &str| format!("{n}=[..]");
        let approved = ["x", "y", "u", "q"]
            .map(free)
            .into_iter()
            .chain(["z=[0..=10, 100..=200]".to_string(), "w=[0..]".to_string()])
            .collect::<Vec<_>>();
        let refused: Vec<String> = names().iter().map(|n| free(n)).collect();
        assert_eq!(a, vec![(true, approved), (true, refused)], "d = {d}");
    }
}

#[test]
fn a_rule_named_once_and_used_at_one_tier_is_the_rule_itself() {
    // At one tier the rule is used once: `z` small with the rule, or large.
    let a = summary(&arms_of(named(1)));
    assert_eq!(a[0].1[4], "z=[0..=10, 100..=200]");
    assert_eq!(a[0].1[5], "w=[0..]");
}

#[test]
fn arms_of_a_named_rule_at_each_tier_take_time_near_linear_in_the_depth() {
    // Depths 30 and 240. With the rule's formula copied at each tier the work grew 43 times
    // (1.25 to 54.0 billion instructions); shared, it grows 7.7 times.
    std::thread::Builder::new()
        .stack_size(1 << 29)
        .spawn(|| {
            let tests: BTreeMap<usize, Term> =
                [30, 240].map(|d| (d, if_(named(d), lit(1), lit(2)))).into();
            let scope = ints(&names());
            scaling::check(
                "arms of a rule named once, used at each of d tiers",
                30,
                |d| {
                    std::hint::black_box(arms(&tests[&d], &scope));
                },
            );
        })
        .expect("a thread")
        .join()
        .expect("the test passes");
}
