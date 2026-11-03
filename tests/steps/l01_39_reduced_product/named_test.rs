//! A credit rule named once with `let` and checked at each tier of an approval: tier `i`
//! approves a request of size `z` in `100..=200` when the waiting time `w` is at least `i`,
//! or, for a small request (`z` in `0..=10`), when the credit rule `t` holds, one of two
//! limits holds and the next tier approves; the last tier asks `w >= d`. The rule is a chain
//! of fallbacks on the balance `x` and the credit `y`, as long as the approval is deep. The
//! formula of the test holds the rule's formula once at each tier, shared and not copied, so
//! the arms take time near linear in `d` and not in `d²` (COMPLEXITY.md S31). A named
//! conjunction of many credit limits, a named disjunction of many exemptions, or a named
//! disjunction of many credit limits any one of which a tier requires, is still read once at
//! each tier (COMPLEXITY.md S31b, open in ST-formula-wide); three ignored tests below measure
//! it.

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

/// The credit limits, `k` of them: `x + j y >= j` for each `j` below `k`, one for each kind of
/// account, on the balance `x` and the credit `y`.
fn limits(k: usize) -> Vec<Term> {
    (0..k as i64)
        .map(|j| {
            let line = prim(
                Prim::Add,
                vec![var("x"), prim(Prim::Mul, vec![lit(j), var("y")])],
            );
            prim(Prim::Ge, vec![line, lit(j)])
        })
        .collect()
}

/// The approval `d` tiers deep, with every one of `k` credit limits required at each tier.
fn approval_within(d: usize, k: usize, named: bool) -> Term {
    let limits = || all(limits(k));
    if named {
        let_("t", limits(), approval(d, &|| var("t")))
    } else {
        approval(d, &limits)
    }
}

/// The approval `d` tiers deep where a small request needs any one of `k` credit limits at each
/// tier, the limits in place of the rule.
fn approval_any_limit(d: usize, k: usize, named: bool) -> Term {
    let any = || limits(k).into_iter().reduce(either).expect("a limit");
    if named {
        let_("t", any(), approval(d, &|| var("t")))
    } else {
        approval(d, &any)
    }
}

/// The approval `d` tiers deep where any one of `k` exemptions approves at each tier, beside a
/// large request or a small one that the next tier approves.
fn approval_exempt(d: usize, k: usize, named: bool) -> Term {
    let exempt = || limits(k).into_iter().reduce(either).expect("an exemption");
    let tiers = |t: &dyn Fn() -> Term| {
        (0..d).rev().fold(ge("w", d as i64), |inner, i| {
            let i = i as i64;
            either(
                either(t(), all(vec![ge("z", 100), le("z", 200), ge("w", i)])),
                all(vec![
                    ge("z", 0),
                    le("z", 10),
                    either(ge("q", i), le("u", -i)),
                    inner,
                ]),
            )
        })
    };
    if named {
        let_("t", exempt(), tiers(&|| var("t")))
    } else {
        tiers(&exempt)
    }
}

#[test]
fn named_limits_and_exemptions_at_each_tier_narrow_as_if_written_out() {
    for (d, k) in [(1, 1), (1, 3), (2, 2), (5, 5)] {
        let within = summary(&arms_of(approval_within(d, k, true)));
        assert_eq!(within, summary(&arms_of(approval_within(d, k, false))));
        let exempt = summary(&arms_of(approval_exempt(d, k, true)));
        assert_eq!(exempt, summary(&arms_of(approval_exempt(d, k, false))));
        let any = summary(&arms_of(approval_any_limit(d, k, true)));
        assert_eq!(any, summary(&arms_of(approval_any_limit(d, k, false))));
    }
}
/// Runs the scaling check of `arms` on `family(d, d, true)` at d = 30 and 240.
fn wide_scaling(what: &str, family: fn(usize, usize, bool) -> Term) {
    scaling::on_a_thread(1 << 29, || {
        let tests: BTreeMap<usize, Term> = [30, 240]
            .map(|d| (d, if_(family(d, d, true), lit(1), lit(2))))
            .into();
        let scope = ints(&names());
        scaling::check(what, 30, |d| {
            std::hint::black_box(arms(&tests[&d], &scope));
        });
    });
}

#[test]
#[ignore = "fails: a shared conjunction is flattened into each place; open in ST-formula-wide (COMPLEXITY.md S31b)"]
fn arms_of_a_wide_named_conjunction_at_each_tier_take_time_near_linear_in_the_depth() {
    // k = d credit limits named once and required at each of d tiers. Measured on the branch
    // of ST-formula-share, in instructions at d = 30, 60, 120, 240: 1.18, 3.87, 14.8, 59.0 G
    // (about 4 times per doubling); written out at each tier 12.1, 56.0, 251 G at d = 30 to
    // 120. `Formula::and` flattens the shared conjunction into each tier's conjunction, so its
    // k constraints are read at each tier (tradeoff comments at `Formula::and` and `Parts::of`).
    wide_scaling(
        "arms of k = d credit limits named once, required at each of d tiers",
        approval_within,
    );
}

#[test]
#[ignore = "fails: a shared disjunction is flattened into each place; open in ST-formula-wide (COMPLEXITY.md S31b)"]
fn arms_of_a_wide_named_disjunction_at_each_tier_take_time_near_linear_in_the_depth() {
    // k = d exemptions named once, any of which approves at each of d tiers. Measured on the
    // branch of ST-formula-share, in instructions at d = 30, 60, 120, 240: 0.37, 1.14, 3.88,
    // 14.2 G (3.1 to 3.7 times per doubling); written out at each tier 7.5, 33.7, 150 G at
    // d = 30 to 120. `Formula::or` flattens the shared disjunction into each tier's
    // disjunction (tradeoff comments at `Formula::or` and `Parts::of`).
    wide_scaling(
        "arms of k = d exemptions named once, any of which approves at each of d tiers",
        approval_exempt,
    );
}

#[test]
#[ignore = "fails: a shared disjunction used as a conjunct is read once per place; open in ST-formula-wide (COMPLEXITY.md S31b)"]
fn arms_of_a_wide_named_disjunction_required_at_each_tier_take_time_near_linear_in_the_depth() {
    // Any one of k = d credit limits, named once, required of a small request at each of d
    // tiers. Measured by ST-formula-share verify#2, in instructions at d = 30, 60, 120, 240:
    // 2.76, 10.4, 40.2, 157.6 G (3.8 times per doubling), 0.73 to 39.6 GB allocated; written
    // out at each tier, d = 30, 60 and 120 did not finish in 300 s together. The test fails at
    // 54.1 times the bytes (limit 24). `Parts::of` makes the disjunction's k disjuncts once but
    // copies its list at each place, and `settle`, `pick` and `witness` read the k disjuncts
    // once per place (tradeoff comment at `Parts::of`).
    wide_scaling(
        "arms of any of k = d credit limits named once, required at each of d tiers",
        approval_any_limit,
    );
}
