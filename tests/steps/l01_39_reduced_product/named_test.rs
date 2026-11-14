//! A credit rule named once with `let` and checked at each tier of an approval: tier `i`
//! approves a request of size `z` in `100..=200` when the waiting time `w` is at least `i`,
//! or, for a small request (`z` in `0..=10`), when the credit rule `t` holds, one of two
//! limits holds and the next tier approves; the last tier asks `w >= d`. The rule is a chain
//! of fallbacks on the balance `x` and the credit `y`, as long as the approval is deep. The
//! formula of the test holds the rule's formula once at each tier, shared and not copied, so
//! the arms take time near linear in `d` and not in `d²` (COMPLEXITY.md S31). A named
//! conjunction of many credit limits, a named disjunction of many exemptions, a named
//! disjunction of many credit limits any one of which a tier requires, and a chain of names
//! each joining the two before it are each held once and read once, near linear in `d`
//! (COMPLEXITY.md S31b).

use std::collections::BTreeMap;

use zed_kernel::term::build::{if_, let_, lit, prim, var};
use zed_kernel::{Prim, Term};
use zed_tests::scaling;
use zed_tests::step_helpers::l01_39_reduced_product::{
    all, approval_any_tier, either, ge, le, limits, names,
};
use zedc::store::product::{Arm, arms};

use super::ints;

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
        let tier = summary(&arms_of(approval_any_tier(d, k, true)));
        assert_eq!(tier, summary(&arms_of(approval_any_tier(d, k, false))));
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

/// The chain `a0 = x >= 0 && y >= 0`, `a1 = x >= 1 <join> a0` and `ai = x >= i <join> a(i-1)
/// <join> a(i-2)`, each a name when `named` and written out in full when not, and the test
/// `ad`. Written out it holds `a0` a number of times exponential in `d`; named, each name's
/// formula is held once, so a reader that reads a shared part at each place it is reached
/// from takes time exponential in `d`.
fn chain(d: usize, join: fn(Term, Term) -> Term, named: bool) -> Term {
    let name = |i: usize| format!("a{i}");
    let mut defs: Vec<Term> = Vec::new();
    for i in 0..=d {
        let at = |j: usize| {
            if named {
                var(&name(j))
            } else {
                defs[j].clone()
            }
        };
        let def = match i {
            0 => all(vec![ge("x", 0), ge("y", 0)]),
            1 => join(ge("x", 1), at(0)),
            _ => join(join(ge("x", i as i64), at(i - 1)), at(i - 2)),
        };
        defs.push(def);
    }
    if !named {
        return defs.pop().expect("the last name");
    }
    let mut body = var(&name(d));
    for (i, def) in defs.into_iter().enumerate().rev() {
        body = let_(&name(i), def, body);
    }
    body
}

fn and2(a: Term, b: Term) -> Term {
    prim(Prim::And, vec![a, b])
}

#[test]
fn a_chain_of_names_narrows_as_if_written_out() {
    for d in [1, 2, 5, 10] {
        let and = summary(&arms_of(chain(d, and2, true)));
        assert_eq!(and, summary(&arms_of(chain(d, and2, false))), "d = {d}");
        let x = format!("x=[{d}..]");
        assert_eq!(and[0].1[..2], [x, "y=[0..]".to_string()], "d = {d}");
        let or = summary(&arms_of(chain(d, either, true)));
        assert_eq!(or, summary(&arms_of(chain(d, either, false))), "d = {d}");
    }
}

/// Runs the scaling check of `arms` on `chain(d, join, true)` at d = 30 and 240.
fn chain_scaling(what: &str, join: fn(Term, Term) -> Term) {
    scaling::on_a_thread(1 << 29, || {
        let tests: BTreeMap<usize, Term> = [30, 240]
            .map(|d| (d, if_(chain(d, join, true), lit(1), lit(2))))
            .into();
        let scope = ints(&names());
        scaling::check(what, 30, |d| {
            std::hint::black_box(arms(&tests[&d], &scope));
        });
    });
}

/// Runs the scaling check of `arms` on `family(1, k, true)` at k = n and 8n: one tier, so that
/// the work is that of the chain of k limits alone.
fn limit_scaling(what: &str, n: usize, family: fn(usize, usize, bool) -> Term) {
    scaling::on_a_thread(1 << 29, || {
        let tests: BTreeMap<usize, Term> = [n, scaling::FACTOR * n]
            .map(|k| (k, if_(family(1, k, true), lit(1), lit(2))))
            .into();
        let scope = ints(&names());
        scaling::check(what, n, |k| {
            std::hint::black_box(arms(&tests[&k], &scope));
        });
    });
}

#[test]
fn arms_of_named_limits_in_side_by_side_tiers_narrow_as_with_each_tier_read_apart() {
    // The limits every tier needs are taken out of the disjunction of the tiers
    // (`presburger::factored`, ST-formula-sibling); the arms are those of the formula as
    // written, each tier with the limits, and those of the limits written out at each tier.
    use zedc::store::presburger::UNFACTORED;
    for (d, k) in [(1, 1), (2, 2), (3, 1), (5, 5), (8, 3)] {
        let now = summary(&arms_of(approval_any_tier(d, k, true)));
        UNFACTORED.with(|u| u.set(true));
        let as_written = summary(&arms_of(approval_any_tier(d, k, true)));
        UNFACTORED.with(|u| u.set(false));
        assert_eq!(now, as_written, "d = {d}, k = {k}");
        assert_eq!(now, summary(&arms_of(approval_any_tier(d, k, false))));
    }
}

mod bench;
