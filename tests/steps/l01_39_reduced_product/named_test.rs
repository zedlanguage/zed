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

#[test]
fn arms_of_a_wide_named_conjunction_at_each_tier_take_time_near_linear_in_the_depth() {
    // k = d credit limits named once and required at each of d tiers. Measured on the branch
    // of ST-formula-share, in instructions at d = 30, 60, 120, 240: 1.18, 3.87, 14.8, 59.0 G
    // (about 4 times per doubling); written out at each tier 12.1, 56.0, 251 G at d = 30 to
    // 120. That code flattened the shared conjunction into each tier's conjunction; on
    // origin/main ae9b63e9 this test fails at 36.4 times the bytes (limit 24). `Formula::and`
    // now keeps the named conjunction whole and `Parts::of` reads it once: 10.0 times the
    // instructions and 8.8 times the bytes from d = 30 to 240.
    wide_scaling(
        "arms of k = d credit limits named once, required at each of d tiers",
        approval_within,
    );
}

#[test]
fn arms_of_a_wide_named_disjunction_at_each_tier_take_time_near_linear_in_the_depth() {
    // k = d exemptions named once, any of which approves at each of d tiers. Measured on the
    // branch of ST-formula-share, in instructions at d = 30, 60, 120, 240: 0.37, 1.14, 3.88,
    // 14.2 G (3.1 to 3.7 times per doubling); written out at each tier 7.5, 33.7, 150 G at
    // d = 30 to 120. That code flattened the shared disjunction into each tier's disjunction;
    // on origin/main ae9b63e9 this test fails at 41.6 times the bytes. `Formula::or` now keeps
    // the named disjunction whole: 13.9 times the instructions and 12.3 times the bytes.
    wide_scaling(
        "arms of k = d exemptions named once, any of which approves at each of d tiers",
        approval_exempt,
    );
}

#[test]
fn arms_of_a_wide_named_disjunction_required_at_each_tier_take_time_near_linear_in_the_depth() {
    // Any one of k = d credit limits, named once, required of a small request at each of d
    // tiers. Measured by ST-formula-share verify#2, in instructions at d = 30, 60, 120, 240:
    // 2.76, 10.4, 40.2, 157.6 G (3.8 times per doubling), 0.73 to 39.6 GB allocated; written
    // out at each tier, d = 30, 60 and 120 did not finish in 300 s together. The test fails at
    // 54.1 times the bytes (limit 24) on origin/main ae9b63e9. `Parts::of` now makes the
    // disjunction once and skips it at each tier below the first that conjoined it: 9.7 times
    // the instructions and 8.9 times the bytes.
    wide_scaling(
        "arms of any of k = d credit limits named once, required at each of d tiers",
        approval_any_limit,
    );
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

#[test]
fn arms_of_a_chain_of_named_conjunctions_take_time_near_linear_in_its_length() {
    // With the named conjunctions kept whole, and `project_parts` and `Conjuncts::and` reading
    // a shared part at each path to it, 82 s at d = 28 (about 1.618 to the d); read once,
    // 10.6 times the instructions and 11.1 times the bytes from d = 30 to 240. Without the
    // `project_parts` memo it did not finish in 100 s.
    chain_scaling(
        "arms of d names, each the conjunction of the two before it",
        and2,
    );
}

#[test]
fn arms_of_a_chain_of_named_disjunctions_take_time_near_linear_in_its_length() {
    // Read once per base and symbols in `project_parts`, 7.6 times the instructions and the
    // bytes from d = 30 to 240. Without that memo it did not finish in 100 s, and on
    // origin/main ae9b63e9 it did not finish in 150 s.
    chain_scaling(
        "arms of d names, each the disjunction of the two before it",
        either,
    );
}

/// The approval where any of `d` tiers approves, tier `i` a request of size `z` at most `i`
/// that waited at least `i`, each tier needing every one of `k` credit limits, named once.
/// The tiers are side by side, so the limits are a conjunct of each disjunct.
fn approval_any_tier(d: usize, k: usize, named: bool) -> Term {
    let tiers = |t: &dyn Fn() -> Term| {
        (0..d as i64)
            .map(|i| all(vec![t(), ge("w", i), le("z", i)]))
            .reduce(either)
            .expect("a tier")
    };
    if named {
        let_("t", all(limits(k)), tiers(&|| var("t")))
    } else {
        tiers(&|| all(limits(k)))
    }
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
fn arms_of_a_named_conjunction_of_k_limits_take_time_near_linear_in_k() {
    // The translator made the conjunction of each prefix of `l0 && l1 && ...` in turn, copying
    // and tightening the prefix again at each limit: k² (ST-formula-k2). At k = 240 and 1920, on
    // origin/main 64781908 this test fails at 39.8 times the bytes (0.47 to 18.7 GB; limit 24;
    // at k = 120 and 960 only 27.7 times). Joined in one pass (`Tx::chain`): 1.16 to 9.61 G
    // instructions (8.3 times) and 7.6 times the bytes, 2.4 s.
    limit_scaling(
        "arms of a conjunction of k credit limits named once",
        240,
        approval_within,
    );
}

#[test]
fn arms_of_a_named_disjunction_of_k_limits_take_time_near_linear_in_k() {
    // As for the conjunction, the disjunction of each prefix of `l0 || l1 || ...` was made in
    // turn (ST-formula-k2). At k = 240 and 1920, on origin/main 64781908 this test fails at 35.7
    // times the bytes (0.53 to 18.8 GB; at k = 120 and 960 only 25.3 times). Joined in one
    // pass: 1.21 to 9.41 G instructions (7.7 times) and 7.6 times the bytes, 2.6 s.
    limit_scaling(
        "arms of any of k credit limits named once, required of a small request",
        240,
        approval_any_limit,
    );
}

#[test]
fn arms_of_k_named_exemptions_take_time_near_linear_in_k() {
    // A disjunction of k exemptions beside the tier's own disjuncts (ST-formula-k2). On
    // origin/main 64781908 this test fails at 38.8 times the bytes (0.12 to 4.55 GB). Joined in
    // one pass: 0.29 to 2.36 G instructions (8.3 times) and 7.6 times the bytes.
    limit_scaling(
        "arms of any of k exemptions named once",
        120,
        approval_exempt,
    );
}

#[test]
fn arms_of_a_tier_needing_k_named_limits_take_time_near_linear_in_k() {
    // A conjunction of k limits as a conjunct of the tier's disjunct (ST-formula-k2). On
    // origin/main 64781908 this test fails at 36.5 times the bytes (0.12 to 4.37 GB). Joined in
    // one pass: 0.36 to 3.72 G instructions (10.4 times) and 8.7 times the bytes.
    limit_scaling(
        "arms of a tier needing k credit limits named once",
        120,
        approval_any_tier,
    );
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

#[test]
fn arms_of_named_limits_in_side_by_side_tiers_take_time_near_linear_in_the_depth() {
    // k = d credit limits named once, needed by each of d tiers side by side. Each disjunct
    // held the limits, and the projection read them in each: on origin/main d6d1840d, in
    // instructions at d = 30, 60, 120, 240: 0.834, 2.96, 11.5, 46.6 G (55.9 times), 0.128 to
    // 5.97 GB allocated (46.6 times). With the limits taken out of the disjunction
    // (`presburger::factored`): 0.267, 0.535, 1.08, 2.16 G (8.1 times), 0.044 to 0.350 GB
    // (8.0 times).
    wide_scaling(
        "arms of k = d credit limits named once, needed by each of d tiers side by side",
        approval_any_tier,
    );
}

#[test]
#[ignore]
fn pncx_tiers_axis() {
    scaling::on_a_thread(1 << 29, || {
        let mut meter = scaling::Meter::new();
        for d in std::env::var("PNCX_SIZES")
            .unwrap()
            .split(',')
            .map(|s| s.parse().unwrap())
        {
            let term = if_(approval_any_tier(d, d, true), lit(1), lit(2));
            let scope = ints(&names());
            let work = meter.work(|| {
                std::hint::black_box(arms(&term, &scope));
            });
            println!(
                "TIERS n={d} work={} bytes={} unit={}",
                work.units,
                work.bytes,
                meter.unit()
            );
        }
    });
}
