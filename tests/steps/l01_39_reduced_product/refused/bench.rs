//! Benchmarks of `refused`: each times the work at a size and at 8 times it, run apart from
//! the correctness tests (`tools/run_tests.sh --bench`).

use super::*;

/// `k` refused tests on disjoint names: assuming them one after another records one refusal
/// each, at a cost near linear in `k`.
#[test]
fn narrowing_by_many_refused_tests_scales() {
    use zed_tests::scaling::{self, FACTOR};
    use zedc::store::cell::Premises;
    let none = Premises::new();
    let (names, guards) = (refused_names, refused_guards);
    let n = 128;
    let inputs = [n, FACTOR * n].map(|k| {
        let ns = names(k);
        (super::super::ints(&ns), guards(&ns))
    });
    scaling::check("narrowing by refused tests", n, |k| {
        let (scope, guards) = &inputs[usize::from(k != n)];
        let s = guards
            .iter()
            .fold(scope.clone(), |s, g| s.assume(g, true, &none));
        assert_eq!(s.warnings().len(), k);
    });
}

/// The check of [`narrowing_by_many_refused_tests_scales`] is mostly the solver's work, about
/// 26M instructions per refused test since PERF-refused-assume (42M before it, 11M when it was
/// written, 2026-11-03; `one_refused_test_costs_at_most_a_fixed_number_of_instructions` below
/// holds it under a limit), so the refusals' own cost is measured alone: keeping `k` refusals,
/// each once, in a scope costs near linear in `k`.
#[test]
fn keeping_many_refusals_scales() {
    use zed_tests::scaling::{self, FACTOR};
    let names = refused_names;
    let n = 32_768;
    let refused = [n, FACTOR * n].map(|k| -> Vec<(Refused, Kept, Vec<Arc<str>>)> {
        names(k)
            .chunks(4)
            .map(|c| {
                let r = Refused {
                    constraint: growth_test([&*c[0], &*c[1], &*c[2], &*c[3]]).into(),
                    asked: Asked::Test { outcome: true },
                    cause: Refusal::Growth.into(),
                };
                let sets = c.iter().map(|n| (n.clone(), IntervalSet::top()));
                (r, Arc::new(sets.collect()), c.to_vec())
            })
            .collect()
    });
    let empty = super::super::ints(&[]);
    scaling::check("keeping refusals", n, |k| {
        let s = refused[usize::from(k != n)]
            .iter()
            .fold(empty.clone(), |mut s, (r, kept, on)| {
                s.refuse(r.clone(), kept.clone(), on);
                s
            });
        assert_eq!(s.refusals.len(), k);
    });
}

/// Finding the refusals on each of `k` names among `k` refusals in one scope costs near linear
/// in `k`: each look-up goes through the scope's index by name, and not through every refusal.
#[test]
fn finding_the_refusals_on_many_names_scales() {
    use zed_tests::scaling::{self, FACTOR};
    let n = 65_536;
    let scopes = [n, FACTOR * n].map(|k| {
        let names = refused_names(k);
        let s = names.chunks(4).fold(super::super::ints(&[]), |mut s, c| {
            let r = Refused {
                constraint: growth_test([&*c[0], &*c[1], &*c[2], &*c[3]]).into(),
                asked: Asked::Test { outcome: true },
                cause: Refusal::Growth.into(),
            };
            s.refuse(r, Arc::new(Default::default()), c);
            s
        });
        let firsts: Vec<Arc<str>> = names.chunks(4).map(|c| c[0].clone()).collect();
        (s, firsts)
    });
    scaling::check("finding the refusals on a name", n, |k| {
        let (s, firsts) = &scopes[usize::from(k != n)];
        let found: usize = (firsts.iter()).map(|x| s.refused_on([&**x]).len()).sum();
        assert_eq!(found, k);
    });
}

/// The join of two arms that share `k - 2` refused tests on disjoint names and add one refused
/// test each, and the join's warnings, cost near linear in `k`.
#[test]
fn the_join_of_arms_with_many_refused_tests_and_its_warnings_scale() {
    use zed_tests::scaling::{self, FACTOR};
    use zedc::store::cell::Premises;
    let none = Premises::new();
    let (names, guards) = (refused_names, refused_guards);
    // At sizes n and 8n: the scope after k - 2 shared tests, then each arm after one more.
    // Below n = 256 a fixed cost of about 2.8M instructions per join hides a union quadratic in
    // k. Two arms that each add many tests the other lacks are not measured here: that join was
    // superlinear before ST-join and is measured in `disjoint` (COMPLEXITY.md S29).
    let n = 256;
    let arms = [n, FACTOR * n].map(|k| {
        let ns = names(k);
        let gs = guards(&ns);
        let shared = gs[..k - 2]
            .iter()
            .fold(super::super::ints(&ns), |s, g| s.assume(g, true, &none));
        [k - 2, k - 1].map(|i| shared.assume(&gs[i], true, &none))
    });
    scaling::check("the join of refused arms", n, |k| {
        let [l, r] = &arms[usize::from(k != n)];
        assert_eq!(l.join(r).refusals.len(), k);
    });
    // The warnings of the joins, built before they are measured.
    let joins = arms.map(|[l, r]| l.join(&r));
    scaling::check("the warnings of a join of refused arms", n, |k| {
        assert_eq!(joins[usize::from(k != n)].warnings().len(), k);
    });
}

/// The instructions of one assume of a refused Growth test, the mean of 16 on disjoint names,
/// stay at most [`ASSUME_LIMIT`]. The scaling test above checks only the ratio from n to 8n, so
/// it did not catch the constant growing from about 15M (c3d19a6e, 2026-11-03) to about 41M
/// (465a54b5, 2026-11-10); PERF-refused-assume cut it to about 26M. Counts of processor time
/// vary too much with load for a fixed limit, so on a machine that cannot count instructions
/// the test measures nothing.
#[test]
fn one_refused_test_costs_at_most_a_fixed_number_of_instructions() {
    use zed_tests::scaling::Meter;
    use zedc::store::cell::Premises;
    let mut meter = Meter::new();
    if meter.unit() != "instructions" {
        return;
    }
    let none = Premises::new();
    let k = 16;
    let ns: Vec<Arc<str>> = (0..4 * k).map(|i| format!("v{i}").into()).collect();
    let gs: Vec<Term> = ns.chunks(4).map(growth_term).collect();
    let scope = super::super::ints(&ns);
    let run = || {
        let s = gs
            .iter()
            .fold(scope.clone(), |s, g| s.assume(g, true, &none));
        assert_eq!(s.warnings().len(), k);
    };
    let least = (0..2)
        .map(|_| meter.work(run).units)
        .min()
        .expect("two runs");
    let each = least / k as u64;
    let load = std::fs::read_to_string("/proc/loadavg")
        .map(|l| l.split(' ').next().unwrap_or("").to_string())
        .unwrap_or_default();
    eprintln!("one refused test: {each} instructions (limit {ASSUME_LIMIT}), load {load}");
    assert!(
        each <= ASSUME_LIMIT,
        "one refused test took {each} instructions, more than {ASSUME_LIMIT} (load {load})"
    );
}
