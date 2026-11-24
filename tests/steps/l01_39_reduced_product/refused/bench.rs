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
///
/// The scopes are built by `check_inputs`, only at the sizes this process runs: built at both
/// before the first run, under DynamoRIO, the first phase passed its limit of 20 s (rc 124 on
/// l43, b22-tests8 job f2, FAIL-bench-pieces-past-limit-on-main).
#[test]
fn finding_the_refusals_on_many_names_scales() {
    use zed_tests::scaling;
    let n = 65_536;
    let scope = |k: usize| {
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
        (k, s, firsts)
    };
    scaling::check_inputs(
        "finding the refusals on a name",
        n,
        scope,
        |(k, s, firsts)| {
            let found: usize = (firsts.iter()).map(|x| s.refused_on([&**x]).len()).sum();
            assert_eq!(found, *k);
        },
    );
}

/// The join of two arms that share `k - 2` refused tests on disjoint names and add one refused
/// test each, and the join's warnings, cost near linear in `k`.
///
/// The arms are built by `check_inputs`, only at the sizes this process runs: built at both
/// before the first run, under DynamoRIO, the first phase passed its limit of 20 s (rc 124 on
/// l43, b22-tests8 job f2, FAIL-bench-pieces-past-limit-on-main). The join and its warnings
/// are measured in one run, on one input: as two checks, the second check's process for 8n
/// built the arms at 2048 again, by 2046 assumes, after replaying the first check's input at
/// 256, and wrote no line in 20 s (job f16 on v5e1, FAIL-bench-refused-join-past-limit). The
/// sum of two costs grows near linearly only when each does, so a quadratic part of either
/// still fails the check, once it is large next to the rest at 8n. The piece still stops on a
/// VM: the one process for 8n, started 6.5 s into the piece, writes no line in 20 s, its
/// set-up being the 2046 assumes under DynamoRIO (job f33 on hm3, load 3; open).
#[test]
fn the_join_of_arms_with_many_refused_tests_and_its_warnings_scale() {
    use zed_tests::scaling;
    use zedc::store::cell::Premises;
    let none = Premises::new();
    let (names, guards) = (refused_names, refused_guards);
    // At sizes n and 8n: the scope after k - 2 shared tests, then each arm after one more.
    // Below n = 256 a fixed cost of about 2.8M instructions per join hides a union quadratic in
    // k. Two arms that each add many tests the other lacks are not measured here: that join was
    // superlinear before ST-join and is measured in `disjoint` (COMPLEXITY.md S29).
    let n = 256;
    let arms = |k: usize| {
        let ns = names(k);
        let gs = guards(&ns);
        let shared = gs[..k - 2]
            .iter()
            .fold(super::super::ints(&ns), |s, g| s.assume(g, true, &none));
        (
            k,
            [k - 2, k - 1].map(|i| shared.assume(&gs[i], true, &none)),
        )
    };
    let what = "the join of refused arms and its warnings";
    scaling::check_inputs(what, n, arms, |(k, [l, r])| {
        let j = l.join(r);
        assert_eq!(j.refusals.len(), *k);
        assert_eq!(j.warnings().len(), *k);
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
