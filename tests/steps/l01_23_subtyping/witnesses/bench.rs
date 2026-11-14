//! The benchmarks of `witnesses.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `witnesses.rs`.

use super::*;

#[test]
fn a_list_of_a_period_is_shown_in_linear_time() {
    // The list is kept as its length, `n - 1`; the work is the walk of the cycle of `n`
    // definitions.
    scaling::check("a list of a period, by period", 64, |n| {
        let t = Type::tuple(vec![period(n, n - 1), Type::int()]);
        assert_eq!(t.verdict(), Verdict::Inhabited);
    });
}

#[test]
fn the_meet_of_prime_cycles_scales() {
    // Ten primes are 129 definitions, twenty-five are 1060, 8.2 times as many; the shortest
    // lists have about 10^10 and 10^36 links.
    let (small, large) = (prime_cycles(10), prime_cycles(25));
    let defs = |k: usize| PRIMES[..k].iter().sum::<usize>();
    assert_eq!((defs(10), defs(25)), (129, 1060));
    let run = |t: &Type| {
        Type::forget_emptiness();
        assert_eq!(t.verdict(), Verdict::Inhabited);
        assert_eq!(
            Type::tuple(vec![t.clone(), Type::int()]).verdict(),
            Verdict::Inhabited
        );
    };
    scaling::compare(
        "a meet of cycles, the first 10 and 25 primes: 129 and 1060 definitions, 8.2 times",
        1,
        || run(&small),
        || run(&large),
    );
}

#[test]
fn a_union_of_cycles_less_one_scales() {
    // Each class of the union is tested by one lookup in the residues covered modulo its
    // period, built once per period over its divisors: O(n log n) in the definitions. The naive
    // form, each class of the union decided against every class taken out by the rule on
    // residues, is the classes squared, n^(4/3) here: run once and not committed, it took
    // 11.5 times the work where this rule took 8.2 (REFUSAL-periodic-split).
    let ((small, n), (large, m)) = (halves(16), halves(32));
    assert_eq!((n, m), (13476, 111240));
    let run = |t: &Type| {
        Type::forget_emptiness();
        assert_eq!(t.verdict(), Verdict::Empty);
    };
    scaling::compare(
        &format!(
            "a union of cycles less a union holding each: {n} and {m} definitions, 8.25 times"
        ),
        1,
        || run(&small),
        || run(&large),
    );
}
