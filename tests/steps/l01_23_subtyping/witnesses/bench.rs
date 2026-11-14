//! The benchmarks of `witnesses.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `witnesses.rs`.

use super::*;

#[test]
fn a_list_of_a_period_is_shown_in_linear_time() {
    // The list is kept as its length, `n - 1`; the work is the walk of the cycle of `n`
    // definitions.
    // TEST-bench-move-l0123, author P169: period 64 before, now 12_288; 1x 0.31 s by `ns`,
    // load 28.
    scaling::check("a list of a period, by period", 12_288, |n| {
        let t = Type::tuple(vec![period(n, n - 1), Type::int()]);
        assert_eq!(t.verdict(), Verdict::Inhabited);
    });
}

/// The first `k` primes, by trial division by the primes before: `O(k sqrt(p_k))` divisions,
/// a few hundred thousand at the sizes used, made before any run is timed.
fn first_primes(k: usize) -> Vec<usize> {
    let mut primes: Vec<usize> = Vec::with_capacity(k);
    let mut p = 2;
    while primes.len() < k {
        if (primes.iter())
            .take_while(|&&q| q * q <= p)
            .all(|&q| p % q != 0)
        {
            primes.push(p);
        }
        p += 1;
    }
    primes
}

#[test]
fn the_meet_of_prime_cycles_scales() {
    // Ten primes were 129 definitions and twenty-five 1060, 8.2 times as many; the shortest
    // lists have about 10^10 and 10^36 links. TEST-bench-move-l0123, author P169: the first
    // 10 and 25 primes (`PRIMES`) before, measured at 0.99 ms for the first at load 35 (that
    // is, at the old size); now the first 100 and 257 primes, made here, since `PRIMES` holds
    // 25; 1x 0.44 s by `ns`, load 60. The shortest list's length, the product of the primes
    // less one, is a big integer at either size.
    let (a, b) = (100, 257);
    let primes = first_primes(b);
    let defs = |k: usize| primes[..k].iter().sum::<usize>();
    let (n, m) = (defs(a), defs(b));
    assert!((8.0..8.1).contains(&(m as f64 / n as f64)), "{n} and {m}");
    let meet = |k: usize| (primes[..k].iter()).fold(Type::top(), |t, &p| &t & &period(p, p - 1));
    let (small, large) = (meet(a), meet(b));
    let run = |t: &Type| {
        Type::forget_emptiness();
        assert_eq!(t.verdict(), Verdict::Inhabited);
        assert_eq!(
            Type::tuple(vec![t.clone(), Type::int()]).verdict(),
            Verdict::Inhabited
        );
    };
    scaling::compare(
        &format!(
            "a meet of cycles, the first {a} and {b} primes: {n} and {m} definitions, {:.2} times",
            m as f64 / n as f64
        ),
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
    // 11.5 times the work where this rule took 8.2 (REFUSAL-periodic-split; at the old sizes,
    // 16 and 32). TEST-bench-move-l0123, author P169: `halves(16)` and `halves(32)` before,
    // 13476 and 111240 definitions; now `halves(24)` and `halves(48)`, 46446 and 379308
    // definitions; 1x 0.17 s by `ns`, load 36. `halves(32)` and `halves(64)` ran past the
    // 25 s stop at 3.5 GB.
    let ((small, n), (large, m)) = (halves(24), halves(48));
    assert_eq!((n, m), (46_446, 379_308));
    let run = |t: &Type| {
        Type::forget_emptiness();
        assert_eq!(t.verdict(), Verdict::Empty);
    };
    scaling::compare(
        &format!(
            "a union of cycles less a union holding each: {n} and {m} definitions, {:.2} times",
            m as f64 / n as f64
        ),
        1,
        || run(&small),
        || run(&large),
    );
}
