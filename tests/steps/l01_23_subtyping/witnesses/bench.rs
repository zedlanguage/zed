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
fn a_list_of_cycles_less_many_scales() {
    // KERNEL-witness-length-miss: a list less the classes 1 and 2 modulo `p²` for each of the
    // first `k` primes `p`, whose shares sum to less than one (twice the sum of `1 / p²`, below
    // 0.91), so a length is shown, chosen by conditional expectations on each prime in turn. The
    // first 14 and 25 primes are 16_514 and 131_592 definitions, 7.97 times as many; the
    // length is a big integer at either size. 8.15 times the instructions, 1x 0.11 s by `ns`,
    // load 31; the first 26 and 47 primes (151_994 and 1_219_172 definitions) ran past the 26 s
    // stop.
    let (a, b) = (14, 25);
    let primes = first_primes(b);
    let defs = |k: usize| primes[..k].iter().map(|p| 2 * p * p).sum::<usize>();
    let (n, m) = (defs(a), defs(b));
    assert_eq!((n, m), (16_514, 131_592));
    let less = |k: usize| {
        (primes[..k].iter()).fold(period(1, 0), |t, &p| {
            &(&t - &period(p * p, 1)) - &period(p * p, 2)
        })
    };
    let (small, large) = (less(a), less(b));
    let run = |t: &Type| {
        Type::forget_emptiness();
        assert_eq!(
            Type::tuple(vec![t.clone(), Type::int()]).verdict(),
            Verdict::Inhabited
        );
    };
    scaling::compare(
        &format!(
            "a list less two classes modulo the square of each of the first {a} and {b} primes: \
             {n} and {m} definitions, {:.2} times",
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

#[test]
fn a_list_of_cycles_less_many_disjoint_classes_scales() {
    // XR-wlen round 1 (Gemini seat): the even lists of a meet of prime cycles, less the classes
    // `2s + 1` modulo `2j` for `s < j <= t`, all odd and so disjoint from the even lists, each
    // its own cycle. The length is checked against every class taken out; that check took one
    // remainder of the lcm-sized length per class (`t²/2` of them) and now takes one per
    // distinct period (`t`). The classes cost the sum of `2j²` definitions, the cycles the sum
    // of their primes; the first odd primes are added until the two sizes are 8 times apart.
    // 17_782 and 142_511 definitions: 8.056 times the instructions with one remainder per
    // period (load 63), 8.057 with one per class (load 51, the old check run once and not
    // committed); through types the remainders are a small part of the work at these sizes,
    // so this is a scaling record of the family, not a control that tells the two apart.
    // 1x 0.21 s by `ns`.
    let defs_less = |t: usize| (1..=t).map(|j| 2 * j * j).sum::<usize>();
    let primes = first_primes(400);
    let defs_primes = |k: usize| primes[1..=k].iter().sum::<usize>();
    let size = |t: usize, k: usize| 2 + defs_less(t) + defs_primes(k);
    let (ta, ka, tb) = (24, 60, 48);
    let n = size(ta, ka);
    let kb = (ka..399)
        .find(|&k| size(tb, k) >= 8 * n)
        .expect("enough primes");
    let m = size(tb, kb);
    assert!((7.95..8.1).contains(&(m as f64 / n as f64)), "{n} and {m}");
    let list = |t: usize, k: usize| {
        let all = (primes[1..=k].iter()).fold(period(2, 0), |a, &p| &a & &period(p, 0));
        let less =
            Type::union_all((1..=t).flat_map(|j| (0..j).map(move |s| period(2 * j, 2 * s + 1))));
        &all - &less
    };
    let (small, large) = (list(ta, ka), list(tb, kb));
    let run = |t: &Type| {
        Type::forget_emptiness();
        assert_eq!(
            Type::tuple(vec![t.clone(), Type::int()]).verdict(),
            Verdict::Inhabited
        );
    };
    scaling::compare(
        &format!(
            "a meet of prime cycles less {} and {} odd classes: {n} and {m} definitions, {:.2} \
             times",
            ta * (ta + 1) / 2,
            tb * (tb + 1) / 2,
            m as f64 / n as f64
        ),
        1,
        || run(&small),
        || run(&large),
    );
}

/// The lists of the classes 1 to `p - 1` modulo `p`, one for each rotation of a single cycle of
/// `p` definitions: rotation `i` reaches the empty list after the lengths `l` with
/// `i + l = 0` modulo `p`. So the `p - 1` classes cost `p` definitions in all.
fn rotations(p: usize) -> Vec<Type> {
    let defs = (0..p)
        .map(|i| {
            let cons = Expr::Atom(
                "cons".into(),
                vec![Expr::Type(Type::int()), Expr::Ref((i + 1) % p, vec![])],
            );
            Def {
                name: format!("R{i}"),
                params: vec![],
                body: match i {
                    0 => Expr::Union(vec![Expr::Type(Type::atom("nil")), cons]),
                    _ => cons,
                },
            }
        })
        .collect();
    let mut all = Group::new(defs).unwrap().instance(vec![]);
    all.remove(0);
    all
}

#[test]
fn a_list_less_the_rotations_of_two_cycles_scales() {
    // PERF-residue-length-cost, family 3: the rule refuses, since the shares of the classes 1
    // to `p - 1` modulo `p` and 1 to `2p - 1` modulo `2p` sum past one. The length is then
    // chosen on every prime and checked; the lengths 0 modulo `2p` are left.
    let (a, b) = (521, 4169);
    let list = |p: usize| {
        let less = rotations(p).into_iter().chain(rotations(2 * p));
        &period(1, 0) - &Type::union_all(less)
    };
    let (small, large) = (list(a), list(b));
    let run = |t: &Type| {
        Type::forget_emptiness();
        assert_eq!(
            Type::tuple(vec![t.clone(), Type::int()]).verdict(),
            Verdict::Inhabited
        );
    };
    scaling::compare(
        &format!(
            "a list less the classes of the rotations of cycles of {a} and {b} definitions and \
             twice those, {:.2} times",
            b as f64 / a as f64
        ),
        1,
        || run(&small),
        || run(&large),
    );
}

#[test]
fn a_list_less_the_rotations_of_two_prime_cycles_scales() {
    // PERF-residue-length-cost, family 2: `residue_classes` splits on residues and runs
    // `shares` again on each split. The primes `p < q < 2p` give the classes 1 to `p - 1`
    // modulo `p` and half the classes 1 to `q - 1` modulo `q`, all rotations, so `p + q`
    // definitions; lengths 0 modulo `pq` are left.
    let ((p, q), (r, s)) = ((257, 263), (2053, 2063));
    let list = |p: usize, q: usize| {
        let less = rotations(p)
            .into_iter()
            .chain(rotations(q).into_iter().step_by(2));
        &period(1, 0) - &Type::union_all(less)
    };
    let (small, large) = (list(p, q), list(r, s));
    let run = |t: &Type| {
        Type::forget_emptiness();
        assert_eq!(
            Type::tuple(vec![t.clone(), Type::int()]).verdict(),
            Verdict::Inhabited
        );
    };
    scaling::compare(
        &format!(
            "a list less the rotations of cycles of the primes {p} and {q}, and {r} and {s}: \
             {:.2} times the definitions",
            (r + s) as f64 / (p + q) as f64
        ),
        1,
        || run(&small),
        || run(&large),
    );
}

#[test]
fn a_list_less_the_rotations_of_one_cycle_scales() {
    // PERF-residue-length-cost, family 1 (XR-wlen round 1, Gemini seat): a list less the
    // classes 1 to `m - 1` modulo `m`, which are the rotations of one cycle and so cost `m`
    // definitions, and less 0 and `m` modulo `3m` and `m` and `2m` modulo `6m`. The shares sum
    // to one and two of the classes meet (`m` modulo `3m` and modulo `6m`), so the lengths `5m`
    // modulo `6m` are left. The search for a meeting pair tried each pair of the `m + 3`
    // classes: 63.4 times the pair checks per 8 times the classes in the harness.
    let (a, b) = (521, 4169);
    let list = |m: usize| {
        let less = rotations(m).into_iter().chain([
            period(3 * m, 0),
            period(3 * m, m),
            period(6 * m, m),
            period(6 * m, 2 * m),
        ]);
        &period(1, 0) - &Type::union_all(less)
    };
    let (small, large) = (list(a), list(b));
    let run = |t: &Type| {
        Type::forget_emptiness();
        assert_eq!(
            Type::tuple(vec![t.clone(), Type::int()]).verdict(),
            Verdict::Inhabited
        );
    };
    scaling::compare(
        &format!(
            "a list less the classes of the rotations of a cycle of {a} and {b} definitions, \
             {:.2} times",
            b as f64 / a as f64
        ),
        1,
        || run(&small),
        || run(&large),
    );
}
