//! The natural coprime base of word inputs, and which of them share a prime, found by factoring
//! each input into primes (PERF-negated-chain-unsolved, negchain1, 2026-11-20). zed-kernel
//! `num::coprime` takes these on many word inputs under its measured switchover
//! `FACTOR_BITS`; the general method there is Bernstein's, on product and remainder trees.

use std::collections::HashMap;

use crate::factor::factor;
use crate::word::gcd_u64;

/// The distinct primes of the inputs and, for each, the inputs it divides with their
/// exponents: `primes[j]` divides input `i` exactly `e` times for each `(i, e)` of
/// `entries[starts[j]..starts[j + 1]]`, those in increasing order of `i`. The primes are in
/// order of their first input. Every input must be above 0; a 1 has no prime.
struct ByPrime {
    primes: Vec<u64>,
    starts: Vec<usize>,
    entries: Vec<(u32, u64)>,
}

// Complexity tradeoff: one `factor` per input, then one hash lookup per (prime, input) pair
// (at most 15 an input, as the product of the first 16 primes passes 2^64) and a counting sort
// of the pairs by the prime's slot, O(k) for `k` inputs beside the factoring, in expectation
// over the hash (std's SipHash with a random key). A comparison sort of the pairs by prime
// would cost O(k log k): 9.6 times the work at 8 times the inputs in a trial (2026-11-20),
// above the goal 9. The cost of `factor` is in the comment of `coprime_base_by_factoring`.
fn by_prime(xs: &[u64]) -> ByPrime {
    let mut slot_of: HashMap<u64, usize> = HashMap::new();
    let mut primes: Vec<u64> = Vec::new();
    // (slot of the prime, input, exponent), in input order.
    let mut seen: Vec<(usize, u32, u64)> = Vec::new();
    for (i, &x) in xs.iter().enumerate() {
        assert!(x != 0, "a coprime base of positive integers, given 0");
        let i = u32::try_from(i).expect("fewer than 2^32 inputs");
        for (p, e) in factor(x) {
            let slot = *slot_of.entry(p).or_insert_with(|| {
                primes.push(p);
                primes.len() - 1
            });
            seen.push((slot, i, e));
        }
    }
    // Counting sort by slot, stable, so each prime's inputs stay in increasing order.
    let mut starts = vec![0usize; primes.len() + 1];
    for &(slot, _, _) in &seen {
        starts[slot + 1] += 1;
    }
    for j in 0..primes.len() {
        starts[j + 1] += starts[j];
    }
    let mut next = starts.clone();
    let mut entries = vec![(0u32, 0u64); seen.len()];
    for (slot, i, e) in seen {
        entries[next[slot]] = (i, e);
        next[slot] += 1;
    }
    ByPrime {
        primes,
        starts,
        entries,
    }
}

/// The natural coprime base `cb S` of the word inputs `xs`, each above 0, and the multiplicity
/// of each element in each input, by increasing element: the contract of
/// [`crate::coprime_base_u64`]. The elements are in order of their least prime's first input.
///
/// Method: factor each input into primes. For a prime `p` let `v_p` be its vector of exponents
/// over the inputs, `l_p >= 1` the gcd of its entries and `w_p = v_p / l_p`. Two primes are in
/// one class when their `w` are equal; the element of a class `C` is `E_C = prod_{p in C}
/// p^(l_p)`, and its multiplicity in input `i` is the common `w_p[i]`.
///
/// Proof that the elements are `cb S`, with `T` the closure of the inputs `S` and Theorem 7.3
/// of D. J. Bernstein, "Factoring into coprimes in essentially linear time", J. Algorithms
/// 54(1), 2005, pp. 1-30, doi:10.1016/j.jalgor.2004.04.009, Section 7 (read 2026-11-19 in the
/// author's preprint, as cited in zed-kernel `num/coprime.rs`; checked again 2026-11-20: the
/// DOI's identity by allpapers-locate, no new reading): `T` is the least set holding `S` and 1
/// closed under products, exact quotients and gcds, and "Let P be a coprime base for S ... If
/// P ⊆ T − {1} then P = cb S". (This is the definition the zed-kernel test helper `by_primes`
/// states; the steps below write out the argument its comment sketches.)
/// 1. Let `Q` be the output of [`crate::coprime_base_u64`] on the same inputs: a coprime base
///    of `S` inside `T - {1}` (steps 2 to 4 of its proof), so `Q = cb S` by Theorem 7.3. It
///    is left to show that `Q` is the set of the `E_C`.
/// 2. Each prime `p` of an input lies in exactly one `q` of `Q`: the input is a product of
///    powers of `Q`, so some `q` holds `p`, and the `q` are pairwise coprime.
/// 3. For `q` in `Q` let `a_q[i]` be its multiplicity in input `i`, so input `i` is
///    `prod_q q^(a_q[i])` and, for `p | q`, `v_p = ord_p(q) a_q` (step 2: no other `q` holds
///    `p`). So all primes of `q` have proportional `v`, so equal `w`: they lie in one class.
/// 4. For `p`, `p'` of one class let `f_p(t) = ord_p(t) / l_p`. On each input `f_p = w_p[i] =
///    f_p'`; both are 0 on 1; both are additive on products and subtractive on exact quotients;
///    and `f_p(gcd(a, b)) = min(f_p(a), f_p(b))`, as `ord_p(gcd(a, b)) = min(ord_p a, ord_p b)`
///    and `l_p > 0`. So the set of `t` with `f_p(t) = f_p'(t)` holds `S` and 1 and is closed,
///    so it holds `T`, and so every `q` of `Q`. Hence if `p | q` then `f_p'(q) = f_p(q) > 0`,
///    and `p' | q`: each `q` holds whole classes, and by step 3 exactly one, `C`.
/// 5. With `t_q` the common `f_p(q)` over `C` (step 4), `q = prod_{p in C} p^(t_q l_p) =
///    E_C^(t_q)`. And `t_q = 1`: `v_p = t_q l_p a_q` (step 3), so the gcd of its entries,
///    `l_p`, is `t_q l_p g` for `g` the gcd of `a_q`, so `t_q g = 1`.
/// 6. Every class has a prime of an input, which some `q` holds (step 2). So `Q` is the set of
///    the `E_C`, each once.
/// 7. The multiplicities: input `i` is `prod_p p^(v_p[i]) = prod_C E_C^(w_C[i])`, and the `E_C`
///    are pairwise coprime, so `w_C[i]` is the multiplicity of `E_C` in it.
///
/// Each `E_C` is a word: `w_C` is not 0 (the gcd of its entries is 1), so some input `i` has
/// `w_C[i] >= 1`, and `E_C^(w_C[i])` divides it (step 7).
///
/// Cost: `factor` on each input, then O(k) for `k` inputs (at `by_prime`), in expectation over
/// the hash. `factor` of a prime or of a product of primes below 38 is deterministic:
/// Miller-Rabin with the bases that decide every 64-bit number, O(log n) word products (cited
/// at `is_prime`), after a division by each prime up to 37. Splitting a composite runs
/// Pollard's rho in Brent's form with `c = 1` (R. P. Brent 1980, doi:10.1007/BF01933190), and
/// R. S. Lehman's method (Math. Comp. 28, 1974, doi:10.1090/S0025-5718-1974-0340163-2) when
/// that run ends without a factor; both end on every input (proved at `factor::rho` and
/// `factor::lehman_search`). Rho's O(sqrt p) expected products for the least prime `p` is
/// Pollard's heuristic, not a theorem (the walk is a fixed polynomial, not a random function):
/// about `2^(b/4)` products for a balanced product of two primes of `b / 2` bits, which is why
/// the kernel takes this path only up to its measured switchover `FACTOR_BITS` (44).
///
/// Below 2^44 the cost of `factor` on one input is bounded by a proved constant `C_44`, with no
/// heuristic (PROOF-factored-coprime-cost, 2026-11-20; every step in the cost comment at
/// `factor.rs`): the run with `c = 1` on a composite stops no later than the run on its
/// least prime, which is below 2^22, and the run on every odd prime below 2^22 is computed once
/// by the test `factor::tests::the_rho_cost_below_2_22_is_the_table` (at most 25854 steps,
/// 9471 products and 80 gcds, then at most 128 steps and gcds back); Lehman's method is at most
/// 26006 divisions and 65019 tries at `n < 2^44`; there are at most 26 splits and 53 primality
/// tests an input. So `k` inputs of at most 44 bits cost at most `C_44 k` in `factor`, plus
/// O(k) in expectation over the hash for the rest: linear in `k`. Wider inputs (which the
/// kernel never sends here) still end, with a finite largest cost `C_b` at each width, but its
/// size above 44 bits rests on the heuristic. Tests:
/// `tests::the_factored_coprime_base_is_natural` (against [`crate::coprime_base_u64`]), and in
/// zed-kernel `num::coprime::tests`.
// Complexity tradeoff: factor refinement ([`crate::coprime_base_u64`]) costs O(k^2) word gcds;
// Bernstein's algorithms on trees (zed-kernel `num::coprime::by_halves`) cost O(M(N) log^2 N)
// for `N` bits, measured at 12.8 to 16.3 times the work at 8 times the word inputs
// (zed-kernel `num::bench::the_coprime_base_of_*`, PERF-negated-chain-unsolved); this is
// linear in `k` beside the factoring, which costs a fixed amount for each input of a fixed
// width.
pub fn coprime_base_by_factoring(xs: &[u64]) -> (Vec<u64>, Vec<Vec<(u32, u64)>>) {
    let ByPrime {
        primes,
        starts,
        mut entries,
    } = by_prime(xs);
    // `w_p` in place of `v_p`, with `l_p` kept.
    let mut ls: Vec<u64> = Vec::with_capacity(primes.len());
    for j in 0..primes.len() {
        let run = &mut entries[starts[j]..starts[j + 1]];
        let l = run.iter().fold(0, |g, &(_, e)| gcd_u64(g, e));
        for (_, e) in run.iter_mut() {
            *e /= l;
        }
        ls.push(l);
    }
    let mut class_of: HashMap<&[(u32, u64)], usize> = HashMap::new();
    let mut elements: Vec<u64> = Vec::new();
    let mut classes: Vec<&[(u32, u64)]> = Vec::new();
    for (j, (&p, &l)) in primes.iter().zip(&ls).enumerate() {
        let w = &entries[starts[j]..starts[j + 1]];
        let c = *class_of.entry(w).or_insert_with(|| {
            elements.push(1);
            classes.push(w);
            elements.len() - 1
        });
        // A word: `p^l` divides `E_C`, which is a word (the proof above).
        let power = u32::try_from(l)
            .ok()
            .and_then(|l| p.checked_pow(l))
            .expect("p^l_p divides a word input");
        elements[c] = elements[c]
            .checked_mul(power)
            .expect("an element divides a word input");
    }
    let mut exponents: Vec<Vec<(u32, u64)>> = vec![Vec::new(); xs.len()];
    // By increasing class, so each input's list is in increasing order of element.
    for (c, w) in classes.iter().enumerate() {
        let c = u32::try_from(c).expect("at most 15 elements for each input");
        for &(i, k) in *w {
            exponents[i as usize].push((c, k));
        }
    }
    (elements, exponents)
}

/// For each of the word inputs `xs`, each above 0, whether it shares a prime with another of
/// them: so when one of its primes divides another input. Equal inputs above 1 share; a 1
/// shares none. The contract of zed-kernel `num::coprime::shares_a_factor`.
///
/// Cost: that of `by_prime`, `factor` on each input and O(k) beside it in expectation; the
/// cost of `factor` is in the comment of [`coprime_base_by_factoring`]. Tests:
/// `tests::the_factored_shares_agree_with_pairwise_gcds`, and in zed-kernel
/// `num::coprime::tests`.
// Complexity tradeoff: the kernel's general method is the product and remainder trees,
// O(M(B) log k) for `B` bits, measured at 16.1 times the work at 8 times the values on U1's
// moduli `2 p` (PERF-negated-chain-unsolved); this is linear in `k` beside the factoring.
pub fn shares_a_factor_by_factoring(xs: &[u64]) -> Vec<bool> {
    let ByPrime {
        starts, entries, ..
    } = by_prime(xs);
    let mut out = vec![false; xs.len()];
    for w in starts.windows(2) {
        let run = &entries[w[0]..w[1]];
        if run.len() > 1 {
            for &(i, _) in run {
                out[i as usize] = true;
            }
        }
    }
    out
}
