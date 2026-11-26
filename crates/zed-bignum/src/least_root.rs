//! The least root of an integer, `b == r ^ m` with `r` no perfect power, and the residues of a
//! number modulo many words by one remainder tree. Moved here from zedc-int (`int.rs`) on
//! 2026-11-23 so that the kernel's printer of integers (zed-kernel `Rat::integer_text`, plan row
//! KEPT-power-form-print) and zedc-int's kept integers share one routine.

use num_bigint::BigUint;
use num_traits::{One, ToPrimitive, Zero};
use zed_numtheory::{
    inverse_mod_2_64, is_prime, odd_primes_below, odd_root_mod_2_64, pow_mod, pow_mod_2_64,
    rem_big_u64,
};

use crate::fast::{self, mul as mul_uint, pow as pow_uint};
use crate::trees;
use zed_numtheory::BitLen;

/// `(s, r)` with `s = floor(sqrt(a))` and `r = a - s^2`, so `0 <= r <= 2s`, for integers held
/// outside a `Rat`: Zimmermann's Karatsuba square root (P. Zimmermann, "Karatsuba Square
/// Root", INRIA research report RR-3805, 1999, <https://inria.hal.science/inria-00072854>; R. P.
/// Brent and P. Zimmermann, Modern Computer Arithmetic, Cambridge University Press, 2010,
/// section 1.5, algorithm SqrtRem), on the kernel's product and division. The algorithm, for
/// `a` of `n` bits with `n = 0` or `3` mod 4 (else `4a` is taken, below):
/// `k = floor((n + 1) / 4)`, `B = 2^k`, `a = a_hi B^2 + a1 B + a0` with `a1, a0 < B`;
/// `(s', r') = sqrt_rem(a_hi)`; `(q, u) = div_rem(r' B + a1, 2s')`; `s = s' B + q`,
/// `r = u B + a0 - q^2`; when `r < 0`, `r += 2s - 1` and `s -= 1`. It is here, beside its
/// user [`least_root`], and not in `num.rs`, which re-exports it, so that this file imports
/// nothing of `num.rs` and the two make no import cycle (step S.1f, KEPT-power-form-print).
///
/// Proof, every step (checked by `square_roots_agree_with_num_bigint` against num-bigint's
/// `sqrt`, at every width from 1 to 640 bits and at the remainders 0, 1, `2s - 1` and `2s`):
/// 1. `4k` is `n` or `n + 1`, so `a_hi`, of `n - 2k` bits, that is `2k` or `2k - 1`, has
///    `B^2 / 4 <= a_hi < B^2`; so `B / 2 <= s' < B`, and `0 <= r' <= 2s'`.
/// 2. `s^2 + r = s'^2 B^2 + (2s'q + u) B + a0 = s'^2 B^2 + (r' B + a1) B + a0 = a`.
/// 3. `r <= 2s`: `u <= 2s' - 1` and `a0 <= B - 1`, so `r < 2s' B <= 2s`. So `(s + 1)^2 =
///    s^2 + 2s + 1 > a`, and `s >= floor(sqrt(a))`.
/// 4. `r >= 1 - 2s`: `q <= (r' B + a1) / 2s' <= (2s' B + B - 1) / 2s' < B + 1`, as `s' >= B/2`,
///    so `q <= B`; then `(q - 1)^2 < B^2 <= 2s' B`, so `q^2 <= 2s' B + 2q - 2`, and
///    `r >= -q^2 >= 1 - 2s` (as `2s = 2s' B + 2q`). So `(s - 1)^2 = s^2 - 2s + 1 <= a`, and
///    `s - 1 <= floor(sqrt(a)) <= s`: one correction, when `r < 0`, gives
///    `r + 2s - 1 = a - (s - 1)^2`, at least 0 by this step.
/// 5. For `n = 1` or `2` mod 4, `4a` has `n + 2` bits, `0` or `3` mod 4. With `S' =
///    floor(sqrt(4a)) = floor(2 sqrt(a))`, `S = floor(S' / 2) = floor(sqrt(a))`; writing `S' =
///    2S + e`, `e` in {0, 1}, `r' = 4a - S'^2 = 4(a - S^2) - 4Se - e`, so `a - S^2 = (r' + e(4S +
///    1)) / 4`, with no square.
/// 6. At most 128 bits it is `u128::isqrt`. Above, `n > 128` gives `k >= 32`, and `a_hi` has
///    about `n / 2` bits, so the recursion ends after about `log2(n / 64)` levels.
///
/// Complexity tradeoff: num-bigint's `sqrt` is Newton's iteration on num-bigint's division
/// and Toom-3 product, both above O(M(n)): 0.56 s at 1,661,955 bits and 19.2 s at 13,295,631
/// (34.5 times for 8 times the bits; `least_root`, then in zedc-int, item
/// PERF-wide-odd-base-ratio-9, 2026-11-20, load 41). Here level `j` divides `2k_j` by
/// `k_j + 1` bits and squares `k_j` bits, `k_j` about `n / 2^(j+2)`, so the sum is a constant
/// times the top level: O(M(n)) with the kernel's O(n log n) product and division (bench
/// `num::bench::square_roots_scale`).
pub fn sqrt_rem_uint(a: &BigUint) -> (BigUint, BigUint) {
    let n = a.bits();
    if n <= 128 {
        // Step 6; `n <= 128`, so the value fits in a `u128`.
        let v = a.to_u128().expect("at most 128 bits");
        let s = v.isqrt();
        return (BigUint::from(s), BigUint::from(v - s * s));
    }
    if matches!(n % 4, 1 | 2) {
        // Step 5.
        let (s2, r2) = sqrt_rem_uint(&(a << 2u32));
        let odd = s2.bit(0);
        let s = s2 >> 1u32;
        let r = match odd {
            true => (r2 + (&s << 2u32) + 1u32) >> 2u32,
            false => r2 >> 2u32,
        };
        return (s, r);
    }
    let k = (n + 1) / 4;
    let mask = (BigUint::one() << k) - 1u32;
    let (s1, r1) = sqrt_rem_uint(&(a >> (2 * k)));
    let a1 = (a >> k) & &mask;
    let a0 = a & &mask;
    let (q, u) = fast::div_rem(&((r1 << k) + a1), &(&s1 << 1u32));
    let mut s = (s1 << k) + &q;
    let t = (u << k) + a0;
    let q2 = mul_uint(&q, &q);
    let r = match t >= q2 {
        true => t - q2,
        false => {
            // Step 4: `t - q^2 >= 1 - 2s`, so this is at least 0.
            let r = t + (&s << 1u32) - 1u32 - q2;
            s -= 1u32;
            r
        }
    };
    (s, r)
}

/// `(r, m)` with `b == r ^ m` and `r` not a perfect power, for `b >= 2`. Square roots are taken
/// while `b` is a square, each by the kernel's [`sqrt_rem_uint`], O(M(n)), which also says
/// whether it is one (num-bigint's `sqrt`, taken here until PERF-wide-odd-base-ratio-9, is
/// above O(M(n)), so this bound did not hold: 34.5 times the time for 8 times the bits at
/// 13.3M bits); then each odd prime `p` below the bits of `b` is tried as the index of
/// a root (`OddPart::root`), and tried again after it succeeds. A root found for a larger
/// prime is no power of a smaller one, since `b` would then have been. An index whose root
/// fits in a word costs `O(log p)` word operations; a wider one is first tested by residues
/// (`OddPart::passes`, all from one remainder tree), and one that passes costs a 2-adic root
/// of `bits / p` bits. So the cost is at most `O(M(n) log n)` for `n` the bits of `b` and `M(n)`
/// the cost of a product of `n` bits, whatever the exponent `b` is raised to, and near `M(n)`
/// when the residues reject most indices; a found root, or an index that passes the filters
/// there without being one, adds one `p`-th power.
// Complexity tradeoff: naive version, each prime index `p` tried by a full 2-adic Newton root
// of `bits / p` bits on allocated big integers, with the inverse of the derivative recomputed
// at each step: one root of cost about M(n) per index, O(n / log n) indices. Used: a root of
// at most 64 bits is found and checked in one word with nothing allocated; a wider one is
// tried only when the odd part is a `p`-th power residue modulo the small primes `q < 1024`
// with `p | q - 1` (residues from one remainder tree per base), and its Newton root carries
// the inverse from step to step. Tradeoffs: the remainder tree is built once per base as soon
// as one wide root is looked for, even when few indices reach it; the filters are a necessary
// condition only, so an index that passes them still costs its root. Results unchanged (unit tests
// against trial roots). Test
// `l01_24_refinement_lattices::scaling::the_cube_of_a_wide_end_scales_with_its_bits`; COMPLEXITY.md
// row S46.
pub fn least_root(mut b: BigUint) -> (BigUint, BigUint) {
    let mut m = BigUint::from(1u32);
    // r >= 2, so r ^ p has at least p + 1 bits.
    while b.bits() > 2 {
        // O(M(n)) by the kernel's square root, where num-bigint's `sqrt` took 19.2 s at 13.3M
        // bits, 34.5 times its time at 1.66M (item PERF-wide-odd-base-ratio-9).
        let (r, rem) = sqrt_rem_uint(&b);
        if !rem.is_zero() {
            break;
        }
        b = r;
        m *= 2u32;
    }
    let prime = odd_primes_below(b.bits());
    let mut odd = OddPart::of(&b);
    let mut p = 3u64;
    while p < b.bits() {
        if prime[(p / 2) as usize]
            && let Some(r) = odd.root(p)
        {
            b = r;
            m *= p;
            odd = OddPart::of(&b);
        } else {
            p += 2;
        }
    }
    (b, m)
}

/// The primes by which [`OddPart::root`] checks a candidate root `r` cheaply before it computes
/// the full power `r^p`: `2^64 - 59 = 18446744073709551557`, `2^63 - 25 = 9223372036854775783`
/// and `2^62 - 57 = 4611686018427387847`, the largest primes below `2^64`, `2^63` and `2^62`
/// (test `the_root_check_primes_are_the_largest_below_their_powers_of_two`).
///
/// The check: [`OddPart::of`] keeps `o mod q` for each `q`, and a candidate passes when
/// `(r mod q)^p mod q` equals it for all three. A candidate that fails at one `q` is not the
/// root, since `r^p = o` gives `r^p = o (mod q)`; so the check only rejects, and rejects
/// correctly. A candidate that passes is still decided by the full power `r^p == o`, so the
/// answer is exact whatever these primes are; the check only saves the full power, O(M(n) log p)
/// for `n` the bits of `o`, against O(log p) word products per prime.
///
/// Why these values: a wrong candidate passes at `q` exactly when `q` divides `r^p - o`, which
/// is not zero. For a candidate that is not built to fool the check, that happens about once in
/// `q` tries, so the larger `q`, the better; a word-sized `q` keeps `o mod q`, `r mod q` and the
/// products of [`pow_mod`] in `u64` and `u128` arithmetic. Why three: each prime costs O(log p)
/// word products, small beside the full power, and three make a wasted full power rarer
/// (about `2^-64 · 2^-63 · 2^-62 = 2^-189` by the estimate above, where one prime gives about
/// `2^-64`). No proof bounds
/// how often a wrong candidate passes; none is needed, since a pass never decides alone.
const ROOT_CHECK_PRIMES: [u64; 3] = [
    18_446_744_073_709_551_557,
    9_223_372_036_854_775_783,
    4_611_686_018_427_387_847,
];

/// The bound below the odd primes `q` by which [`OddPart::root`] rejects an index `p` dividing
/// `q - 1` before it looks for a root wider than one word: if `o == r ^ p` then
/// `o ^ ((q - 1) / p) == 1` modulo `q` unless `q` divides `o`, and a number that is no `p`-th
/// power passes one such `q` with chance about `1 / p`, since the `p`-th powers are one in `p`
/// of the units modulo `q`. No prime below it is 1 modulo an index above `FILTER_BOUND / 2`.
/// Proof: the indices are odd primes `p` ([`OddPart::filter`]); a prime `q` that is 1 modulo
/// `p` is `q = k * p + 1` with `k >= 1`, and `q` is odd (`q = 2` would need `p = 1`), so
/// `k * p` is even, and as `p` is odd, `k` is even, `k >= 2`; then `q >= 2 * p + 1`, which for
/// `p > 512` exceeds 1025. So each index wider than a word also gets the least prime that is
/// 1 modulo it ([`Filter`]): without it such an index would meet no prime of the filter.
/// Test: `least_roots_agree_with_trial_and_with_powers_of_large_bases`, at the exponents 521
/// and 1042 = 2 * 521, where the index 521 passes or fails by its `Filter::wide` prime alone;
/// fixed exponents, it cannot catch a wrong residue at an index it does not reach.
/// The bound sets cost only, never the answer: a rejection is proved by the residue argument
/// above, and an index that passes is decided by [`OddPart::root`]. 1024 gives the 171 odd
/// primes below it, whose residues come from one remainder tree; the code records no
/// measurement behind this value.
const FILTER_BOUND: u64 = 1024;

/// The residues of `o` by which [`OddPart::passes`] rejects an index: `(q, o mod q)` for each
/// odd prime `q` below [`FILTER_BOUND`], and `(p, q, o mod q)` for each index `p` whose root is
/// wider than one word, in increasing order of `p`, with `q` the least prime that is 1 modulo
/// `p`.
struct Filter {
    small: Vec<(u64, u64)>,
    wide: Vec<(u64, u64, u64)>,
}

/// `b = 2^v * o` with `o` odd, `o` modulo each of [`ROOT_CHECK_PRIMES`], and, once a root wider
/// than one word is looked for, the residues of `o` in a [`Filter`].
struct OddPart {
    v: u64,
    o: BigUint,
    residues: [u64; 3],
    filter: std::cell::OnceCell<Filter>,
}

impl OddPart {
    fn of(b: &BigUint) -> OddPart {
        let v = b.trailing_zeros().expect("a base is at least 2");
        let o = b >> v;
        // `o mod q` for the cheap root check ([`ROOT_CHECK_PRIMES`]).
        let residues = ROOT_CHECK_PRIMES.map(|q| rem_big_u64(&o, q));
        OddPart {
            v,
            o,
            residues,
            filter: std::cell::OnceCell::new(),
        }
    }

    /// The [`Filter`] of `o`. The indices wider than a word are the odd primes `p` with
    /// `64 * p < n`, for `n` the bits of `o`, and the least prime `q = k * p + 1` is found by
    /// trying `k = 2, 4, ...`, about `ln q` tries ([`is_prime`]: Miller-Rabin with bases that
    /// decide every 64-bit number, Miller 1976, doi:10.1016/S0022-0000(76)80043-8, and Rabin
    /// 1980, doi:10.1016/0022-314X(80)90084-0; the full comment is in zed-numtheory `factor.rs`,
    /// at its head and fn `is_prime`). All the residues come from
    /// one remainder tree ([`remainders`]): the primes, multiplied into words, are `O(n / 64)`
    /// bits together, so the tree costs `O(M(n) log n)`, where one division of `o` per word cost
    /// `O(n)` per index and `O(n^2 / log n)` in all.
    fn filter(&self) -> &Filter {
        self.filter.get_or_init(|| {
            let prime = odd_primes_below(FILTER_BOUND);
            let small = (1..FILTER_BOUND / 2)
                .filter(|&i| prime[i as usize])
                .map(|i| 2 * i + 1);
            let n = self.o.bits();
            let index = odd_primes_below(n.div_ceil(64));
            let wide: Vec<(u64, u64)> = (1..index.len() as u64)
                .filter(|&i| index[i as usize])
                .map(|i| {
                    let p = 2 * i + 1;
                    let q = (1u64..)
                        .map(|k| 2 * k * p + 1)
                        .find(|&q| is_prime(q))
                        .expect("a prime in each progression");
                    (p, q)
                })
                .collect();
            let qs: Vec<u64> = small.chain(wide.iter().map(|&(_, q)| q)).collect();
            // The primes multiplied into words: `ends[w]` is one past the last prime of word `w`.
            let (mut ms, mut ends) = (Vec::new(), Vec::new());
            let mut end = 0;
            while end < qs.len() {
                let mut m = 1u64;
                while let Some(next) = qs.get(end).and_then(|&q| m.checked_mul(q)) {
                    m = next;
                    end += 1;
                }
                ms.push(m);
                ends.push(end);
            }
            let mut rq = Vec::with_capacity(qs.len());
            for (end, om) in ends.into_iter().zip(remainders(&self.o, &ms)) {
                rq.extend(qs[rq.len()..end].iter().map(|&q| om % q));
            }
            let cut = qs.len() - wide.len();
            Filter {
                small: qs[..cut].iter().zip(&rq).map(|(&q, &r)| (q, r)).collect(),
                wide: wide
                    .iter()
                    .zip(&rq[cut..])
                    .map(|(&(p, q), &r)| (p, q, r))
                    .collect(),
            }
        })
    }

    /// Whether `o` is a `p`-th power residue modulo each prime of the [`Filter`] that is 1
    /// modulo `p` and does not divide `o`, as it is when `o` is a `p`-th power.
    fn passes(&self, p: u64) -> bool {
        let residue = |q: u64, oq: u64| oq == 0 || pow_mod(oq, (q - 1) / p, q) == 1;
        let filter = self.filter();
        filter
            .small
            .iter()
            .all(|&(q, oq)| !(q - 1).is_multiple_of(p) || residue(q, oq))
            && match filter.wide.binary_search_by_key(&p, |&(p, _, _)| p) {
                Ok(i) => {
                    let (_, q, oq) = filter.wide[i];
                    residue(q, oq)
                }
                Err(_) => true,
            }
    }

    /// The `r` with `r ^ p == 2^v * o`, for an odd prime `p`, when there is one. Such an `r`
    /// is `2^(v / p)` times the odd `p`-th root of `o`, which is below `2^s` for `s` the bits of
    /// `o` over `p`, rounded up, and so is the one odd `p`-th root of `o` modulo `2^s`
    /// ([`odd_root_mod_pow2`]). That candidate is checked by its bit count and modulo
    /// [`ROOT_CHECK_PRIMES`], in time of order its own bits, and only then by its `p`-th power,
    /// which decides.
    fn root(&self, p: u64) -> Option<BigUint> {
        if !self.v.is_multiple_of(p) {
            return None;
        }
        let shift = self.v / p;
        if self.o.is_one() {
            return Some(BigUint::from(1u32) << shift);
        }
        let n = self.o.bits();
        let s = n.div_ceil(p);
        if s <= 64 {
            // A root of at most 64 bits, as for every index above the bits over 64, is found
            // and filtered in one word, with nothing allocated: the root modulo `2^64` cut to
            // `s` bits is the one modulo `2^s`.
            let low = self.o.iter_u64_digits().next().expect("o is odd");
            let r = odd_root_mod_2_64(low, p) & (u64::MAX >> (64 - s));
            let rb = u64::from(r.bit_len());
            if n <= p * (rb - 1) || n > p * rb {
                return None;
            }
            // The cheap check modulo three primes, which only rejects; the full power below
            // decides ([`ROOT_CHECK_PRIMES`]).
            let agree = ROOT_CHECK_PRIMES
                .iter()
                .zip(&self.residues)
                .all(|(&q, &oq)| pow_mod(r % q, p, q) == oq);
            let r = BigUint::from(r);
            return (agree && pow_uint(&r, p) == self.o).then(|| r << shift);
        }
        if !self.passes(p) {
            return None;
        }
        let r = odd_root_mod_pow2(&self.o, p, s);
        // r ^ p has more than p * (bits(r) - 1) bits and at most p * bits(r).
        let rb = r.bits();
        if n <= p * (rb - 1) || n > p * rb {
            return None;
        }
        // The cheap check modulo three primes, which only rejects; the full power below decides
        // ([`ROOT_CHECK_PRIMES`]).
        let agree = ROOT_CHECK_PRIMES
            .iter()
            .zip(&self.residues)
            .all(|(&q, &oq)| pow_mod(rem_big_u64(&r, q), p, q) == oq);
        (agree && pow_uint(&r, p) == self.o).then(|| r << shift)
    }
}

/// `x mod m` for each `m` of `ms`, every `m` above 0, by the kernel's product and remainder
/// trees ([`crate::trees`]): the `ms` are multiplied in pairs up to one product `P`,
/// `x` is reduced modulo `P` once, and each remainder modulo the two products below it. For
/// `B` the bits of `P` the cost is that of the one division and O(M(B) log k) for `k` moduli,
/// where one division of `x` a modulus costs O(bits of `x`) each.
//
// Source: D. J. Bernstein, "Fast multiplication and its applications", in Algorithmic Number
// Theory, MSRI Publications 44, Cambridge University Press, 2008, pp. 325-384,
// https://cr.yp.to/lineartime/multapps-20080515.pdf. Section 12 (product tree) and section 18
// (remainder tree): "The root of the remainder tree is h mod f1 f2 ... ft. If t ≤ 1 then
// that's the complete tree. If t ≥ 2 then the left subtree is the remainder tree of h,
// f1, ..., fs, and the right subtree is the remainder tree of h, fs+1, ..., ft" (18.2); 18.3
// gives O(n (lg n)^2 lg lg n) operations over the FFT, an O(M(n) log n) bound. Departures:
// integers rather than polynomials (the integer case of 18.6 and 18.7), and the kernel pairs
// the leaves in order rather than splitting at s = ⌈t/2⌉, which keeps the depth ⌈lg t⌉.
// Checked 2026-11-20 against the author's copy. Tests:
// `tests::a_remainder_tree_gives_each_remainder`, every tree shape of 0 to 9 word moduli
// against one division each, and the kernel's `the_remainders_agree_with_one_division_a_leaf`;
// neither measures the cost.
pub fn remainders(x: &BigUint, ms: &[u64]) -> Vec<u64> {
    let leaves: Vec<BigUint> = ms.iter().map(|&m| BigUint::from(m)).collect();
    let levels = trees::product_tree(&leaves);
    (trees::remainders(x, &leaves, &levels).iter())
        .map(|r| u64::try_from(r).expect("below a word"))
        .collect()
}

/// The odd `x < 2^k` with `x ^ p == o` modulo `2^k`, for `o` odd, `p` an odd prime and
/// `k >= 1`. Since `p` is odd, `x -> x ^ p` permutes the odd residues modulo `2^k`, so there is
/// exactly one. Newton's method over the 2-adic integers finds it: `p * x ^ (p - 1)` is odd, so
/// each step doubles the bits that are right. The first 64 bits come from
/// [`odd_root_mod_2_64`], with the inverse of the derivative there, in one word; from there the
/// inverse of the derivative is carried from step to step and refined by one Newton step of
/// its own, so the cost is `O(M(k) log p)`, with `M(k)` that of a product of `k` bits, and a
/// root of `k` bits takes `log2(k / 64)` steps on numbers wider than a word, not `log2 k`.
fn odd_root_mod_pow2(o: &BigUint, p: u64, k: u64) -> BigUint {
    let low = o.iter_u64_digits().next().expect("o is odd");
    let word = odd_root_mod_2_64(low, p);
    if k <= 64 {
        return BigUint::from(word & (u64::MAX >> (64 - k)));
    }
    let mut x = BigUint::from(word);
    // The inverse of the derivative at `x`, right modulo 2^64.
    let mut z = BigUint::from(inverse_mod_2_64(pow_mod_2_64(word, p - 1).wrapping_mul(p)));
    let mut j = 64;
    while j < k {
        j = (2 * j).min(k);
        let unit = BigUint::from(1u32) << j;
        let mask = &unit - 1u32;
        let y = pow_mod_pow2(&x, p - 1, &mask);
        // x ^ p - o, and the derivative p * x ^ (p - 1), modulo 2^j.
        let f = (mul_uint(&y, &x) + &unit - (o & &mask)) & &mask;
        let d = (y * p) & &mask;
        // `x` changed only above the bits that were right at the last step, so `z`, the
        // inverse of the last derivative to half of those bits, is that of this one too; one
        // step `z * (2 - d * z)` doubles them, past the `j - j / 2` bits the update reads.
        z = mul_uint(&z, &((&unit + 2u32 - (mul_uint(&d, &z) & &mask)) & &mask)) & &mask;
        let step = mul_uint(&f, &z) & &mask;
        x = (x + unit - step) & mask;
    }
    x
}

/// `x ^ e` modulo `mask + 1`, a power of 2.
fn pow_mod_pow2(x: &BigUint, e: u64, mask: &BigUint) -> BigUint {
    let mut out = BigUint::from(1u32);
    for i in (0..e.bit_len()).rev() {
        out = mul_uint(&out, &out) & mask;
        if e >> i & 1 == 1 {
            out = mul_uint(&out, x) & mask;
        }
    }
    out
}

/// `(r, a - r^k)` with `r = floor(a^(1/k))`, for `k >= 1`, for integers held outside a
/// zed-kernel `Rat` (moved here from zed-kernel `num.rs`, DRY-bignum-crate-2026-11-26):
/// [`sqrt_rem_uint`] for `k = 2`; for `k >= 3`, `nth_root_near`, `r` or `r + 1`, and
/// one check: `r` is `y = nth_root_near(a, k)` when `y^k <= a`, else `y - 1`, and the remainder
/// is `a` less the power checked last.
///
/// Complexity tradeoff: num-bigint's `nth_root` at every size, whose divisions are schoolbook
/// (`O(n R)` for a quotient of `R` bits): from 4,096 to 32,768 words, 19.3 times the time for
/// `k = 3`, 32.6 for `k = 5`, 36.3 for `k = 64` (2026-11-20, load 95). Its start (num-bigint
/// 0.4.8 `biguint.rs`, `nth_root`: an `f64` guess, from the top 1,023 bits when wider, else
/// `2^(bits / k + 1)`) holds few right bits for a large `k`, and Newton's iteration from far
/// above falls only by about `(k - 1) / k` a turn: about `k` turns of a power of `n` bits.
/// Here: `nth_root_near`, O(M(n)) for a fixed `k`, then one power `y^k` of at most `n + k`
/// bits, O(M(n)) by squarings whose sizes double, and at most one power more. So O(M(n)) for a
/// fixed `k` (bench `num::bench::kth_roots_scale`). Callers: zedc-int `Num::root_big` and
/// `Atom::expand`, and `poly::roots::positive_roots` (item PERF-wide-odd-base-ratio-9).
pub fn nth_root_rem_uint(a: &BigUint, k: u32) -> (BigUint, BigUint) {
    assert!(k >= 1, "a root of index 0");
    match k {
        1 => return (a.clone(), BigUint::ZERO),
        2 => return sqrt_rem_uint(a),
        _ => {}
    }
    let k64 = u64::from(k);
    let y = nth_root_near(a, k);
    let t = pow_uint(&y, k64);
    if t <= *a {
        return (y, a - t);
    }
    let r = y - 1u32;
    let rem = a - pow_uint(&r, k64);
    (r, rem)
}

/// `r` or `r + 1` for `r = floor(a^(1/k))` and `k >= 3`: the root of the top bits by
/// recursion, then one turn of Newton's iteration on the integers from above (R. P. Brent and
/// P. Zimmermann, Modern Computer Arithmetic, Cambridge University Press, 2010, section 1.5,
/// the integer k-th root by Newton's method), on the kernel's power and division.
///
/// With `R = ceil(n / k)` for `a` of `n` bits (so `2^(R - 1) <= rho = a^(1/k) < 2^R`), `c` the
/// bits of `k - 1`, and `h = floor((R - c - 4) / 2)`: `s = nth_root_near(a >> kh, k)`, `x = (s
/// + 1) 2^h`, `A = a >> (k - 1) h`, `P = (s + 1)^(k-1)`, `Q` the bits of `A` less those of `P`,
/// plus 1, `d` the bits of `P` less `Q + 2` (0 if fewer), `q' = floor((A >> d) / (P >> d))`,
/// and the result is `y' = floor(((k - 1) x + q') / k)`.
///
/// Proof, every step (checked through [`nth_root_rem_uint`] by `kth_roots_agree_with_num_bigint`
/// against num-bigint's `nth_root`, for `k` from 3 to 9 at every width up to 1,500 bits,
/// `k = 64` up to 24,000 bits and `k = 1000` at 64,000, at `r^k - 1`, `r^k` and `r^k + 1`):
/// 1. Start: `r0 = floor((a >> kh)^(1/k))`, and `s` is `r0` or `r0 + 1` by recursion (or
///    `r0` from the leaf, step 7). `(r0 + 1)^k >= (a >> kh) + 1`, so `x^k >= (r0 + 1)^k
///    2^(kh) >= ((a >> kh) + 1) 2^(kh) > a`, and `x > rho`. And `(r0 2^h)^k <= (a >> kh)
///    2^(kh) <= a`, so `rho >= r0 2^h` and `e = x - rho <= (r0 + 2) 2^h - r0 2^h = 2^(h + 1)`.
/// 2. The quotient: `x^(k-1) = P 2^((k - 1) h)`, and `floor(floor(a / 2^m) / P) = floor(a /
///    (2^m P))` for integers `P >= 1` (both are the greatest `q` with `q P 2^m <= a`), so `q =
///    floor(A / P) = floor(a / x^(k-1))`, from a power of `s + 1`, about `R / 2` bits, not of
///    `x`, about `R`.
/// 3. The truncated quotient: `q <= q' <= q + 1`. With `A = A' 2^d + A''` and `P = P' 2^d +
///    P''`, `0 <= A'', P'' < 2^d`: `A / P < (A' + 1) / P'`, so `q <= q'` (if `(A' + 1) / P'` is
///    an integer `j`, `q <= j - 1 = q'`, else `q <= floor((A' + 1) / P') = q'`). And `A / P >=
///    A' / (P' + 1) = A' / P' - A' / (P' (P' + 1)) > A' / P' - 1`, as `P'` has `Q + 2` bits
///    (when `d > 0`; else `q' = q`), `P' >= 2^(Q + 1)`, and `A' < 2^(Q + 2 + Q - 1) <= P'^2`;
///    so `q >= q' - 1`. The division is then `2Q + 1` bits by `Q + 2`, near balanced, at every
///    `k`.
/// 4. `y' >= r`: `q' >= q` gives `y' >= y = floor(((k - 1) x + q) / k)`, and `floor((j +
///    floor(u)) / k) = floor((j + u) / k)` for an integer `j`, so `y = floor(((k - 1) x + a /
///    x^(k-1)) / k)`; by the inequality of the arithmetic and geometric means on `k - 1` copies
///    of `x` and one of `a / x^(k-1)`, the inside is at least `(x^(k-1) a / x^(k-1))^(1/k) =
///    rho`; so `y >= floor(rho) = r`.
/// 5. `y' <= r + 1`: the inside of step 4 is the real Newton step `N(x) = x - (x^k - a) / (k
///    x^(k-1))`, and `k x^(k-1) (N(x) - rho) = (k - 1) x^k - k rho x^(k-1) + rho^k = G(x)`, with
///    `G(rho) = 0` and `G'(t) = k (k - 1) t^(k-2) (t - rho)`, so `G(x)`, the integral of `G'`
///    from `rho` to `x`, is at most `k (k - 1) x^(k-2) e^2 / 2`, and `N(x) - rho <= (k - 1) e^2
///    / (2 x) <= (k - 1) 2^(2h + 2) / 2^R` (step 1, `x > rho >= 2^(R - 1)`). `k - 1 < 2^c` and
///    `2h <= R - c - 4`, so `N(x) < rho + 1/4`. `q' <= q + 1 <= a / x^(k-1) + 1` (step 3), so
///    `y' <= floor(N(x) + 1 / k)`, and `N(x) + 1 / k < rho + 1/4 + 1/3 < r + 2` for `k >= 3`.
/// 6. So `y'` is `r` or `r + 1`, which is what the recursion of step 1 needs of `s`.
/// 7. The recursion stops at `R <= b + 64` with `b` the bits of `k`; above it `R - c - 4 >=
///    61`, so `h >= 30` and `a >> kh` is shorter than `a`. There the root is found exactly, bit
///    by bit from the top, `R` turns that keep the greatest `t` with `t^k <= a` (each turn sets
///    the next bit when the power stays at most `a`); a value within 64 bits takes the word root
///    of num-integer instead.
///
/// Complexity tradeoff: a level is one power of `k - 1` of `s + 1`, about `n / 2` bits, O(M(n))
/// by squarings whose sizes double, and one division of about `2R` bits by `R`, O(M(R)); the
/// level below has `a >> kh`, about `n / 2` bits, so the sum is O(M(n)) above the leaf; the
/// leaf is `b + 64` powers of at most `k (b + 64)` bits. Three versions before this one, all
/// measured by `kth_roots_scale` from 2,048 to 8,192 words for `k` 3 and 64 (2026-11-20):
/// `h = floor(R / 2)` and turns until `y >= x`, 2 or 3 turns a level, the last only to
/// confirm, and `T(8n) / T(n)` from 8.9 to 12.8 as the turn count changed between sizes; one
/// turn and a check at every level, with powers of `x` itself, about half the work but still
/// 9.3 to 12.3, as each level below the top cost nearly as much as the top; no check below the
/// top and powers of `s + 1`, half again, 9.3 to 11.6 with the exact quotient `q`, whose `R`
/// bits by `n / 2` went to num-bigint's schoolbook division at `n` and to the reciprocal at
/// `8n` for `k = 64` (27 times the work of that division alone at 2,048 words).
fn nth_root_near(a: &BigUint, k: u32) -> BigUint {
    let k64 = u64::from(k);
    let wide = a.bits().div_ceil(k64);
    if wide <= u64::from(k.bit_len()) + 64 {
        // Step 7.
        return match a.to_u64() {
            Some(w) => BigUint::from(num_integer::Roots::nth_root(&w, k)),
            None => (0..wide).rev().fold(BigUint::ZERO, |r, i| {
                let mut t = r.clone();
                t.set_bit(i, true);
                match pow_uint(&t, k64) <= *a {
                    true => t,
                    false => r,
                }
            }),
        };
    }
    // Step 5: `c + 4` guard bits.
    let c = u64::from((k - 1).bit_len());
    let h = (wide - c - 4) / 2;
    // Step 1.
    let s = nth_root_near(&(a >> (k64 * h)), k) + 1u32;
    // Steps 2 and 3.
    let big_a = a >> ((k64 - 1) * h);
    let p = pow_uint(&s, k64 - 1);
    let wq = (big_a.bits() + 1).saturating_sub(p.bits());
    let d = p.bits().saturating_sub(wq + 2);
    let (q, _) = fast::div_rem(&(big_a >> d), &(p >> d));
    // Steps 4 to 6.
    ((s << h) * (k - 1) + q) / k
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The least root by trying every index from the largest down, written out.
    fn least_root_by_trial(b: u64) -> (u64, u64) {
        (2..64)
            .rev()
            .find_map(|m: u32| {
                let r = (b as f64).powf(1.0 / f64::from(m)).round() as u64;
                (r.max(2) - 1..=r + 1)
                    .find(|&r| r >= 2 && r.checked_pow(m) == Some(b))
                    .map(|r| (r, u64::from(m)))
            })
            .unwrap_or((b, 1))
    }

    #[test]
    fn least_roots_agree_with_trial_and_with_powers_of_large_bases() {
        for b in 2..50_000u64 {
            let (r, m) = least_root(BigUint::from(b));
            assert_eq!((r, m), {
                let (r, m) = least_root_by_trial(b);
                (BigUint::from(r), BigUint::from(m))
            });
        }
        // Powers of bases that are no powers, odd, even and with odd parts, to prime and
        // composite exponents, and their neighbors, which are no powers. No prime below
        // FILTER_BOUND is 1 modulo an index above 511, so for 521 and 1042 = 2 * 521 a root
        // wider than a word passes or fails by the one `Filter::wide` prime alone
        // (TEST-l0123-leftovers); the bases of a few bits find theirs in one word.
        let mersenne = (BigUint::from(1u32) << 127u32) - 1u32;
        let bases = [
            mersenne.clone(),
            &mersenne << 5u32,
            &mersenne * 6u32,
            BigUint::from(6u32),
            BigUint::from(10u32).pow(40u32) + 3u32,
        ];
        for r in &bases {
            for m in [2u32, 3, 5, 6, 7, 12, 31, 97, 210, 521, 1042] {
                let b = r.pow(m);
                assert_eq!(least_root(b.clone()), (r.clone(), BigUint::from(m)));
                for d in [1u32, 2] {
                    let near = &b + d;
                    assert_eq!(least_root(near.clone()), (near, BigUint::from(1u32)));
                }
            }
        }
        // A power of 2 alone, whatever its exponent.
        assert_eq!(
            least_root(BigUint::from(1u32) << 4099u32),
            (BigUint::from(2u32), BigUint::from(4099u32))
        );
    }

    #[test]
    fn a_root_in_one_word_is_the_root_by_big_numbers() {
        let (mut rng, _) = crate::seed::Rng::fresh("a_root_in_one_word_is_the_root_by_big_numbers");
        for p in [3u64, 5, 7, 11, 13, 31, 61, 127, 509, 4093, 65_521] {
            for _ in 0..200 {
                let o = rng.next_u64() | 1;
                let word = odd_root_mod_2_64(o, p);
                for k in [1u64, 2, 17, 63, 64] {
                    let mask = u64::MAX >> (64 - k);
                    let big = odd_root_mod_pow2(&BigUint::from(o), p, k);
                    assert_eq!(BigUint::from(word & mask), big, "o = {o}, p = {p}, k = {k}");
                    // The one odd root below 2^k.
                    let m = BigUint::from(1u32) << k;
                    assert!(big.bit(0) && big < m, "o = {o}, p = {p}, k = {k}");
                    assert_eq!(big.modpow(&BigUint::from(p), &m), BigUint::from(o) % &m);
                }
            }
        }
        // Wider roots, by the same test.
        for (p, k) in [(3u64, 65u64), (3, 1000), (5, 4097), (31, 300), (509, 129)] {
            for seed in 0..20u32 {
                let o = (BigUint::from(3u32).pow(2000 + seed) << 1u32) + 1u32;
                let r = odd_root_mod_pow2(&o, p, k);
                let m = BigUint::from(1u32) << k;
                assert!(r.bit(0) && r < m, "p = {p}, k = {k}");
                assert_eq!(r.modpow(&BigUint::from(p), &m), &o % &m, "p = {p}, k = {k}");
            }
        }
    }

    #[test]
    fn a_remainder_tree_gives_each_remainder() {
        let x = BigUint::from(3u32).pow(5000u32) + 12_345u32;
        // Lengths 0 to 9 take every shape of tree, with products moved up at odd lengths.
        let all: Vec<u64> = (0..9u64).map(|i| u64::MAX - 58 - 2 * i).collect();
        for len in 0..=all.len() {
            let ms = &all[..len];
            let want: Vec<u64> = ms
                .iter()
                .map(|&m| u64::try_from(&x % m).expect("below m"))
                .collect();
            assert_eq!(remainders(&x, ms), want, "{len} moduli");
        }
        // A number below the product of the moduli.
        assert_eq!(remainders(&BigUint::from(5u32), &[7, 11, 13]), [5, 5, 5]);
    }

    /// The remainder tree past the kernel's switches: 2,001 word moduli (a product of about 2,000
    /// words, an odd count so nodes are carried), `x` of 7/8 of its width less and more a bit
    /// and at its full width, where the kernel's `remainders` chooses between the exact descent
    /// and the scaled tree, which turns to the exact descent at a level its costs choose; each
    /// against one division a modulus.
    #[test]
    fn a_remainder_tree_past_the_scaled_switch_gives_each_remainder() {
        let ms: Vec<u64> = (0..2001u64).map(|i| u64::MAX - 2 * i).collect();
        let p = ms.iter().fold(BigUint::from(1u32), |p, &m| p * m);
        let n = p.bits();
        for w in [7 * n / 8 - 1, 7 * n / 8 + 1, n] {
            let x = (&p >> (n - w)) - 12_345u32;
            let want: Vec<u64> = ms
                .iter()
                .map(|&m| u64::try_from(&x % m).expect("below m"))
                .collect();
            assert_eq!(remainders(&x, &ms), want, "x of {w} of {n} bits");
        }
    }

    #[test]
    fn each_index_wider_than_a_word_has_its_least_prime() {
        let o = BigUint::from(3u32).pow(3000u32);
        let odd = OddPart::of(&o);
        let filter = odd.filter();
        // 3000 * log2(3) is 4755 bits: the indices wider than a word are the odd primes to 73.
        let ps: Vec<u64> = filter.wide.iter().map(|&(p, _, _)| p).collect();
        assert_eq!(
            ps,
            [
                3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73
            ]
        );
        for &(p, q, oq) in &filter.wide {
            assert!(is_prime(q) && (q - 1).is_multiple_of(p), "p = {p}, q = {q}");
            assert!(
                (1..q / p).all(|k| !is_prime(k * p + 1)),
                "{q} is the least prime 1 modulo {p}"
            );
            assert_eq!(BigUint::from(oq), &o % q, "p = {p}");
        }
        // 3 ^ 3000 is a 3rd and a 5th power, so it passes both indices.
        for p in [3u64, 5] {
            assert!(odd.passes(p), "p = {p}");
        }
    }

    // The four tests below were in zedc-int's `int/completeness.rs` before `least_root` moved
    // here (2026-11-23, KEPT-power-form-print); they read its private helpers.

    /// The primes of the cheap root check are what their comment says: prime, and the largest
    /// below `2^64`, `2^63` and `2^62`.
    #[test]
    fn the_root_check_primes_are_the_largest_below_their_powers_of_two() {
        for (q, k) in ROOT_CHECK_PRIMES.into_iter().zip([64u32, 63, 62]) {
            assert!(is_prime(q), "{q}");
            // `2^(k-1) <= q < 2^k`, and the next prime is at least `2^k` (none below `2^64`).
            assert_eq!(q.ilog2(), k - 1, "{q}");
            let next = zed_numtheory::next_prime(q);
            assert!(next.is_none_or(|n| n.ilog2() >= k), "{q}: next {next:?}");
        }
    }

    #[test]
    fn word_arithmetic_helpers_on_their_ends() {
        // pow_mod_2_64, pow_mod and inverse_mod_2_64 are tested in zed-numtheory.
        // pow_mod_pow2 against num-bigint, exponents 0, 1 and many, moduli of one bit and past
        // a word.
        let x = BigUint::from(3u32).pow(50u32) + 1u32;
        for (e, k) in [
            (0u64, 1u32),
            (1, 1),
            (1, 200),
            (5, 64),
            (17, 65),
            (100, 300),
        ] {
            let unit = BigUint::from(1u32) << k;
            let mask = &unit - 1u32;
            assert_eq!(
                pow_mod_pow2(&x, e, &mask),
                x.modpow(&BigUint::from(e), &unit),
                "x ^ {e} mod 2^{k}"
            );
        }
    }

    #[test]
    fn a_root_by_odd_part_rejects_each_way_a_candidate_fails() {
        // (case, base, index, root)
        let wide = BigUint::from(3u32).pow(100u32) + 2u32; // odd, no power
        let cases: Vec<(&str, BigUint, u64, Option<BigUint>)> = vec![
            // The power of 2 is not a multiple of the index.
            ("2^4 * 27, index 3", BigUint::from(16u32 * 27), 3, None),
            // The odd part is 1: the root is a power of 2.
            (
                "2^9, index 3",
                BigUint::from(512u32),
                3,
                Some(BigUint::from(8u32)),
            ),
            // A one-word root, found and checked.
            (
                "2^3 * 7^3, index 3",
                BigUint::from(8u32 * 343),
                3,
                Some(BigUint::from(14u32)),
            ),
            // A one-word candidate of the wrong bit count, and one off by the test primes.
            ("7^3 + 2, index 3", BigUint::from(345u32), 3, None),
            (
                "3^40 + 2, index 5",
                BigUint::from(3u32).pow(40u32) + 2u32,
                5,
                None,
            ),
            // A wide root, found; a wide odd part that is no power, refused.
            (
                "(3^100 + 2)^3, index 3",
                wide.pow(3u32),
                3,
                Some(wide.clone()),
            ),
            ("(3^100 + 2)^3 + 2, index 3", wide.pow(3u32) + 2u32, 3, None),
            ("3^100 + 2, index 3", wide.clone(), 3, None),
        ];
        for (case, b, p, want) in cases {
            assert_eq!(OddPart::of(&b).root(p), want, "{case}");
        }
    }

    #[test]
    fn the_residue_filter_passes_powers_and_ignores_indices_it_holds_no_prime_for() {
        // 3^(3·5·7·11·13) is a power for each of those indices, and passes each of them, wide
        // ones included; an index past the filter's wide primes passes on the small primes
        // alone.
        let o = BigUint::from(3u32).pow(3 * 5 * 7 * 11 * 13);
        let odd = OddPart::of(&o);
        for p in [3u64, 5, 7, 11, 13] {
            assert!(odd.passes(p), "index {p}");
        }
        // 521 is past the wide indices (those below 23,798 / 64 bits) and has no prime 1 modulo
        // it below 1024, so no residue applies: it passes, though 521 does not divide 15,015.
        // The filter is a necessary condition only; the root decides.
        let top = odd
            .filter()
            .wide
            .last()
            .map(|&(p, _, _)| p)
            .expect("wide indices");
        assert!(top < 521, "the widest index {top}");
        assert!(odd.passes(521), "index 521, no residue applies");
        assert_eq!(odd.root(521), None, "3^15015 is no 521st power");
        // A number that is no cube fails a small prime 1 modulo 3: 3 is not a cube modulo 7.
        assert!(!OddPart::of(&BigUint::from(3u32)).passes(3), "3, index 3");
        // A number with a factor of each small filter prime passes every index: every residue
        // is 0.
        let mut all = BigUint::from(1u32);
        for &(q, _) in &OddPart::of(&BigUint::from(3u32)).filter().small {
            all *= q;
        }
        let all = OddPart::of(&all);
        for p in [3u64, 5, 7, 11, 13, 101] {
            assert!(all.passes(p), "every residue 0, index {p}");
        }
    }
}
