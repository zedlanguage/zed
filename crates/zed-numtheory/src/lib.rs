//! Number theory shared by every crate of the workspace, zed-kernel included (DRY-number-theory,
//! the author, 2026-11-19: "create a `numtheory` crate and move and combine all number theory
//! code into that crate", one routine per job; named `zed-numtheory` by the author the same day).
//! The greatest common divisor of words and of a
//! big integer with a word, products and powers modulo a word, arithmetic modulo the Mersenne
//! prime `2^61 - 1`, the inverse modulo `2^64`, primality, factoring, the next prime, and the
//! sieves.
//!
//! The gcd, inverse and Bezout coefficients of big integers stay in zed-kernel (`num::gcd_uint`,
//! `num::inverse_mod_uint`, `num::bezout_int`), since their half gcd is built on the kernel's
//! fast multiplication (`num/fast.rs`); for a word operand they call [`gcd_big_u64`] here.

mod factor;
mod word;

use num_bigint::BigUint;

pub use factor::{factor, is_prime};
pub use word::{gcd_u64, gcd_u128, inverse_mod_2_64, mul_mod, pow_mod};

/// `(g, s, t)` with `g = gcd(a, b) >= 0` and `s a + t b = g`, by the extended Euclidean
/// algorithm on `|a|` and `|b|`, `s` and `t` then signed as `a` and `b` are; `(0, 1, 0)` for
/// two zeros. `None` when `a` or `b` is `i128::MIN`, whose magnitude is not an `i128`.
///
/// No step overflows: from `s_1 = 0` on, the cofactors `s_i` alternate in sign with
/// `|s_(i+1)| = |s_(i-1)| + q_i |s_i|`, so their magnitudes rise, and the last,
/// `|s_(k+1)| = |b| / g`, is at most `|b| < 2^127`; with `s_0 = 1`, every `q_i s_i` and
/// `s_(i+1)` fits, and likewise for `t` with `|a|`. The returned pair is the one before the
/// last, so `|s| <= max(1, |b| / g)` and `|t| <= max(1, |a| / g)` (the 1 for a zero operand).
// Complexity tradeoff: O(log min(|a|, |b|)) steps of one 128-bit division each. The binary
// extended gcd avoids the divisions but needs a correction step per shift and can return other
// cofactors than Euclid's, which callers see (the presburger callers lift points by them), so
// Euclid's are kept.
pub fn bezout_i128(a: i128, b: i128) -> Option<(i128, i128, i128)> {
    let (Some(x), Some(y)) = (a.checked_abs(), b.checked_abs()) else {
        return None;
    };
    let (mut r0, mut r1) = (x, y);
    let (mut s0, mut s1) = (1i128, 0i128);
    let (mut t0, mut t1) = (0i128, 1i128);
    while r1 != 0 {
        let q = r0 / r1;
        (r0, r1) = (r1, r0 - q * r1);
        (s0, s1) = (s1, s0 - q * s1);
        (t0, t1) = (t1, t0 - q * t1);
    }
    let s = if a < 0 { -s0 } else { s0 };
    let t = if b < 0 { -t0 } else { t0 };
    Some((r0, s, t))
}

/// `x mod m` for `m > 0`, by Horner over the words of `x` from the most significant, in
/// registers and with nothing allocated.
// Complexity tradeoff: `x % m` in num-bigint 0.4 copies `x` and divides it as a big number, so
// a remainder of an n-word `x` takes n words that are never used; here each word is one `u128`
// remainder: O(n) time, as before, and O(1) space (item ENGINE-one).
pub fn rem_big_u64(x: &BigUint, m: u64) -> u64 {
    let m = u128::from(m);
    let r = x
        .iter_u64_digits()
        .rev()
        .fold(0u128, |r, d| ((r << 64) | u128::from(d)) % m);
    // Unreachable: each fold step ends with `% m`, so `r < m <= u64::MAX`.
    u64::try_from(r).expect("a remainder below a u64 modulus")
}

/// `gcd(x, d)` for a word `d > 0`: `gcd(x mod d, d)` ([`rem_big_u64`], then [`gcd_u64`]),
/// since `x` and `x mod d` differ by a multiple of `d`.
// Complexity tradeoff: building `d` as a big integer and running the big gcd costs an
// allocation and a big division; here one O(n) pass over the n words of `x` leaves two words,
// whose gcd is O(log d) steps in registers.
pub fn gcd_big_u64(x: &BigUint, d: u64) -> u64 {
    debug_assert!(d > 0, "a divisor above 0");
    if d == 1 {
        return 1;
    }
    gcd_u64(rem_big_u64(x, d), d)
}

/// `a^e mod m`, for `m > 0`, with an unbounded exponent, by squaring from the high bit of `e`:
/// O(bits of `e`) products, with nothing allocated.
pub fn pow_mod_big(a: u64, e: &BigUint, m: u64) -> u64 {
    let b = a % m;
    let mut r = 1 % m;
    for i in (0..e.bits()).rev() {
        r = mul_mod(r, r, m);
        if e.bit(i) {
            r = mul_mod(r, b, m);
        }
    }
    r
}

/// `b^e mod 2^64`, by squaring over the bits of `e`: O(log e) products. `0^0 = 1`.
// Complexity tradeoff: `e` products by `b` are O(e); squaring is O(log e), at most 64
// squarings and 64 products, all wrapping, with no division.
pub fn pow_mod_2_64(mut b: u64, mut e: u64) -> u64 {
    let mut out = 1u64;
    while e > 0 {
        if e & 1 == 1 {
            out = out.wrapping_mul(b);
        }
        b = b.wrapping_mul(b);
        e >>= 1;
    }
    out
}

/// The odd `x` with `x^p = o mod 2^64`, for `o` and `p` odd. There is exactly one: for odd `p`,
/// `x -> x^p` permutes the odd residues modulo `2^k` for every `k`. Newton's method over the
/// 2-adic integers finds it: the derivative `p x^(p-1)` is odd, so each step doubles the low
/// bits that are right (Hensel's lemma), and the start `x = 1` is right in one bit (`1^p` and
/// `o` are both odd), so six steps give 2, 4, 8, 16, 32, 64.
// Complexity tradeoff: a search over the 2^63 odd residues is out of the question; lifting one
// bit at a time is 63 steps; Newton's six steps each cost a power, O(log p) products, and one
// inverse ([`inverse_mod_2_64`]). The wide roots built on this one (zedc-int `int.rs`
// `odd_root_mod_pow2`) stay in zedc-int, since they need zed-kernel's fast products.
pub fn odd_root_mod_2_64(o: u64, p: u64) -> u64 {
    debug_assert!(o % 2 == 1 && p % 2 == 1, "an odd residue and an odd index");
    let mut x = 1u64;
    for _ in 0..6 {
        let y = pow_mod_2_64(x, p - 1);
        let f = y.wrapping_mul(x).wrapping_sub(o);
        // The inverse of the odd derivative `p x^(p-1)`.
        x = x.wrapping_sub(f.wrapping_mul(inverse_mod_2_64(y.wrapping_mul(p))));
    }
    x
}

/// The least prime above `n`, or `None` when none is below `2^64` (`n` at or past
/// 18446744073709551557, the largest 64-bit prime).
// Complexity tradeoff: trial division of each candidate `q` costs O(sqrt q) divisions. Here
// each candidate goes to [`is_prime`] (trial division by the twelve primes to 37, which rejects
// about 85% of all candidates, then Miller-Rabin with twelve bases, exact on 64 bits): O(log q)
// products for a prime, and on average about `ln q <= 45` candidates to the next prime (the
// prime number theorem). The search ends: a prime above `n` exists below `2^64` whenever the
// answer is `Some`, and otherwise the range runs out at `u64::MAX`.
pub fn next_prime(n: u64) -> Option<u64> {
    (n.checked_add(1)?..=u64::MAX).find(|&q| is_prime(q))
}

/// The marker [`least_prime_factors`] stores for a prime.
pub const PRIME: u16 = u16::MAX;

/// For each `j <= top`, below `2^32`: the least prime factor of a composite `j`, [`PRIME`] for a
/// prime, and 0 for 0 and 1. The least prime factor of a composite `j` is at most
/// `sqrt(j) < 2^16`, and the largest prime below `2^16` is 65521, below the marker, so every
/// entry fits a `u16`.
///
/// The segmented sieve of Eratosthenes. The primes `p <= r = isqrt(top)` come from
/// [`odd_primes_below`] (and 2). The table is filled one block of at least [`SIEVE_BLOCK`]
/// entries at a time, and in each block every prime `p <= r`, from the greatest down to 2,
/// writes `p` at each of its multiples in the block from `p^2` on. Proof that a composite
/// `j <= top` ends with its least prime factor `p`: `p^2 <= j`, so `p <= r` and `p` writes at
/// `j`; every other prime that writes at `j` divides `j`, so it is above `p` and, in the
/// descending order within `j`'s block, writes before `p`. A prime `j` is written by no prime:
/// a writer `p` divides `j`, so `p = j`, but `p` writes only from `p^2 > j`. So `j` stays 0
/// and gets the marker at the end of its block, as 0 and 1, never written, keep 0. (The
/// textbook segmented sieve; the proof here is complete, and no paper is relied on.)
// Complexity tradeoff: the linear sieve this replaced (one write per composite, at most
// `2 top` steps, O(top)) wrote `least(i q)` for each listed prime `q <= least(i)`, spread over
// the whole table, so once the table (2 top bytes) left the caches nearly every write missed.
// Measured (FAIL-bench-least-prime-factors-scaling, 2026-11-19, release, perf stat at load
// 70 on 32 cores): from top = 2^20 to 2^23, instructions rose 7.95 times (145M to 1157M,
// linear) but cycles 11.1 times (82M to 914M), with cache misses 12.2 times (0.65M to 7.89M,
// 0.62 to 0.94 a table entry); the timing example's T(8n)/T(n) was 11.2 to 14.0 (dry1). This
// sieve does O(top log log top) writes, each inside one block that stays in the cache; on
// its whole domain, `top < 2^32`, that is still linear with a small constant: a prime `p`
// writes at most `top / p + 1` times, so there are at most `top S + pi(2^16)` writes, with
// `S` the sum of `1 / p` over the primes below 2^16, which the test
// `the_sieve_writes_fewer_than_three_times_top` computes as 2.6678 (below 3). A
// block holds at least `isqrt(top) + 1` entries, so the cost of finding a prime's first
// multiple in a block, one division, is below that prime's writes there: O(top log log top)
// in all. A fixed block length B would add `(top / B) pi(sqrt top)` divisions,
// O(top^1.5 / (B log top)). Measured after: see COMPLEXITY.md, row
// FAIL-bench-least-prime-factors-scaling.
// For primality alone, [`odd_primes_below`] is the second sieve, kept for a measured reason:
// it holds half a byte per number, against 2 bytes here (DRY-number-theory).
pub fn least_prime_factors(top: u32) -> Vec<u16> {
    least_prime_factors_in_blocks(top, SIEVE_BLOCK.max(top.isqrt() as usize + 1))
}

/// [`least_prime_factors`] with blocks of `block` entries, so that the tests can run block
/// edges on small tables. Any `block >= 1` gives the same table, by the proof at
/// [`least_prime_factors`]; only the cost depends on it.
fn least_prime_factors_in_blocks(top: u32, block: usize) -> Vec<u16> {
    // `top as usize` is exact: `usize` is 64 bits on the one supported target (Linux x86_64).
    let len = top as usize + 1;
    let mut table = vec![0u16; len];
    let r = top.isqrt();
    let odd = odd_primes_below(u64::from(r) + 1);
    // The primes up to `r` (and perhaps `r + 1`, which writes nothing: its square is past
    // `top`), from the greatest down. `r + 1 <= 2^16`, and 2^16 is even, so each is at most
    // 65535 and fits a `u16`; 65535 = 3 * 5 * 17 * 257 is not prime, so none is the marker.
    let primes: Vec<u16> = (1..odd.len())
        .rev()
        .filter(|&i| odd[i])
        .map(|i| (2 * i + 1) as u16)
        .chain((r >= 2).then_some(2))
        .collect();
    for lo in (0..len).step_by(block) {
        let hi = lo.saturating_add(block).min(len);
        let part = &mut table[lo..hi];
        for &p in &primes {
            let p = usize::from(p);
            let first = (p * p).max(lo.div_ceil(p) * p);
            if first >= hi {
                continue;
            }
            for j in (first - lo..hi - lo).step_by(p) {
                // `p` came from a `u16` above and is not the marker.
                part[j] = p as u16;
            }
        }
        for (j, e) in part.iter_mut().enumerate() {
            if *e == 0 && lo + j >= 2 {
                *e = PRIME;
            }
        }
    }
    table
}

/// The entries of one block of [`least_prime_factors`], at least: 2^15 `u16`s, 64 KiB, which
/// fits in the second-level cache (1 to 2 MiB a core on the x86_64 machines of the first
/// release), so the writes of a block hit the cache. Nothing relies on the value for
/// correctness: any length above 0 gives the same table (test
/// `the_least_prime_table_agrees_with_trial_division`, which also runs tops across several
/// blocks). Measured: COMPLEXITY.md, row FAIL-bench-least-prime-factors-scaling.
const SIEVE_BLOCK: usize = 1 << 15;

/// `prime[i]` holds when `2 i + 1` is prime, for `i < ceil(n / 2)`: every odd number below `n`,
/// and `n` itself when it is odd. The sieve of Eratosthenes over the odd numbers, in
/// O(n log log n) steps and `n / 2` bytes. Each odd prime `q` strikes its odd multiples from
/// `q^2` (a smaller multiple `k q` has a factor `k < q`, struck by then), and the striking
/// stops once `q^2` passes the table: a composite `c = q m` of the table, `q <= m`, has
/// `q^2 <= c < 2 ceil(n / 2)`.
// Complexity tradeoff: this is the second sieve of the module, beside [`least_prime_factors`],
// for a measured reason given there: for primality alone it is 4 to 5 times faster and holds a
// quarter of the memory. Trial division of each odd number would be O(n sqrt n / log n).
pub fn odd_primes_below(n: u64) -> Vec<bool> {
    let len = usize::try_from(n.div_ceil(2)).expect("a table held in memory");
    let mut prime = vec![true; len];
    if let Some(one) = prime.first_mut() {
        *one = false;
    }
    let mut i = 1;
    while (2 * i + 1) * (2 * i + 1) < 2 * len {
        if prime[i] {
            let q = 2 * i + 1;
            // Odd multiples of q from q * q: index (q q - 1) / 2 = q q / 2, step 2 q / 2 = q.
            for j in ((q * q) / 2..len).step_by(q) {
                prime[j] = false;
            }
        }
        i += 1;
    }
    prime
}

/// The first `n` primes, in rising order.
// Complexity tradeoff: `n` calls of [`next_prime`] cost O(n log p_n) primality tests of
// O(log p_n) products each, about 45 candidates per prime near `2^64`; the odd sieve to a bound
// that doubles from 64 until it holds `n` primes costs O(p_n log log p_n) steps over all the
// rounds (each round at most doubles the bound, so the rounds sum to at most twice the last),
// with `p_n` about `n ln n`, and `p_n` bytes at most.
pub fn first_primes(n: usize) -> Vec<u64> {
    let mut top: u64 = 64;
    loop {
        let odd = odd_primes_below(top);
        let primes: Vec<u64> = std::iter::once(2)
            .chain((1..odd.len()).filter(|&i| odd[i]).map(|i| 2 * i as u64 + 1))
            .take(n)
            .collect();
        if primes.len() == n {
            return primes;
        }
        top *= 2;
    }
}

/// Arithmetic modulo the Mersenne prime `P = 2^61 - 1`, the one copy for every residue and
/// hash of the workspace that works modulo it.
///
/// Why `2^61 - 1`. It is a Mersenne prime, so `2^61 = 1 (mod P)`: a product `x = hi 2^61 + lo`
/// reduces to `hi + lo` by a shift, a mask, an addition and one conditional subtraction, with
/// no division (a `u128 % u64` is a call into the software division). It is the largest
/// Mersenne prime below `2^64` (the next is `2^89 - 1`), so a residue and the sum of two fit a
/// `u64`, and a product fits a `u128`.
///
/// What the callers rely on:
/// - that `P` is prime, so the residues form a field: zed-kernel `num::Rat::residues` reduces
///   exponents modulo `P - 1` (Fermat), `value.rs` inverts by `x^(P - 2)` and reduces key
///   exponents modulo `P - 1`, and `poly.rs` evaluates polynomials at random points, where a
///   nonzero polynomial of degree `d` vanishes at no more than `d` of the `P` points
///   (Schwartz-Zippel);
/// - that the value never changes: hashes made with it (`text.rs` `poly_hash`, `btree.rs` map
///   sums, `value.rs` family hashes, zedc-lattice `interval.rs` content hashes, zedc
///   `suppress/addresses.rs` text hashes) must be the same on every run;
/// - that a residue is below `2^61`, which leaves the top three bits of a `u64` free:
///   `btree.rs` marks a sum by bit 62 (`NEG_ZERO`) and keeps `u64::MAX` as "no sum".
pub mod m61 {
    use num_bigint::BigUint;
    use num_traits::Zero;

    use super::rem_big_u64;

    /// The Mersenne prime `2^61 - 1`.
    pub const P: u64 = (1 << 61) - 1;

    /// `a + b mod P`, for `a < P` and `b <= P` (`b = P` is read as 0, so `sub(a, 0)` needs no
    /// special case): `a + b < 2P < 2^62`, and one subtraction brings it below `P`.
    pub const fn add(a: u64, b: u64) -> u64 {
        let s = a + b;
        if s >= P { s - P } else { s }
    }

    /// `a - b mod P`, for `a, b < P`: `a + (P - b)`, with `P - b` in `1..=P` ([`add`]).
    pub const fn sub(a: u64, b: u64) -> u64 {
        add(a, P - b)
    }

    /// `a * b mod P`, for `a, b < P`.
    // Complexity tradeoff: the fold below is a shift, a mask, an addition and a compare. The
    // compiler turns `a * b % P` by the constant `P` into multiplications too, and the two
    // measured the same (`examples/timing.rs`, 2^20 dependent products: 4.9 ms and 5.0 ms), so
    // the fold is kept for being one `const` routine with a proof, not for speed. Division by a
    // modulus known only at run time (`mul_mod`) is the slow case.
    pub const fn mul(a: u64, b: u64) -> u64 {
        let x = (a as u128) * (b as u128);
        // `2^61 = 1 (mod P)`, so the high part adds to the low part, and one subtraction ends
        // it. Proof that one is enough: `a, b <= P - 1` give `x <= (P - 1)^2 < P^2`, and
        // `P^2 - 1 = 2^61 (2^61 - 2)`, so `x >> 61 <= 2^61 - 2 = P - 1`; with `x & P <= P`,
        // `r <= 2P - 1` before the subtraction and `r <= P - 1` after it. The `as u64` casts
        // are exact: `x & P < 2^61` and `x >> 61 < 2^61`.
        let r = (x as u64 & P) + (x >> 61) as u64;
        if r >= P { r - P } else { r }
    }

    /// `b^e mod P` for any `b`, with the exponent reduced modulo `P - 1` by Fermat when `b` is
    /// not a multiple of `P`: O(n) for an `e` of n words ([`rem_big_u64`]) and 61 squarings.
    /// `0^0 = 1`.
    pub fn pow(b: u64, e: &BigUint) -> u64 {
        let base = b % P;
        if base == 0 {
            return u64::from(e.is_zero());
        }
        pow_word(base, rem_big_u64(e, P - 1))
    }

    /// `b^e mod P`, for `b < P`, by squaring over the bits of `e`: at most 64 squarings and 64
    /// products. `0^0 = 1`.
    pub const fn pow_word(mut b: u64, mut e: u64) -> u64 {
        let mut r = 1;
        while e > 0 {
            if e & 1 == 1 {
                r = mul(r, b);
            }
            b = mul(b, b);
            e >>= 1;
        }
        r
    }
}

/// The seed and generator of a random test, new on each run and printed, shared with the step
/// tests.
#[cfg(test)]
#[path = "../../../tests/src/seed.rs"]
#[allow(
    dead_code,
    reason = "each crate's tests use only some of the generator's draws"
)]
mod seed;

#[cfg(test)]
mod tests;
