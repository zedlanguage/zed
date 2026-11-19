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

use num_bigint::BigUint;

pub use factor::{factor, is_prime};

/// The greatest common divisor by Stein's binary algorithm: shifts and subtractions, no
/// division. `gcd(0, b) = b`.
// Tried and not kept: counting the trailing zeros of `b - a` so the count, the `min` and the
// difference of a step do not wait on one another (the "binary GCD" chapter of Algorithmica,
// "Algorithms for Modern Hardware"). With both loops in one file, so inlined alike, and timed
// alternately five times on 2^20 pairs of random words (DRY-number-theory, 2026-11-19, load
// about 60 on 32 cores), this loop took 64 to 76 ms and that one 77 to 87 ms; on 128-bit words
// the runs varied too much under the load to tell them apart. COMPLEXITY.md, row
// DRY-number-theory.
macro_rules! stein {
    ($(#[$doc:meta])* $name:ident, $t:ty) => {
        $(#[$doc])*
        pub const fn $name(mut a: $t, mut b: $t) -> $t {
            if a == 0 || b == 0 {
                return a | b;
            }
            let s = (a | b).trailing_zeros();
            a >>= a.trailing_zeros();
            loop {
                b >>= b.trailing_zeros();
                if a > b {
                    (a, b) = (b, a);
                }
                b -= a;
                if b == 0 {
                    return a << s;
                }
            }
        }
    };
}

stein!(
    /// The greatest common divisor of two words, `gcd(0, b) = b`.
    // Complexity tradeoff: Euclid's `(a, b) = (b, a % b)` takes O(log n) steps, each a
    // hardware division of 20 to 90 cycles; Stein's takes O(log n) steps of a shift, a compare
    // and a subtraction. Both are O(log n). Measured (DRY-number-theory, 2026-11-19, 10^6 pairs
    // of random words, dev profile): Stein 64 to 67 ms, Euclid 109 to 112 ms; COMPLEXITY.md,
    // row DRY-number-theory.
    gcd_u64,
    u64
);
stein!(
    /// The greatest common divisor of two 128-bit words, `gcd(0, b) = b`.
    // Complexity tradeoff: on 128 bits Euclid's `%` is a call into the software division
    // (`__umodti3`); both are O(log n) steps. Measured with `gcd_u64` on 10^6 pairs of random
    // 128-bit words: Stein 360 to 382 ms, Euclid 486 to 517 ms; COMPLEXITY.md, row
    // DRY-number-theory.
    gcd_u128,
    u128
);

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

/// `a * b mod m`, for `m > 0`. The operands need not be below `m`.
pub const fn mul_mod(a: u64, b: u64, m: u64) -> u64 {
    // `as` here is exact: the remainder is below `m`, a `u64` (`try_from` is not `const`).
    ((a as u128) * (b as u128) % (m as u128)) as u64
}

/// `a^e mod m`, for `m > 0`, by squaring over the bits of `e`: O(log e) products. `0^0 = 1`,
/// except modulo 1, where everything is 0.
// Complexity tradeoff: `e` products by `a` are O(e); squaring is O(log e). Montgomery form
// would save the divisions of `mul_mod` when one modulus serves many products, but costs a
// conversion in and out, more than it saves for one power of at most 64 squarings.
pub const fn pow_mod(a: u64, mut e: u64, m: u64) -> u64 {
    let (mut b, mut r) = (a % m, 1 % m);
    while e > 0 {
        if e & 1 == 1 {
            r = mul_mod(r, b, m);
        }
        b = mul_mod(b, b, m);
        e >>= 1;
    }
    r
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

/// `x^-1 mod 2^64` for an odd `x`: `3x XOR 2` is right in its low 5 bits (`x (3x XOR 2) = 1
/// mod 32` for each of the 16 odd residues modulo 32, checked by
/// `the_inverse_seed_is_right_in_five_bits`), and each of four Newton steps `y (2 - x y)`
/// doubles the right bits (`x y = 1 + 2^h t` gives `x y (2 - x y) = 1 - 2^2h t^2`): 5, 10, 20,
/// 40, 80 >= 64.
// Complexity tradeoff: the seed `x` (right in 3 bits, since `x^2 = 1 mod 8`) needs five steps
// to pass 64 bits and the seed 1 needs six; this seed costs one product and saves one or two
// steps of two products each. The extended Euclid algorithm is O(64) divisions.
pub const fn inverse_mod_2_64(x: u64) -> u64 {
    debug_assert!(x % 2 == 1, "an odd number");
    let mut y = x.wrapping_mul(3) ^ 2;
    let mut i = 0;
    while i < 4 {
        y = y.wrapping_mul(2u64.wrapping_sub(x.wrapping_mul(y)));
        i += 1;
    }
    y
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
/// The linear sieve: for `i` from 2 up, an `i` with no entry is prime, gets the marker and
/// enters the list; then `least(i * q) = q` for the listed primes `q` in rising order, stopping
/// at the first `q` above `least(i)` (which is `i` for a prime `i`) or with `i * q` above `top`.
/// Proof that every composite `j <= top` gets its least prime factor `p`, and gets it once:
/// `i = j / p` is at least `p` and below `j`, every prime factor of `i` is one of `j`, so
/// `least(i) >= p`, and each prime `q <= p` is listed by then (`q <= i`) with
/// `i * q <= j <= top`; so the loop at `i` reaches `q = p` and writes `least(j) = p`. A write
/// `least(i * q) = q` is made only with `q <= least(i)`, so `q` is the least prime factor of
/// `i * q`, and `j` fixes both `q` and `i`: one write per composite, and never over a prime's
/// marker. With at most one stopping step per `i`, the sieve takes at most `2 top` steps. (The
/// textbook linear sieve; the proof here is complete, and no paper is relied on.)
// Complexity tradeoff: the sieve of Eratosthenes takes O(top log log top) steps and answers
// only primality; this one takes O(top) steps and also gives the least prime factor, so a
// value `v <= top` factors in one division per prime factor, at most `log2 v` of them. It holds
// 2 bytes per number. For primality alone, [`odd_primes_below`] is the second sieve, kept for
// a measured reason: it holds half a byte per number and ran 4 to 5 times faster up to
// `top = 2^24` (DRY-number-theory, 2026-11-19, dev profile: 1.37 ms against 6.2 ms at 2^20,
// 24 ms against 100 ms at 2^24, 1.40 s against 1.54 s at 2^27); COMPLEXITY.md, row
// DRY-number-theory.
pub fn least_prime_factors(top: u32) -> Vec<u16> {
    // `top as usize` is exact: `usize` is 64 bits on the one supported target (Linux x86_64).
    let mut table = vec![0u16; top as usize + 1];
    let mut primes: Vec<u32> = Vec::new();
    for i in 2..=top {
        let least_i = match table[i as usize] {
            0 => {
                table[i as usize] = PRIME;
                primes.push(i);
                i
            }
            e => u32::from(e),
        };
        for &q in &primes {
            let j = u64::from(i) * u64::from(q);
            if q > least_i || j > u64::from(top) {
                break;
            }
            // `q <= least(j) <= sqrt(j) < 2^16`, by the doc comment's proof.
            table[j as usize] = q as u16;
        }
    }
    table
}

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

#[cfg(test)]
mod tests;
