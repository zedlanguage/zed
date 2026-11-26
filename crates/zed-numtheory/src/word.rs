//! Arithmetic on words: the greatest common divisor, products and powers modulo a word, and the
//! inverse modulo `2^64`; and the sieve of the odd primes. A file apart from `lib.rs`, which
//! re-exports them, since `factor.rs` uses them and `lib.rs` uses `factor.rs` (`next_prime`
//! calls `is_prime`): in one file with `lib.rs` they closed an import cycle, which the
//! import-graph test (step S.1f) refuses.

/// The greatest common divisor by Stein's binary algorithm: shifts and subtractions, no
/// division. `gcd(0, b) = b`.
///
/// Source: J. Stein, "Computational problems associated with Racah algebra", J. Comput. Phys.
/// 1(3):397-405, 1967, doi:10.1016/0021-9991(67)90047-2. Read 2026-11-21 in the publisher's
/// PDF. Section "Greatest Common Divisor", p. 400: "if a and b are odd integers and a > b,
/// then GCD(a, b) = GCD(b, (a - b)/2)"; the method sets `a_1 = max(a, b)`, `b_1 = min(a, b)`,
/// shifts `a_i - b_i` "to the right as far as possible without losing nonzero digits"
/// (SHIFT), keeps the larger and the smaller of the result and `b_i`, and stops when
/// `a_n = b_n`, which is the GCD; the steps are at most the bit length of `a_1` less one. The
/// loop below is that method: each difference loses all its twos in one shift, and a zero
/// difference is the stop `a_n = b_n`. The paper treats odd operands only; an earlier note
/// here gave it the rules for even operands, which it does not state. Those are added here,
/// with this proof: for `a = 2^i a'` and `b = 2^j b'` with `a'`, `b'` odd, every common odd
/// divisor divides `a'` and `b'`, and the common power of two is `2^min(i, j)`, so `gcd(a, b)
/// = 2^min(i, j) gcd(a', b')`. The code takes `s = min(i, j)` as the trailing zeros of `a | b`,
/// works on the odd parts, and shifts the result back by `s`. The paper's other method (p. 401,
/// left shifts by the count of a normalize instruction) is not used.
/// `the_word_gcds_agree_with_euclid` checks both widths against Euclid's algorithm on all
/// pairs below 200, on edge words, on random words with a common factor and on powers of two
/// at the top bit; it samples the large words, so it cannot show that no pair fails.
// Tried and not kept: counting the trailing zeros of `b - a` so the count, the `min` and the
// difference of a step do not wait on one another (the "binary GCD" chapter of S. Slotin,
// "Algorithms for Modern Hardware", https://en.algorithmica.org/hpc/algorithms/gcd/). With both
// loops in one file, so inlined alike, and timed alternately five times on 2^20 pairs of random
// words (DRY-number-theory, 2026-11-19, load about 60 on 32 cores), this loop took 64 to 76 ms
// and that one 77 to 87 ms; on 128-bit words the runs varied too much under the load to tell
// them apart. COMPLEXITY.md, row DRY-number-theory.
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

// `#[inline]` on the three word routines below: zed-kernel and the compiler crates call them
// in loops, and both sides are dylibs, so without it each is a call out of line (the reason
// given at `m61`).

/// `a * b mod m`, for `m > 0`. The operands need not be below `m`.
#[inline]
pub const fn mul_mod(a: u64, b: u64, m: u64) -> u64 {
    // `as` here is exact: the remainder is below `m`, a `u64` (`try_from` is not `const`).
    ((a as u128) * (b as u128) % (m as u128)) as u64
}

/// `(a + b) mod m`, for `m > 0`. The operands need not be below `m`: the sum is taken in 128
/// bits, so it never overflows, and a caller may pass `b = m` (zedc-presburger's sumset walks
/// back by `b = r - v`, which is `r` at `v = 0`; XR-presburger4 round 4 P4-D).
#[inline]
pub const fn add_mod(a: u64, b: u64, m: u64) -> u64 {
    // `as` is exact: the remainder is below `m`.
    ((a as u128 + b as u128) % (m as u128)) as u64
}

/// `(a b + c) mod m`, for `m > 0`. The operands need not be below `m`: `a b + c <= (2^64 - 1)^2
/// + 2^64 - 1 < 2^128`, so the 128-bit sum never overflows.
#[inline]
pub const fn mul_add_mod(a: u64, b: u64, c: u64, m: u64) -> u64 {
    // `as` is exact: the remainder is below `m`.
    ((a as u128 * b as u128 + c as u128) % (m as u128)) as u64
}

/// `a^-1 mod m`, the `x` in `0..m` with `a x = 1 (mod m)`, for `m > 0`; `None` when `a` and `m`
/// share a factor (`a = 0` among them, for `m > 1`). Modulo 1 every number is 0, the inverse of
/// every `a`, so it is `Some(0)`. The one routine for a word modulus (DRY-num-words-2026-11-26):
/// it replaced two copies of Fermat's `a^(m - 2)` (zed-numtheory `siqs`, zed-kernel
/// `num::fast`'s Garner constants), which were right only for a prime `m` and gave 0 for
/// `a = 0`, and an extended Euclid in i128 (zed-kernel `types::empty`).
///
/// The extended Euclidean algorithm on `(m, a mod m)`, keeping the cofactor `s_i` of `a` with
/// `s_i a = r_i (mod m)`: `(r_0, s_0) = (m, 0)`, `(r_1, s_1) = (a mod m, 1)`, then
/// `r_(i+1) = r_(i-1) - q_i r_i`, `s_(i+1) = s_(i-1) - q_i s_i` for `q_i = floor(r_(i-1) / r_i)`,
/// until `r_(k+1) = 0`; `r_k = gcd(a, m)`, and when it is 1, `s_k a = 1 (mod m)`.
///
/// Proof that the cofactors fit an `i128` and that `s_k` reduces by one addition. The `s_i`
/// from `s_1` on alternate in sign (`s_2 = -q_1`, and `s_(i+1) = s_(i-1) - q_i s_i` adds two
/// terms of the sign of `s_(i-1)`), so `|s_(i+1)| = |s_(i-1)| + q_i |s_i|`. By induction
/// `|s_i| r_(i-1) + |s_(i-1)| r_i = m` for `i >= 1`: at `i = 1` it is `1 · m + 0 = m`, and
/// `|s_(i+1)| r_i + |s_i| r_(i+1) = |s_(i-1)| r_i + q_i |s_i| r_i + |s_i| (r_(i-1) - q_i r_i)`,
/// which is the case `i`. So for `r_i >= 1`, `q_i |s_i| <= |s_(i+1)| <= m / r_i <= m < 2^64`:
/// every product and sum fits an `i128` with room. At the end `r_k = 1`, and for `m >= 2`,
/// `r_(k-1) >= 2` (the remainders fall strictly, and `r_0 = m >= 2`), so `|s_k| <= m / 2 < m`
/// and `s_k + m` is in `0..m` when `s_k < 0`; for `m = 1` the loop does not run and
/// `s_0 = 0`.
///
/// Tests: `tests::inverses_modulo_a_word`, against `a x mod m` and, for a prime `m`, against
/// Fermat's `a^(m - 2)`, the copies it replaced.
// Complexity tradeoff: Fermat's `a^(m - 2)` is up to 128 products modulo `m`, each a 128-bit
// remainder (a call into `__umodti3`); Euclid's algorithm takes O(log m) steps, each one 64-bit
// hardware division, and needs no prime modulus. The step count is at most 91 for a word: n
// steps need `m >= F_(n+2)`, the Fibonacci number (G. Lamé, 1844; D. E. Knuth, The Art of
// Computer Programming, vol. 2, 3rd ed., sec. 4.5.3, from memory, not checked), and
// `F_94 > 2^64`. zed-numtheory's `bezout_i128` gives the same cofactor
// but divides in 128 bits at every step.
#[inline]
pub const fn inverse_mod_u64(a: u64, m: u64) -> Option<u64> {
    assert!(m > 0, "a modulus above 0");
    let (mut r0, mut r1) = (m, a % m);
    let (mut s0, mut s1) = (0i128, 1i128);
    while r1 != 0 {
        let q = r0 / r1;
        (r0, r1) = (r1, r0 - q * r1);
        (s0, s1) = (s1, s0 - q as i128 * s1);
    }
    if r0 != 1 {
        return None;
    }
    // `as` is exact: `s0` is in `-m..m` (proof above), so the sum is in `0..m`.
    Some(if s0 < 0 {
        (s0 + m as i128) as u64
    } else {
        s0 as u64
    })
}

/// `a^e mod m`, for `m > 0`, by squaring over the bits of `e`: O(log e) products. `0^0 = 1`,
/// except modulo 1, where everything is 0.
// Complexity tradeoff: `e` products by `a` are O(e); squaring is O(log e). Montgomery form
// (cited at `factor.rs` `Montgomery`) would save the divisions of `mul_mod` when one modulus
// serves many products, but costs a conversion in and out, more than it saves for one power of
// at most 64 squarings.
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

/// `floor(n^(1/3))`, the integer cube root.
///
/// Exact for every `n`: the float estimate only starts the search, and the two loops end at the
/// one `r` with `r^3 <= n < (r + 1)^3`, the cubes taken in `u128` (`r < 2^22`, so `(r + 1)^3 <
/// 2^67`). The estimate is within 1 of the root, so each loop runs at most once or twice: `n`
/// rounds to a float within a relative `2^-53`, the cube root (`libm` `cbrt`) adds about one
/// unit in the last place, and the root is below `2^22`, so the absolute error is below
/// `2^22 * 2^-51 < 1` and the truncation adds less than 1. No step of the result rests on that:
/// a worse estimate only costs more turns of the loops. `the_cube_roots_are_exact` checks it at
/// every cube `k^3` and its neighbors up to `2^64 - 1`.
// Complexity tradeoff: binary search on the root is about 22 steps of a cube each; Newton's
// method in integers needs a division per step; the float estimate costs one `cbrt` and one or
// two cubes.
pub fn cbrt_floor(n: u64) -> u64 {
    // `as` from a float saturates and truncates: an estimate, corrected below.
    let mut r = (n as f64).cbrt() as u64;
    let cube = |r: u64| u128::from(r).pow(3);
    while cube(r) > u128::from(n) {
        r -= 1;
    }
    while cube(r + 1) <= u128::from(n) {
        r += 1;
    }
    r
}

/// Whether `v` is the square of an integer, and that integer.
///
/// A square is a square modulo 64, so the filter `SQUARES_MOD_64` (the residues `i^2 mod 64`,
/// computed below, 12 of the 64) never turns a square away; the rest are decided by `isqrt`,
/// exactly. `the_square_test_is_exact` checks it against squaring.
// Complexity tradeoff: `isqrt` of a `u128` is a few dozen word operations; the filter rejects
// 52 of 64 residues with one shift and mask, so most non-squares cost no root.
pub fn sqrt_exact_u128(v: u128) -> Option<u128> {
    const SQUARES_MOD_64: u64 = {
        let mut mask = 0u64;
        let mut i = 0;
        while i < 64 {
            mask |= 1 << (i * i % 64);
            i += 1;
        }
        mask
    };
    if SQUARES_MOD_64 >> (v % 64) & 1 == 0 {
        return None;
    }
    let s = v.isqrt();
    (s * s == v).then_some(s)
}

/// Whether `v` is the `k`-th power of an integer, for `k >= 3`, and that integer.
///
/// The float estimate `v^(1/k)` only starts the search: the two loops end at the one `r` with
/// `r^k <= v < (r + 1)^k`, the powers taken with `checked_pow`, an overflow counting as above
/// `v`. The root is below `2^43` (`k >= 3`, `v < 2^128`), so the estimate is off by far less than
/// 1 and each loop runs once or not at all; a worse estimate would only cost more turns.
/// `odd_roots_are_exact` checks it against powering.
// Complexity tradeoff: one `powf` and two or three powers of at most `log2 k` products each;
// binary search on the root costs about 43 powers.
pub(crate) fn root_exact_u128(v: u128, k: u32) -> Option<u128> {
    debug_assert!(k >= 3);
    let above = |r: u128| r.checked_pow(k).is_none_or(|p| p > v);
    // `as` from a float saturates and truncates: an estimate, corrected below.
    let mut r = (v as f64).powf(1.0 / f64::from(k)) as u128;
    while r > 0 && above(r) {
        r -= 1;
    }
    while !above(r + 1) {
        r += 1;
    }
    (r.pow(k) == v).then_some(r)
}

/// `x^-1 mod 2^64` for an odd `x`: `3x XOR 2` is right in its low 5 bits (`x (3x XOR 2) = 1
/// mod 32` for each of the 16 odd residues modulo 32, checked by
/// `the_inverse_seed_is_right_in_five_bits`), and each of four Newton steps `y (2 - x y)`
/// doubles the right bits (`x y = 1 + 2^h t` gives `x y (2 - x y) = 1 - 2^2h t^2`): 5, 10, 20,
/// 40, 80 >= 64.
// Complexity tradeoff: the seed `x` (right in 3 bits, since `x^2 = 1 mod 8`) needs five steps
// to pass 64 bits and the seed 1 needs six; this seed costs one product and saves one or two
// steps of two products each. The extended Euclid algorithm is O(64) divisions.
// `#[inline]`: zed-kernel's binary gcd (`num::fast`) calls it once per step of its inner loop.
#[inline]
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

/// `x^-1 mod 2^128` for an odd `x`: [`inverse_mod_2_64`] of the low word, right in 64 bits
/// (the inverse modulo `2^64` depends only on `x mod 2^64`), and one more Newton step, which
/// doubles the right bits to 128 (the argument at [`inverse_mod_2_64`]). The one copy
/// (DRY-num-words-2026-11-26): zed-numtheory's `Montgomery` on `u128` and zed-kernel's binary
/// gcd step (`num::fast::step`) each wrote the step out. Test:
/// `tests::inverses_modulo_2_128_are_inverses`.
#[inline]
pub const fn inverse_mod_2_128(x: u128) -> u128 {
    let y = inverse_mod_2_64(x as u64) as u128;
    y.wrapping_mul(2u128.wrapping_sub(x.wrapping_mul(y)))
}

/// `prime[i]` holds when `2 i + 1` is prime, for `i < ceil(n / 2)`: every odd number below `n`,
/// and `n` itself when it is odd. The sieve of Eratosthenes over the odd numbers, in
/// O(n log log n) steps and `n / 2` bytes. Each odd prime `q` strikes its odd multiples from
/// `q^2` (a smaller multiple `k q` has a factor `k < q`, struck by then), and the striking
/// stops once `q^2` passes the table: a composite `c = q m` of the table, `q <= m`, has
/// `q^2 <= c < 2 ceil(n / 2)`. In this file, not `lib.rs`, since the cost table test of
/// `factor.rs` uses it and `lib.rs` uses `factor.rs`: from `lib.rs` it closed an import cycle.
// Complexity tradeoff: this is the second sieve of the crate, beside `least_prime_factors` in
// `lib.rs`, for a measured reason given there: for primality alone it is 4 to 5 times faster
// and holds a quarter of the memory. Trial division of each odd number would be
// O(n sqrt n / log n).
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
