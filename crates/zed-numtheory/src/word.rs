//! Arithmetic on words: the greatest common divisor, products and powers modulo a word, and the
//! inverse modulo `2^64`. A file apart from `lib.rs`, which re-exports them, since `factor.rs`
//! uses them and `lib.rs` uses `factor.rs` (`next_prime` calls `is_prime`): in one file with
//! `lib.rs` they closed an import cycle, which the import-graph test (step S.1f) refuses.

/// The greatest common divisor by Stein's binary algorithm: shifts and subtractions, no
/// division. `gcd(0, b) = b`.
///
/// Source: J. Stein, "Computational problems associated with Racah algebra", J. Comput. Phys.
/// 1(3):397-405, 1967, doi:10.1016/0021-9991(67)90047-2: `gcd(2a, 2b) = 2 gcd(a, b)`, `gcd(2a,
/// b) = gcd(a, b)` for odd `b`, and `gcd(a, b) = gcd(|a - b|, min(a, b))` for odd `a`, `b`.
/// Departure: the common power of two is taken out at once by `trailing_zeros` and put back
/// at the end, and each odd part loses all its twos in one shift, not one bit per step.
/// Checked 2026-11-20: the DOI on Crossref; the paper not read, the rules from memory (they
/// are elementary). `the_word_gcds_agree_with_euclid` checks both widths against Euclid's
/// algorithm on random words with a common factor and on powers of two at the top bit.
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

/// `a * b mod m`, for `m > 0`. The operands need not be below `m`.
pub const fn mul_mod(a: u64, b: u64, m: u64) -> u64 {
    // `as` here is exact: the remainder is below `m`, a `u64` (`try_from` is not `const`).
    ((a as u128) * (b as u128) % (m as u128)) as u64
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

/// `x^-1 mod 2^64` for an odd `x`:`3x XOR 2` is right in its low 5 bits (`x (3x XOR 2) = 1
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
