//! Subquadratic arithmetic on wide integers: multiplication by number-theoretic transforms,
//! division by a Newton reciprocal, the binary recursive gcd of Stehlé and Zimmermann, and
//! decimal printing by halves. num-bigint 0.4.8's multiplication is Toom-3, about `n^1.46`; its
//! division above 64 words is Burnikel and Ziegler's recursion over that multiplication, and
//! its decimal printing is by halves over that division, both about `n^1.46` too; its gcd is
//! Stein's, O(n^2) (COMPLEXITY.md K30 and K41).
//!
//! `M(n)` below is the cost of a product of two `n`-bit numbers, O(n log n) here. Division
//! costs O(M(n)), and gcd and printing O(M(n) log n). Below a leaf size each operation hands
//! its operands to num-bigint, which is faster there; the value computed does not depend on
//! the leaf sizes.
//!
//! # The methods
//!
//! A number is a list of 64-bit words, the coefficients of a polynomial in `2^64`. The design
//! makes the product O(n log n) and builds division, gcd and printing from a bounded number of
//! products at each level of a recursion that halves the width.
//!
//! **Multiplication** ([`mul`], [`transform_mul`]). The product of two numbers is the
//! convolution of their word lists followed by carrying, O(n^2) done directly. A transform
//! turns the convolution into pointwise products: evaluate both polynomials at the `n`-th
//! roots of unity ([`Field::forward`], an FFT), multiply the values pairwise, interpolate back
//! ([`Field::inverse`]), O(n log n). The arithmetic is modulo a prime `p = c 2^50 + 1`, so roots
//! of unity of every order up to `2^50` exist and the values are exact; a coefficient of the
//! convolution can reach `n 2^128`, more than one 62-bit prime holds, so the convolution is
//! done modulo three primes ([`FIELDS`], product above `2^185`) and each coefficient rebuilt by
//! the Chinese remainder theorem in Garner's form, then the carries propagated, in one pass.
//! Products modulo `p` use Montgomery's form and Shoup's precomputed quotients for the
//! twiddle factors. The length is padded to a power of two, so the time rises in steps:
//! doubling the padded length doubles the time, and sizes between two powers cost the same. A
//! square needs one forward transform fewer. A factor with few nonzero words (as `2^s + 1`,
//! which the exact numbers keep) is multiplied by schoolbook over those words
//! ([`sparse_mul`]). Above [`MUL_LEAF`] words in the narrower factor, [`mul`] takes whichever of
//! three computed costs is lowest: rows over nonzero words, the transforms ([`transform_plan`])
//! and num-bigint's product ([`TOOM_COST`]); at or below it, num-bigint's.
//!
//! **Division** ([`div_rem`], [`Level`], [`approx_reciprocal`]). To divide by `d` of `n` bits
//! a quotient of `k <= n` bits, take the top `k` bits `t` of `d` and an approximate reciprocal
//! `X`, `t X < 2^2k <= t (X + 2)`, from Newton's iteration (Brent and Zimmermann, Modern
//! Computer Arithmetic, Algorithm 3.5): from a reciprocal of [`RECIP_LEAF`] bits by
//! num-bigint's division, each step goes from `h = ceil((p + 3) / 2)` bits to `p` with two
//! cyclic products of `p / 2` bits that share one factor's transforms ([`newton`]), so the
//! whole costs about 5/3 of a product of `k` bits. With `X` taken to `w = 64 ceil(k / 64)`
//! bits, the estimate `q0 = xh + floor(xh (X - 2^w) / 2^w)`, `xh` the dividend's bits above
//! the divisor's, is a product of `k` bits, at most four below the quotient (two above it when
//! `k < n`), and the remainder `x - q0 d`, in `(-2d, 5d)`, is a cyclic product of `d`'s width
//! modulo `2^(64 m) - 1` read back by its low word ([`unfold`]); at most four steps of `d`
//! correct both. A quotient wider than the divisor is found in blocks
//! of the divisor's width ([`div_rem_blocks`]) by one [`Divisor`], whose reciprocal and both
//! factors' transforms are built once: about one product of the divisor's width a block. A
//! divisor with few nonzero words is divided by long division over those words
//! ([`sparse_div_rem`]), chosen by computed cost as for products.
//!
//! **Gcd** ([`gcd`], [`half`], [`step`], [`half_leaf`]). Euclid's algorithm takes O(n) steps of
//! O(n) each. The half gcd avoids touching the full numbers at each step. It uses the binary
//! step: with `a` odd and `b = 2^j b'`, `b'` odd, choose `q`, `|q| < 2^j`, with `a + q b'`
//! divisible by `2^(j+1)` ([`inverse_mod_pow2`] gives `q`), and replace the pair by
//! `(b', (a + q b') / 2^j)`. This keeps the gcd's odd part ([`gcd`] divides each number by its
//! own power of two first and multiplies the result by the smaller power at the end), and is the 2 by 2 integer matrix `[[0, 2^j], [2^j, q]]` over `2^2j` ([`Mat`]).
//! Because the steps work from the low end, the steps whose halvings total at most `k` depend
//! only on `a` and `b` modulo `2^(2k+1)`: no carry from the high bits reaches them, which is
//! why the binary form is used rather than the classical half gcd, which works from the high
//! end and must correct for carries. So [`half`] finds the matrix of the first half of the
//! steps from residues of half the width, applies it to the whole pair (a few products), takes
//! one step, and recurses on the second half: `T(n) = 2 T(n/2) + O(M(n))`, O(M(n) log n). The
//! recursion's leaf ([`half_leaf`], at or below [`HALF_LEAF`]) runs on 128-bit integers, which
//! the residues and matrix entries provably never exceed. [`gcd`] repeats one half gcd and one
//! step until the second number is zero, and hands what is left to num-bigint's Stein gcd at
//! or below [`GCD_LEAF`]. Reference: Stehlé and Zimmermann, "A binary recursive gcd
//! algorithm", ANTS 2004.
//!
//! **Printing** ([`to_decimal`]). The powers `10^(L 2^i)`, `L` being [`PRINT_LEAF`], are built
//! once by squaring. `x` is written as `high 10^(L 2^i) + low` by one division by the largest
//! power at most `x`, and each half is printed by the next power down, the low half padded with
//! zeros to its fixed width. The largest power's reciprocal is found by Newton's iteration to
//! only the precision that division and the level below need; each power below is a
//! [`Level`] whose reciprocal is derived from the one above by one product and one cyclic
//! product ([`derive()`]), and whose reciprocal and power are transformed once for all its
//! divisions. A division at a level takes one product for the quotient and one cyclic product
//! of half its length for the remainder, which lies in `[0, 4d)` and so is found modulo
//! `2^(64 m) - 1`. Each level divides numbers of `n` bits in total, O(M(n)), over
//! `log2(n / L)` levels: O(M(n) log n). Parts below powers of [`PRINT_HANDOFF`] words, and
//! numbers of fewer than [`PRINT_WHOLE`] words, are printed by num-bigint.
//!
//! **Where the constants lose** (measured 2026-11-06 and, for products, 2026-11-07;
//! COMPLEXITY.md section "Crossovers"). A transform product costs three convolutions and the
//! recombination, so num-bigint's product is faster up to about 1024 words a factor, and
//! again just above each power of two of the transform's points, up to about 6144 words, where
//! the padding nearly doubles the transform's time. Division of `2w` by `w` words costs about
//! 4.1 squarings of `w` words from 16,384 to 131,072 words (KERNEL-div-newton, 2026-11-09; it
//! was 7.4 to 12.4 before), and takes 1.3 to 2.5 times num-bigint's Burnikel and Ziegler
//! division's time from 96 to 4096 words, the same at 8192 and 0.76, 0.59 and 0.46 times at
//! 16,384, 32,768 and 65,536 (load 15 to 17); printing, by the levels above, is slower than
//! num-bigint's up to about 60,000 words (2026-11-08), where its fixed costs (the powers, one
//! Newton reciprocal) outweigh num-bigint's `n^1.5`.
//! The gcd gains from about 300 words, since num-bigint's is quadratic. Open for the port:
//! [`DIV_LEAF`] against the crossover near 8192 words measured above, by a computed cost as
//! [`TOOM_COST`] is for products; and [`PRINT_WHOLE`], set when [`reciprocal`] cost about
//! three products and is now [`approx_reciprocal`] and one cyclic product, not measured again.
//!
//! **At the port to Zed.** The results must stay those of num-bigint's operations, which the
//! unit tests compare at every leaf setting. What depends on measurement and is to be measured
//! again on the Zed code: the leaves [`MUL_LEAF`], [`DIV_LEAF`], [`RECIP_LEAF`], [`GCD_LEAF`],
//! [`PRINT_HANDOFF`], [`PRINT_WHOLE`] and the cost constants [`TOOM_COST`],
//! [`TRANSFORM_COST`], [`SPARSE_WORD`], [`SPARSE_STEP`]. [`HALF_LEAF`] and [`PRINT_LEAF`] are
//! derived, not measured. The Rust constructs that need a Zed form are listed in
//! ZED_PORT_GAPS.md, sections "Entries from NUM-subquad", "Entries from BIGINT-fast-mul" and
//! "Entries from NUM-print-fast".
//!
//! Each leaf is a crossover between two methods whose results are identical, set from timings
//! rather than solved from the two methods' cost formulas. The author accepted this for now
//! (2026-11-06) because nothing observable changes at a crossover, on the condition that each
//! is commented with the timings it rests on. The timings move with the load and the code: at
//! load 45 to 75 on 2026-11-05 multiplication and the gcd crossed at about 1024 and 512 words,
//! at load 1 on 2026-11-06 at about 4096 and 300. They are to be measured again when this file
//! is rewritten in Zed for self-hosting, by the procedure in COMPLEXITY.md section
//! "Crossovers", which also lists the curves on both sides of each leaf and what is not yet
//! understood about them. Where one method is never slower than the other, it is used alone,
//! with no crossover.

use std::borrow::Cow;
use std::rc::{Rc, Weak};

use num_bigint::{BigInt, BigUint, Sign};
use num_integer::Integer;
use num_traits::{One, Signed, ToPrimitive, Zero};

/// The 64-bit words at or below which the narrower factor goes to num-bigint's
/// multiplication, the other methods' costs not computed. Measured on 2026-11-07 at load 34
/// to 41 (BIGINT-fast-mul), the transform took 1.74 times num-bigint's time at 256 by 256
/// words, 1.30 at 512 by 512, 1.16 at 256 by 65536 and 1.07 at 512 by 65536, slower at every
/// shape measured with the narrower at 512 words or fewer; above, [`TOOM_COST`] decides. It
/// was 1024 from 2026-11-05 (load 68), when the transform's constant was higher (COMPLEXITY.md,
/// "Crossovers"). Measured again on 2026-11-12 (RADIX-depth) in instructions, in the test
/// build, after the transform's constant fell to 7: at 512 by 512 words the transform takes
/// 1.24 million against num-bigint's 1.02, at 1024 by 1024 2.68 against 2.76, so the
/// instruction counts cross between, and 512 stands. The product does not depend on it; the
/// unit tests use a smaller leaf, so that they reach the transforms at small sizes.
#[cfg(not(test))]
const MUL_LEAF: usize = 512;
#[cfg(test)]
const MUL_LEAF: usize = 48;

/// num-bigint 0.4.8's cost of a product of `s` by `l >= s` words, per `l s^0.465`, in the
/// units of [`TRANSFORM_COST`]. Its multiplication is Toom-3 above 256 words, `s^log3(5)` =
/// `s^1.465` for balanced factors, and cuts the longer factor in halves while it has twice
/// the other's words (`biguint/multiplication.rs` lines 102 to 166), so `l / s` such products.
/// It was 10.4 from times measured on 2026-11-07 (BIGINT-fast-mul). Measured again on
/// 2026-11-12 (RADIX-depth) in instructions, in the test build, over balanced factors of 512
/// to 24,576 words: 6.48 to 7.19 units per `l s^0.465`, 6.8 on average. With it and
/// [`TRANSFORM_COST`] the two methods' instruction counts cross where they are measured to:
/// num-bigint's product is taken at 768 by 768 words (1.80 million instructions against the
/// transform's 2.53) and the transform at 1024 by 1024 (2.68 against 2.76) and from 2048
/// (5.54 against 8.12). Between, the two are near: the transform is taken at 1280 by 1280
/// (3.99 against 3.92) and 1536 by 1536 (5.42 against 5.17), where the wrapped plan of
/// [`points`] is estimated within 1% of num-bigint's product. The product does not depend on
/// it; the unit tests never take num-bigint's product above [`MUL_LEAF`], so that they reach
/// the transforms.
#[cfg(not(test))]
const TOOM_COST: f64 = 6.8;
#[cfg(test)]
const TOOM_COST: f64 = f64::INFINITY;

/// `log3(5) - 1`, the exponent of the narrower factor in [`TOOM_COST`].
const TOOM_POWER: f64 = 0.465;

/// The bits at or below which the divisor, or the quotient, goes to num-bigint's division,
/// which then costs at most this many bits times the dividend's. The result does not depend
/// on it. Not measured when it was set. On 2026-11-06 at load 1, the Newton division then used
/// took 1.13 times num-bigint's time at `w` = 64, 1.00 at 96, 2.03 at 1024, 3.84 at 2048 and
/// 2.60 at 8192 words, for `2w` by `w`. The division by [`Level`] (KERNEL-div-newton) took, on
/// 2026-11-09 at load 15 to 17, 1.31 times at 96, 2.54 at 1024, 1.88 at 2048, 1.36 at 4096,
/// 1.02 at 8192, 0.76 at 16,384 and 0.46 at 65,536: the curves cross near 8192 words, not
/// moved here (COMPLEXITY.md, "Crossovers").
const DIV_LEAF: u64 = 64 * 64;

/// The bits at or below which a reciprocal is found by num-bigint's division. Not measured
/// apart from [`DIV_LEAF`]. The reciprocal does not depend on it; the unit tests use the
/// least that Newton's step allows, 4 (a step to `p` bits starts from `ceil((p + 3) / 2)`,
/// fewer only for `p >= 5`), so that every step is reached on small numbers.
#[cfg(not(test))]
const RECIP_LEAF: u64 = 64 * 32;
#[cfg(test)]
const RECIP_LEAF: u64 = 4;

/// The bits at or below which the gcd of what is left goes to num-bigint's gcd: near the
/// crossover measured on 2026-11-05, 2.2 ms against 1.7 ms at 256 words and 12 ms against
/// 30 ms at 1024 (load 75). Measured again on 2026-11-06 at load 1, the half gcd takes 1.20
/// times num-bigint's time at 256 words, 0.76 at 384, 0.78 at 512 and 0.50 at 1024, so the
/// curves cross near 300 words (COMPLEXITY.md, "Crossovers"). The gcd does not depend on it;
/// the unit tests use a smaller leaf.
#[cfg(not(test))]
const GCD_LEAF: u64 = 64 * 512;
#[cfg(test)]
const GCD_LEAF: u64 = 64 * 16;

/// The valuation budget at or below which the half gcd runs its steps on 128-bit integers:
/// residues of `2k + 1 <= 121` bits stay below `2^120`, and so do the matrix entries.
const HALF_LEAF: u64 = 60;

/// The digits of the narrowest power of ten [`to_decimal`] divides by, `10^597`: the most
/// digits whose power fits in 31 words (`597 log2(10) < 1984 = 31 * 64 < 598 log2(10)`), so
/// that `10^(L 2^i)` has at most `31 * 2^i` words and its cyclic product (see [`Level`]) is
/// on `32 * 2^i` points, a power of two with little padding. Derived, not measured.
const PRINT_LEAF: usize = 597;

/// The widest power of ten, in words, by which [`to_decimal`] hands a part to num-bigint rather
/// than split it further. Measured on 2026-11-08 (load 23 to 28), the whole print of 320,000
/// and 1,280,000 digits takes 72.9 and 386 ms with 62 words, 69.0 and 351 with 124, 67.0 and
/// 345 with 248, 66.8 and 343 with 496, 65.6 and 344 with 992, 68.1 and 413 with 1984 and
/// 80.5 and 383 with 3968: flat from 248 to 992 words. The digits do not depend on it.
#[cfg(not(test))]
const PRINT_HANDOFF: usize = 496;
/// One in the unit tests, below every power's words, so that their small numbers reach the
/// transforms.
#[cfg(test)]
const PRINT_HANDOFF: usize = 1;

/// The fewest words of a number that [`to_decimal`] splits itself; a narrower one is printed
/// whole by num-bigint. Measured on 2026-11-08 (load 6 to 5, five runs each), num-bigint
/// against [`to_decimal`] above this takes 211 against 239 ms at 49,829 words (1.13), 236
/// against 251 at 53,982 (1.07), 262 against 264 at 58,134 (1.01), 292 against 273 at 62,287
/// (0.93), 353 against 337 at 66,439 (0.96), 396 against 374 at 74,744 (0.94), 664 against
/// 575 at 107,963 (0.87) and 1304 against 961 at 166,097 (0.74). The digits do not depend on
/// it.
#[cfg(not(test))]
const PRINT_WHOLE: usize = 60_000;
/// One in the unit tests, so that every number of at least `3 L` bits is split.
#[cfg(test)]
const PRINT_WHOLE: usize = 1;

/// The cost of a transform product on `n` points, per `n log2(n)`, in units of one word
/// product of [`sparse_mul`]. Only which of two equal results is computed depends on it. It was
/// 12 from times measured on 2026-11-07 (BIGINT-fast-mul). Measured again on 2026-11-12
/// (RADIX-depth) in instructions, after the butterflies' reductions by a sign test, in the
/// test build: a word product of `sparse_mul` takes 16.42 instructions, and a balanced product
/// of `m` by `m` words on `n = 2m` points 7.37, 7.25, 6.86, 6.83, 6.54 and 6.53 units per
/// `n log2(n)` at `m` = 512, 1024, 2048, 4096, 8192 and 16,384: 7.
const TRANSFORM_COST: u128 = 7;

/// The cost of a word of a step of [`sparse_div_rem`], and of a step besides its words (the
/// quotient word's estimate is a 128-bit division), in the units of [`TRANSFORM_COST`]:
/// measured on 2026-11-05, 2.3 ns a word.
const SPARSE_WORD: u128 = 2;
const SPARSE_STEP: u128 = 20;

/// The number of 64-bit words of `x`.
fn words(x: &BigUint) -> usize {
    x.iter_u64_digits().len()
}

// ------------------------------------------------------------------------------------------
// Multiplication

/// A prime `c * 2^50 + 1` below `2^62`, for transforms of up to `2^50` points, with what
/// Montgomery multiplication modulo it needs.
struct Field {
    p: u64,
    /// `-p^-1 mod 2^64`.
    neg_inv: u64,
    /// `2^128 mod p`.
    r2: u64,
    /// A generator of the multiplicative group.
    root: u64,
}

impl Field {
    const fn new(p: u64, root: u64) -> Field {
        // Newton's iteration doubles the correct low bits of `p^-1`: 1, 2, 4, ..., 64.
        let mut inv = 1u64;
        let mut i = 0;
        while i < 6 {
            inv = inv.wrapping_mul(2u64.wrapping_sub(p.wrapping_mul(inv)));
            i += 1;
        }
        let r = (1u128 << 64) % p as u128;
        Field {
            p,
            neg_inv: inv.wrapping_neg(),
            r2: (r * r % p as u128) as u64,
            root,
        }
    }

    /// `a * b / 2^64 mod p`, reduced, for `a, b < 2p` (Montgomery): `a b + m p < 2^128` and its
    /// quotient by `2^64` is below `2p`, since `4p < 2^64`.
    #[inline]
    fn mul(&self, a: u64, b: u64) -> u64 {
        let t = u128::from(a) * u128::from(b);
        let m = (t as u64).wrapping_mul(self.neg_inv);
        let u = ((t + u128::from(m) * u128::from(self.p)) >> 64) as u64;
        below(u, self.p)
    }

    /// `x mod p` for any 64-bit `x`, without a division: with `q = floor(x / 2^62) <= 3`,
    /// `x - q p = (x mod 2^62) + q (2^62 - p)` lies in `[0, 2p)`, since each prime is above
    /// `2^62 - 2^57` (`2^62 + 3 * 2^57 < 2p`), and one subtraction finishes it.
    #[inline]
    fn reduce(&self, x: u64) -> u64 {
        let r = x - (x >> 62) * self.p;
        below(r, self.p)
    }

    #[inline]
    fn add(&self, a: u64, b: u64) -> u64 {
        let s = a + b;
        below(s, self.p)
    }

    #[inline]
    fn sub(&self, a: u64, b: u64) -> u64 {
        // `a - b` lies in `(-p, p)` for `a, b < p`; `a + p - b` in `(0, 2p)` is below `2^64`.
        below(a.wrapping_add(self.p).wrapping_sub(b), self.p)
    }

    /// `x * 2^64 mod p`, the Montgomery form of `x < p`.
    fn to_mont(&self, x: u64) -> u64 {
        self.mul(x, self.r2)
    }

    /// `x^e`, both in Montgomery form.
    fn pow(&self, mut x: u64, mut e: u64) -> u64 {
        let mut r = self.to_mont(1);
        while e > 0 {
            if e & 1 == 1 {
                r = self.mul(r, x);
            }
            x = self.mul(x, x);
            e >>= 1;
        }
        r
    }

    /// The roots of the stages of a transform on `n` points, a power of two, in bit-reversed
    /// order: entry `k < n/2` is `w^brv(k)`, `w` a primitive `n`-th root and `brv` the reversal
    /// of `log2(n) - 1` bits, each with its Shoup quotient (see [`Field::shoup`]). For
    /// `k < 2^s` that is `w_(2^(s+1))^brv_s(k)`, the root of block `k` of the stage with `2^s`
    /// blocks ([`Field::forward`]), so every stage reads a prefix of the table, one root a
    /// block, and the table of a larger power of two serves a smaller one. Built by doubling:
    /// `brv(2^s + i) = brv(i) + n/2^(s+2)`, so entries `2^s .. 2^(s+1)` are entries
    /// `0 .. 2^s` times `w_(2^(s+2))`. `n/2` pairs, as before, so a product's memory is
    /// unchanged.
    fn twiddles(&self, n: usize) -> Vec<(u64, u64)> {
        // `w_(2^t)` for `t` from 2 to `log2(n)`, in Montgomery form, by squaring down from a
        // primitive `n`-th root, the generator to the power `(p - 1) / n`.
        let mut step = Vec::with_capacity(n.trailing_zeros() as usize);
        let mut w = self.pow(self.to_mont(self.root), (self.p - 1) / n as u64);
        for _ in 2..=n.trailing_zeros() {
            step.push(w);
            w = self.mul(w, w);
        }
        // `mul(t, w)` of `t` in plain form and `w` in Montgomery form is `t w` in plain form.
        // The Shoup quotient `s = floor(t 2^64 / p)` is found without a division: with
        // `r = t 2^64 mod p` (`to_mont(t)`), `s p = t 2^64 - r` is exact, so
        // `s = -r p^-1 mod 2^64 = r neg_inv`, and `s < 2^64` since `t < p`.
        let mut tw = Vec::with_capacity(n / 2);
        tw.push((1, 0));
        // `step` holds `w_n, w_(n/2), ..., w_4`; doubling from 1 entry uses `w_4` first.
        for &r in step.iter().rev() {
            let have = tw.len();
            for i in 0..have {
                let t = self.mul(tw[i].0, r);
                tw.push((t, 0));
            }
        }
        for (t, s) in &mut tw {
            *s = self.to_mont(*t).wrapping_mul(self.neg_inv);
        }
        tw
    }

    /// `x w mod p`, in `[0, 2p)`, for any `x` and `w < p` with `s = floor(w 2^64 / p)`
    /// (Shoup): the quotient `x s / 2^64` is at most one below `x w / p`.
    #[inline]
    fn shoup(&self, x: u64, (w, s): (u64, u64)) -> u64 {
        let q = ((u128::from(x) * u128::from(s)) >> 64) as u64;
        x.wrapping_mul(w).wrapping_sub(q.wrapping_mul(self.p))
    }

    /// The transform of `a`, in place, `a.len()` a power of two: the evaluations at the
    /// powers of a primitive `a.len()`-th root, in bit-reversed order, by Cooley and Tukey's
    /// butterflies `(x + r y, x - r y)`, one root `r` a block ([`Field::twiddles`]), with `tw`
    /// from [`Field::twiddles`] of `a.len()` points or of any larger power of two. The entries
    /// from `filled` up are zero. Values below `4p` go in, and values below `2p` come out, the
    /// same residues (Harvey's lazy reduction: between stages every value is below
    /// `4p < 2^64`).
    ///
    /// A stage whose blocks' upper halves are all zero, as the first is for a factor padded to
    /// the points of a product, makes each block's upper half a copy of its lower half, so the
    /// leading stages of half `filled` or more are done at once by copying the first block.
    /// The other stages are done two at a time ([`Field::forward_pair`]), which loads and stores
    /// each value once for both, and an odd one left over at the end alone.
    fn forward(&self, a: &mut [u64], filled: usize, tw: &[(u64, u64)]) {
        let p2 = 2 * self.p;
        let n = a.len();
        debug_assert!(2 * tw.len() >= n, "a table of at least the points");
        debug_assert!(
            a[filled.min(n)..].iter().all(|&x| x == 0),
            "zeros from `filled` up"
        );
        let mut len = n / 2;
        while len > 0 && len >= filled {
            len /= 2;
        }
        let size = (2 * len).max(1);
        if size < n {
            let (first, rest) = a.split_at_mut(size);
            for block in rest.chunks_exact_mut(size) {
                block.copy_from_slice(first);
            }
        }
        let mut blocks = n / size;
        while len >= 2 {
            // Block `k` of the first stage of the two has root `tw[k]`; its two halves are
            // blocks `2k` and `2k + 1` of the second, with roots `tw[2k]` and `tw[2k + 1]`.
            // Index loops, not `zip`: the test build has no inlining across codegen units, so
            // `Zip::new` there is a call per block. With it, the larger run of
            // `reading_a_rat_of_two_wide_parts_scales` took 8349 M instructions; without, 7571 M.
            let first = &tw[..blocks];
            let second = tw[..2 * blocks].as_chunks::<2>().0;
            for k in 0..blocks {
                let block = &mut a[2 * len * k..2 * len * (k + 1)];
                let (wa, [wb, wc]) = (first[k], second[k]);
                match len == 2 {
                    true => self.forward_pair::<true>(block, wa, wb, wc),
                    false => self.forward_pair::<false>(block, wa, wb, wc),
                }
            }
            len /= 4;
            blocks *= 4;
        }
        if len == 1 {
            for (pair, &w) in a.as_chunks_mut::<2>().0.iter_mut().zip(&tw[..blocks]) {
                // As in [`Field::butterfly`], then each output brought below `2p` by one
                // subtraction.
                let (s, d) = self.butterfly(pair[0], pair[1], w);
                pair[0] = below(s, p2);
                pair[1] = below(d, p2);
            }
        }
    }

    /// Cooley and Tukey's butterfly `(x + w y, x - w y)` for `x, y < 4p`, each output below
    /// `4p`: `u = x mod 2p < 2p` and Shoup's `t = w y < 2p`, so `u + t < 4p` and `u + 2p - t`
    /// lies in `(0, 4p)`; `4p < 2^64`, so nothing wraps.
    #[inline]
    fn butterfly(&self, x: u64, y: u64, w: (u64, u64)) -> (u64, u64) {
        let p2 = 2 * self.p;
        let u = below(x, p2);
        let t = self.shoup(y, w);
        (u.wrapping_add(t), u.wrapping_add(p2).wrapping_sub(t))
    }

    /// Two stages of [`Field::forward`] on one block of the first, of `2 len` values, `len`
    /// at least 2: the first's butterflies of root `wa` across its halves, then the second's
    /// of roots `wb` and `wc` across each half's halves. With `LAST`, each output is brought
    /// below `2p`.
    #[inline]
    fn forward_pair<const LAST: bool>(
        &self,
        block: &mut [u64],
        wa: (u64, u64),
        wb: (u64, u64),
        wc: (u64, u64),
    ) {
        let p2 = 2 * self.p;
        let half = block.len() / 4;
        let (lo, hi) = block.split_at_mut(2 * half);
        let (q0, q1) = lo.split_at_mut(half);
        let (q2, q3) = hi.split_at_mut(half);
        let q3 = &mut q3[..half];
        // An index loop, not `zip`, as in [`Field::forward`].
        for i in 0..half {
            let (a0, a2) = self.butterfly(q0[i], q2[i], wa);
            let (a1, a3) = self.butterfly(q1[i], q3[i], wa);
            let (b0, b1) = self.butterfly(a0, a1, wb);
            let (b2, b3) = self.butterfly(a2, a3, wc);
            match LAST {
                // Each below `4p`, so one subtraction brings it below `2p`.
                true => {
                    q0[i] = below(b0, p2);
                    q1[i] = below(b1, p2);
                    q2[i] = below(b2, p2);
                    q3[i] = below(b3, p2);
                }
                false => (q0[i], q1[i], q2[i], q3[i]) = (b0, b1, b2, b3),
            }
        }
    }

    /// The inverse of [`Field::forward`] times `a.len()`, from bit-reversed order to natural
    /// order, by Gentleman and Sande's butterflies `(x + y, (x - y) / r)`, with `tw` as for
    /// [`Field::forward`]. The stage with `2^s` blocks undoes the forward stage with as many:
    /// block 0 has root 1, and for block `k` in `[2^t, 2^(t+1))`, `t < s`, `1/r` is
    /// `-tw[3 2^t - 1 - k]`. (With `r = w^b`, `w` of order `2^(s+1)`, `b = 2^(s-1-t) (2m + 1)`
    /// for `m = brv_t(k - 2^t)`, `1/r = w^(2^(s+1) - b) = -w^(2^s - b)`, and `2^s - b` is
    /// `2^(s-1-t) (2 (2^t - 1 - m) + 1)`, the exponent of entry `3 2^t - 1 - k`, since bit
    /// reversal commutes with complementing the bits.) So the blocks of group `t` read the
    /// table's entries `2^t .. 2^(t+1)` from the top down, and the sign goes into the
    /// difference: `(y - x) r'` for `r' = tw[3 2^t - 1 - k]`. The stages are done two at a
    /// time ([`Field::inverse_pair`]), an odd one left over at the end alone. Values below
    /// `2p` go in, and values below `p` come out.
    fn inverse(&self, a: &mut [u64], tw: &[(u64, u64)]) {
        let p = self.p;
        let n = a.len();
        debug_assert!(2 * tw.len() >= n, "a table of at least the points");
        let mut len = 1;
        while 4 * len <= n {
            let size = 4 * len;
            // Block 0: roots 1 and `1/tw[1]` in the first stage, 1 in the second.
            match size == n {
                true => self.inverse_pair::<true>(&mut a[..size], None, tw[1], None),
                false => self.inverse_pair::<false>(&mut a[..size], None, tw[1], None),
            }
            // Block `k` of group `t` (`2^t <= k < 2^(t+1)`): halves `2k` and `2k + 1` of
            // group `t + 1` read entries `3 2^(t+1) - 1 - 2k` and the one below it, a pair
            // of the table's entries `2^(t+1) .. 2^(t+2)` from the top down. Index loops, not
            // `zip`, as in [`Field::forward`].
            let mut group = 1;
            while group < n / size {
                let halves = tw[2 * group..4 * group].as_chunks::<2>().0;
                let whole = &tw[group..2 * group];
                for j in 0..group {
                    let k = group + j;
                    let [wb, wa] = halves[group - 1 - j];
                    let wc = whole[group - 1 - j];
                    let block = &mut a[size * k..size * (k + 1)];
                    self.inverse_pair::<false>(block, Some(wa), wb, Some(wc));
                }
                group *= 2;
            }
            len *= 4;
        }
        if len < n {
            // The last stage, one block of root 1, each output brought below `p`.
            let (lo, hi) = a.split_at_mut(len);
            for (x, y) in lo.iter_mut().zip(hi.iter_mut()) {
                let (s, d) = self.inverse_one(*x, *y);
                *x = below(s, p);
                *y = below(d, p);
            }
        } else if n == 1 && a[0] >= p {
            a[0] -= p;
        }
    }

    /// Gentleman and Sande's butterfly of root 1, `(x + y, x - y)`, for `x, y < 2p`: `x + y <
    /// 4p` and `x + 2p - y` in `(0, 4p)`, each brought below `2p` by one subtraction; `4p <
    /// 2^64`, so nothing wraps.
    #[inline]
    fn inverse_one(&self, x: u64, y: u64) -> (u64, u64) {
        let p2 = 2 * self.p;
        let (s, d) = (x.wrapping_add(y), x.wrapping_add(p2).wrapping_sub(y));
        (below(s, p2), below(d, p2))
    }

    /// Gentleman and Sande's butterfly `(x + y, (x - y) / r)` with `-1/r = w`, for `x, y <
    /// 2p`: `x + y < 4p`, brought below `2p` by one subtraction, and `(y + 2p - x) w`, Shoup's
    /// product of a value in `(0, 4p)`, below `2p`; `4p < 2^64`, so nothing wraps.
    #[inline]
    fn inverse_root(&self, x: u64, y: u64, w: (u64, u64)) -> (u64, u64) {
        let p2 = 2 * self.p;
        let s = x.wrapping_add(y);
        (
            below(s, p2),
            self.shoup(y.wrapping_add(p2).wrapping_sub(x), w),
        )
    }

    /// Two stages of [`Field::inverse`] on one block of the second, of `4 len` values: the
    /// first's butterflies across each half's halves, the lower half's with `-1/r = wa` (root
    /// 1 for `None`) and the upper's with `wb`, then the second's across the halves, with `wc`
    /// (root 1 for `None`). With `LAST`, each output is brought below `p`.
    #[inline]
    fn inverse_pair<const LAST: bool>(
        &self,
        block: &mut [u64],
        wa: Option<(u64, u64)>,
        wb: (u64, u64),
        wc: Option<(u64, u64)>,
    ) {
        let p = self.p;
        let half = block.len() / 4;
        let (lo, hi) = block.split_at_mut(2 * half);
        let (q0, q1) = lo.split_at_mut(half);
        let (q2, q3) = hi.split_at_mut(half);
        let q3 = &mut q3[..half];
        let pair = |x: u64, y: u64, w: Option<(u64, u64)>| match w {
            Some(w) => self.inverse_root(x, y, w),
            None => self.inverse_one(x, y),
        };
        // An index loop, not `zip`, as in [`Field::forward`].
        for i in 0..half {
            let (a0, a1) = pair(q0[i], q1[i], wa);
            let (a2, a3) = self.inverse_root(q2[i], q3[i], wb);
            let (b0, b2) = pair(a0, a2, wc);
            let (b1, b3) = pair(a1, a3, wc);
            match LAST {
                // Each below `2p`, so one subtraction brings it below `p`.
                true => {
                    q0[i] = below(b0, p);
                    q1[i] = below(b1, p);
                    q2[i] = below(b2, p);
                    q3[i] = below(b3, p);
                }
                false => (q0[i], q1[i], q2[i], q3[i]) = (b0, b1, b2, b3),
            }
        }
    }

    /// The coefficients of the product of the words of `a` from `sa` up and those of `b` from
    /// `sb` up (`b` is `None` for a square of `a`'s), `la + lb - 1` of them, each below `p`,
    /// with room for one more. `tw` as for [`Field::forward`], of at least the points used,
    /// and `fb` a buffer as for [`Field::convolve`].
    ///
    /// With `n` the power of two of points at or above the coefficients, `N = n / 2` and `r`
    /// the coefficients above `N`, the product is taken on `n` points, or, when the costs of
    /// [`transform_cost`] say it is cheaper, on `N`: the cyclic product modulo `x^N - 1` holds
    /// `c_t + c_(N+t)` at `t < r`, and the top `r` coefficients `c_(N+t)` are those of the
    /// product of the top `min(la, r)` and `min(lb, r)` words alone (a word `a_i` reaches
    /// `c_(N+t)` only with some `b_j`, `j <= lb - 1`, so `i >= N - lb + 1 = la - r`, and the
    /// same for `b`), found by this function on at most `2 r - 1` coefficients and subtracted.
    /// So no product pays for up to twice its points, as one just above a power of two did.
    fn linear(
        &self,
        a: &BigUint,
        sa: usize,
        b: Option<(&BigUint, usize)>,
        tw: &[(u64, u64)],
        fb: &mut Vec<u64>,
    ) -> Vec<u64> {
        let la = words(a) - sa;
        let lb = b.map_or(la, |(b, sb)| words(b) - sb);
        let coeffs = la + lb - 1;
        let (n, wrap) = points(la, lb);
        if !wrap {
            let mut v = self.convolve(a, sa, b, n, coeffs + 1, tw, fb);
            v.truncate(coeffs);
            return v;
        }
        let mut v = self.convolve(a, sa, b, n, coeffs + 1, tw, fb);
        let r = coeffs - n;
        let (ra, rb) = (la.min(r), lb.min(r));
        let top = b.map(|(b, sb)| (b, sb + lb - rb));
        let d = self.linear(a, sa + la - ra, top, tw, fb);
        // `d_k` is the coefficient at `la - ra + lb - rb + k = N + t` for
        // `k = t + ra + rb - 1 - r`, and `ra + rb >= r + 1` since both are at least 1 and one is
        // `r`.
        let high = &d[ra + rb - 1 - r..];
        debug_assert_eq!(high.len(), r, "the top `r` coefficients");
        for (x, &h) in v.iter_mut().zip(high) {
            *x = self.sub(*x, h);
        }
        // Within the capacity `coeffs + 1` asked of `convolve`.
        v.extend_from_slice(high);
        v
    }

    /// The cyclic convolution modulo `p` of the words of `a` from `sa` up and those of `b`
    /// from `sb` up (`b` is `None` for a square of `a`'s) on `n` points, each coefficient
    /// reduced below `p`, in a vector of capacity at least `room`; each has at most `n` words. `tw`
    /// as for [`Field::forward`]; `b`'s
    /// transform is written into `fb`, so that one buffer serves the three primes.
    #[allow(clippy::too_many_arguments)]
    fn convolve(
        &self,
        a: &BigUint,
        sa: usize,
        b: Option<(&BigUint, usize)>,
        n: usize,
        room: usize,
        tw: &[(u64, u64)],
        fb: &mut Vec<u64>,
    ) -> Vec<u64> {
        let load = |x: &BigUint, s: usize, v: &mut Vec<u64>| {
            v.clear();
            v.extend(x.iter_u64_digits().skip(s).map(|d| self.reduce(d)));
            let filled = v.len();
            debug_assert!(filled <= n, "at most `n` words");
            v.resize(n, 0);
            self.forward(v, filled, tw);
        };
        let mut fa = Vec::with_capacity(room.max(n));
        load(a, sa, &mut fa);
        // The pointwise product is `a b / 2^64`; the inverse multiplies by `n`; the scale
        // `2^128 / n`, in Montgomery form, undoes both.
        let n_inv = self.p - (self.p - 1) / n as u64;
        let scale = self.to_mont(self.to_mont(n_inv));
        match b {
            Some((b, sb)) => {
                load(b, sb, fb);
                for (x, y) in fa.iter_mut().zip(fb.iter()) {
                    *x = self.mul(self.mul(*x, *y), scale);
                }
            }
            None => {
                for x in fa.iter_mut() {
                    *x = self.mul(self.mul(*x, *x), scale);
                }
            }
        }
        self.inverse(&mut fa, tw);
        fa
    }

    /// The transform of the words `x` on `n >= x.len()` points, a power of two, each value
    /// multiplied by `2^64 / n` modulo `p` and below `p`: a factor transformed once for
    /// [`Field::cyclic`], which then needs one product a point, with `tw` as for
    /// [`Field::forward`].
    fn spectrum(&self, x: &[u64], n: usize, tw: &[(u64, u64)]) -> Vec<u64> {
        let mut v = Vec::with_capacity(n);
        v.extend(x.iter().map(|&d| self.reduce(d)));
        v.resize(n, 0);
        self.forward(&mut v, x.len(), tw);
        // As in [`Field::convolve`]: `2^128 / n` in Montgomery form, so that the pointwise
        // product `x s / 2^64` is `x y / n`, and the inverse's factor `n` cancels.
        let n_inv = self.p - (self.p - 1) / n as u64;
        let scale = self.to_mont(self.to_mont(n_inv));
        for y in &mut v {
            *y = self.mul(*y, scale);
        }
        v
    }

    /// The transform of the words of `x` on `n` points, a power of two, each value below `2p`,
    /// written into `v`, with `tw` as for [`Field::forward`]. Word `i` goes to point `i mod n`,
    /// added to those before it there: the transform of `x(z) mod (z^n - 1)`, which is `x`'s
    /// itself when `n` is at or above its words.
    fn transform_into(&self, x: &BigUint, n: usize, tw: &[(u64, u64)], v: &mut Vec<u64>) {
        v.clear();
        let mut digits = x.iter_u64_digits();
        v.extend(digits.by_ref().take(n).map(|d| self.reduce(d)));
        let filled = v.len();
        v.resize(n, 0);
        for (i, d) in digits.enumerate() {
            v[i % n] = self.add(v[i % n], self.reduce(d));
        }
        self.forward(v, filled, tw);
    }

    /// `x 2^128 / n` in Montgomery form for each `x` of `v`, each below `p`: as
    /// [`Field::spectrum`] scales a transform, so that the pointwise products are those of
    /// the cyclic product.
    fn scale(&self, v: &mut [u64], n: usize) {
        let n_inv = self.p - (self.p - 1) / n as u64;
        let scale = self.to_mont(self.to_mont(n_inv));
        for y in v {
            *y = self.mul(*y, scale);
        }
    }

    /// The cyclic convolution modulo `p` of the words `x` and the number whose
    /// [`Field::spectrum`] is `s`, on `s.len() >= x.len()` points, each coefficient below `p`.
    fn cyclic(&self, x: &[u64], s: &[u64], tw: &[(u64, u64)]) -> Vec<u64> {
        // Two words more than the points, for the carry [`Factor::mul`] appends.
        let mut v = Vec::with_capacity(s.len() + 2);
        v.extend(x.iter().map(|&d| self.reduce(d)));
        v.resize(s.len(), 0);
        self.forward(&mut v, x.len(), tw);
        for (a, b) in v.iter_mut().zip(s) {
            *a = self.mul(*a, *b);
        }
        self.inverse(&mut v, tw);
        v
    }
}

/// The constants of Garner's form of the Chinese remainder theorem over [`FIELDS`], computed
/// once at compile time (each product computed them before, by exponentiations whose u128
/// remainders took a fifth of a 64-word product's time).
struct Garner {
    /// `p0^-1 mod p1`, in Montgomery form modulo `p1`.
    inv01: u64,
    /// `(p0 p1)^-1 mod p2`, in Montgomery form modulo `p2`.
    inv012: u64,
    /// `p0 mod p2`, in Montgomery form modulo `p2`.
    p0_in_2: u64,
    /// `p0 p1`.
    p01: u128,
}

/// `x 2^64 mod p`, the Montgomery form, at compile time.
const fn mont_of(x: u64, p: u64) -> u64 {
    (((x as u128) << 64) % p as u128) as u64
}

const GARNER: Garner = {
    let [p0, p1, p2] = [FIELDS[0].p, FIELDS[1].p, FIELDS[2].p];
    let p01 = p0 as u128 * p1 as u128;
    Garner {
        inv01: mont_of(inv_mod(p0 % p1, p1), p1),
        inv012: mont_of(inv_mod((p01 % p2 as u128) as u64, p2), p2),
        p0_in_2: mont_of(p0 % p2, p2),
        p01,
    }
};

/// `x mod m` for `x < 2m`, `m < 2^63`, `x < 2^64`: `x - m` read as signed is negative exactly
/// when `x < m` (it is then at least `2^64 - m > 2^63`, and otherwise below `m < 2^63`), and a
/// test of the sign compiles to a subtraction and a conditional move, two instructions fewer
/// than a comparison with `m`.
#[inline]
fn below(x: u64, m: u64) -> u64 {
    let d = x.wrapping_sub(m);
    if (d as i64) < 0 { x } else { d }
}

/// Three primes `c * 2^50 + 1` with a generator each; their product exceeds `2^185`, above
/// every coefficient of a product of `2^50` words, `2^50 * 2^128`.
const FIELDS: [Field; 3] = [
    Field::new(4_601_552_919_265_804_289, 3),
    Field::new(4_546_383_823_830_515_713, 10),
    Field::new(4_522_739_925_786_820_609, 37),
];

/// The cost of a product by transforms whose coefficients number `coeffs`, in units of one
/// word product of [`sparse_mul`], as [`Field::linear`] takes it: `TRANSFORM_COST n log2(n)`
/// for `n` points, the constant measured (see [`TRANSFORM_COST`]), on the power of two of
/// points at or above the coefficients, or on half as many plus the cost of the top
/// coefficients' product when that is less (see [`points`]).
fn transform_cost(coeffs: usize) -> u128 {
    let (n, wrap) = points(coeffs.div_ceil(2), coeffs / 2 + 1);
    let top = match wrap {
        true => transform_cost(2 * (coeffs - n) - 1),
        false => 0,
    };
    TRANSFORM_COST * points_cost(n) + top
}

/// `n log2(n)`, at least `n`, the steps of a transform on `n` points.
fn points_cost(n: usize) -> u128 {
    let n = n as u128;
    n * u128::from(n.trailing_zeros().max(1))
}

/// The points of a product of `la` and `lb` words by [`Field::linear`], and whether it wraps
/// its top coefficients around: `n`, the power of two at or above the `la + lb - 1`
/// coefficients, or `n / 2` when that plus the product of the top words (the `r = la + lb -
/// 1 - n / 2` coefficients above `n / 2` need at most `min(la, r) + min(lb, r) - 1`) costs
/// less by [`transform_cost`]. The choice is the cheaper of two computed costs, with no size
/// constant. Both factors must fit in `n / 2` words to wrap: a wider one would have to be
/// folded by coefficients, and [`spectra`] folds by words.
fn points(la: usize, lb: usize) -> (usize, bool) {
    let coeffs = la + lb - 1;
    let n = coeffs.next_power_of_two();
    if coeffs <= 2 || n == coeffs || la.max(lb) > n / 2 {
        return (n, false);
    }
    let r = coeffs - n / 2;
    let top = la.min(r) + lb.min(r) - 1;
    match TRANSFORM_COST * points_cost(n / 2) + transform_cost(top)
        < TRANSFORM_COST * points_cost(n)
    {
        true => (n / 2, true),
        false => (n, false),
    }
}

/// The cheapest way to multiply a factor of `short` words by one of `long >= short` words by
/// transforms, and its cost: the longer cut into pieces of the returned length, each
/// multiplied by the shorter on the next power of two of points above their coefficients.
/// The pieces tried are those whose coefficients just fit a power of two of points, one for
/// each power from the shorter's width to the whole product's, so no more points are wasted
/// to rounding up than in the product whole, and an unbalanced product costs
/// O((long / short) M(short)).
fn transform_plan(short: usize, long: usize) -> (u128, usize) {
    let mut best = (transform_cost(short + long - 1), long);
    let mut points = short.next_power_of_two();
    while points < short + long - 1 {
        let piece = points + 1 - short;
        let cost = long.div_ceil(piece) as u128 * transform_cost(points);
        if cost < best.0 {
            best = (cost, piece);
        }
        points *= 2;
    }
    best
}

/// The nonzero 64-bit words of `x`.
fn nonzero_words(x: &BigUint) -> usize {
    x.iter_u64_digits().filter(|&d| d != 0).count()
}

/// `a * b`. When the narrower factor has at most `MUL_LEAF` (512) words, by num-bigint's
/// multiplication; above that, by whichever of three methods has the least computed cost:
/// num-bigint's (Toom-3, about `n^1.465`), rows over the nonzero words of one factor, or
/// transforms modulo three primes joined by the Chinese remainder theorem, O(n log n). Every
/// method gives the same product; only the time depends on the choice.
pub fn mul(a: &BigUint, b: &BigUint) -> BigUint {
    let (la, lb) = (words(a), words(b));
    let (short, long) = (la.min(lb), la.max(lb));
    // Complexity tradeoff: two timed crossovers of algorithms with identical results, nothing
    // given up. A product whose narrower factor has at most `MUL_LEAF` words, and one above it
    // where `toom_cost` is the least of the three computed costs, is num-bigint's Toom-3, about
    // `n^1.465`, in place of the O(n log n) transforms, because num-bigint was measured faster
    // there (the timings, dates and loads are in the doc comments of `MUL_LEAF` and
    // `TOOM_COST`). Every method gives the same product (tests
    // `l01_17_value_representation::subquadratic::products_agree_with_num_bigint_across_the_crossovers`
    // and `tests::products_agree_with_num_bigint`, with the leaf and `TOOM_COST` set so the
    // transforms are reached at small sizes); the growth above the leaf is tested by
    // `a_dense_product_scales` (COMPLEXITY.md K82 and section "Crossovers", BIGINT-fast-mul).
    // A complete solution solves the crossings from the methods' cost formulas rather than
    // from timings; both constants are to be measured again at the Zed port (ZED_PORT_GAPS.md,
    // "Entries from BIGINT-fast-mul").
    if short <= MUL_LEAF {
        return a * b;
    }
    // Complexity tradeoff: rows over the nonzero words cost `nonzero(a) words(b)` word
    // products, below the transforms' O(n log n) when a factor has few nonzero words, as a
    // kept power `2^s + 1` has; the cheaper of the two computed costs is taken, from the
    // operands' counts and the measured `TRANSFORM_COST`, with no size constant, and both give
    // the same product. A dense factor costs O(n) more for the count. Tested by
    // `a_sparse_product_scales` and `products_agree_with_num_bigint` (COMPLEXITY.md K30).
    let rows = (nonzero_words(a) as u128 * lb as u128).min(nonzero_words(b) as u128 * la as u128);
    let (cost, piece) = transform_plan(short, long);
    // The second crossover of the tradeoff above (`TOOM_COST`): num-bigint's product where its
    // computed cost is the least, which follows the transform's steps at each power of two of
    // its points.
    if toom_cost(short, long) <= rows.min(cost) as f64 {
        return a * b;
    }
    if rows <= cost {
        return sparse_mul(a, b);
    }
    pieces_mul(a, b, piece)
}

/// A factor `x` that multiplies many numbers of at most `other` words, with its spectra on
/// the points of such a product (see [`Field::spectrum`]) when that costs less than [`mul`]:
/// each product then transforms only the other factor and the result, two of the three
/// transforms of [`transform_mul`].
pub(crate) struct Factor {
    x: BigUint,
    other: usize,
    spectra: Option<([Vec<u64>; 3], Rc<Roots>)>,
}

impl Factor {
    /// `x`, for `uses` products with numbers of at most `other` words.
    pub(crate) fn new(x: BigUint, other: usize, uses: usize) -> Factor {
        let (points, _) = self::points(words(&x), other);
        // Complexity tradeoff: the spectra cost a third of a product's transforms, once, and
        // each product by them then costs `cached_cost` (two of its three transforms, measured
        // as `CACHED_COST`), so they are kept when the computed costs, in the
        // units of `TRANSFORM_COST`, say `uses` products by them cost less than by `mul`'s
        // cheapest method for dense factors; else `mul` alone, with no memory held. Both give
        // the same products. Kept, they hold three words a point, about six of `x`'s words for
        // each, for as long as the factor lives (COMPLEXITY.md C31, RADIX-depth).
        let spectra = (uses as f64
            * (cached_total(points, words(&x), other) - dense_cost(words(&x), other))
            + transform_cost(points) as f64 / 3.0
            < 0.0)
            .then(|| {
                let tw = roots(points);
                (spectra(&x.to_u64_digits(), points, &tw), tw)
            });
        Factor { x, other, spectra }
    }

    /// `y * x`, for `y` of at most `other` words, by the spectra when they are kept and cost
    /// less than [`mul`] for `y`'s width; the product is the same.
    pub(crate) fn mul(&self, y: &BigUint) -> BigUint {
        let wy = words(y);
        match &self.spectra {
            Some((s, tw))
                if wy <= self.other
                    && cached_total(s[0].len(), words(&self.x), wy)
                        < dense_cost(wy, words(&self.x)) =>
            {
                // The cyclic product on the points, less the top coefficients above them, which
                // wrapped around, as in [`Field::linear`]; then the carry out of its top word
                // as in `transform_mul`.
                let wx = words(&self.x);
                let coeffs = wx + wy - 1;
                let n = s[0].len();
                let yw = y.to_u64_digits();
                let mut fb = Vec::new();
                let [mut r0, r1, r2] = [0, 1, 2].map(|k| {
                    let mut v = FIELDS[k].cyclic(&yw, &s[k], &tw[k]);
                    if coeffs > n {
                        let r = coeffs - n;
                        let (rx, ry) = (wx.min(r), wy.min(r));
                        let top = Some((y, wy - ry));
                        let d = FIELDS[k].linear(&self.x, wx - rx, top, &tw[k], &mut fb);
                        let high = &d[rx + ry - 1 - r..];
                        for (x, &h) in v.iter_mut().zip(high) {
                            *x = FIELDS[k].sub(*x, h);
                        }
                        v.extend_from_slice(high);
                    }
                    v
                });
                let carry = garner(&mut r0, &r1, &r2);
                drop((r1, r2));
                let mut out = r0;
                out.extend([carry as u64, (carry >> 64) as u64]);
                trim(&mut out);
                from_words(out)
            }
            _ => mul(y, &self.x),
        }
    }

    /// The factor itself.
    pub(crate) fn value(&self) -> &BigUint {
        &self.x
    }
}

/// The cost of a product by a [`Factor`]'s spectra on `n` points, per `n log2(n)`, in the
/// units of [`TRANSFORM_COST`]: two of the three transforms of a product, so about two thirds
/// of it. It was 11 from cycles measured on 2026-11-12 (load 50). Measured again the same day
/// (RADIX-depth) in instructions, in the test build: 4.89, 4.82, 4.57, 4.54, 4.35, 4.35 and
/// 4.15 units per `n log2(n)` at 1024 to 65,536 points: 5. Only which of two equal products is
/// computed depends on it; the unit tests use the same value.
#[cfg(not(test))]
const CACHED_COST: u128 = 5;
#[cfg(test)]
const CACHED_COST: u128 = 5;

/// The cost of a product of `wx` and `wy` words by spectra on `points` points: the cached
/// product, plus, when the coefficients pass the points, the product of the top words that
/// wrapped (see [`Field::linear`]).
fn cached_total(points: usize, wx: usize, wy: usize) -> f64 {
    let coeffs = wx + wy - 1;
    let top = match coeffs > points {
        true => {
            let r = coeffs - points;
            transform_cost(wx.min(r) + wy.min(r) - 1) as f64
        }
        false => 0.0,
    };
    cached_cost(points) + top
}

/// The cost of a product by a [`Factor`]'s spectra on `points` points, in the units of
/// [`TRANSFORM_COST`]: [`CACHED_COST`] `n log2(n)` for `n` points.
fn cached_cost(points: usize) -> f64 {
    let n = points.next_power_of_two() as u128;
    (CACHED_COST * n * u128::from(n.trailing_zeros().max(1))) as f64
}

/// The cost [`mul`] computes for its cheapest method on dense factors of `a` and `b` words,
/// in the units of [`TRANSFORM_COST`]: zero at or below [`MUL_LEAF`], where num-bigint's
/// product is taken with no cost computed, so that no other method is taken there.
fn dense_cost(a: usize, b: usize) -> f64 {
    let (short, long) = (a.min(b), a.max(b));
    match short <= MUL_LEAF {
        true => 0.0,
        false => toom_cost(short, long).min(transform_plan(short, long).0 as f64),
    }
}

/// num-bigint's cost of a product of `short <= long` words, `TOOM_COST long short^0.465`, in
/// the units of [`TRANSFORM_COST`].
fn toom_cost(short: usize, long: usize) -> f64 {
    TOOM_COST * long as f64 * (short as f64).powf(TOOM_POWER)
}

/// `a * b` by transforms, the longer factor cut into pieces of `piece` words (whole when it
/// has no more), as [`transform_plan`] chose.
fn pieces_mul(a: &BigUint, b: &BigUint, piece: usize) -> BigUint {
    let (la, lb) = (words(a), words(b));
    let (short, long) = match la <= lb {
        true => (a, b),
        false => (b, a),
    };
    if piece >= words(long) {
        return transform_mul(a, b);
    }
    // Complexity tradeoff: a product is cut into pieces when that costs less by
    // `transform_plan`, which also bounds its memory by that of the pieces' transforms; a
    // square so cut loses its single transform, which the plan does not count, so it may cost
    // up to a third more than whole. Tested by `products_agree_with_num_bigint`
    // (COMPLEXITY.md K30).
    let mut out = vec![0u64; la + lb];
    let mut digits = long.iter_u64_digits();
    let mut at = 0;
    while digits.len() > 0 {
        let part = from_words(digits.by_ref().take(piece).collect());
        let p = transform_mul(short, &part);
        drop(part);
        let mut slots = out[at..].iter_mut();
        let mut carry = false;
        for d in p.iter_u64_digits() {
            let slot = slots.next().expect("the product fits in its words");
            let (v, c1) = slot.overflowing_add(d);
            let (v, c2) = v.overflowing_add(u64::from(carry));
            *slot = v;
            carry = c1 || c2;
        }
        for slot in slots {
            if !carry {
                break;
            }
            (*slot, carry) = slot.overflowing_add(1);
        }
        at += piece;
    }
    from_words(out)
}

/// `a * b` by transforms modulo three primes joined by the Chinese remainder theorem.
fn transform_mul(a: &BigUint, b: &BigUint) -> BigUint {
    let (la, lb) = (words(a), words(b));
    // The product has `la + lb - 1` coefficients and `la + lb` words: the top word is the
    // last carry, pushed into the room [`Field::linear`] leaves.
    let (n, _) = points(la, lb);
    assert!(n <= 1 << 50, "a product of at most 2^50 words");
    let square = std::ptr::eq(a, b) || a == b;
    let other = (!square).then_some((b, 0));
    let tw = roots(n);
    // `b`'s transform for each prime in turn, in one buffer; the peak, during the last
    // transform, is four vectors of `n` words (two residues, `a`'s transform and `b`'s), and
    // the roots, kept by [`roots`] for later products.
    let mut fb = Vec::with_capacity(if square { 0 } else { n });
    let [mut r0, r1, r2] = [0, 1, 2].map(|k| FIELDS[k].linear(a, 0, other, &tw[k], &mut fb));
    drop(fb);
    let carry = garner(&mut r0, &r1, &r2);
    debug_assert!(
        carry >> 64 == 0,
        "the product fits in the words of both factors"
    );
    drop((r1, r2));
    r0.push(carry as u64);
    from_words(r0)
}

/// The coefficients whose residues modulo the primes of [`FIELDS`] are `r0`, `r1` and `r2`,
/// each below its prime, joined by Garner's form of the Chinese remainder theorem and carried:
/// they are written over `r0` as words, and the carry out of the top is returned. `r1` and
/// `r2` have at least as many entries as `r0`.
fn garner(r0: &mut [u64], r1: &[u64], r2: &[u64]) -> u128 {
    let [f0, f1, f2] = &FIELDS;
    // Garner's form: c = v0 + v1 p0 + v2 p0 p1, each `v_i < p_i`, with the constants of
    // [`GARNER`].
    let Garner {
        inv01,
        inv012,
        p0_in_2,
        p01,
    } = GARNER;
    let (p01_lo, p01_hi) = (p01 as u64, (p01 >> 64) as u64);
    // Coefficient `i` is read before word `i` is written.
    let mut carry = 0u128;
    for i in 0..r0.len() {
        let v0 = r0[i];
        let v1 = f1.mul(f1.sub(r1[i], f1.reduce(v0)), inv01);
        let low = f2.add(f2.reduce(v0), f2.mul(v1, p0_in_2));
        let v2 = f2.mul(f2.sub(r2[i], low), inv012);
        // c = s + v2 p01_lo + v2 p01_hi 2^64, with s = v0 + v1 p0 < 2^125.
        let s = u128::from(v0) + u128::from(v1) * u128::from(f0.p);
        let s = s + u128::from(v2) * u128::from(p01_lo);
        let hi = (s >> 64) + u128::from(v2) * u128::from(p01_hi);
        let t = u128::from(s as u64) + (carry & u128::from(u64::MAX));
        r0[i] = t as u64;
        carry = hi + (carry >> 64) + (t >> 64);
    }
    carry
}

/// [`garner`] for coefficients that may be negative, each of absolute value below `P / 2`,
/// `P = p0 p1 p2`: the residue `v2 = c / (p0 p1)` of a coefficient `c` in `[0, P)` is taken
/// as `v2 - p2` when it is above `p2 / 2`, which gives `c - P`, the negative coefficient. With
/// `s = v0 + v1 p0 < p0 p1 < 2^125` and `|v2| < 2^62`, `s + v2 p01_lo` lies within `2^127`
/// and `v2 p01_hi` within `2^122`, and the carry stays within `2^123`. The words written over
/// `r0` and the carry returned are the sum's two's complement.
fn garner_signed(r0: &mut [u64], r1: &[u64], r2: &[u64]) -> i128 {
    let [f0, f1, f2] = &FIELDS;
    let Garner {
        inv01,
        inv012,
        p0_in_2,
        p01,
    } = GARNER;
    let (p01_lo, p01_hi) = (i128::from(p01 as u64), i128::from((p01 >> 64) as u64));
    let mut carry = 0i128;
    for i in 0..r0.len() {
        let v0 = r0[i];
        let v1 = f1.mul(f1.sub(r1[i], f1.reduce(v0)), inv01);
        let low = f2.add(f2.reduce(v0), f2.mul(v1, p0_in_2));
        let v2 = f2.mul(f2.sub(r2[i], low), inv012);
        let v2 = match v2 > f2.p / 2 {
            true => i128::from(v2) - i128::from(f2.p),
            false => i128::from(v2),
        };
        let s = u128::from(v0) + u128::from(v1) * u128::from(f0.p);
        let x = s as i128 + v2 * p01_lo;
        let t = u128::from(x as u64) + u128::from(carry as u64);
        r0[i] = t as u64;
        carry = (x >> 64) + v2 * p01_hi + (carry >> 64) + (t >> 64) as i128;
    }
    carry
}

/// The number whose two's complement is the words `w`, lowest first, followed by those of
/// `carry`.
fn signed_from_words(mut w: Vec<u64>, carry: i128) -> BigInt {
    w.extend([carry as u64, (carry >> 64) as u64]);
    if carry >= 0 {
        trim(&mut w);
        return BigInt::from_biguint(Sign::Plus, from_words(w));
    }
    // The magnitude is the two's complement: the words inverted, plus one.
    let mut one = true;
    for d in &mut w {
        (*d, one) = (!*d).overflowing_add(u64::from(one));
    }
    trim(&mut w);
    BigInt::from_biguint(Sign::Minus, from_words(w))
}

/// The number whose 64-bit words, lowest first, are `w`.
///
/// num-bigint takes only 32-bit digits, which it copies into its own vector, so the halves
/// go through a vector made and dropped here. A buffer kept for the thread would save that
/// allocation but stay live, as wide as the widest number made, after the operation ended,
/// counted against the memory limit (test
/// `a_wide_number_modulo_a_wide_one_answers_when_its_peak_is_given`).
fn from_words(w: Vec<u64>) -> BigUint {
    let halves: Vec<u32> = w
        .iter()
        .flat_map(|d| [*d as u32, (*d >> 32) as u32])
        .collect();
    drop(w);
    BigUint::new(halves)
}

/// `a * b` by schoolbook rows, one for each nonzero word of the factor with fewer, across
/// the other's words: O(nonzero(a) words(b)).
fn sparse_mul(a: &BigUint, b: &BigUint) -> BigUint {
    let (la, lb) = (words(a), words(b));
    let (rows, across) = match nonzero_words(a) * lb <= nonzero_words(b) * la {
        true => (a, b),
        false => (b, a),
    };
    let mut out = vec![0u64; la + lb];
    for (i, x) in rows.iter_u64_digits().enumerate().filter(|&(_, x)| x != 0) {
        let mut carry = 0u128;
        for (slot, y) in out[i..].iter_mut().zip(across.iter_u64_digits()) {
            let t = u128::from(x) * u128::from(y) + u128::from(*slot) + carry;
            *slot = t as u64;
            carry = t >> 64;
        }
        // The row's sum is below `2^(64 (i + words(across) + 1))`, so the carry stops in the
        // product.
        for slot in &mut out[i + words(across)..] {
            if carry == 0 {
                break;
            }
            let t = u128::from(*slot) + carry;
            *slot = t as u64;
            carry = t >> 64;
        }
    }
    from_words(out)
}

/// `x^-1 mod p` for a prime `p` and `x` not a multiple of it, by Fermat.
const fn inv_mod(x: u64, p: u64) -> u64 {
    let (mut b, mut e, mut r) = (x as u128, p - 2, 1u128);
    let p = p as u128;
    while e > 0 {
        if e & 1 == 1 {
            r = r * b % p;
        }
        b = b * b % p;
        e >>= 1;
    }
    r as u64
}

/// `a * b` of signed numbers, by [`mul`].
pub fn mul_int(a: &BigInt, b: &BigInt) -> BigInt {
    BigInt::from_biguint(a.sign() * b.sign(), mul(a.magnitude(), b.magnitude()))
}

/// `b^e`, by squaring with [`mul`].
pub fn pow(b: &BigUint, mut e: u64) -> BigUint {
    let mut b = Cow::Borrowed(b);
    let mut r = BigUint::one();
    while e > 0 {
        if e & 1 == 1 {
            r = mul(&r, &b);
        }
        e >>= 1;
        if e > 0 {
            b = Cow::Owned(mul(&b, &b));
        }
    }
    r
}

// ------------------------------------------------------------------------------------------
// Division

/// `(a / b, a mod b)` for `b` not zero. A narrow divisor or quotient goes to num-bigint, and a
/// quotient wider than the divisor goes block by block ([`div_rem_blocks`]). Otherwise the
/// quotient, of `k` bits, is estimated from the reciprocal of the divisor's top `k` bits, at
/// most a few off, and the remainder, found by a cyclic product ([`Level::div_rem`]), corrects
/// it. O(M(n)): about four squarings of the quotient's width (4.0 at 4096 to 65,536 words,
/// 2026-11-09), and the same for `2w` by `w` words through [`div_rem_blocks`].
pub(crate) fn div_rem(a: &BigUint, b: &BigUint) -> (BigUint, BigUint) {
    assert!(!b.is_zero(), "a division by zero");
    if a < b {
        return (BigUint::zero(), a.clone());
    }
    let (m, n) = (a.bits(), b.bits());
    // The quotient has at most `k` bits.
    let k = m - n + 1;
    // Complexity tradeoff: a timed crossover with identical results, nothing given up. A
    // divisor or quotient of at most `DIV_LEAF` bits goes to num-bigint's division, which costs
    // at most `DIV_LEAF` bits times the dividend's, O(n), and was measured faster there; the
    // measured curves now cross near 8192 words, higher than this leaf (its doc comment).
    // Both sides are tested by `tests::quotients_agree_with_num_bigint` and
    // `tests::wide_quotients_agree_with_num_bigint`; the growth above it by
    // `dividing_a_wide_number_scales` (COMPLEXITY.md K30, "Crossovers"; ZED_PORT_GAPS.md,
    // "Entries from KERNEL-div-newton").
    if n.min(k) <= DIV_LEAF {
        return a.div_rem(b);
    }
    // Complexity tradeoff: long division over the divisor's nonzero words costs
    // `nonzero(b)` word products for each quotient word, below the reciprocal's O(M(n)) when
    // the divisor has few nonzero words, as a kept power `2^s + 1` has; the cheaper of the two
    // computed costs is taken, with no size constant, and both give the same result. Tested
    // by `a_sparse_division_scales` and `quotients_agree_with_num_bigint` (COMPLEXITY.md K30).
    let (aw, bw) = (words(a), words(b));
    if sparse_div_cost(aw - bw + 1, nonzero_words(b)) <= newton_cost(aw - bw + 1, bw) {
        return sparse_div_rem(a, b);
    }
    if k > n {
        return div_rem_blocks(a, b);
    }
    let (linear, cyclic) = level_points(n, k);
    let tw = roots(linear.max(cyclic));
    let level = Level::new(b.to_u64_digits(), n, k, &tw);
    let (q, r) = level.div_rem(&a.to_u64_digits(), &tw);
    (from_words(q), from_words(r))
}

/// `a mod b` for `b` not zero, as [`div_rem`] finds it. A quotient wider than `b` is not built:
/// [`Divisor::rem`] reads `a` block by block and keeps only the remainder.
pub(crate) fn rem(a: &BigUint, b: &BigUint) -> BigUint {
    if a.bits().saturating_sub(b.bits()) >= b.bits() {
        return Divisor::new(Cow::Borrowed(b)).rem(a);
    }
    div_rem(a, b).1
}

/// [`div_rem`] of a quotient wider than the divisor `b`: `a` is read from the top in blocks of
/// as many words as `b` has, each step dividing the remainder so far joined to the next block,
/// below `b 2^(64 len)`, by `b` through one [`Divisor`], and the quotient's blocks are written
/// into place. O((m / n) M(n)) for `m` bits by `n`, and the memory of a step is O(n).
fn div_rem_blocks(a: &BigUint, b: &BigUint) -> (BigUint, BigUint) {
    Divisor::new(Cow::Borrowed(b)).div_rem(a)
}

/// The cost of [`sparse_div_rem`] of a quotient of `qw` words by a divisor with `nonzero`
/// nonzero words.
fn sparse_div_cost(qw: usize, nonzero: usize) -> u128 {
    (qw as u128 + 1) * (SPARSE_WORD * nonzero as u128 + SPARSE_STEP)
}

/// The cost of [`div_rem`] by a reciprocal of a quotient of `qw` words by a divisor of `bw`,
/// in products: [`approx_reciprocal`] costs about 5/3 of a product of the quotient's width,
/// the estimate one, and the remainder a cyclic product of the divisor's width, which is one
/// product's transforms on half the points. A quotient wider than the divisor
/// ([`div_rem_blocks`]) builds that once, about three products of the divisor's width, and
/// then costs about one product for each block, its two factors' transforms kept.
fn newton_cost(qw: usize, bw: usize) -> u128 {
    match qw > bw {
        true => (qw.div_ceil(bw) as u128 + 3) * transform_cost(2 * bw),
        false => 8 * transform_cost(2 * qw) / 3 + transform_cost(bw),
    }
}

/// `(a / b, a mod b)` by long division (Knuth's algorithm D) over the nonzero words of `b`,
/// which has at least two words: `a` is read from the top, a word at a time, into a window
/// of `words(b) + 1` words holding the remainder so far, and each step subtracts a quotient
/// word times `b`, touching only the words where `b` is nonzero and those a borrow passes.
/// A borrow passes a zero word and leaves it all ones, which stops the next borrow, so the
/// borrows cost O(words(a)) in all and the division O(words(a) + quotient words times
/// nonzero(b)). Its memory is that of `b` and the quotient, whatever the size of `a`.
fn sparse_div_rem(a: &BigUint, b: &BigUint) -> (BigUint, BigUint) {
    if a < b {
        return (BigUint::zero(), a.clone());
    }
    let (q, r) = sparse_div_rem_words(a.iter_u64_digits(), b);
    (from_words(q), from_words(r))
}

/// [`sparse_div_rem`] of the words `a`, lowest first, at least `words(b) - 1` of them, as
/// words with no zero on top.
fn sparse_div_rem_words(
    a: impl DoubleEndedIterator<Item = u64> + ExactSizeIterator,
    b: &BigUint,
) -> (Vec<u64>, Vec<u64>) {
    let la = a.len();
    // Normalized: the top word of `b 2^sh` has its top bit set, so a quotient word estimated
    // from the window's top two words and the divisor's top word is at most two above.
    let sh = b
        .iter_u64_digits()
        .next_back()
        .expect("b is not zero")
        .leading_zeros();
    let bs = (b << sh).to_u64_digits();
    let lb = bs.len();
    debug_assert!(lb >= 2);
    let nonzero: Vec<usize> = (0..lb).filter(|&k| bs[k] != 0).collect();
    let (b1, b2) = (u128::from(bs[lb - 1]), u128::from(bs[lb - 2]));
    // The words of `a 2^sh`, highest first, one more than `a` has.
    let mut prev = 0u64;
    debug_assert!(la + 1 >= lb, "a has at least words(b) - 1 words");
    let mut shifted = a.rev().chain(std::iter::once(0)).map(|d| {
        let w = (((u128::from(prev) << 64) | u128::from(d)) >> (64 - sh)) as u64;
        prev = d;
        w
    });
    // The remainder so far, `lb` words, lowest first, lies in `buf[start..start + lb]`; a step
    // writes the next word below it and leaves the top word zero, so the remainder moves down
    // a word, and when it reaches the bottom it is copied to the top, once every `lb + 2`
    // steps. It starts as the top `lb - 1` words of `a 2^sh`, below `b 2^sh`, and a zero.
    let mut buf = vec![0u64; 2 * lb + 2];
    let mut start = lb + 2;
    for (i, w) in shifted.by_ref().take(lb - 1).enumerate() {
        buf[start + lb - 2 - i] = w;
    }
    let mut quotient: Vec<u64> = Vec::with_capacity(la + 2 - lb);
    for w in shifted {
        if start == 0 {
            buf.copy_within(0..lb, lb + 2);
            start = lb + 2;
        }
        start -= 1;
        buf[start] = w;
        let win = &mut buf[start..=start + lb];
        let top = (u128::from(win[lb]) << 64) | u128::from(win[lb - 1]);
        let (mut q, mut r) = (top / b1, top % b1);
        while q >> 64 != 0 || (r >> 64 == 0 && q * b2 > (r << 64 | u128::from(win[lb - 2]))) {
            q -= 1;
            r += b1;
        }
        let q = q as u64;
        // `q b 2^sh` is subtracted word by word with the carry kept while the divisor's
        // nonzero words follow each other, and carried up by `sub_at` where they do not.
        let (mut carry, mut at, mut below) = (0u64, 0usize, false);
        for &k in &nonzero {
            if k != at && carry != 0 {
                below |= sub_at(win, at, carry);
                carry = 0;
            }
            // At most `(2^64 - 1)^2 + 2^64 - 1`, so the carry stays a word.
            let t = u128::from(q) * u128::from(bs[k]) + u128::from(carry);
            let (v, borrow) = win[k].overflowing_sub(t as u64);
            win[k] = v;
            carry = (t >> 64) as u64 + u64::from(borrow);
            at = k + 1;
        }
        if carry != 0 {
            below |= sub_at(win, at, carry);
        }
        let q = match below {
            // The window went below zero by less than `b 2^sh`: one addition makes it right.
            true => {
                let (mut carry, mut at) = (false, 0usize);
                for &k in &nonzero {
                    if k != at && carry {
                        add_at(win, at, 1);
                        carry = false;
                    }
                    let (v, c1) = win[k].overflowing_add(bs[k]);
                    let (v, c2) = v.overflowing_add(u64::from(carry));
                    win[k] = v;
                    carry = c1 || c2;
                    at = k + 1;
                }
                if carry {
                    add_at(win, at, 1);
                }
                q - 1
            }
            false => q,
        };
        debug_assert_eq!(win[lb], 0, "the remainder is below the divisor");
        quotient.push(q);
    }
    quotient.reverse();
    trim(&mut quotient);
    buf.truncate(start + lb);
    buf.drain(..start);
    (quotient, shr_words(&buf, u64::from(sh)))
}

/// Subtracts `x` from `w` at word `i`, the borrow carried up; whether it passes the top.
fn sub_at(w: &mut [u64], mut i: usize, x: u64) -> bool {
    let (v, mut borrow) = w[i].overflowing_sub(x);
    w[i] = v;
    while borrow {
        i += 1;
        if i == w.len() {
            return true;
        }
        (w[i], borrow) = w[i].overflowing_sub(1);
    }
    false
}

/// Adds `x` to `w` at word `i`, the carry carried up and dropped past the top.
fn add_at(w: &mut [u64], mut i: usize, x: u64) {
    if i == w.len() {
        return;
    }
    let (v, mut carry) = w[i].overflowing_add(x);
    w[i] = v;
    while carry {
        i += 1;
        if i == w.len() {
            return;
        }
        (w[i], carry) = w[i].overflowing_add(1);
    }
}

/// The quotient and remainder from an estimate `q` of `a / b` a few off, given `q b`.
fn settle(a: &BigUint, b: &BigUint, mut q: BigUint, mut qb: BigUint) -> (BigUint, BigUint) {
    while qb > *a {
        qb -= b;
        q -= 1u32;
    }
    let mut r = a - &qb;
    drop(qb);
    while r >= *b {
        r -= b;
        q += 1u32;
    }
    (q, r)
}

/// `2^2k / x`, floored, for `x` of exactly `k` bits: [`approx_reciprocal`], one below or
/// exact, made exact by the sign of `2^2k - x y - x`, found by one cyclic product. O(M(k)).
fn reciprocal(x: &BigUint, k: u64) -> BigUint {
    let m = cyclic_points(k);
    let tw = roots(m);
    let mut y = approx_reciprocal(x, k, &tw);
    // `e = 2^2k - x y` lies in `(0, 2x)`, below `2^(64 m + 61)`; the floor is `y + 1` when
    // `e >= x`.
    let (xw, yw) = (x.to_u64_digits(), y.to_u64_digits());
    let (mut xy, carry) = cyclic_product(&folded(&xw, m), &spectra(&yw, m, &tw), &tw);
    add_around(&mut xy, carry);
    let e = sub_around(power_around(2 * k, m), &xy);
    let low = low_power(2 * k).wrapping_sub(first(&xw).wrapping_mul(first(&yw)));
    let (negative, e) = unfold(e, m, low);
    debug_assert!(!negative, "the estimate is below the reciprocal");
    if cmp_words(&e, &xw).is_ge() {
        y += 1u32;
    }
    y
}

/// `X` with `a X < 2^2p <= a (X + 2)`, for `a` of exactly `p` bits, so that
/// `2^p <= X < 2^(p + 1)`, by Newton's iteration on the top bits of `a`, each precision `p`
/// from `h = ceil((p + 3) / 2)` ([`newton`]), from num-bigint's division at or below
/// [`RECIP_LEAF`] bits. Each precision costs five transforms on the points of a product of
/// `p / 2` bits by `p / 2`, so the whole about 5/3 of a product of `p` bits by `p`. `tw` as for
/// [`Field::forward`], of at least [`cyclic_points`]`(p)` points. Brent and Zimmermann, Modern
/// Computer Arithmetic (2010), Algorithm 3.5, in bits rather than words.
fn approx_reciprocal(a: &BigUint, p: u64, tw: &Roots) -> BigUint {
    debug_assert_eq!(a.bits(), p);
    let mut sizes = vec![p];
    // Complexity tradeoff: the precisions at or below `RECIP_LEAF` bits start from one
    // division by num-bigint, O(RECIP_LEAF^2) once, in place of further Newton steps whose
    // transforms cost more at that width; the reciprocal's bounds do not depend on it, which
    // `tests::approximate_reciprocals_keep_their_bounds` checks with the leaf at 4 bits.
    while let Some(&s) = sizes.last().filter(|&&s| s > RECIP_LEAF) {
        sizes.push((s + 3).div_ceil(2));
    }
    let mut h = sizes.pop().expect("p is listed");
    // `a_h X < 2^2h <= a_h (X + 1)` for `a_h` the top `h` bits.
    let mut x = ((BigUint::one() << (2 * h)) - 1u32) / (a >> (p - h));
    while let Some(q) = sizes.pop() {
        let top = match q == p {
            true => Cow::Borrowed(a),
            false => Cow::Owned(a >> (p - q)),
        };
        x = newton(&top, q, x, h, tw);
        h = q;
    }
    x
}

/// One step of [`approx_reciprocal`]: from `xh` for the top `h` bits `a_h` of `a`, which has
/// `p` bits, `a_h xh < 2^2h <= a_h (xh + 2)`, the same for `a`, with `l = p - h <= h - 3`.
///
/// `T = a xh` lies in `(2^(p + h) - 2a, 2^(p + h) + 2^(p + 1))`: `a_h xh <= a / 2^l xh` and
/// `xh < 2^(h + 1)` bound it above, and `a_h (xh + 2) >= 2^2h` with `a_h 2^l <= a` below. So
/// `R = T - 2^(p + h)` is found modulo `M = 2^(64 m) - 1` by a cyclic product and [`unfold`],
/// and taking `a` from it for each one taken from `xh` (at most four times) leaves
/// `t = 2^(p + h) - a xh` in `(0, 2a)`. Then `2^2p / a = xh 2^l / (1 - d)` with
/// `d = t / 2^(p + h)`, `= xh 2^l + xh t / 2^2h + Q`, `Q = (2^2p / a) d^2`, and the step returns
/// `X = xh 2^l + floor(xh floor(t / 2^l) / 2^(2h - l))`. What it leaves out is positive, as
/// `Q > 0`, so `a X < 2^2p`, and below 2: the floor less than 1, the low bits of `t` less than
/// `2^(h + 1) 2^l / 2^2h <= 1/4`, and `Q < 4a / 2^2h < 2^(p + 2 - 2h) <= 1/2`.
///
/// Both products are cyclic on `m` points and share `xh`'s transforms: five transforms per
/// prime, `m` the least power of two with `64 m >= p - 55`, so that `|R| < 2^(p + 1)` and
/// `xh floor(t / 2^l) < 2^(2h + 2)` are both below `2^(64 m + 61)`.
fn newton(a: &BigUint, p: u64, xh: BigUint, h: u64, tw: &Roots) -> BigUint {
    let l = p - h;
    debug_assert!(l + 3 <= h);
    let m = cyclic_points(p);
    let xw = xh.to_u64_digits();
    let xs = spectra(&xw, m, tw);
    let aw = a.to_u64_digits();
    let (mut t, carry) = cyclic_product(&folded(&aw, m), &xs, tw);
    add_around(&mut t, carry);
    let r = sub_around(t, &power_around(p + h, m));
    let low = first(&aw)
        .wrapping_mul(first(&xw))
        .wrapping_sub(low_power(p + h));
    drop(aw);
    let (negative, r) = unfold(r, m, low);
    let mut r = from_words(r);
    // `t = 2^(p + h) - a xh`, `xh` lowered by `taken`.
    let mut taken = 0u32;
    let t = match negative {
        true => r,
        false => loop {
            taken += 1;
            if r < *a {
                break a - &r;
            }
            r -= a;
        },
    };
    debug_assert!(taken <= 4, "R is below 2^(p + 1) and a at least 2^(p - 1)");
    let tm = t >> l;
    let tmw = tm.to_u64_digits();
    // `xh tm`, `tm = floor(t / 2^l)`, for the `xh` before it was lowered, whose transforms are
    // kept, then `taken tm` taken off.
    let (mut u, carry) = cyclic_product(&folded(&tmw, m), &xs, tw);
    add_around(&mut u, carry);
    let (negative, u) = unfold(u, m, first(&tmw).wrapping_mul(first(&xw)));
    debug_assert!(!negative, "a product of positive numbers");
    drop((xs, xw, tmw));
    let u = from_words(u) - &tm * taken;
    ((xh - taken) << l) + (u >> (2 * h - l))
}

/// `a / g` for a `g` that divides `a`, positive, the sign of `a` kept.
pub(crate) fn exact_quotient(a: &BigInt, g: &BigInt) -> BigInt {
    let (q, r) = div_rem(a.magnitude(), g.magnitude());
    debug_assert!(r.is_zero(), "g divides a");
    BigInt::from_biguint(a.sign() * g.sign(), q)
}

/// The Euclidean quotient `floor`-like `a div m`, the remainder in `[0, |m|)`, `m` not zero.
pub(crate) fn div_euclid(a: &BigInt, m: &BigInt) -> BigInt {
    let (q, r) = div_rem(a.magnitude(), m.magnitude());
    let q = match (a.is_negative(), r.is_zero()) {
        (true, false) => q + 1u32,
        _ => q,
    };
    let sign = match a.is_negative() == m.is_negative() {
        true => Sign::Plus,
        false => Sign::Minus,
    };
    BigInt::from_biguint(sign, q)
}

// ------------------------------------------------------------------------------------------
// Greatest common divisor

/// A 2x2 matrix `[[m00, m01], [m10, m11]]` of the binary gcd's steps.
struct Mat([BigInt; 4]);

impl Mat {
    fn identity() -> Mat {
        Mat([BigInt::one(), BigInt::zero(), BigInt::zero(), BigInt::one()])
    }

    /// `self * other`.
    fn times(&self, other: &Mat) -> Mat {
        let [a, b, c, d] = &self.0;
        let [e, f, g, h] = &other.0;
        let [w, x, y, z] = matrix_product([a, b, c, d], &[e, f, g, h], None)
            .try_into()
            .expect("a 2x2 product");
        Mat([w, x, y, z])
    }

    /// `self * (a, b) / 2^2j`, exact.
    fn apply(&self, a: &BigInt, b: &BigInt, j: u64) -> (BigInt, BigInt) {
        let [m00, m01, m10, m11] = &self.0;
        let [c, d] = matrix_product([m00, m01, m10, m11], &[a, b], Some(2 * j))
            .try_into()
            .expect("a 2x1 product");
        (c, d)
    }
}

/// `l r` for the 2x2 matrix `l` and the 2 x `c` matrix `r`, both by rows (`r` has `2 c`
/// entries), its `2 c` entries by rows.
///
/// Each entry is a sum of two products, and each factor is in two products. By transforms,
/// on points enough for the widest product, each nonzero factor is transformed once and each
/// sum is formed among the transforms and transformed back once: `4 + 2 c` transforms forward
/// and `2 c` back, where the products one by one take three each, `12 c`. That is 8 in place
/// of 12 for `c = 1` ([`Mat::apply`]) and 12 in place of 24 for `c = 2` ([`Mat::times`]). It is
/// taken when its cost, `TRANSFORM_COST / 3` [`points_cost`] a transform (a third of a
/// product's), is less than the sum of the costs [`mul`] computes for the products, and every
/// product is above `MUL_LEAF`, where `mul` takes num-bigint's with no cost computed; else the
/// products are taken one by one by [`mul_int`]. Both give the same entries.
///
/// With `shift` `Some(s)`, each entry, known to be a multiple of `2^s`, is divided by it, and
/// the points are planned for the quotient, not the product: the transforms give the entry
/// modulo `2^(64 n) - 1`, enough to find a quotient of fewer than `64 n - 2` bits (see
/// [`unrotate`]). [`Mat::apply`] after `j` steps has entries below `2^(2 j)` and the shift
/// `2 j`, so for numbers of `b` bits the quotients have about `b` bits where the products have
/// `b + 2 j`: in [`half`], with `b` about `2 k` and `2 j` about `k`, the points are planned for
/// about `2 k` bits in place of `3 k`.
fn matrix_product(l: [&BigInt; 4], r: &[&BigInt], shift: Option<u64>) -> Vec<BigInt> {
    let c = r.len() / 2;
    let width = |x: &BigInt| x.magnitude().iter_u64_digits().len();
    let terms = || {
        (0..2 * c).flat_map(move |out| {
            let (i, j) = (out / c, out % c);
            [(l[2 * i], r[j]), (l[2 * i + 1], r[c + j])]
        })
    };
    let (mut separate, mut widest, mut leaf) = (0.0, 0, false);
    for (x, y) in terms().filter(|(x, y)| !x.is_zero() && !y.is_zero()) {
        let (wx, wy) = (width(x), width(y));
        leaf |= wx.min(wy) <= MUL_LEAF;
        separate += dense_cost(wx, wy);
        widest = widest.max(wx + wy - 1);
    }
    let factors = l.iter().chain(r).filter(|x| !x.is_zero()).count();
    let n = match shift {
        None => widest.next_power_of_two(),
        // Each entry `e = 2^s q`, `|q| < 2^(bl + br + 1 - s)` for factors below `2^bl` and
        // `2^br`; with `64 n >= bl + br + 3 - s` its residue modulo `2^(64 n) - 1` gives `q`
        // (see [`unrotate`]). A factor of more than `n` words is folded into `n` (see
        // [`Field::transform_into`]); with `n` at least a quarter of the widest, each point
        // holds at most four words, and each coefficient, a sum of at most `2 n` products of
        // two points, is below `2 n 16 2^128 <= 2^183` for `n <= 2^50`: within `P / 2`, as
        // [`garner_signed`] needs.
        Some(s) => {
            let bits = |x: &[&BigInt]| x.iter().map(|x| x.bits()).max().unwrap_or(0);
            let q = (bits(&l) + bits(r) + 3).saturating_sub(s).div_ceil(64) as usize;
            let wide = l.iter().chain(r).map(|x| width(x)).max().unwrap_or(0);
            q.max(wide.div_ceil(4)).next_power_of_two()
        }
    };
    let shared = ((factors + 2 * c) as u128 * TRANSFORM_COST * points_cost(n)) as f64 / 3.0;
    if leaf || widest == 0 || shared >= separate {
        return (0..2 * c)
            .map(|out| {
                let (i, j) = (out / c, out % c);
                (mul_int(l[2 * i], r[j]) + mul_int(l[2 * i + 1], r[c + j])) >> shift.unwrap_or(0)
            })
            .collect();
    }
    #[cfg(test)]
    SHARED_PRODUCTS.with(|v| {
        let folded = l.iter().chain(r).any(|x| width(x) > n);
        let (shared, folds) = v.get();
        v.set((shared + 1, folds + u32::from(folded)));
    });
    let tw = roots(n);
    // For each prime, the left factors' transforms, scaled, the right factors' transforms, in
    // buffers kept for the three primes, and each entry's sum of pointwise products, signed,
    // transformed back, with room for the two words of the carry.
    let mut residues: Vec<[Vec<u64>; 3]> = (0..2 * c).map(|_| Default::default()).collect();
    let mut ls: Vec<Vec<u64>> = (0..4).map(|_| Vec::with_capacity(n)).collect();
    let mut rs: Vec<Vec<u64>> = (0..2 * c).map(|_| Vec::with_capacity(n)).collect();
    for (k, field) in FIELDS.iter().enumerate() {
        for (x, v) in l.iter().zip(&mut ls).filter(|(x, _)| !x.is_zero()) {
            field.transform_into(x.magnitude(), n, &tw[k], v);
            field.scale(v, n);
        }
        for (y, v) in r.iter().zip(&mut rs).filter(|(y, _)| !y.is_zero()) {
            field.transform_into(y.magnitude(), n, &tw[k], v);
        }
        for (out, slot) in residues.iter_mut().enumerate() {
            let (i, j) = (out / c, out % c);
            let mut acc = Vec::with_capacity(n + 2);
            acc.resize(n, 0);
            for (t, (x, y)) in [(2 * i, j), (2 * i + 1, c + j)].into_iter().enumerate() {
                let (lx, ry) = (l[2 * i + t], r[y]);
                if lx.is_zero() || ry.is_zero() {
                    continue;
                }
                let plus = lx.is_negative() == ry.is_negative();
                for ((a, &u), &v) in acc.iter_mut().zip(&ls[x]).zip(&rs[y]) {
                    let p = field.mul(u, v);
                    *a = match plus {
                        true => field.add(*a, p),
                        false => field.sub(*a, p),
                    };
                }
            }
            field.inverse(&mut acc, &tw[k]);
            slot[k] = acc;
        }
    }
    residues
        .into_iter()
        .map(|[mut r0, r1, r2]| {
            let carry = garner_signed(&mut r0, &r1, &r2);
            drop((r1, r2));
            match shift {
                None => signed_from_words(r0, carry),
                Some(s) => unrotate(r0, carry, s),
            }
        })
        .collect()
}

#[cfg(test)]
thread_local! {
    /// The products [`matrix_product`] took by shared transforms, and how many of them folded
    /// a factor.
    static SHARED_PRODUCTS: std::cell::Cell<(u32, u32)> = const { std::cell::Cell::new((0, 0)) };
}

/// `q` from the words `w` (two's complement, `n` of them) and the signed `carry` of
/// `v = w + carry 2^(64 n)`, where `v = 2^s q mod M`, `M = 2^(64 n) - 1`, and `|q| < 2^(64 n - 2)`.
/// As `2^(64 n)` is 1 modulo `M`, `v` is `w + carry` there, and `2^s` turns the words round by
/// `s` bits, so turning them back by `s` bits gives `q mod M`, read as negative when its top
/// bit is set: `q - M`, whose magnitude is the complement of the words.
fn unrotate(mut w: Vec<u64>, carry: i128, s: u64) -> BigInt {
    let n = w.len();
    match carry >= 0 {
        true => add_around(&mut w, carry as u128),
        false => {
            let c = carry.unsigned_abs();
            // `w - c + 2^(64 n) >= 1` when it borrows, `c < 2^123` being below `2^(64 n)`;
            // `n` is above `MUL_LEAF`, so at least the two words of `c`.
            if sub_words(&mut w, &[c as u64, (c >> 64) as u64]) {
                sub_at(&mut w, 0, 1);
            }
        }
    }
    let (words, bits) = ((s / 64) as usize % n, (s % 64) as u32);
    w.rotate_left(words);
    if bits != 0 {
        let low = w[0] << (64 - bits);
        for i in 0..n - 1 {
            w[i] = (w[i] >> bits) | (w[i + 1] << (64 - bits));
        }
        w[n - 1] = (w[n - 1] >> bits) | low;
    }
    let sign = match w[n - 1] >> 63 {
        0 => Sign::Plus,
        _ => {
            w.iter_mut().for_each(|d| *d = !*d);
            Sign::Minus
        }
    };
    trim(&mut w);
    BigInt::from_biguint(sign, from_words(w))
}

/// `x` modulo `2^w`, centered: in `[-2^(w-1), 2^(w-1))`.
fn cmod(x: &BigInt, w: u64) -> BigInt {
    let one = BigInt::one();
    let r = x & ((&one << w) - &one);
    match r.bit(w - 1) {
        true => r - (one << w),
        false => r,
    }
}

/// `x` modulo `2^128`, from the two's complement of a negative `x`.
fn low128(x: &BigInt) -> u128 {
    let mut d = x.iter_u64_digits();
    let lo = u128::from(d.next().unwrap_or(0)) | (u128::from(d.next().unwrap_or(0)) << 64);
    match x.is_negative() {
        true => lo.wrapping_neg(),
        false => lo,
    }
}

/// `x^-1 mod 2^64` for an odd `x`: `3x XOR 2` is right in its low 5 bits, and each of four
/// Newton steps `y (2 - x y)` doubles the right bits, to 80.
fn inverse_mod_2_64(x: u64) -> u64 {
    let mut y = x.wrapping_mul(3) ^ 2;
    for _ in 0..4 {
        y = y.wrapping_mul(2u64.wrapping_sub(x.wrapping_mul(y)));
    }
    y
}

/// The 2-adic valuation of `x`; `None` for 0.
fn nu(x: &BigInt) -> Option<u64> {
    x.trailing_zeros()
}

/// `x^-1 mod 2^w` for an odd `x`, by Newton's iteration `y (2 - x y)`, which doubles the
/// correct bits.
fn inverse_mod_pow2(x: &BigUint, w: u64) -> BigUint {
    let low = x.iter_u64_digits().next().expect("x is odd");
    let mut inv = 1u64;
    for _ in 0..6 {
        inv = inv.wrapping_mul(2u64.wrapping_sub(low.wrapping_mul(inv)));
    }
    let mut y = BigUint::from(inv);
    let mut bits = 64;
    while bits < w {
        bits = (2 * bits).min(w);
        let mask = (BigUint::one() << bits) - 1u32;
        let xy = mul(&(x & &mask), &y) & &mask;
        // `2 - x y mod 2^bits`, as `2^bits + 2 - x y`, `x y` being below `2^bits`.
        let e = ((&mask + 3u32) - xy) & &mask;
        y = mul(&y, &e) & &mask;
    }
    let mask = (BigUint::one() << w) - 1u32;
    y & mask
}

/// One binary division step of `(a, b)` with `a` odd and `b` of valuation `j`: with
/// `b' = b / 2^j` and `q = -a / b' mod 2^(j+1)` centered, `|q| < 2^j`, the pair becomes
/// `(b', (a + q b') / 2^j)`, which is `[[0, 2^j], [2^j, q]] (a, b) / 2^2j`. The new second
/// number is even, and the odd part of the gcd is kept.
fn step(a: &BigInt, b: &BigInt, j: u64) -> (BigInt, BigInt, BigInt) {
    let b1 = b >> j;
    let w = j + 1;
    let q = match w < 128 {
        // In 128-bit registers: `b1^-1 mod 2^128` by one more Newton step from 64 bits.
        true => {
            let y = low128(&b1);
            let inv = u128::from(inverse_mod_2_64(y as u64));
            let inv = inv.wrapping_mul(2u128.wrapping_sub(y.wrapping_mul(inv)));
            let t = low128(a).wrapping_neg().wrapping_mul(inv) & ((1u128 << w) - 1);
            match t >> j {
                0 => BigInt::from(t),
                _ => -BigInt::from((1u128 << w) - t),
            }
        }
        false => {
            // The residues modulo `2^w`, not negative (`&` reads a negative number in two's
            // complement).
            let mask = (BigInt::one() << w) - 1;
            let inv = BigInt::from(inverse_mod_pow2((&b1 & &mask).magnitude(), w));
            cmod(&-mul_int(&(a & &mask), &inv), w)
        }
    };
    let r = (a + mul_int(&q, &b1)) >> j;
    (q, b1, r)
}

/// The steps of the binary gcd of `(a, b)`, `a` odd and `b` even or 0, whose valuations sum
/// to at most `k`, as many as fit: their number of halvings `j` and their product `R`, with
/// `R (a, b) / 2^2j` the pair they reach. The steps depend only on `a` and `b` modulo
/// `2^(2k+1)`, so the first half is found from those residues of half the width, and the
/// rest from the pair it reaches (Stehlé and Zimmermann, "A binary recursive gcd algorithm",
/// ANTS 2004). O(M(k) log k).
fn half(a: &BigInt, b: &BigInt, k: u64) -> (u64, Mat) {
    match nu(b) {
        Some(v) if v <= k => {}
        _ => return (0, Mat::identity()),
    }
    if k <= HALF_LEAF {
        return half_leaf(a, b, k);
    }
    let k1 = k / 2;
    let (j1, r1) = half(&cmod(a, 2 * k1 + 1), &cmod(b, 2 * k1 + 1), k1);
    let (a2, b2) = r1.apply(a, b, j1);
    let j0 = match nu(&b2) {
        Some(v) if j1 + v <= k => v,
        _ => return (j1, r1),
    };
    let (q, a3, b3) = step(&a2, &b2, j0);
    drop((a2, b2));
    let k2 = k - j1 - j0;
    let (j2, r2) = half(&cmod(&a3, 2 * k2 + 1), &cmod(&b3, 2 * k2 + 1), k2);
    drop((a3, b3));
    // The step's matrix [[0, 2^j0], [2^j0, q]] times r1.
    let [m00, m01, m10, m11] = &r1.0;
    let qr1 = Mat([
        m10 << j0,
        m11 << j0,
        (m00 << j0) + mul_int(&q, m10),
        (m01 << j0) + mul_int(&q, m11),
    ]);
    drop(r1);
    (j1 + j0 + j2, r2.times(&qr1))
}

/// [`half`] on 128-bit integers, for `k <= HALF_LEAF`: the residues modulo `2^(2k+1)` stay
/// below `2^120` in size through the steps, since a step's new second number is at most the
/// sum of the two over `2^j`, and the matrix entries below `2^(2 j)`, since a step multiplies
/// their size by less than `2^(j+1)`.
fn half_leaf(a: &BigInt, b: &BigInt, k: u64) -> (u64, Mat) {
    let w = 2 * k + 1;
    let low = |x: &BigInt| -> i128 {
        let r = low128(x) & ((1u128 << w) - 1);
        match r >> (w - 1) {
            1 => r as i128 - (1i128 << w),
            _ => r as i128,
        }
    };
    let (mut x, mut y) = (low(a), low(b));
    let [mut m00, mut m01, mut m10, mut m11] = [1i128, 0, 0, 1];
    let mut j = 0u64;
    while y != 0 {
        let v = u64::from(y.trailing_zeros());
        if j + v > k {
            break;
        }
        let y1 = y >> v;
        // `q = -x / y1 mod 2^(v+1)`, centered.
        let inv = inverse_mod_2_64(y1 as u64);
        let t = (x as u64).wrapping_neg().wrapping_mul(inv) & ((1u64 << (v + 1)) - 1);
        let q = match t > 1 << v {
            true => i128::from(t) - (1i128 << (v + 1)),
            false => i128::from(t),
        };
        (x, y) = (y1, (x + q * y1) >> v);
        (m00, m01, m10, m11) = (
            m10 << v,
            m11 << v,
            (m00 << v) + q * m10,
            (m01 << v) + q * m11,
        );
        j += v;
    }
    (j, Mat([m00, m01, m10, m11].map(BigInt::from)))
}

#[cfg(test)]
thread_local! {
    static STEIN_ACCEPTED_SHIFT: std::cell::Cell<u32> = const {std::cell::Cell::new(0)};
    static STEIN_REJECTED_SHIFT: std::cell::Cell<u32> = const {std::cell::Cell::new(0)};
}
/// 2-adic Lehmer binary gcd on the positive odd parts `a >> za` and `b >> zb`: each outer pass
/// advances up to 30 halving steps in 128-bit registers from the low 128 bits (`[[m00, m01],
/// [m10, m11]]` with `|m_ij| < 2^62`, determinant `+-2^(2j)`) and applies the resulting signed
/// `i64` matrix to two reusable `u64` word buffers in one pass, dropping to 128-bit and 64-bit
/// Stein registers once both operands fit in two words, with no per-pass heap allocations.
fn stein_odd(a: &BigUint, za: u64, b: &BigUint, zb: u64) -> BigUint {
    fn odd_words(x: &BigUint, z: u64) -> Vec<u64> {
        let w = (z / 64) as usize;
        let sh = (z % 64) as u32;
        let mut v: Vec<u64> = x.iter_u64_digits().skip(w).collect();
        if sh != 0 && !v.is_empty() {
            for i in 0..v.len() - 1 {
                v[i] = (v[i] >> sh) | (v[i + 1] << (64 - sh));
            }
            if let Some(last) = v.last_mut() {
                *last >>= sh;
            }
        }
        while v.last() == Some(&0) {
            v.pop();
        }
        v
    }
    fn cmp_words(u: &[u64], v: &[u64]) -> std::cmp::Ordering {
        u.len().cmp(&v.len()).then_with(|| {
            for i in (0..u.len()).rev() {
                if u[i] != v[i] {
                    return u[i].cmp(&v[i]);
                }
            }
            std::cmp::Ordering::Equal
        })
    }
    fn shr_odd_in_place(u: &mut Vec<u64>) {
        while u.last() == Some(&0) {
            u.pop();
        }
        let Some(w) = u.iter().position(|&x| x != 0) else {
            u.clear();
            return;
        };
        let sh = u[w].trailing_zeros();
        let len = u.len() - w;
        if sh == 0 {
            if w != 0 {
                u.copy_within(w.., 0);
                u.truncate(len);
            }
        } else {
            for j in 0..len - 1 {
                u[j] = (u[j + w] >> sh) | (u[j + w + 1] << (64 - sh));
            }
            u[len - 1] = u[len - 1 + w] >> sh;
            u.truncate(len);
            while u.last() == Some(&0) {
                u.pop();
            }
        }
    }
    fn sub_shr_odd(u: &mut Vec<u64>, v: &[u64]) {
        let mut borrow = 0u64;
        for (ui, &vi) in u.iter_mut().zip(v) {
            let (d1, b1) = ui.overflowing_sub(vi);
            let (d2, b2) = d1.overflowing_sub(borrow);
            *ui = d2;
            borrow = u64::from(b1 | b2);
        }
        let mut i = v.len();
        while borrow != 0 {
            let (d, b) = u[i].overflowing_sub(1);
            u[i] = d;
            borrow = u64::from(b);
            i += 1;
        }
        shr_odd_in_place(u);
    }
    fn lin_shr_odd(out: &mut Vec<u64>, m0: i64, m1: i64, u: &[u64], v: &[u64]) {
        out.clear();
        let len = u.len().max(v.len());
        let (c0, c1) = (i128::from(m0), i128::from(m1));
        let mut carry = 0i128;
        for i in 0..len {
            let ui = i128::from(u.get(i).copied().unwrap_or(0));
            let vi = i128::from(v.get(i).copied().unwrap_or(0));
            let acc = carry + c0 * ui + c1 * vi;
            out.push(acc as u64);
            carry = acc >> 64;
        }
        if carry > 0 {
            out.push(carry as u64);
        } else if carry < 0 {
            out.push(carry as u64);
            let mut borrow = 0u64;
            for w in out.iter_mut() {
                let (d1, b1) = 0u64.overflowing_sub(*w);
                let (d2, b2) = d1.overflowing_sub(borrow);
                *w = d2;
                borrow = u64::from(b1 | b2);
            }
        }
        shr_odd_in_place(out);
    }
    let mut u = odd_words(a, za);
    let mut v = odd_words(b, zb);
    let mut c_buf: Vec<u64> = Vec::new();
    let mut d_buf: Vec<u64> = Vec::new();
    loop {
        if u.len() <= 2 && v.len() <= 2 {
            let mut uu = v128_from(&u);
            let mut vv = v128_from(&v);
            loop {
                if uu <= u128::from(u64::MAX) && vv <= u128::from(u64::MAX) {
                    let (mut a64, mut b64) = (uu as u64, vv as u64);
                    while a64 != b64 {
                        if a64 < b64 {
                            (a64, b64) = (b64, a64);
                        }
                        a64 -= b64;
                        a64 >>= a64.trailing_zeros();
                    }
                    return BigUint::from(a64);
                }
                if uu == vv {
                    return BigUint::from(uu);
                }
                if uu < vv {
                    (uu, vv) = (vv, uu);
                }
                uu -= vv;
                uu >>= uu.trailing_zeros();
            }
        }
        match cmp_words(&u, &v) {
            std::cmp::Ordering::Equal => return from_words(u),
            std::cmp::Ordering::Less => std::mem::swap(&mut u, &mut v),
            std::cmp::Ordering::Greater => {}
        }
        let mut x = v128_from(&u);
        let mut y = v128_from(&v).wrapping_sub(x);
        let [mut m00, mut m01, mut m10, mut m11] = [1i64, 0, -1, 1];
        let mut j = 0u32;
        while y != 0 {
            let tz = y.trailing_zeros();
            if j + tz > 30 {
                #[cfg(test)]
                STEIN_REJECTED_SHIFT.with(|v| v.set(v.get().max(j + tz)));
                break;
            }
            let y1 = y >> tz;
            let y1_64 = y1 as u64;
            let mut inv = 1u64;
            for _ in 0..6 {
                inv = inv.wrapping_mul(2u64.wrapping_sub(y1_64.wrapping_mul(inv)));
            }
            let mask = (1u64 << (tz + 1)) - 1;
            let t = (x as u64).wrapping_neg().wrapping_mul(inv) & mask;
            let q = if t > (1u64 << tz) {
                (t as i64) - (1i64 << (tz + 1))
            } else {
                t as i64
            };
            let q128 = (q as i128) as u128;
            (x, y) = (y1, x.wrapping_add(q128.wrapping_mul(y1)) >> tz);
            (m00, m01, m10, m11) = (
                m10 << tz,
                m11 << tz,
                (m00 << tz) + q * m10,
                (m01 << tz) + q * m11,
            );
            j += tz;
            #[cfg(test)]
            STEIN_ACCEPTED_SHIFT.with(|v| v.set(v.get().max(j)));
        }
        if j == 0 {
            sub_shr_odd(&mut u, &v);
        } else {
            lin_shr_odd(&mut c_buf, m00, m01, &u, &v);
            lin_shr_odd(&mut d_buf, m10, m11, &u, &v);
            if d_buf.is_empty() {
                return from_words(c_buf);
            }
            std::mem::swap(&mut u, &mut c_buf);
            std::mem::swap(&mut v, &mut d_buf);
        }
    }
}

fn v128_from(v: &[u64]) -> u128 {
    u128::from(v[0]) | (v.get(1).copied().map_or(0, u128::from) << 64)
}

/// The greatest common divisor of `a` and `b`. The powers of 2 are taken out first; the odd
/// parts then go through the binary gcd, half of what is left at a time by [`half`], whose
/// steps keep the odd part of the gcd. O(M(n) log n).
pub(crate) fn gcd(a: &BigUint, b: &BigUint) -> BigUint {
    gcd_using(a, b, true)
}

/// The same half-GCD without the historical wide Stein handoff. The solver
/// already performs machine-sized gcds directly, so its big values take this
/// path at every width. Test: pncx_fibonacci_scale and the gcd axis.
pub(crate) fn gcd_recursive(a: &BigUint, b: &BigUint) -> BigUint {
    gcd_using(a, b, false)
}

fn gcd_using(a: &BigUint, b: &BigUint, handoff: bool) -> BigUint {
    let (Some(za), Some(zb)) = (a.trailing_zeros(), b.trailing_zeros()) else {
        return a | b;
    };
    let z = za.min(zb);
    if (a.bits() - za).max(b.bits() - zb) <= GCD_LEAF {
        return stein_odd(a, za, b, zb) << z;
    }
    let mut x = BigInt::from(a >> za);
    let mut y = BigInt::from(b >> zb) - &x;
    let _hold = HoldRoots::open();
    // Complexity tradeoff: the half gcd costs O(M(n) log n) = O(n log^2 n), a log factor above
    // a product, accepted because no faster gcd is known: the subquadratic gcds (Schönhage 1971;
    // the binary recursive gcd of Stehlé and Zimmermann, ANTS 2004, used here; Möller 2008)
    // all take O(M(n) log n) (author decision A47, 2026-11-09; COMPLEXITY.md C31). The
    // scaling test holds it to the limit of work of order n log^2 n. Below `GCD_LEAF`,
    // `stein_odd` runs 2-adic Lehmer passes (up to 30 halvings per pass in 128-bit registers,
    // applied in one pass over two reusable word buffers) and drops to 128-bit and 64-bit Stein
    // registers once both operands fit in two words, avoiding num-bigint's per-step shift
    // allocations while keeping O(n^2) bounded to the leaf width with a 30x smaller pass count.
    // Measured on 2026-11-06: 1.8 s at 32768 words, 11.0 s at 131072; Stein's gcd is faster
    // below about 300 words at load 1 (2026-11-06), 512 to 1024 at load 45 to 75 (2026-11-05);
    // see `GCD_LEAF`. Test `a_gcd_of_wide_numbers_scales`.
    while !y.is_zero() {
        let n = x.bits().max(y.bits());
        if handoff && n <= GCD_LEAF {
            let (xm, ym) = (x.magnitude(), y.magnitude());
            let (zx, zy) = (xm.trailing_zeros().unwrap(), ym.trailing_zeros().unwrap());
            return (stein_odd(xm, zx, ym, zy) << zx.min(zy)) << z;
        }
        let (j, r) = half(&x, &y, n / 2);
        if j > 0 {
            (x, y) = r.apply(&x, &y, j);
        }
        drop(r);
        if let Some(v) = nu(&y) {
            let (_, a1, b1) = step(&x, &y, v);
            (x, y) = (a1, b1);
        }
    }
    x.magnitude() << z
}

/// `a^-1 mod m` for `m` above zero, or `None` when `a` and `m` have a common factor. The odd
/// part `o` of `m` by [`inverse_mod_odd`], the power `2^e` by [`inverse_mod_pow2`], joined by
/// the Chinese remainder theorem: `x = x1 + o ((x2 - x1) o^-1 mod 2^e)`, below `o 2^e = m`.
/// O(M(n) log n).
pub(crate) fn inverse_mod(a: &BigUint, m: &BigUint) -> Option<BigUint> {
    let e = m.trailing_zeros()?;
    let o = m >> e;
    let x1 = match o.is_one() {
        true => BigUint::zero(),
        false => inverse_mod_odd(&rem(a, &o), &o)?,
    };
    if e == 0 {
        return Some(x1);
    }
    if !a.bit(0) {
        return None;
    }
    let mask = (BigUint::one() << e) - 1u32;
    let x2 = inverse_mod_pow2(a, e);
    let d = (x2 + &mask + 1u32 - (&x1 & &mask)) & &mask;
    let t = mul(&d, &inverse_mod_pow2(&o, e)) & &mask;
    Some(x1 + mul(&o, &t))
}

/// `a^-1 mod b` for `b` odd and above 1 and `a` below `b`, or `None` when they have a common
/// factor. The binary gcd of `(b, y0)`, `y0` being `a` or `a - b`, whichever is even, is run
/// as in [`gcd`] but down to `y = 0`, with no leaf of [`GCD_LEAF`] (the leaf of [`half`] is
/// [`half_leaf`]), and the second column `(c0, c1)` of the product `T` of its steps is kept:
/// each pair it reaches is `T (b, y0) / 2^e`, so modulo `b` it is `(c0, c1) y0 / 2^e`. At the
/// end `x = ±g`; with `g = 1`, `x c0 2^-e` is the inverse of `y0`, which is `a` modulo `b`.
/// `2^-e mod b` is `(1 + b s) / 2^e` with `s = -b^-1 mod 2^e`. O(M(n) log n), as [`gcd`].
fn inverse_mod_odd(a: &BigUint, b: &BigUint) -> Option<BigUint> {
    let bi = BigInt::from(b.clone());
    let mut x = bi.clone();
    let mut y = BigInt::from(a.clone());
    if a.bit(0) {
        y -= &bi;
    }
    let (mut c0, mut c1) = (BigInt::zero(), BigInt::one());
    let mut e = 0u64;
    while !y.is_zero() {
        let n = x.bits().max(y.bits());
        let (j, r) = half(&x, &y, n / 2);
        if j > 0 {
            (x, y) = r.apply(&x, &y, j);
            let [m00, m01, m10, m11] = &r.0;
            (c0, c1) = (
                mul_int(m00, &c0) + mul_int(m01, &c1),
                mul_int(m10, &c0) + mul_int(m11, &c1),
            );
            e += 2 * j;
        }
        drop(r);
        if let Some(v) = nu(&y) {
            let (q, a1, b1) = step(&x, &y, v);
            (x, y) = (a1, b1);
            (c0, c1) = (&c1 << v, (&c0 << v) + mul_int(&q, &c1));
            e += 2 * v;
        }
    }
    if !x.magnitude().is_one() {
        return None;
    }
    let num = c0 * x;
    let r = rem(num.magnitude(), b);
    let r = match num.is_negative() && !r.is_zero() {
        true => b - r,
        false => r,
    };
    let two_inv = match e {
        0 => BigUint::one(),
        _ => {
            let s = (BigUint::one() << e) - inverse_mod_pow2(b, e);
            (BigUint::one() + mul(b, &s)) >> e
        }
    };
    Some(rem(&mul(&r, &two_inv), b))
}

/// Extended binary half-GCD on nonnegative inputs. The half-GCD's matrix
/// acts on the pair over a power of two. Only its coefficient of the second
/// input is accumulated; an exact division recovers the other coefficient.
// Complexity tradeoff: extended Euclid uses O(n^2) bit operations, while
// separately computing the gcd and an inverse repeats the half-GCD. This
// computes both in one O(M(n) log n) pass. An overflow of the halving count
// returns None. Tests: pncx_fast_bezout_matches_euclid,
// bezout_coefficients_with_unequal_widths, pncx_fibonacci_scale.
pub(super) fn bezout(a: &BigUint, b: &BigUint) -> Option<(BigUint, BigInt, BigInt)> {
    let (Some(za), Some(zb)) = (a.trailing_zeros(), b.trailing_zeros()) else {
        return Some((
            a | b,
            BigInt::from(!a.is_zero()),
            BigInt::from(!b.is_zero()),
        ));
    };
    let common = za.min(zb);
    let (a, b) = (a >> common, b >> common);
    let swapped = !a.bit(0);
    let (u, v) = if swapped { (&b, &a) } else { (&a, &b) };
    let mut x = BigInt::from(u.clone());
    let mut y = BigInt::from(v.clone());
    if v.bit(0) {
        y -= &x;
    }
    let (mut bx, mut by) = (BigInt::zero(), BigInt::one());
    let mut halvings = 0u64;
    while !y.is_zero() {
        let n = x.bits().max(y.bits());
        let (j, r) = half(&x, &y, (n / 2).max(1));
        if j > 0 {
            (x, y) = r.apply(&x, &y, j);
            let [m00, m01, m10, m11] = &r.0;
            (bx, by) = (
                mul_int(m00, &bx) + mul_int(m01, &by),
                mul_int(m10, &bx) + mul_int(m11, &by),
            );
            halvings = halvings.checked_add(j)?;
        }
        drop(r);
        if let Some(j) = y.trailing_zeros() {
            let (q, a1, b1) = step(&x, &y, j);
            (bx, by) = (&by << j, (&bx << j) + mul_int(&q, &by));
            (x, y) = (a1, b1);
            halvings = halvings.checked_add(j)?;
        }
    }
    let g = x.magnitude();
    let modulus = div_rem(u, g).0;
    let m = modulus.bits();
    let (v_coefficient, inverse) = if modulus.is_one() {
        (BigUint::zero(), BigUint::one())
    } else {
        let coefficient = if x.is_negative() { -bx } else { bx };
        let c = rem(coefficient.magnitude(), &modulus);
        let mut c = if coefficient.is_negative() && !c.is_zero() {
            &modulus - c
        } else {
            c
        };
        // Divide c by 2^shift modulo the odd modulus without another gcd, in chunks of at
        // most `m` bits, `m` the modulus's width: c + k modulus is divisible by 2^s, with
        // 0 < k < 2^s, k = -c modulus^-1 mod 2^s, when c is not 0 mod 2^s. Each chunk keeps
        // c below 2 modulus, so one subtraction ends below the modulus.
        // Complexity tradeoff: one chunk of all `shift` bits needs modulus^-1 to `shift` bits,
        // O(M(shift)) even for a small modulus; chunks of `m` bits reuse one inverse of `m`
        // bits and cost O((shift / m + 1) M(m)), no more. Test pncx_fast_bezout_matches_euclid.
        let mut shift = halvings.checked_mul(2)?;
        let inverse = inverse_mod_pow2(&modulus, m);
        while shift > 0 {
            let s = shift.min(m);
            let mask = (BigUint::one() << s) - 1u32;
            let low = &c & &mask;
            if !low.is_zero() {
                let k = (&mask + 1u32) - (mul(&low, &inverse) & &mask);
                c = (c + mul(&k, &modulus)) >> s;
            } else {
                c >>= s;
            }
            shift -= s;
        }
        if c >= modulus {
            c -= &modulus;
        }
        debug_assert!(c < modulus);
        (c, inverse)
    };
    // The other coefficient is (g - t v) / u = (1 - t V) / U for U = u / g and V = v / g,
    // an exact quotient q of A = |1 - t V| by the odd U of `m` bits. Its low `m` bits are
    // A U^-1 mod 2^m, from the inverse above; its high bits are floor((A >> m) / U), since
    // A = U (q_high 2^m + q_low) with q_low U < 2^m U.
    // Complexity tradeoff: dividing g - t v by u, about 2n bits by n, costs a general
    // division, O(M(n)) with a large constant (about an eighth of the call at 356 words);
    // the low bits cost one product of m bits, and the high part divides only the bits of A
    // above m, under the width of V, so nothing for balanced inputs. Test
    // bezout_coefficients_with_unequal_widths.
    let second = BigInt::from(v_coefficient);
    let reduced_v = match g.is_one() {
        true => Cow::Borrowed(v),
        false => Cow::Owned(div_rem(v, g).0),
    };
    let numerator = BigInt::one() - BigInt::from(mul(second.magnitude(), &reduced_v));
    let a_mag = numerator.magnitude();
    let mask = (BigUint::one() << m) - 1u32;
    let low = mul(&(a_mag & &mask), &inverse) & mask;
    let high = div_rem(&(a_mag >> m), &modulus).0;
    let first = BigInt::from_biguint(numerator.sign(), (high << m) + low);
    let (s, t) = if swapped {
        (second, first)
    } else {
        (first, second)
    };
    Some((g << common, s, t))
}

// ------------------------------------------------------------------------------------------
// Decimal printing

/// A divisor used many times, with how it is divided by: num-bigint's division when it has at
/// most [`DIV_LEAF`] bits, long division over its nonzero words when that costs less, else a
/// [`Level`]: its reciprocal and itself transformed once, with the roots for every product.
pub(crate) struct Divisor<'a> {
    d: Cow<'a, BigUint>,
    /// The words of `d`.
    len: usize,
    by: By,
}

enum By {
    Leaf,
    Sparse,
    Reciprocal(Box<Level>, Rc<Roots>),
}

/// The points of the transforms a [`Divisor`] of `d` keeps, the most of its [`level_points`],
/// or `None` when it divides without them: by num-bigint, for at most [`DIV_LEAF`] bits, or by
/// long division over its nonzero words when that costs less. Its memory is a multiple of
/// these points (`num::Rat::rem_euclid` and `num::Rat::div_euclid` ask for it).
pub(crate) fn reciprocal_points(d: &BigUint) -> Option<usize> {
    let (n, len) = (d.bits(), words(d));
    // Complexity tradeoff: as in `div_rem`, the cheaper of long division over the nonzero
    // words and the reciprocal, for a dividend of twice the divisor's words, by the computed
    // costs and with no size constant (COMPLEXITY.md K30).
    match n <= DIV_LEAF || sparse_div_cost(len, nonzero_words(d)) <= newton_cost(len, len) {
        true => None,
        false => {
            let (linear, cyclic) = level_points(n, n);
            Some(linear.max(cyclic))
        }
    }
}

impl<'a> Divisor<'a> {
    pub(crate) fn new(d: Cow<'a, BigUint>) -> Divisor<'a> {
        assert!(!d.is_zero(), "a division by zero");
        let n = d.bits();
        let by = match reciprocal_points(&d) {
            None if n <= DIV_LEAF => By::Leaf,
            None => By::Sparse,
            Some(points) => {
                let tw = roots(points);
                By::Reciprocal(Box::new(Level::new(d.to_u64_digits(), n, n, &tw)), tw)
            }
        };
        Divisor {
            len: words(&d),
            d,
            by,
        }
    }

    /// `(a / d, a mod d)`, by [`Divisor::blocks`].
    pub(crate) fn div_rem(&self, a: &BigUint) -> (BigUint, BigUint) {
        let mut quotient = vec![0u64; words(a)];
        let r = self.blocks(a, |at, q| quotient[at..at + q.len()].copy_from_slice(q));
        (from_words(quotient), from_words(r))
    }

    /// `a mod d`, by [`Divisor::blocks`], its memory that of `d` whatever the size of `a`.
    pub(crate) fn rem(&self, a: &BigUint) -> BigUint {
        from_words(self.blocks(a, |_, _| {}))
    }

    /// The words of `a mod d`, `a` read from the top in blocks of as many words as `d` has:
    /// each step divides the remainder so far joined to the next block, below `d 2^(64 len)`,
    /// by `d` ([`Divisor::step`]), and gives the words of its quotient to `put` with the place
    /// of their lowest word in `a / d`. The words of each step are built in one buffer, so a
    /// step copies nothing of `a` but its block. O((m / n) M(n)) for `m` bits by `n`.
    fn blocks(&self, a: &BigUint, mut put: impl FnMut(usize, &[u64])) -> Vec<u64> {
        let len = self.len;
        let mut digits = a.iter_u64_digits();
        let mut left = digits.len();
        let take = match left % len {
            0 => len.min(left),
            k => k,
        };
        // The first block has at most `len` words, so its quotient is below `2^64` and
        // num-bigint's long division finds it with O(n) word products, where the reciprocal
        // would cost a product; every later step has a quotient as wide as `d`.
        let mut x: Vec<u64> = digits.by_ref().rev().take(take).collect();
        x.reverse();
        left -= take;
        let (q, r) = from_words(x).div_rem(&*self.d);
        put(left, &q.to_u64_digits());
        let mut r = r.to_u64_digits();
        let mut x: Vec<u64> = Vec::with_capacity(2 * len);
        while left > 0 {
            // `x = r 2^(64 len) + block`, the block's words read from the top.
            x.clear();
            x.resize(len, 0);
            for (slot, w) in x.iter_mut().rev().zip(digits.by_ref().rev()) {
                *slot = w;
            }
            x.extend_from_slice(&r);
            trim(&mut x);
            left -= len;
            let (q, rest) = self.step(&x);
            put(left, &q);
            r = rest;
        }
        r
    }

    /// `(x / d, x mod d)` as words with no zero on top, for the words `x`, with no zero on
    /// top, below `d 2^(64 len)`: num-bigint's division, long division over `d`'s nonzero
    /// words ([`sparse_div_rem`]), or a [`Level`] ([`Level::div_rem`]), O(M(n)), about one
    /// product's transforms of `d`'s width.
    fn step(&self, x: &[u64]) -> (Vec<u64>, Vec<u64>) {
        match &self.by {
            By::Leaf => {
                let (q, r) = from_words(x.to_vec()).div_rem(&*self.d);
                (q.to_u64_digits(), r.to_u64_digits())
            }
            // Long division needs at least `len - 1` words; fewer are below `d`.
            By::Sparse => match x.len() + 1 < self.len {
                true => (Vec::new(), x.to_vec()),
                false => sparse_div_rem_words(x.iter().copied(), &self.d),
            },
            By::Reciprocal(level, tw) => {
                debug_assert!(
                    x.len() <= level.d.len() + level.yw,
                    "x is below d 2^(64 len)"
                );
                level.div_rem(x, tw)
            }
        }
    }
}

/// One table of roots for each prime of [`FIELDS`] (see [`Field::twiddles`]).
type Roots = [Vec<(u64, u64)>; 3];

/// The roots [`roots`] built last on a thread, and the scopes that keep them.
struct Kept {
    /// The table, while something holds it: a product while it runs, a [`Factor`] or a
    /// printer's level that keeps spectra, or `held`. A table serves every smaller power of
    /// two (see [`Field::twiddles`]), so while it is held it is not built again. Only a weak
    /// reference is kept for the thread: a table of three words a point of the widest
    /// transform, held for the thread's life, would stay counted against the memory limit
    /// after the operation that built it ended (and failed
    /// `a_wide_number_modulo_a_wide_one_answers_when_its_peak_is_given`).
    table: Weak<Roots>,
    /// The table, held while `holds` is above zero.
    held: Option<Rc<Roots>>,
    /// How many [`HoldRoots`] scopes are open on the thread.
    holds: u32,
}

thread_local! {
    static ROOTS: std::cell::RefCell<Kept> = const {
        std::cell::RefCell::new(Kept { table: Weak::new(), held: None, holds: 0 })
    };
}

/// While it lives, [`roots`] keeps the table it built last, so that products run one after
/// another, as the gcd's matrix products are, share one table instead of each building its
/// own. Opened for one operation and dropped at its end, which frees the table once nothing
/// else holds it. Measured, `reading_a_rat_of_two_wide_parts_scales` at 640,000 digits:
/// 7,620 M instructions without it, 7,558 M with it.
struct HoldRoots;

impl HoldRoots {
    fn open() -> HoldRoots {
        ROOTS.with(|kept| kept.borrow_mut().holds += 1);
        HoldRoots
    }
}

impl Drop for HoldRoots {
    fn drop(&mut self) {
        ROOTS.with(|kept| {
            let mut kept = kept.borrow_mut();
            kept.holds -= 1;
            if kept.holds == 0 {
                kept.held = None;
            }
        });
    }
}

/// The roots of [`FIELDS`] for transforms of up to `n` points, a power of two: those of two
/// points for `n = 1`, whose transform is itself but whose table [`Field::forward`] checks.
/// The table [`ROOTS`] refers to when it is still held and wide enough, else a new one,
/// which an open [`HoldRoots`] keeps.
fn roots(n: usize) -> Rc<Roots> {
    ROOTS.with(|kept| {
        let mut kept = kept.borrow_mut();
        match kept.table.upgrade() {
            Some(tw) if 2 * tw[0].len() >= n => tw,
            _ => {
                let tw = Rc::new(roots_of(n));
                kept.table = Rc::downgrade(&tw);
                if kept.holds > 0 {
                    kept.held = Some(Rc::clone(&tw));
                }
                tw
            }
        }
    })
}

/// The roots of [`FIELDS`] for transforms of exactly `n.max(2)` points, built.
fn roots_of(n: usize) -> Roots {
    FIELDS.each_ref().map(|f| f.twiddles(n.max(2)))
}

/// The [`Field::spectrum`] of the words `x` for each prime of [`FIELDS`], on `n` points, `x`
/// folded modulo `2^(64 n) - 1` when it has more words.
fn spectra(x: &[u64], n: usize, tw: &Roots) -> [Vec<u64>; 3] {
    let x = folded(x, n);
    [0, 1, 2].map(|k| FIELDS[k].spectrum(&x, n, &tw[k]))
}

/// `x` folded modulo `2^(64 m) - 1` ([`fold_words`]) when it has more than `m` words, else
/// itself.
fn folded(x: &[u64], m: usize) -> Cow<'_, [u64]> {
    match x.len() > m {
        true => Cow::Owned(fold_words(x, m)),
        false => Cow::Borrowed(x),
    }
}

/// The points of the cyclic products modulo `M = 2^(64 m) - 1` that find a number `v`,
/// `|v| < 2^(bits + 6)`, from its residue modulo `M` and its low word ([`unfold`]): the least
/// power of two `m` with `64 m >= bits - 55`, so that `|v|` is below `2^(64 m + 61)`. The
/// widest use is [`newton`]'s `xh tm < 2^(2h + 2) <= 2^(p + 6)`.
fn cyclic_points(bits: u64) -> usize {
    let words = bits.saturating_sub(55).div_ceil(64).max(1);
    usize::try_from(words)
        .expect("a number whose words fit in memory")
        .next_power_of_two()
}

/// The points of the two products of a [`Level`] for a divisor of `bits` bits whose top `k`
/// bits give the reciprocal: the estimate's, on the `2 yw` words of a product of two numbers of
/// `yw` words, `k` bits' words, and the remainder's ([`cyclic_points`]); the reciprocal's own
/// need no more than the first.
fn level_points(bits: u64, k: u64) -> (usize, usize) {
    let yw = usize::try_from(k.div_ceil(64)).expect("a number whose words fit in memory");
    ((2 * yw).next_power_of_two(), cyclic_points(bits))
}

/// `2^e mod (2^(64 m) - 1)`, as `m` words: one bit.
fn power_around(e: u64, m: usize) -> Vec<u64> {
    let mut power = vec![0u64; m];
    let at = e % (64 * m as u64);
    power[(at / 64) as usize] = 1 << (at % 64);
    power
}

/// `2^e mod 2^64`.
fn low_power(e: u64) -> u64 {
    match e < 64 {
        true => 1 << e,
        false => 0,
    }
}

/// The lowest word of `x`, zero for no words.
fn first(x: &[u64]) -> u64 {
    x.first().copied().unwrap_or(0)
}

/// The number `v`, as whether it is below zero and the words of `|v|`, from `r`, `v` modulo
/// `M = 2^(64 m) - 1` in at most `m` words (`M` itself allowed), and `low`, `v` modulo `2^64`,
/// for `|v| < 2^(64 m + 61)`. With `v = r + j M`, `M = -1` modulo `2^64` gives
/// `j = r - low` modulo `2^64`, and `|j| <= |v| / M + 1 < 2^62`, so `j` is that residue read
/// as signed. O(m).
fn unfold(mut r: Vec<u64>, m: usize, low: u64) -> (bool, Vec<u64>) {
    let j = first(&r).wrapping_sub(low) as i64;
    let k = j.unsigned_abs();
    r.resize(m + 1, 0);
    let negative = j < 0;
    if negative {
        // `|v| = k M - r`, computed modulo `2^(64 (m + 1))`, which holds it: `-r`, then
        // `k 2^(64 m) - k` added.
        for v in r.iter_mut() {
            *v = !*v;
        }
        add_at(&mut r, 0, 1);
    }
    // `v = r + k 2^(64 m) - k`, or `|v|` as above; the borrow past the top, if any, cancels
    // the carry into the top word, both modulo `2^(64 (m + 1))`.
    r[m] = r[m].wrapping_add(k);
    sub_at(&mut r, 0, k);
    trim(&mut r);
    (negative && !r.is_empty(), r)
}

/// The remainder `x - q d`, as whether it is below zero and the words of its magnitude, from
/// its residue modulo `M = 2^(64 m) - 1`, where `q d` is a cyclic product with `d`'s spectra
/// `dc` on `m` points, and its low word ([`unfold`]), for `|x - q d| < 2^(64 m + 61)`.
fn remainder(x: &[u64], d: &[u64], dc: &[Vec<u64>; 3], q: &[u64], tw: &Roots) -> (bool, Vec<u64>) {
    let m = dc[0].len();
    let (mut qd, carry) = cyclic_product(&folded(q, m), dc, tw);
    add_around(&mut qd, carry);
    let r = sub_around(fold_words(x, m), &qd);
    let low = first(x).wrapping_sub(first(q).wrapping_mul(first(d)));
    unfold(r, m, low)
}

/// The decimal digits of `x`, by halves: `x = high * 10^(L 2^i) + low`, `L` being 597, each
/// half written alone and the low half padded with zeros to its width. The widest power, which
/// divides once, is divided by a reciprocal of only the precision that division and the level
/// below need; each power below it has its reciprocal derived from the one above by one
/// product and one cyclic product, transformed once and reused by every division at its level.
/// O(M(n) log n), the recursion `log2(n / L)` deep. Numbers of fewer than 60,000 words are
/// written by num-bigint, which is faster there; the text is the same.
pub fn to_decimal(x: &BigUint) -> String {
    // Complexity tradeoff: a number of fewer than `PRINT_WHOLE` words is printed whole by
    // num-bigint, whose printing is faster there: it costs about 2.85 times as much per
    // doubling of the words, against about 2.3 for the split below, whose fixed costs (the
    // powers and one reciprocal) make it slower up to about 60,000 words. The two print the
    // same digits. The crossover is measured (see `PRINT_WHOLE`) and measured again at the
    // port to Zed (COMPLEXITY.md K81). `x < 2^(3 L) < 10^L` is a single leaf.
    if words(x) < PRINT_WHOLE || x.bits() < 3 * PRINT_LEAF as u64 {
        return x.to_string();
    }
    let mut powers = vec![BigUint::from(10u32).pow(PRINT_LEAF as u32)];
    loop {
        let last = powers.last().expect("the first power is built");
        // `last^2 > x` once its bits exceed `x`'s.
        if 2 * last.bits() - 1 > x.bits() {
            break;
        }
        let next = mul(last, last);
        if next > *x {
            break;
        }
        powers.push(next);
    }
    // Each power listed is at most `x`, except perhaps the first, and the last squared is
    // above it, so `high` and `low` below are each under the next power down squared.
    let top = powers.pop().expect("the first power is listed");
    // Complexity tradeoff: a number whose split would divide by a power of ten of at most
    // `PRINT_HANDOFF` words is printed by num-bigint, whose printing is faster there; the two
    // print the same digits. The crossover is measured (see `PRINT_HANDOFF`) and measured
    // again at the port to Zed (COMPLEXITY.md K81).
    if top > *x || words(&top) <= PRINT_HANDOFF {
        return x.to_string();
    }
    // Complexity tradeoff: the digits are written by halves, each level of the recursion
    // dividing by one power of ten, so the cost is O(M(n) log n) = O(n log^2 n), a log factor
    // above a product, accepted because no faster radix conversion is known: the subquadratic
    // method (Schönhage 1971; the scaled remainder tree of Bernstein, 2004; Brent and
    // Zimmermann, Modern Computer Arithmetic, 2010, section 1.7) takes O(M(n) log n) (author
    // decision A47, 2026-11-09; COMPLEXITY.md C31), against num-bigint's O(n^2). Tested by
    // `printing_a_wide_number_scales` and `writing_a_wide_end_scales` (COMPLEXITY.md K30,
    // K81).
    let n = top.bits();
    // The quotient has at most `k` bits. The reciprocal of `top` is taken to `p` bits, enough
    // for the quotient and for the level below (see [`derive()`]), which needs `p >= w + 3`
    // for its `w` bits of words, its square being `top`.
    let k = x.bits() - n + 1;
    let p = powers
        .last()
        .map_or(k, |d| k.max(d.bits().next_multiple_of(64) + 4));
    // `r = 2^2p / t`, floored, for `t` the top `p` bits of `top` (or `top 2^(p - n)`), lies in
    // `[R, R + 4]`, `R = 2^(p + n) / top` floored: `t <= top / 2^(n - p) < t + 1`, and
    // `2^2p / t - 2^2p / (t + 1) < 2^2p / t^2 <= 4`.
    let r = match p <= n {
        true => reciprocal(&(&top >> (n - p)), p),
        false => reciprocal(&(&top << (p - n)), p),
    };
    // With `a = x / 2^(n - 1)`, floored, `a r / 2^(p + 1)` is within 3 of `x / top`: the
    // error of `r` adds less than `4 x / 2^(p + n) <= 2`, as `x < 2^(n + k - 1)` and `p >= k`,
    // and the floors take off at most 2.
    let a = x >> (n - 1);
    let estimate = mul(&a, &r) >> (p + 1);
    drop(a);
    let product = mul(&estimate, &top);
    let (high, low) = settle(x, &top, estimate, product);
    drop(top);
    let printer = Printer::new(powers, (r, p + n));
    // `log10(2) < 1234 / 4096`.
    let digits = usize::try_from(x.bits() * 1234 / 4096 + 2).expect("a text that fits in memory");
    let mut out = String::with_capacity(digits);
    let level = printer.levels.len() + printer.first;
    // `high` is not zero, the power being at most `x`.
    printer.write(high.to_u64_digits(), level, false, &mut out);
    drop(high);
    printer.write(low.to_u64_digits(), level, true, &mut out);
    out
}

/// The levels of [`to_decimal`] below its widest power: `levels[j]` divides by
/// `10^(L 2^(first + j))`, and a number below `10^(L 2^first)` is a leaf, printed by
/// num-bigint. `tw` holds one table of roots for each prime of [`FIELDS`], of as many points
/// as the widest product needs, which serves every narrower one (see [`Field::forward`]).
struct Printer {
    first: usize,
    levels: Vec<Level>,
    tw: [Vec<(u64, u64)>; 3],
}

/// A divisor `d`, of `n` bits, divided by many times, with what each division needs
/// transformed once (per prime of [`FIELDS`], [`Field::spectrum`]): `y`, the spectra of
/// `X' = X - 2^w` on enough points for its product with a number of `yw` words, `X` the
/// reciprocal of `t`, the top `k <= n` bits of `d`, shifted to `w = 64 yw` bits, with
/// `T X <= 2^2w <= T (X + 2)`, `T = t 2^(w - k)` (the floor, or [`approx_reciprocal`]); and `dc`,
/// the spectra of `d` on `m` points, `64 m >= n - 55` ([`cyclic_points`]), or more.
struct Level {
    d: Vec<u64>,
    bits: u64,
    yw: usize,
    y: [Vec<u64>; 3],
    dc: [Vec<u64>; 3],
}

impl Level {
    /// The level of `d`, as words, of `bits` bits, its reciprocal from its top `k` bits, with
    /// the points of [`level_points`] and `tw` as for [`Field::forward`] of at least that many.
    fn new(d: Vec<u64>, bits: u64, k: u64, tw: &Roots) -> Level {
        let (linear, cyclic) = level_points(bits, k);
        let w = k.next_multiple_of(64);
        let t = from_words(shr_words(&d, bits - k)) << (w - k);
        let x = approx_reciprocal(&t, w, tw);
        drop(t);
        // `2^w <= X < 2^(w + 1)`: the top word is 1.
        let mut low = x.to_u64_digits();
        drop(x);
        let top = low.pop();
        debug_assert_eq!(top, Some(1), "the reciprocal has w + 1 bits");
        trim(&mut low);
        Level {
            y: spectra(&low, linear, tw),
            dc: spectra(&d, cyclic, tw),
            yw: usize::try_from(w / 64).expect("a number whose words fit in memory"),
            d,
            bits,
        }
    }

    /// `(x / d, x mod d)` as words, for `x < 2^(n + w)` when `k = n`, and `x < 2^(n + k - 1)`
    /// when `k < n`. With `xh = x / 2^n`, floored, below `2^w`, the estimate
    /// `q0 = xh X / 2^w`, floored, is `xh + xh X' / 2^w`, a product of `yw` words by `yw`, and
    /// lies in `[q - 4, q]` for `k = n`: `xh X / 2^w > xh 2^k / t - 2`, `x / d < (xh + 1) 2^k /
    /// t`, `2^k / t <= 2`, and the floor takes off less than 1 more. For `k < n` the top bits
    /// `t` of `d` make the estimate up to 2 above as well (`x / d < 2^k`, so `(x / d) / t < 2`),
    /// `[q - 4, q + 2]`. So the remainder `x - q0 d` lies in `[-2d, 5d)`, below
    /// `2^(64 m + 61)` in size, and is found by a cyclic product on `d`'s `m` points
    /// ([`remainder`]); at most four steps of one `d` correct it. O(M(n)).
    fn div_rem(&self, x: &[u64], tw: &Roots) -> (Vec<u64>, Vec<u64>) {
        // A high half often is below the power: its quotient is zero, with no transform.
        if cmp_words(x, &self.d).is_lt() {
            return (Vec::new(), x.to_vec());
        }
        let xh = shr_words(x, self.bits);
        debug_assert!(xh.len() <= self.yw, "x / 2^n is below 2^w");
        let (yx, carry) = cyclic_product(&xh, &self.y, tw);
        debug_assert_eq!(carry, 0, "the product fits in its points");
        let mut q = xh;
        add_words(&mut q, yx.get(self.yw..).unwrap_or(&[]));
        drop(yx);
        trim(&mut q);
        let (mut negative, mut r) = remainder(x, &self.d, &self.dc, &q, tw);
        let mut steps = 0;
        while negative {
            // `-r + d`: below zero while `r > d`.
            negative = cmp_words(&r, &self.d).is_gt();
            r = match negative {
                true => {
                    sub_words(&mut r, &self.d);
                    r
                }
                // `d - r` as `-(r - d)` modulo `2^(64 len(d))`, in place.
                false => {
                    r.resize(self.d.len(), 0);
                    sub_words(&mut r, &self.d);
                    for v in r.iter_mut() {
                        *v = !*v;
                    }
                    add_at(&mut r, 0, 1);
                    r
                }
            };
            trim(&mut r);
            let borrow = sub_at(&mut q, 0, 1);
            debug_assert!(!borrow, "the estimate is above the quotient");
            trim(&mut q);
            steps += 1;
        }
        while cmp_words(&r, &self.d).is_ge() {
            let borrow = sub_words(&mut r, &self.d);
            debug_assert!(!borrow, "r is at least d");
            trim(&mut r);
            increment(&mut q);
            steps += 1;
        }
        debug_assert!(steps <= 4, "the estimate is at most four off");
        (q, r)
    }
}

/// The coefficients of the product, cyclic on `s[k].len()` points, of the words `x` and the
/// number whose spectra (see [`Field::spectrum`]) are `s`, joined and carried into words,
/// with the carry out of the top; `tw` as for [`Field::forward`].
fn cyclic_product(x: &[u64], s: &[Vec<u64>; 3], tw: &[Vec<(u64, u64)>; 3]) -> (Vec<u64>, u128) {
    let [f0, f1, f2] = &FIELDS;
    let mut r0 = f0.cyclic(x, &s[0], &tw[0]);
    let r1 = f1.cyclic(x, &s[1], &tw[1]);
    let r2 = f2.cyclic(x, &s[2], &tw[2]);
    let carry = garner(&mut r0, &r1, &r2);
    (r0, carry)
}

/// `(a - b) mod M`, `M = 2^(64 m) - 1`, for `a` and `b` of `m` words each below or at `M`,
/// as words with no zero on top, `M` itself read as `0`.
fn sub_around(mut a: Vec<u64>, b: &[u64]) -> Vec<u64> {
    if sub_words(&mut a, b) {
        // `a - b + 2^(64 m) >= 1`, so taking one off borrows nothing past the top.
        sub_at(&mut a, 0, 1);
    }
    if a.iter().all(|&v| v == u64::MAX) {
        a.fill(0);
    }
    trim(&mut a);
    a
}

/// `floor(2^(w + n) / d)` for `d` of `n` bits, `w` the bits of its words, from `ya`, which is
/// `Y = floor(2^ea / d^2)` with `ea >= w + 2n`, or up to 4 above it with `ea >= w + 2n + 3`;
/// `d` also given as words `dw` and as the spectra `dc` of its cyclic product (see
/// [`Level`]). As `1/d = d / d^2`, with `R = floor(2^(w + 2n) / d^2) = Y / 2^(ea - w - 2n)`
/// (floors compose), `r = ya / 2^(ea - w - 2n)` is `R` or `R + 1`, and `R d` lies in
/// `(2^(w + 2n) / d - d, 2^(w + 2n) / d]`, so `t = r d / 2^n`, floored, is the quotient,
/// one below or one above, since `d < 2^n`; which is told by the remainder
/// `2^(w + n) - t d`, in `[-d, 2d)` and so found modulo `2^(64 m) - 1` by a cyclic product. One product of `n`
/// bits and one cyclic one, against several of Newton's iteration. O(M(n)).
fn derive(
    d: &BigUint,
    dw: &[u64],
    dc: &[Vec<u64>; 3],
    tw: &[Vec<(u64, u64)>; 3],
    ya: &BigUint,
    ea: u64,
) -> BigUint {
    let n = d.bits();
    let w = n.next_multiple_of(64);
    let shift = ea
        .checked_sub(w + 2 * n)
        .expect("the reciprocal above is at least as precise");
    let mut t = mul(&(ya >> shift), d) >> n;
    let m = dc[0].len();
    let (mut td, carry) = cyclic_product(&fold_words(&t.to_u64_digits(), m), dc, tw);
    add_around(&mut td, carry);
    // `2^(w + n) mod M` is one bit.
    let mut power = vec![0u64; m];
    let at = (w + n) % (64 * m as u64);
    power[(at / 64) as usize] = 1 << (at % 64);
    // The remainder lies in `[-d, 2d)`, `M > 4d`: `[d, 2d)` for `t` one below, and a
    // negative one reads as `M - d` or above, past `2d`.
    let mut rem = sub_around(power, &td);
    if cmp_words(&rem, dw).is_ge() {
        let past = sub_words(&mut rem, dw);
        debug_assert!(!past, "the remainder is at least d");
        trim(&mut rem);
        match cmp_words(&rem, dw).is_lt() {
            true => t += 1u32,
            false => t -= 1u32,
        }
    }
    t
}

impl Printer {
    /// The levels of the powers `10^(L 2^i)` listed, each the square of the one before,
    /// those of at most [`PRINT_HANDOFF`] words left to leaves, given `above = (ya, ea)`, the
    /// reciprocal of the square of the widest as [`derive()`] takes it; each level's reciprocal
    /// is derived from the one above.
    fn new(powers: Vec<BigUint>, above: (BigUint, u64)) -> Printer {
        let first = powers
            .iter()
            .position(|p| words(p) > PRINT_HANDOFF)
            .unwrap_or(powers.len());
        let powers = powers.get(first..).unwrap_or(&[]);
        // The points of each level's products: `xh y'` for `xh` and `y' < 2^w` of at most `W`
        // words each (`y' = 2^w` only for `d` a power of two), and the least power of two `m`
        // at least `W` with `4d < 2^(64 m) - 1`.
        let points = |d: &BigUint| {
            let len = words(d);
            let mut cyclic = len.next_power_of_two();
            if d.bits() + 2 > 64 * cyclic as u64 {
                cyclic *= 2;
            }
            ((2 * len - 1).next_power_of_two(), cyclic)
        };
        let most = powers
            .last()
            .map(|d| {
                let (linear, cyclic) = points(d);
                linear.max(cyclic)
            })
            .unwrap_or(1);
        let tw = FIELDS.each_ref().map(|f| f.twiddles(most));
        let spectra = |x: &[u64], n: usize| [0, 1, 2].map(|k| FIELDS[k].spectrum(x, n, &tw[k]));
        let mut levels = Vec::with_capacity(powers.len());
        // The reciprocal `floor(2^e / d)` of the level above, and `e`.
        let mut above = above;
        for d in powers.iter().rev() {
            let (linear, cyclic) = points(d);
            let bits = d.bits();
            let w = bits.next_multiple_of(64);
            let dw = d.to_u64_digits();
            let dc = spectra(&dw, cyclic);
            // `y = 2^2w / (d 2^s)` = `2^(w + n) / d`, floored.
            let y = derive(d, &dw, &dc, &tw, &above.0, above.1);
            let low = (&y - (BigUint::one() << w)).to_u64_digits();
            levels.push(Level {
                y: spectra(&low, linear),
                dc,
                yw: dw.len(),
                d: dw,
                bits,
            });
            above = (y, w + bits);
        }
        levels.reverse();
        Printer { first, levels, tw }
    }

    /// Writes `x < 10^(L 2^level)` to `out`, padded to `L 2^level` digits when `pad`.
    fn write(&self, x: Vec<u64>, level: usize, pad: bool, out: &mut String) {
        if level <= self.first {
            let s = from_words(x).to_string();
            if pad {
                out.extend(std::iter::repeat_n('0', (PRINT_LEAF << level) - s.len()));
            }
            out.push_str(&s);
            return;
        }
        let (high, low) = self.levels[level - 1 - self.first].div_rem(&x, &self.tw);
        drop(x);
        if !pad && high.is_empty() {
            return self.write(low, level - 1, false, out);
        }
        self.write(high, level - 1, pad, out);
        self.write(low, level - 1, true, out);
    }
}

/// `x / 2^n`, floored, as words with no zero on top.
fn shr_words(x: &[u64], n: u64) -> Vec<u64> {
    let (skip, bits) = ((n / 64) as usize, (n % 64) as u32);
    let src = x.get(skip..).unwrap_or(&[]);
    let mut out: Vec<u64> = match bits {
        0 => src.to_vec(),
        _ => src
            .iter()
            .zip(src.iter().skip(1).map(Some).chain([None]))
            .map(|(lo, hi)| (lo >> bits) | hi.map_or(0, |h| h << (64 - bits)))
            .collect(),
    };
    trim(&mut out);
    out
}

/// Drops the zero words on top of `x`.
fn trim(x: &mut Vec<u64>) {
    while x.last() == Some(&0) {
        x.pop();
    }
}

/// `a += b`, `a` growing as needed.
fn add_words(a: &mut Vec<u64>, b: &[u64]) {
    if a.len() < b.len() {
        a.resize(b.len(), 0);
    }
    let mut carry = false;
    for (x, y) in a.iter_mut().zip(b) {
        let (s, c1) = x.overflowing_add(*y);
        let (s, c2) = s.overflowing_add(u64::from(carry));
        *x = s;
        carry = c1 || c2;
    }
    if carry && carry_at(a, b.len()) {
        a.push(1);
    }
}

/// Adds one to `a` at word `i`, the carry carried up; whether it passes the top.
fn carry_at(a: &mut [u64], mut i: usize) -> bool {
    loop {
        if i == a.len() {
            return true;
        }
        let (v, carry) = a[i].overflowing_add(1);
        a[i] = v;
        if !carry {
            return false;
        }
        i += 1;
    }
}

/// `x + 1`, `x` growing as needed.
fn increment(x: &mut Vec<u64>) {
    if carry_at(x, 0) {
        x.push(1);
    }
}

/// `a -= b` for `a.len() >= b.len()`, modulo `2^(64 a.len())`; whether it borrowed past the
/// top, that is whether `a` was below `b`.
fn sub_words(a: &mut [u64], b: &[u64]) -> bool {
    let mut borrow = false;
    for (x, y) in a.iter_mut().zip(b) {
        let (s, b1) = x.overflowing_sub(*y);
        let (s, b2) = s.overflowing_sub(u64::from(borrow));
        *x = s;
        borrow = b1 || b2;
    }
    borrow && (b.len() == a.len() || sub_at(a, b.len(), 1))
}

/// The order of two numbers given as words with no zero on top.
fn cmp_words(a: &[u64], b: &[u64]) -> std::cmp::Ordering {
    a.len()
        .cmp(&b.len())
        .then_with(|| a.iter().rev().cmp(b.iter().rev()))
}

/// `x mod (2^(64 m) - 1)` in `m` words, perhaps `2^(64 m) - 1` itself: the sum of `x`'s
/// pieces of `m` words, `2^(64 m)` being 1.
fn fold_words(x: &[u64], m: usize) -> Vec<u64> {
    let mut out = vec![0u64; m];
    for piece in x.chunks(m) {
        let mut carry = false;
        for (o, v) in out.iter_mut().zip(piece) {
            let (s, c1) = o.overflowing_add(*v);
            let (s, c2) = s.overflowing_add(u64::from(carry));
            *o = s;
            carry = c1 || c2;
        }
        if carry && carry_at(&mut out, piece.len()) {
            add_around(&mut out, 1);
        }
    }
    out
}

/// `x += c 2^0 mod (2^(64 x.len()) - 1)`: what passes the top is added again at the bottom.
fn add_around(x: &mut [u64], mut c: u128) {
    while c != 0 {
        for v in x.iter_mut() {
            if c == 0 {
                return;
            }
            let t = u128::from(*v) + (c & u128::from(u64::MAX));
            *v = t as u64;
            c = (c >> 64) + (t >> 64);
        }
    }
}

/// `prod p^e`, built. A power of 2 is a shift, done last, so `2^e` costs its `e` bits and
/// not the squarings of a multiplication.
pub(super) fn built(pows: &[(u64, BigUint)]) -> BigInt {
    let mut out = BigUint::one();
    let mut twos = None;
    for (p, e) in pows {
        match (p, e.is_zero()) {
            (_, true) => {}
            (2, false) => twos = Some(e),
            _ => {
                let e = e.to_u64().expect("a power whose bits fit in memory");
                out = mul(&out, &pow(&BigUint::from(*p), e));
            }
        }
    }
    if let Some(e) = twos {
        out <<= e.to_u64().expect("a power of 2 whose bits fit in memory");
    }
    BigInt::from(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bezout_coefficients_with_unequal_widths() {
        for (wa, wb) in [
            (1, 45),
            (45, 1),
            (2, 356),
            (356, 2),
            (45, 356),
            (356, 45),
            (45, 45),
        ] {
            let a = random(wa as u64, wa) | BigUint::one();
            let b = random(wb as u64 + 1, wb) | BigUint::one();
            for factor in [BigUint::one(), random(93, 5) | BigUint::one()] {
                for shift in [0, 1, 77] {
                    let a = (&a * &factor) << shift;
                    let b = &b * &factor;
                    for (a, b) in [(&a, &b), (&b, &a)] {
                        let (g, s, t) = bezout(a, b).expect("exact coefficient recovery");
                        assert_eq!(g, a.gcd(b));
                        assert_eq!(
                            &s * BigInt::from(a.clone()) + &t * BigInt::from(b.clone()),
                            BigInt::from(g.clone())
                        );
                        // The identity and the canonical coefficient uniquely determine the answer.
                        let (odd, coefficient) = if a.trailing_zeros() <= b.trailing_zeros() {
                            (a, &t)
                        } else {
                            (b, &s)
                        };
                        assert!(!coefficient.is_negative());
                        assert!(coefficient.magnitude() < &(odd / &g));
                    }
                }
            }
        }
    }

    /// splitmix64 words.
    fn random(seed: u64, words: usize) -> BigUint {
        let mut x = seed;
        let digits: Vec<u32> = (0..2 * words)
            .map(|_| {
                x = x.wrapping_add(0x9e37_79b9_7f4a_7c15);
                let mut z = x;
                z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
                z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
                (z ^ (z >> 31)) as u32
            })
            .collect();
        BigUint::new(digits)
    }

    /// Edge forms of `words` words: all ones, a power of two, one above a power of two, and
    /// random.
    fn forms(words: usize, seed: u64) -> Vec<BigUint> {
        let bits = 64 * words as u64;
        let one = BigUint::one();
        vec![
            (&one << bits) - 1u32,
            &one << (bits - 1),
            (&one << (bits - 1)) + 1u32,
            random(seed, words),
        ]
    }

    #[test]
    fn the_primes_are_primes_with_a_root_of_order_2_to_the_50() {
        for f in &FIELDS {
            assert!(super::super::factor::is_prime(f.p));
            assert_eq!((f.p - 1) % (1 << 50), 0);
            // A quadratic nonresidue: root^((p-1)/2) = -1, so root^((p-1)/2^50) has order 2^50.
            let r = f.pow(f.to_mont(f.root), (f.p - 1) / 2);
            assert_eq!(f.mul(r, 1), f.p - 1);
            assert!(f.p < 1 << 62);
        }
    }

    /// A [`Factor`] keeps its spectra for two or more products above [`MUL_LEAF`] (here 48
    /// words, with num-bigint's Toom-3 never chosen) and none for one, and its products equal
    /// num-bigint's for every width of the other factor up to `other`, edge forms included,
    /// whose all-ones words give the widest carry out of the top; at points just filled
    /// (`words(x) + other - 1` a power of two) and just past one.
    #[test]
    fn factor_products_agree_with_num_bigint() {
        for (wx, other) in [
            (49, 49),
            (64, 65),
            (65, 64),
            (100, 60),
            (200, 57),
            (300, 300),
        ] {
            for x in forms(wx, wx as u64) {
                assert!(
                    Factor::new(x.clone(), other, 1).spectra.is_none(),
                    "{wx}, one use"
                );
                let factor = Factor::new(x.clone(), other, 2);
                assert!(factor.spectra.is_some(), "{wx} by {other} words, two uses");
                for wy in [1, 2, 48, 49, other - 1, other] {
                    for y in forms(wy, 11 + wy as u64) {
                        assert_eq!(factor.mul(&y), &x * &y, "{wx} by {wy} of {other} words");
                    }
                }
                assert!(factor.mul(&BigUint::zero()).is_zero());
            }
        }
    }

    #[test]
    fn products_agree_with_num_bigint() {
        let sizes = [1, 47, 48, 49, 50, 64, 100, 129, 300, 1000, 1500];
        for (i, &la) in sizes.iter().enumerate() {
            for &lb in &sizes[i..] {
                for (x, y) in forms(la, la as u64)
                    .iter()
                    .zip(forms(lb, 7 + lb as u64).iter())
                {
                    assert_eq!(mul(x, y), x * y, "{la} by {lb} words");
                    assert_eq!(mul(y, x), x * y, "{lb} by {la} words");
                }
            }
            for x in forms(la, 3) {
                assert_eq!(mul(&x, &x), &x * &x, "square of {la} words");
            }
        }
        assert!(mul(&BigUint::zero(), &random(1, 100)).is_zero());
        let neg = -BigInt::from(random(2, 80));
        let pos = BigInt::from(random(3, 90));
        assert_eq!(mul_int(&neg, &pos), &neg * &pos);
        assert_eq!(mul_int(&neg, &neg), &neg * &neg);
    }

    /// Numbers of `words` words whose words are each 0, 1, `2^63`, `2^64 - 2` or `2^64 - 1`,
    /// the top one not zero: the cases where a quotient word's estimate is corrected.
    fn edgy(seed: u64, words: usize) -> BigUint {
        let pick = [0u64, 1, 1 << 63, u64::MAX - 1, u64::MAX];
        let mut w: Vec<u64> = random(seed, words)
            .iter_u64_digits()
            .map(|d| pick[(d % 5) as usize])
            .collect();
        w.resize(words, 0);
        w[words - 1] |= 1;
        from_words(w)
    }

    #[test]
    fn rows_and_long_division_over_nonzero_words_agree_with_num_bigint() {
        for &la in &[1usize, 2, 3, 5, 64, 200] {
            for &lb in &[2usize, 3, 4, 65, 130] {
                for seed in 0..20 {
                    let (x, y) = (edgy(seed, la), edgy(seed + 100, lb));
                    assert_eq!(sparse_mul(&x, &y), &x * &y, "{la} by {lb} words");
                    assert_eq!(sparse_div_rem(&x, &y), x.div_rem(&y), "{la} by {lb} words");
                    let z = &x * &y + (&y - 1u32);
                    assert_eq!(sparse_div_rem(&z, &y), (x.clone(), &y - 1u32));
                }
                for (x, y) in forms(la.max(2), 17 + la as u64)
                    .iter()
                    .zip(forms(lb, 19 + lb as u64).iter())
                {
                    assert_eq!(sparse_mul(x, y), x * y, "{la} by {lb} words");
                    let z = x * y + (y - 1u32);
                    assert_eq!(sparse_div_rem(&z, y), (x.clone(), y - 1u32));
                }
            }
        }
        // A sparse divisor reused, as a kept power's remainder uses one.
        let d = (BigUint::one() << 20_000u32) + 1u32;
        let div = Divisor::new(Cow::Borrowed(&d));
        assert!(matches!(div.by, By::Sparse));
        let x = (random(3, 600) % &d) << (64 * 313) | random(4, 313);
        assert_eq!(div.div_rem(&x), x.div_rem(&d));
    }

    #[test]
    fn quotients_agree_with_num_bigint() {
        let sizes = [1, 60, 64, 65, 70, 100, 200, 400, 777];
        for &la in &sizes {
            for &lb in &sizes {
                for (x, y) in forms(la, 11 + la as u64)
                    .iter()
                    .zip(forms(lb, 13 + lb as u64).iter())
                {
                    assert_eq!(div_rem(x, y), x.div_rem(y), "{la} by {lb} words");
                    assert_eq!(rem(x, y), x % y, "{la} by {lb} words, remainder only");
                    let z = x * y + (y - 1u32);
                    assert_eq!(div_rem(&z, y), (x.clone(), y - 1u32), "{la} by {lb} words");
                    let z = x * y;
                    assert_eq!(div_rem(&z, y), (x.clone(), BigUint::zero()));
                }
            }
        }
        // The reciprocal of every precision near a power of two.
        for k in [2049u64, 4096, 4097, 8191, 8192, 8193, 30001] {
            for x in [
                (BigUint::one() << k) - 1u32,
                BigUint::one() << (k - 1),
                random(k, 470) >> (470 * 64 - k) | (BigUint::one() << (k - 1)),
            ] {
                assert_eq!(
                    reciprocal(&x, k),
                    (BigUint::one() << (2 * k)) / &x,
                    "{k} bits"
                );
            }
        }
        // A divisor reused, of bits not a multiple of 64, and dividends up to `d 2^(64 len)`.
        for (bits, seed) in [(4097u64, 41u64), (6000, 43), (8191, 47), (64 * 100, 53)] {
            let d = random(seed, 130) >> (130 * 64 - bits) | (BigUint::one() << (bits - 1));
            let div = Divisor::new(Cow::Borrowed(&d));
            let len = bits.div_ceil(64);
            let top = (&d << (64 * len)) - 1u32;
            for x in [
                top.clone(),
                &top >> 1u32,
                random(seed + 1, 2 * len as usize) % &top,
                d.clone(),
                &d - 1u32,
            ] {
                assert_eq!(div.div_rem(&x), x.div_rem(&d), "{bits} bits");
            }
        }
        let a = -BigInt::from(random(5, 300));
        let m = BigInt::from(random(6, 120));
        for (a, m) in [(&a, &m), (&-&a, &m), (&a, &-&m), (&-&a, &-&m)] {
            assert_eq!(div_euclid(a, m), num_traits::Euclid::div_euclid(a, m));
        }
    }

    /// [`approx_reciprocal`] keeps `a X < 2^2p <= a (X + 2)` for every `a` of 5 to 13 bits,
    /// where the tests' leaf lets Newton's step start, and for edge and random `a` at
    /// precisions next to a word, the production leaf and powers of two.
    #[test]
    fn approximate_reciprocals_keep_their_bounds() {
        let one = BigUint::one();
        let check = |a: &BigUint, p: u64| {
            let tw = roots(cyclic_points(p));
            let x = approx_reciprocal(a, p, &tw);
            let power = &one << (2 * p);
            assert!(a * &x < power, "{p} bits, a = {a}: a X is not below 2^2p");
            assert!(
                a * (&x + 2u32) >= power,
                "{p} bits, a = {a}: a (X + 2) is below 2^2p"
            );
        };
        for p in 5..=13u64 {
            for a in (1u64 << (p - 1))..(1u64 << p) {
                check(&BigUint::from(a), p);
            }
        }
        for p in [
            63u64, 64, 65, 127, 128, 129, 2047, 2048, 2049, 4096, 4097, 8191, 8192, 8193, 30001,
        ] {
            let w = p.div_ceil(64) as usize;
            let top = &one << (p - 1);
            for a in [
                (&one << p) - 1u32,
                (&one << p) - 2u32,
                top.clone(),
                &top + 1u32,
                random(p, w) >> (64 * w as u64 - p) | &top,
                edgy(p, w) >> (64 * w as u64 - p) | &top,
            ] {
                check(&a, p);
            }
        }
    }

    /// [`unfold`] recovers every value from its residue modulo `2^(64 m) - 1` and its low word,
    /// below zero and above, at the ends of its range.
    #[test]
    fn values_unfold_from_their_residues() {
        let one = BigInt::one();
        for m in [1usize, 2, 4] {
            let modulus: BigInt = (&one << (64 * m)) - 1;
            let limit: BigInt = &one << (64 * m + 61);
            let mut values = vec![BigInt::zero(), one.clone(), &modulus - 1, modulus.clone()];
            values.extend([1u64, 3, 64].map(|s| BigInt::from(random(s, m + 1)) % &limit));
            values.extend([&limit - 1, &modulus + 1, &modulus * 7 + 5]);
            for v in values.clone() {
                values.push(-v);
            }
            for v in values {
                let r = v.mod_floor(&modulus).magnitude().to_u64_digits();
                let low = v.mod_floor(&(&one << 64)).to_u64().expect("below 2^64");
                let (negative, words) = unfold(r, m, low);
                let back = BigInt::from_biguint(Sign::Plus, from_words(words));
                assert_eq!(if negative { -back } else { back }, v, "{m} words");
            }
        }
    }

    /// [`Level::div_rem`], the division of [`div_rem`] and [`Divisor`] past their leaves, for
    /// every divisor of 1 to 6 bits, every precision `k` of its reciprocal and every dividend
    /// below `2^(n + k - 1)`, or below `2^2n` and at the top of its range `2^(n + 64)` for
    /// `k = n`.
    #[test]
    fn levels_divide_like_num_bigint_exhaustively() {
        for n in 1..=6u64 {
            for d in (1u64 << (n - 1))..(1u64 << n) {
                let big = BigUint::from(d);
                for k in 1..=n {
                    let (linear, cyclic) = level_points(n, k);
                    let tw = roots(linear.max(cyclic));
                    let level = Level::new(vec![d], n, k, &tw);
                    let mut xs: Vec<BigUint> = match k == n {
                        true => (0..1u64 << (2 * n)).map(BigUint::from).collect(),
                        false => (0..1u64 << (n + k - 1)).map(BigUint::from).collect(),
                    };
                    if k == n {
                        let top = BigUint::one() << (n + 64);
                        xs.extend([&top - 1u32, (&big << 64u32) - 1u32, &top >> 1u32]);
                        xs.extend((0..8).map(|s| random(s, 2) % &top));
                    }
                    for x in xs {
                        let (q, r) = level.div_rem(&x.to_u64_digits(), &tw);
                        assert_eq!(
                            (from_words(q), from_words(r)),
                            x.div_rem(&big),
                            "{x} by {d}, k = {k}"
                        );
                    }
                }
            }
        }
    }

    /// [`div_rem`] and [`Divisor`] next to the powers of two of their transforms' points, for
    /// random, edge and long-carry operands, with quotients as wide as the divisor and
    /// narrower.
    #[test]
    fn wide_quotients_agree_with_num_bigint() {
        for (la, lb) in [
            (130, 65),
            (1023, 512),
            (2048, 1024),
            (2049, 1025),
            (2047, 1024),
            (1500, 1100),
            (3000, 2000),
            (4100, 2050),
        ] {
            for seed in 0..3 {
                let pairs = [
                    (random(seed, la), random(seed + 50, lb)),
                    (edgy(seed, la), edgy(seed + 50, lb)),
                ];
                for (x, y) in pairs.iter().chain(
                    forms(la, seed + 9)
                        .iter()
                        .zip(forms(lb, seed + 10).iter())
                        .map(|(x, y)| (x.clone(), y.clone()))
                        .collect::<Vec<_>>()
                        .iter(),
                ) {
                    assert_eq!(div_rem(x, y), x.div_rem(y), "{la} by {lb} words");
                    assert_eq!(rem(x, y), x % y, "{la} by {lb} words, remainder only");
                    let q = x >> (64 * (la - lb) as u64);
                    let z = &q * y + (y - 1u32);
                    assert_eq!(div_rem(&z, y), (q.clone(), y - 1u32), "{la} by {lb} words");
                    let div = Divisor::new(Cow::Borrowed(y));
                    let top = (y << (64 * lb as u64)) - 1u32;
                    for v in [&top, &(x % &top), &(&q * y)] {
                        assert_eq!(div.div_rem(v), v.div_rem(y), "{la} by {lb} words, reused");
                    }
                }
            }
        }
    }

    /// [`matrix_product`] equals num-bigint's products, by shared transforms (above
    /// `MUL_LEAF`, here 48 words) and one by one: 2x2 by 2x2 and 2x2 by 2x1, signed, with zero
    /// entries, edge words and unbalanced widths, and with a shift, from entries made
    /// divisible by `2^s` and from the half gcd's own matrices, which divide factors wider
    /// than the result, so that factors are folded.
    #[test]
    fn matrix_products_agree_with_num_bigint() {
        SHARED_PRODUCTS.with(|v| v.set((0, 0)));
        let plain = |l: &[BigInt; 4], r: &[BigInt]| -> Vec<BigInt> {
            let c = r.len() / 2;
            (0..2 * c)
                .map(|out| {
                    let (i, j) = (out / c, out % c);
                    &l[2 * i] * &r[j] + &l[2 * i + 1] * &r[c + j]
                })
                .collect()
        };
        let pick = |s: u64, w: usize| -> BigInt {
            let x = match s % 3 {
                0 => random(s, w),
                1 => edgy(s, w),
                _ => forms(w, s)[(s / 3 % 4) as usize].clone(),
            };
            match (s >> 2) & 1 {
                1 => -BigInt::from(x),
                _ => BigInt::from(x),
            }
        };
        for &(wl, wr) in &[
            (49usize, 49usize),
            (64, 64),
            (60, 200),
            (200, 60),
            (50, 700),
            (300, 301),
        ] {
            for seed in 0..6u64 {
                let mut l: [BigInt; 4] = std::array::from_fn(|i| pick(seed * 8 + i as u64, wl));
                let mut r: [BigInt; 4] = std::array::from_fn(|i| pick(seed * 8 + 4 + i as u64, wr));
                if seed == 5 {
                    (l[1], r[2]) = (BigInt::zero(), BigInt::zero());
                }
                let (lr, rr) = (l.each_ref(), r.each_ref());
                assert_eq!(
                    matrix_product(lr, &rr, None),
                    plain(&l, &r),
                    "{wl} by {wr} words"
                );
                for s in [0u64, 1, 63, 64, 1000, 64 * wl as u64 + 5] {
                    let ls = l.each_ref().map(|x| x << s);
                    let got = matrix_product(ls.each_ref(), &[&r[0], &r[1]], Some(s));
                    assert_eq!(got, plain(&l, &r[..2]), "{wl} by {wr} words, shift {s}");
                }
            }
        }
        // The half gcd's matrices, applied to the whole of numbers wider than their residues.
        for (words, seed) in [(120usize, 1u64), (400, 2), (700, 3)] {
            let a = BigInt::from(random(seed, words) | BigUint::one());
            let b = BigInt::from(random(seed + 10, words) << 1u32);
            for k in [64 * words as u64 / 4, 64 * words as u64 / 2] {
                let (j, m) = half(&a, &b, k);
                let [m00, m01, m10, m11] = &m.0;
                let want = (
                    (m00 * &a + m01 * &b) >> (2 * j),
                    (m10 * &a + m11 * &b) >> (2 * j),
                );
                assert_eq!(m.apply(&a, &b, j), want, "{words} words, k = {k}");
            }
        }
        let (shared, folded) = SHARED_PRODUCTS.with(|v| v.get());
        assert!(shared > 0 && folded > 0, "{shared} shared, {folded} folded");
    }

    #[test]
    fn gcds_agree_with_num_bigint() {
        let sizes = [1, 2, 16, 17, 40, 100, 300, 700];
        for &la in &sizes {
            for &lb in &sizes {
                for (x, y) in forms(la, 17 + la as u64)
                    .iter()
                    .zip(forms(lb, 19 + lb as u64).iter())
                {
                    assert_eq!(gcd(x, y), x.gcd(y), "{la} and {lb} words");
                    let g = random(23, 1 + lb / 3);
                    let (gx, gy) = (x * &g, y * &g);
                    assert_eq!(
                        gcd(&gx, &gy),
                        gx.gcd(&gy),
                        "{la} and {lb} words times a common factor"
                    );
                    let (sx, sy) = (&gx << 77u32, &gy << 300u32);
                    assert_eq!(gcd(&sx, &sy), sx.gcd(&sy), "with powers of two");
                }
            }
        }
        let x = random(29, 500);
        assert_eq!(gcd(&x, &BigUint::zero()), x);
        assert_eq!(gcd(&BigUint::zero(), &x), x);
        assert_eq!(gcd(&x, &x), x);
        // Fibonacci neighbours: the longest Euclidean remainder sequence.
        let (mut f, mut g) = (BigUint::one(), BigUint::one());
        for _ in 0..40_000 {
            (f, g) = (g.clone(), f + g);
        }
        assert!(gcd(&f, &g).is_one());
        assert_eq!(gcd(&(&f * 6u32), &(&g * 4u32)), BigUint::from(2u32));
    }

    #[test]
    fn inverses_agree_with_their_definition() {
        // `a x == 1 mod m` when `gcd(a, m) == 1`, and `None` otherwise; moduli odd, even and
        // powers of two, across the leaf width under test (`GCD_LEAF`).
        let check = |a: &BigUint, m: &BigUint, what: &str| match inverse_mod(a, m) {
            Some(x) => {
                assert!(&x < m, "{what}: below the modulus");
                assert!((a * &x % m).is_one() || m.is_one(), "{what}: an inverse");
            }
            None => assert!(!a.gcd(m).is_one(), "{what}: None only for a common factor"),
        };
        let sizes = [1, 2, 16, 17, 40, 100, 300];
        for &la in &sizes {
            for &lb in &sizes {
                for (x, y) in forms(la, 41 + la as u64)
                    .iter()
                    .zip(forms(lb, 43 + lb as u64).iter())
                {
                    check(x, y, &format!("{la} mod {lb} words"));
                    check(
                        x,
                        &(y | BigUint::one()),
                        &format!("{la} mod {lb} words, odd"),
                    );
                    check(
                        &(x | BigUint::one()),
                        &(y << 5u32),
                        &format!("{la} mod {lb}, even"),
                    );
                    let g = random(47, 1 + lb / 3) | BigUint::one();
                    check(
                        &(x * &g),
                        &(y * &g),
                        &format!("{la} and {lb}, common factor"),
                    );
                }
            }
        }
        let m = BigUint::one() << 700u32;
        check(&random(53, 20), &m, "a power of two");
        check(
            &(random(53, 20) | BigUint::one()),
            &m,
            "a power of two, odd",
        );
        check(&BigUint::from(5u32), &BigUint::one(), "modulo 1");
        // Fibonacci neighbours: the longest Euclidean remainder sequence.
        let (mut f, mut g) = (BigUint::one(), BigUint::one());
        for _ in 0..20_000 {
            (f, g) = (g.clone(), f + g);
        }
        check(&f, &g, "Fibonacci neighbours");
        check(&g, &f, "Fibonacci neighbours, swapped");
        check(&(&f << 3u32), &g, "Fibonacci, times 8");
    }

    #[test]
    fn decimals_agree_with_num_bigint() {
        for words in [1, 50, 100, 106, 107, 200, 213, 500, 1000, 3000] {
            for x in forms(words, 31 + words as u64) {
                assert_eq!(to_decimal(&x), x.to_string(), "{words} words");
            }
        }
        // Zeros in the middle and at the end of a half.
        let ten = BigUint::from(10u32);
        for e in [1024u32, 1025, 2048, 4096, 5000] {
            let x = ten.pow(e);
            assert_eq!(to_decimal(&x), x.to_string());
            let y = &x + 1u32;
            assert_eq!(to_decimal(&y), y.to_string());
            let z = &x - 1u32;
            assert_eq!(to_decimal(&z), z.to_string());
            let w = &x * &x + &x;
            assert_eq!(to_decimal(&w), w.to_string());
        }
        assert_eq!(to_decimal(&BigUint::zero()), "0");
        // Each size at and next to a power's words `31 * 2^i`, where the levels change, and
        // the powers `10^(L 2^i)` and their neighbors, where a half is zero or all nines.
        for i in 0..7 {
            for words in [31 << i, (31 << i) - 1, (31 << i) + 1, 62 << i] {
                for seed in 0..3 {
                    let x = random(seed * 1000 + words as u64, words);
                    assert_eq!(to_decimal(&x), x.to_string(), "{words} words");
                }
            }
            let p = ten.pow((PRINT_LEAF as u32) << i);
            for x in [
                &p - 1u32,
                p.clone(),
                &p + 1u32,
                &p * &p - 1u32,
                &p * &p + &p - 1u32,
            ] {
                assert_eq!(
                    to_decimal(&x),
                    x.to_string(),
                    "10^({PRINT_LEAF} 2^{i}) nearby"
                );
            }
        }
    }

    /// [`derive()`] from the reciprocal of `d^2` and from it plus 1 to 4 (with 3 more bits),
    /// against the reciprocal of `d` by num-bigint's division, for powers of ten and random `d`.
    #[test]
    fn derived_reciprocals_agree_with_division() {
        let ten = BigUint::from(10u32);
        let one = BigUint::one();
        let mut ds: Vec<BigUint> = (0..5).map(|i| ten.pow((PRINT_LEAF as u32) << i)).collect();
        ds.extend([3, 31, 32, 100, 500].map(|w| random(w as u64, w) | &one));
        for d in &ds {
            let n = d.bits();
            let w = n.next_multiple_of(64);
            let dw = d.to_u64_digits();
            let mut m = dw.len().next_power_of_two();
            if n + 2 > 64 * m as u64 {
                m *= 2;
            }
            let tw = FIELDS.each_ref().map(|f| f.twiddles(m));
            let dc = [0, 1, 2].map(|k| FIELDS[k].spectrum(&dw, m, &tw[k]));
            let want = (&one << (w + n)) / d;
            let square = d * d;
            let ea = w + 2 * n;
            let exact = (&one << ea) / &square;
            assert_eq!(
                derive(d, &dw, &dc, &tw, &exact, ea),
                want,
                "{n} bits, exact"
            );
            let above = (&one << (ea + 3)) / &square;
            for e in 0..=4u32 {
                let ya = &above + e;
                assert_eq!(
                    derive(d, &dw, &dc, &tw, &ya, ea + 3),
                    want,
                    "{n} bits, +{e}"
                );
            }
        }
    }
    #[test]
    fn r5_binary_leaf_random_and_adversarial_pairs() {
        use num_integer::Integer;
        let mut checked = 0;
        for words in [3, 4, 5, 16, 31, 64, 127, 256, 511] {
            for seed in 1..=20 {
                let x = random(seed, words) | BigUint::one();
                let y = random(seed + 999, words) | BigUint::one();
                for (a, b) in [
                    (x.clone(), y),
                    (x.clone(), x.clone()),
                    (x.clone(), &x + 2u32),
                    (x.clone(), &x - 2u32),
                    (x.clone(), &x + (BigUint::one() << 20u32)),
                    (x.clone(), &x + (BigUint::one() << 30u32)),
                    (x.clone(), &x + (BigUint::one() << 31u32)),
                    (x.clone(), &x << 129u32),
                    (&x * 35u32, (&x + 2u32) * 35u32),
                    ((BigUint::one() << (64 * words)) - 1u32, x.clone()),
                ] {
                    let want = a.gcd(&b);
                    assert_eq!(gcd(&a, &b), want, "words={words}, seed={seed}");
                    assert_eq!(gcd(&b, &a), want, "reversed words={words}, seed={seed}");
                    checked += 2;
                }
            }
        }
        eprintln!("R5 gcd independent comparisons={checked}");
    }
    #[test]
    fn binary_leaf_exercises_both_sides_of_the_register_shift_bound() {
        use num_integer::Integer;
        let x = (BigUint::one() << 256usize) + 1u32;
        for shift in [30usize, 31] {
            STEIN_ACCEPTED_SHIFT.with(|v| v.set(0));
            STEIN_REJECTED_SHIFT.with(|v| v.set(0));
            let y = &x + (BigUint::one() << shift);
            assert_eq!(stein_odd(&x, 0, &y, 0), x.gcd(&y));
            let accepted = STEIN_ACCEPTED_SHIFT.with(|v| v.get());
            let rejected = STEIN_REJECTED_SHIFT.with(|v| v.get());
            assert!(accepted <= 30);
            if shift == 30 {
                assert_eq!(accepted, 30);
            } else {
                assert!(rejected >= 31);
            }
            eprintln!("gcd boundary shift={shift}, accepted={accepted}, rejected={rejected}");
        }
    }

    /// Plain extended Euclid on nonnegative numbers: `(g, s, t)` with `s a + t b = g`.
    fn euclid(a: &BigUint, b: &BigUint) -> (BigUint, BigInt, BigInt) {
        let (mut r0, mut r1) = (BigInt::from(a.clone()), BigInt::from(b.clone()));
        let (mut s0, mut s1) = (BigInt::one(), BigInt::zero());
        let (mut t0, mut t1) = (BigInt::zero(), BigInt::one());
        while !r1.is_zero() {
            let q = &r0 / &r1;
            let r2 = &r0 - &q * &r1;
            let s2 = &s0 - &q * &s1;
            let t2 = &t0 - &q * &t1;
            r0 = std::mem::replace(&mut r1, r2);
            s0 = std::mem::replace(&mut s1, s2);
            t0 = std::mem::replace(&mut t1, t2);
        }
        (r0.into_parts().1, s0, t0)
    }

    /// [`step`] with `b = 2^j b'` for `j` on both sides of 127, where `q` is found in 128-bit
    /// registers below and from `b'^-1 mod 2^(j+1)` of `j + 1` bits from there on: `q` is
    /// centered, `|q| < 2^j`, `a + q b'` is a multiple of `2^(j+1)`, and the new second number
    /// is `(a + q b') / 2^j`; for odd `a` of either sign and of fewer or more bits than
    /// `2^(j+1)`.
    #[test]
    fn a_step_of_127_halvings_or_more_meets_its_definition() {
        for j in [126u64, 127, 128, 191, 200, 1000] {
            let words = j as usize / 64 + 2;
            for seed in 1..=4 {
                let b1 = BigInt::from(random(seed, words) | BigUint::one());
                let b = &b1 << j;
                let narrow = BigInt::from(random(seed + 50, 1) | BigUint::one());
                let wide = BigInt::from(random(seed + 90, 2 * words) | BigUint::one());
                for a in [
                    BigInt::one(),
                    -BigInt::one(),
                    narrow.clone(),
                    -narrow,
                    wide.clone(),
                    -wide,
                ] {
                    let (q, b1_out, r) = step(&a, &b, j);
                    assert_eq!(b1_out, b1, "j={j}, seed={seed}");
                    assert!(q.magnitude() < &(BigUint::one() << j), "j={j}, seed={seed}");
                    let sum = &a + mul_int(&q, &b1);
                    assert!(
                        sum.trailing_zeros().is_none_or(|z| z > j),
                        "j={j}, seed={seed}: a + q b' is not a multiple of 2^(j+1)"
                    );
                    assert_eq!(r << j, sum, "j={j}, seed={seed}");
                }
            }
        }
    }

    /// [`bezout`] of an odd number and `2^j` times an odd number, `j` from 126 to 4097, in
    /// both orders and with a common power of two, and with odd parts of 1 to 40 words, all
    /// ones among them: a valuation of 127 or more reaches the step whose `q` is found from
    /// an inverse of `j + 1` bits. The gcd is that of plain extended Euclid, and the
    /// coefficients satisfy `s a + t b = g`.
    #[test]
    fn bezout_of_a_number_with_127_or_more_factors_of_two_matches_euclid() {
        let all_ones = |words: usize| (BigUint::one() << (64 * words)) - 1u32;
        for j in [126u64, 127, 128, 129, 200, 255, 256, 1000, 4097] {
            for seed in 1..=3 {
                for (wa, wb) in [(1, 1), (1, 4), (4, 1), (40, 3), (3, 40)] {
                    let odd_a = random(seed, wa) | BigUint::one();
                    let odd_b = random(seed + 30, wb) | BigUint::one();
                    let wide = &odd_b << j;
                    let shared = &odd_a * 3u32 * 5u32 * 7u32;
                    for (a, b) in [
                        (odd_a.clone(), wide.clone()),
                        (wide.clone(), odd_a.clone()),
                        (&odd_a << 5u32, &wide << 5u32),
                        (all_ones(wa), wide.clone()),
                        (shared.clone(), &odd_a << j),
                        (&odd_a << j, shared),
                    ] {
                        let at = format!("j={j}, seed={seed}, words=({wa}, {wb})");
                        let (g, s, t) = bezout(&a, &b).expect("bezout answers");
                        let (want, es, et) = euclid(&a, &b);
                        let (ia, ib) = (BigInt::from(a), BigInt::from(b));
                        let want_int = BigInt::from(want.clone());
                        assert_eq!(&es * &ia + &et * &ib, want_int, "Euclid, {at}");
                        assert_eq!(g, want, "{at}");
                        assert_eq!(mul_int(&s, &ia) + mul_int(&t, &ib), want_int, "{at}");
                    }
                }
            }
        }
    }
}
