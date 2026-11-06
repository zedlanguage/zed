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
//! ([`sparse_mul`]); [`mul`] takes whichever of the two computed costs ([`transform_plan`]) is
//! lower, with no size constant, and num-bigint's Toom-3 at or below [`MUL_LEAF`].
//!
//! **Division** ([`div_rem`], [`reciprocal`], [`settle`]). To divide by `b` of `k` bits, find
//! `y = floor(2^2k / b)`, then `q = floor(a y / 2^2k)`: two products. `y` comes from Newton's
//! iteration `y' = 2 y - b y^2 / 2^2k`, which doubles the correct bits: it starts from a
//! reciprocal of a few words (num-bigint's division, at or below [`RECIP_LEAF`]) and doubles
//! the precision each round, `k / 2^i`, ..., `k / 2`, `k`, so the total is `M(k) + M(k/2) + ...`
//! = O(M(k)). Each estimate is at most a few units off, and [`settle`] makes it exact by
//! computing `q b`, comparing with `a` and moving `q` by one or two. When the quotient has `k`
//! bits and the divisor more, both operands are first shifted down until the divisor has `k`
//! bits, so the reciprocal and both products are of `k` bits, not the divisor's width; the
//! quotient of the shifted operands is at most two above the true one. A quotient wider than the divisor is found in blocks of the
//! divisor's width ([`div_rem_blocks`]) with one reciprocal ([`Divisor`]) reused for every
//! block. A divisor with few nonzero words is divided by long division over those words
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
//! **Printing** ([`to_decimal`], [`write_decimal`]). The powers `10^(L 2^i)`, `L` being
//! [`PRINT_LEAF`], are built once by squaring, each with its reciprocal ([`Divisor`]). `x` is
//! written as `high 10^(L 2^i) + low` by one division by the largest power at most `x`, and
//! each half is printed by the next power down, the low half padded with zeros to its fixed
//! width. Each level divides numbers of `n` bits in total, O(M(n)), over `log2(n / L)` levels:
//! O(M(n) log n). The leaves are printed by num-bigint.
//!
//! **Where the constants lose** (measured 2026-11-06, COMPLEXITY.md section "Crossovers"). A
//! transform product costs three convolutions and the recombination, so num-bigint's Toom-3 is
//! faster up to about 4096 words. Newton division costs several full products per quotient,
//! and is slower than num-bigint's Burnikel and Ziegler division at every size measured, up to
//! 8192 words; printing, which divides at each level, is slower from about 1024 to 131072
//! words. The gcd gains from about 300 words, since num-bigint's is quadratic. Open for the
//! port: why division costs 2.6 to 3.8 times num-bigint's from 2048 to 8192 words (candidates:
//! the full product `a2 y` of which only the high half is used, the product `q b` in
//! [`settle`], a reciprocal built at each call), and whether printing's excess is division's.
//!
//! **At the port to Zed.** The results must stay those of num-bigint's operations, which the
//! unit tests compare at every leaf setting. What depends on measurement and is to be measured
//! again on the Zed code: the leaves [`MUL_LEAF`], [`DIV_LEAF`], [`RECIP_LEAF`], [`GCD_LEAF`],
//! [`PRINT_LEAF`] and the cost constants [`TRANSFORM_COST`], [`SPARSE_WORD`], [`SPARSE_STEP`].
//! [`HALF_LEAF`] is derived, not measured. The Rust constructs that need a Zed form are listed
//! in ZED_PORT_GAPS.md, section "Entries from NUM-subquad".
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

use num_bigint::{BigInt, BigUint, Sign};
use num_integer::Integer;
use num_traits::{One, Signed, Zero};

/// The 64-bit words at or below which the narrower factor goes to num-bigint's
/// multiplication: the crossover measured on 2026-11-05, both about 0.33 ms at 1024 words
/// (load 68). Measured again on 2026-11-06 at load 1, the transform takes 1.50 times
/// num-bigint's time at 1024 words, 1.18 at 2048, 0.96 at 4096 and 0.56 at 16384, so the
/// curves cross near 4096 words (COMPLEXITY.md, "Crossovers"). The product does not depend on
/// it; the unit tests use a smaller leaf, so that they reach the transforms at small sizes.
#[cfg(not(test))]
const MUL_LEAF: usize = 1024;
#[cfg(test)]
const MUL_LEAF: usize = 48;

/// The bits at or below which the divisor, or the quotient, goes to num-bigint's division,
/// which then costs at most this many bits times the dividend's. The result does not depend
/// on it. Not measured when it was set. On 2026-11-06 at load 1, Newton division of `2w` by
/// `w` words takes 1.13 times num-bigint's time at `w` = 64, 1.00 at 96, 2.03 at 1024, 3.84
/// at 2048 and 2.60 at 8192: never faster up to 8192 words. num-bigint's division is about
/// `n^1.46` and Newton's O(n log n), so the curves cross higher up, above 100,000 words by
/// extrapolation, not measured (COMPLEXITY.md, "Crossovers").
const DIV_LEAF: u64 = 64 * 64;

/// The bits at or below which a reciprocal is found by num-bigint's division. Not measured
/// apart from [`DIV_LEAF`].
const RECIP_LEAF: u64 = 64 * 32;

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

/// The decimal digits of a leaf of [`to_decimal`], written by num-bigint. Not a crossover
/// with num-bigint's printing of the whole number: on 2026-11-06 at load 1 printing by halves
/// takes 0.93 times num-bigint's time at 256 words, 1.46 at 4096, 1.74 at 16384, 1.27 at
/// 65536 and 0.96 at 131072, so num-bigint's is faster from about 1024 to 131072 words. The
/// slower range matches that of [`div_rem`], which each level divides by; that this is the
/// cause is not yet measured (COMPLEXITY.md, "Crossovers").
const PRINT_LEAF: usize = 1024;

/// The cost of a transform product on `n` points, per `n log2(n)`, in units of one word
/// product of [`sparse_mul`]: measured on 2026-11-05 at 1024 to 8192 words a factor, 23 to
/// 28 ns per `n log2(n)` against 1.2 to 2 ns a word product (load 45 to 55). Only which of
/// two equal results is computed depends on it. Measured again at the port to Zed, with the
/// leaves above.
const TRANSFORM_COST: u128 = 20;

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
        if u >= self.p { u - self.p } else { u }
    }

    #[inline]
    fn add(&self, a: u64, b: u64) -> u64 {
        let s = a + b;
        if s >= self.p { s - self.p } else { s }
    }

    #[inline]
    fn sub(&self, a: u64, b: u64) -> u64 {
        if a >= b { a - b } else { a + self.p - b }
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

    /// The powers `w^j`, `j < n/2`, of a primitive `n`-th root `w`, each with its Shoup
    /// quotient (see [`Field::shoup`]). The stage of half-width `h` uses the `2h`-th root
    /// `w^(n/2h)`, so it reads every `n/2h`-th entry: one table of `n/2` pairs serves every
    /// stage, which keeps a product's memory at five words a point (see [`mul`]).
    fn twiddles(&self, n: usize) -> Vec<(u64, u64)> {
        // A primitive n-th root: the generator to the power (p - 1) / n.
        let w = self.pow(self.to_mont(self.root), (self.p - 1) / n as u64);
        let mut tw = vec![(0, 0); n / 2];
        // `mul(t, w)` of `t` in plain form and `w` in Montgomery form is `t w` in plain form.
        let mut t = 1;
        for x in &mut tw {
            *x = (t, ((u128::from(t) << 64) / u128::from(self.p)) as u64);
            t = self.mul(t, w);
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
    /// powers of a primitive `a.len()`-th root, in bit-reversed order (decimation in
    /// frequency), with `tw` from [`Field::twiddles`]. Values below `p` go in, and values
    /// below `2p` come out, the same residues (Harvey's lazy reduction; `4p < 2^64`).
    fn forward(&self, a: &mut [u64], tw: &[(u64, u64)]) {
        let p2 = 2 * self.p;
        let mut half = a.len() / 2;
        while half >= 1 {
            let stride = a.len() / (2 * half);
            for block in a.chunks_exact_mut(2 * half) {
                let (lo, hi) = block.split_at_mut(half);
                let roots = tw.iter().step_by(stride);
                for ((x, y), w) in lo.iter_mut().zip(hi.iter_mut()).zip(roots) {
                    let (u, v) = (*x, *y);
                    let s = u + v;
                    *x = if s >= p2 { s - p2 } else { s };
                    *y = self.shoup(u + p2 - v, *w);
                }
            }
            half /= 2;
        }
    }

    /// The inverse of [`Field::forward`] times `a.len()`, from bit-reversed order to natural
    /// order (decimation in time), by the inverse roots `w_2h^-j = p - w_2h^(h - j)`, whose
    /// Shoup quotient is the complement of the other's. Values below `2p` go in, and values
    /// below `p` come out.
    fn inverse(&self, a: &mut [u64], tw: &[(u64, u64)]) {
        let p2 = 2 * self.p;
        let butterfly = |x: &mut u64, y: &mut u64, v: u64| {
            let u = *x;
            let s = u + v;
            let d = u + p2 - v;
            *x = if s >= p2 { s - p2 } else { s };
            *y = if d >= p2 { d - p2 } else { d };
        };
        let n = a.len();
        let mut half = 1;
        while half < n {
            let stride = n / (2 * half);
            for block in a.chunks_exact_mut(2 * half) {
                let (lo, hi) = block.split_at_mut(half);
                let v = hi[0];
                butterfly(&mut lo[0], &mut hi[0], v);
                for ((x, y), (w, s)) in lo[1..]
                    .iter_mut()
                    .zip(hi[1..].iter_mut())
                    .zip(tw[stride..half * stride].iter().step_by(stride).rev())
                {
                    let v = self.shoup(*y, (self.p - w, !s));
                    butterfly(x, y, v);
                }
            }
            half *= 2;
        }
        for x in a.iter_mut() {
            if *x >= self.p {
                *x -= self.p;
            }
        }
    }

    /// The cyclic convolution of `a` and `b` modulo `p` on `n` points, each coefficient
    /// reduced below `p`; `b` is `None` for a square.
    fn convolve(&self, a: &BigUint, b: Option<&BigUint>, n: usize) -> Vec<u64> {
        let tw = self.twiddles(n);
        // One word more than the points, for the product's top word (see [`mul`]).
        let load = |x: &BigUint| {
            let mut v: Vec<u64> = Vec::with_capacity(n + 1);
            v.extend(x.iter_u64_digits().map(|d| d % self.p));
            v.resize(n, 0);
            self.forward(&mut v, &tw);
            v
        };
        let mut fa = load(a);
        // The pointwise product is `a b / 2^64`; the inverse multiplies by `n`; the scale
        // `2^128 / n`, in Montgomery form, undoes both.
        let n_inv = self.p - (self.p - 1) / n as u64;
        let scale = self.to_mont(self.to_mont(n_inv));
        match b {
            Some(b) => {
                let fb = load(b);
                for (x, y) in fa.iter_mut().zip(&fb) {
                    *x = self.mul(self.mul(*x, *y), scale);
                }
            }
            None => {
                for x in fa.iter_mut() {
                    *x = self.mul(self.mul(*x, *x), scale);
                }
            }
        }
        self.inverse(&mut fa, &tw);
        fa
    }
}

/// Three primes `c * 2^50 + 1` with a generator each; their product exceeds `2^185`, above
/// every coefficient of a product of `2^50` words, `2^50 * 2^128`.
const FIELDS: [Field; 3] = [
    Field::new(4_601_552_919_265_804_289, 3),
    Field::new(4_546_383_823_830_515_713, 10),
    Field::new(4_522_739_925_786_820_609, 37),
];

/// The cost of a product by transforms whose coefficients number `coeffs`, in units of one
/// word product of [`sparse_mul`]: `TRANSFORM_COST n log2(n)` for `n` points, the constant
/// measured on 2026-11-05 (see [`TRANSFORM_COST`]).
fn transform_cost(coeffs: usize) -> u128 {
    let n = coeffs.next_power_of_two() as u128;
    TRANSFORM_COST * n * u128::from(n.trailing_zeros().max(1))
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

/// `a * b`, by num-bigint when the narrower has at most [`MUL_LEAF`] words, else by rows over
/// the nonzero words of one factor ([`sparse_mul`]) or by transforms modulo three primes
/// joined by the Chinese remainder theorem, O(n log n), whichever costs less.
pub(crate) fn mul(a: &BigUint, b: &BigUint) -> BigUint {
    let (la, lb) = (words(a), words(b));
    if la.min(lb) <= MUL_LEAF {
        return a * b;
    }
    // Complexity tradeoff: rows over the nonzero words cost `nonzero(a) words(b)` word
    // products, below the transforms' O(n log n) when a factor has few nonzero words, as a
    // kept power `2^s + 1` has; the cheaper of the two computed costs is taken, from the
    // operands' counts and the measured `TRANSFORM_COST`, with no size constant, and both give
    // the same product. A dense factor costs O(n) more for the count. Tested by
    // `a_sparse_product_scales` and `products_agree_with_num_bigint` (COMPLEXITY.md K30).
    let rows = (nonzero_words(a) as u128 * lb as u128).min(nonzero_words(b) as u128 * la as u128);
    let (short, long) = match la <= lb {
        true => (a, b),
        false => (b, a),
    };
    let (cost, piece) = transform_plan(la.min(lb), la.max(lb));
    if rows <= cost {
        return sparse_mul(a, b);
    }
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
    // last carry.
    let coeffs = la + lb - 1;
    let n = coeffs.next_power_of_two();
    assert!(n <= 1 << 50, "a product of at most 2^50 words");
    let square = std::ptr::eq(a, b) || a == b;
    let other = (!square).then_some(b);
    let [f0, f1, f2] = &FIELDS;
    // Each residue vector is cut to its coefficients before the next is computed, so the
    // peak, during the last transform, is two vectors of `coeffs` words and three of `n`.
    let mut r0 = f0.convolve(a, other, n);
    r0.truncate(coeffs);
    r0.shrink_to(coeffs + 1);
    let mut r1 = f1.convolve(a, other, n);
    r1.truncate(coeffs);
    r1.shrink_to_fit();
    let r2 = f2.convolve(a, other, n);
    // Garner's form: c = v0 + v1 p0 + v2 p0 p1, each `v_i < p_i`.
    let inv01 = f1.to_mont(inv_mod(f0.p % f1.p, f1.p));
    let p01 = u128::from(f0.p) * u128::from(f1.p);
    let inv012 = f2.to_mont(inv_mod((p01 % u128::from(f2.p)) as u64, f2.p));
    let p0_in_2 = f2.to_mont(f0.p % f2.p);
    let (p01_lo, p01_hi) = (p01 as u64, (p01 >> 64) as u64);
    // The coefficients are written over `r0` as the product's words: coefficient `i` is read
    // before word `i` is written.
    let mut carry = 0u128;
    for i in 0..coeffs {
        let v0 = r0[i];
        let v1 = f1.mul(f1.sub(r1[i], v0 % f1.p), inv01);
        let low = f2.add(v0 % f2.p, f2.mul(v1, p0_in_2));
        let v2 = f2.mul(f2.sub(r2[i], low), inv012);
        // c = s + v2 p01_lo + v2 p01_hi 2^64, with s = v0 + v1 p0 < 2^125.
        let s = u128::from(v0) + u128::from(v1) * u128::from(f0.p);
        let s = s + u128::from(v2) * u128::from(p01_lo);
        let hi = (s >> 64) + u128::from(v2) * u128::from(p01_hi);
        let t = u128::from(s as u64) + (carry & u128::from(u64::MAX));
        r0[i] = t as u64;
        carry = hi + (carry >> 64) + (t >> 64);
    }
    debug_assert!(
        carry >> 64 == 0,
        "the product fits in the words of both factors"
    );
    drop((r1, r2));
    // Within the capacity `coeffs + 1` kept above.
    r0.push(carry as u64);
    from_words(r0)
}

/// The number whose 64-bit words, lowest first, are `w`.
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
fn inv_mod(x: u64, p: u64) -> u64 {
    let (mut b, mut e, mut r) = (u128::from(x), p - 2, 1u128);
    let p = u128::from(p);
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
pub(crate) fn mul_int(a: &BigInt, b: &BigInt) -> BigInt {
    BigInt::from_biguint(a.sign() * b.sign(), mul(a.magnitude(), b.magnitude()))
}

/// `b^e`, by squaring with [`mul`].
pub(crate) fn pow(mut b: BigUint, mut e: u64) -> BigUint {
    let mut r = BigUint::one();
    while e > 0 {
        if e & 1 == 1 {
            r = mul(&r, &b);
        }
        e >>= 1;
        if e > 0 {
            b = mul(&b, &b);
        }
    }
    r
}

// ------------------------------------------------------------------------------------------
// Division

/// `(a / b, a mod b)` for `b` not zero. A narrow divisor or quotient goes to num-bigint, and a
/// quotient wider than the divisor goes block by block ([`div_rem_blocks`]). Otherwise the
/// divisor is cut to the quotient's `k` bits, the quotient is the cut dividend times the
/// reciprocal `2^2k / b`, at most two off, and the remainder corrects it. O(M(n)).
pub(crate) fn div_rem(a: &BigUint, b: &BigUint) -> (BigUint, BigUint) {
    assert!(!b.is_zero(), "a division by zero");
    if a < b {
        return (BigUint::zero(), a.clone());
    }
    let (m, n) = (a.bits(), b.bits());
    // The quotient has at most `k` bits.
    let k = m - n + 1;
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
    // `a2` has `2k - 1` bits and `b2` has `k`: the divisor's low bits are dropped, and
    // `a2 / b2` is at most two above `a / b`.
    let (a2, b2) = (a >> (n - k), b >> (n - k));
    let y = reciprocal(&b2, k);
    drop(b2);
    // `a2 / b2 - a2 y / 2^2k < a2 / 2^2k < 1/2`, so `q` is `a / b` or up to one below and two
    // above it.
    let q = mul(&a2, &y) >> (2 * k);
    drop((a2, y));
    let qb = mul(&q, b);
    settle(a, b, q, qb)
}

/// [`div_rem`] of a quotient wider than the divisor `b`: `a` is read from the top in blocks of
/// as many words as `b` has, each step dividing the remainder so far joined to the next block,
/// below `b 2^(64 len)`, by `b` through one [`Divisor`], and the quotient's blocks are written
/// into place. O((m / n) M(n)) for `m` bits by `n`, and the memory of a step is O(n).
fn div_rem_blocks(a: &BigUint, b: &BigUint) -> (BigUint, BigUint) {
    let divisor = Divisor::new(Cow::Borrowed(b));
    let len = words(b);
    let mut digits = a.iter_u64_digits().rev();
    let mut left = digits.len();
    let mut quotient = vec![0u32; 2 * left];
    let mut take = match left % len {
        0 => len,
        k => k,
    };
    let mut r = BigUint::zero();
    let mut block: Vec<u32> = Vec::with_capacity(2 * len);
    while left > 0 {
        block.clear();
        for d in digits.by_ref().take(take) {
            // Highest word first, so reversing the block gives the low half-word first.
            block.extend([(d >> 32) as u32, d as u32]);
        }
        block.reverse();
        let (q, rest) = divisor.div_rem(&((r << (64 * take)) + BigUint::from_slice(&block)));
        left -= take;
        for (slot, d) in quotient[2 * left..].iter_mut().zip(q.iter_u32_digits()) {
            *slot = d;
        }
        r = rest;
        take = len;
    }
    (BigUint::new(quotient), r)
}

/// The cost of [`sparse_div_rem`] of a quotient of `qw` words by a divisor with `nonzero`
/// nonzero words.
fn sparse_div_cost(qw: usize, nonzero: usize) -> u128 {
    (qw as u128 + 1) * (SPARSE_WORD * nonzero as u128 + SPARSE_STEP)
}

/// The cost of [`div_rem`] by a reciprocal of a quotient of `qw` words by a divisor of `bw`:
/// about five products of the quotient's width for the reciprocal and the quotient, and one
/// of the quotient by the divisor, or that of each block of [`div_rem_blocks`].
fn newton_cost(qw: usize, bw: usize) -> u128 {
    match qw > bw {
        true => (qw.div_ceil(bw) as u128 + 2) * 2 * transform_cost(2 * bw),
        false => 5 * transform_cost(2 * qw) + transform_cost(qw + bw),
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
    let mut shifted = a
        .iter_u64_digits()
        .rev()
        .chain(std::iter::once(0))
        .map(|d| {
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
    let mut quotient: Vec<u64> = Vec::with_capacity(words(a) + 2 - lb);
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
    buf.truncate(start + lb);
    buf.drain(..start);
    let r = from_words(buf) >> sh;
    (from_words(quotient), r)
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

/// `2^2k / x`, floored, for `x` of exactly `k` bits, by Newton's iteration from the top bits:
/// each precision `k'` comes from about half as many, `h = ceil(k'/2) + 2`, as
/// `y' = 2 y 2^(k'-h) - x' y^2 / 2^2h` with `x'` the top `k'` bits of `x`, then made exact by
/// its remainder. The relative error of `y` is about `2^-h`, so `y'` is a few off. O(M(k)).
fn reciprocal(x: &BigUint, k: u64) -> BigUint {
    debug_assert_eq!(x.bits(), k);
    let mut sizes = vec![k];
    while let Some(&s) = sizes.last().filter(|&&s| s > RECIP_LEAF) {
        sizes.push(s.div_ceil(2) + 2);
    }
    let mut h = sizes.pop().expect("k is listed");
    let mut y = (BigUint::one() << (2 * h)) / (x >> (k - h));
    while let Some(kp) = sizes.pop() {
        let xp = x >> (k - kp);
        let t = mul(&xp, &mul(&y, &y)) >> (2 * h);
        // `x' y^2 2^(2(k'-h)) / 2^2k' < 2 y 2^(k'-h)`, since `y <= 2^2h / x_h` and the top `h`
        // bits `x_h` of `x'` are at least `x' / 2^(k'-h) - 1`.
        let estimate = (y << (kp - h + 1)) - t;
        let product = mul(&xp, &estimate);
        let (q, _) = settle(&(BigUint::one() << (2 * kp)), &xp, estimate, product);
        y = q;
        h = kp;
    }
    y
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
        Mat([
            mul_int(a, e) + mul_int(b, g),
            mul_int(a, f) + mul_int(b, h),
            mul_int(c, e) + mul_int(d, g),
            mul_int(c, f) + mul_int(d, h),
        ])
    }

    /// `self * (a, b) / 2^2j`, exact.
    fn apply(&self, a: &BigInt, b: &BigInt, j: u64) -> (BigInt, BigInt) {
        let [m00, m01, m10, m11] = &self.0;
        let c = (mul_int(m00, a) + mul_int(m01, b)) >> (2 * j);
        let d = (mul_int(m10, a) + mul_int(m11, b)) >> (2 * j);
        (c, d)
    }
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
    // The residues modulo `2^w`, not negative (`&` reads a negative number in two's
    // complement).
    let mask = (BigInt::one() << w) - 1;
    let inv = BigInt::from(inverse_mod_pow2((&b1 & &mask).magnitude(), w));
    let q = cmod(&-mul_int(&(a & &mask), &inv), w);
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
        let mut d = x.iter_u64_digits();
        let lo = u128::from(d.next().unwrap_or(0)) | (u128::from(d.next().unwrap_or(0)) << 64);
        let v = match x.is_negative() {
            true => lo.wrapping_neg(),
            false => lo,
        };
        let r = v & ((1u128 << w) - 1);
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
        // `y1^-1 mod 2^64` by Newton, then `q = -x / y1 mod 2^(v+1)`, centered.
        let mut inv = 1u64;
        for _ in 0..6 {
            inv = inv.wrapping_mul(2u64.wrapping_sub((y1 as u64).wrapping_mul(inv)));
        }
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

/// The greatest common divisor of `a` and `b`. The powers of 2 are taken out first; the odd
/// parts then go through the binary gcd, half of what is left at a time by [`half`], whose
/// steps keep the odd part of the gcd. O(M(n) log n).
pub(crate) fn gcd(a: &BigUint, b: &BigUint) -> BigUint {
    let (Some(za), Some(zb)) = (a.trailing_zeros(), b.trailing_zeros()) else {
        return a | b;
    };
    let mut x = BigInt::from(a >> za);
    let mut y = BigInt::from(b >> zb) - &x;
    // Complexity tradeoff: the half gcd costs O(M(n) log n) = O(n log^2 n), a log factor above
    // a product, accepted for NUM-subquad; num-bigint's Stein gcd below `GCD_LEAF` is O(n^2) in
    // a leaf of bounded width. Measured on 2026-11-06: 1.8 s at 32768 words, 11.0 s at 131072;
    // num-bigint's gcd is faster below about 300 words at load 1 (2026-11-06), 512 to 1024 at
    // load 45 to 75 (2026-11-05); see `GCD_LEAF`. Test
    // `a_gcd_of_wide_numbers_scales`.
    while !y.is_zero() {
        let n = x.bits().max(y.bits());
        if n <= GCD_LEAF {
            x = BigInt::from(x.magnitude().gcd(y.magnitude()));
            break;
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
    x.magnitude() << za.min(zb)
}

// ------------------------------------------------------------------------------------------
// Decimal printing

/// A divisor used many times, with how it is divided by: num-bigint's division when it has at
/// most [`DIV_LEAF`] bits, long division over its nonzero words when that costs less, else
/// its reciprocal, built once: the shift `s` that makes `d 2^s` a whole number of words, `w`
/// bits, and `y = 2^2w / (d 2^s)`.
pub(crate) struct Divisor<'a> {
    d: Cow<'a, BigUint>,
    by: By,
}

enum By {
    Leaf,
    Sparse,
    Reciprocal(u64, BigUint),
}

impl<'a> Divisor<'a> {
    pub(crate) fn new(d: Cow<'a, BigUint>) -> Divisor<'a> {
        assert!(!d.is_zero(), "a division by zero");
        let n = d.bits();
        let len = words(&d);
        // Complexity tradeoff: as in `div_rem`, the cheaper of long division over the nonzero
        // words and the reciprocal, for a dividend of twice the divisor's words, by the
        // computed costs and with no size constant (COMPLEXITY.md K30).
        let by = if n <= DIV_LEAF {
            By::Leaf
        } else if sparse_div_cost(len, nonzero_words(&d)) <= newton_cost(len, len) {
            By::Sparse
        } else {
            let w = n.next_multiple_of(64);
            By::Reciprocal(w - n, reciprocal(&(&*d << (w - n)), w))
        };
        Divisor { d, by }
    }

    /// `(x / d, x mod d)` for `x < 2^(n + w)`, `n` the bits of `d`, so for any `x` below `d`
    /// times a whole number of words as wide as `d`. With `X = x 2^s < 2^2w`, `X y / 2^2w` is
    /// `x / d` or one below, since `X / (d 2^s) - X y / 2^2w < X / 2^2w < 1`; the low `w` bits
    /// of `X` are dropped, which takes off less than `2^w y / 2^2w <= 2` more, so that the
    /// product is of `w` bits by `w + 2`, and its transform of as few points as `d`'s width
    /// allows. O(M(n)).
    pub(crate) fn div_rem(&self, x: &BigUint) -> (BigUint, BigUint) {
        match &self.by {
            By::Leaf => x.div_rem(&*self.d),
            By::Sparse => sparse_div_rem(x, &self.d),
            By::Reciprocal(s, y) => {
                let w = self.d.bits() + s;
                debug_assert!(x.bits() <= self.d.bits() + w);
                let q = mul(&(x >> (w - s)), y) >> w;
                let qd = mul(&q, &self.d);
                settle(x, &self.d, q, qd)
            }
        }
    }
}

/// The decimal digits of `x`, by halves: `x = high * 10^(L 2^i) + low` with the powers
/// `10^(L 2^i)` and their reciprocals built once, `L` being [`PRINT_LEAF`], each half written
/// alone and the low half padded with zeros to its width. O(M(n) log n), the recursion
/// `log2(n / L)` deep.
pub(crate) fn to_decimal(x: &BigUint) -> String {
    // `x < 2^(3 L) < 10^L`: a single leaf, without building `10^L`.
    if x.bits() < 3 * PRINT_LEAF as u64 {
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
    if powers[0] > *x {
        return x.to_string();
    }
    // Complexity tradeoff: the digits are written by halves, each level of the recursion
    // dividing by one power of ten, so the cost is O(M(n) log n) = O(n log^2 n), above
    // num-bigint's multiplication but below its O(n^2) leaves; each power's reciprocal is
    // built once and reused by every division at its level, and the widest power, which
    // divides once, is divided by `div_rem`, whose reciprocal has the quotient's width rather
    // than the power's. Tested by `printing_a_wide_number_scales` (COMPLEXITY.md K30).
    let top = powers.pop().expect("the first power is listed");
    let (high, low) = div_rem(x, &top);
    drop(top);
    let powers: Vec<Divisor> = powers
        .into_iter()
        .map(|p| Divisor::new(Cow::Owned(p)))
        .collect();
    // `log10(2) < 1234 / 4096`.
    let digits = usize::try_from(x.bits() * 1234 / 4096 + 2).expect("a text that fits in memory");
    let mut out = String::with_capacity(digits);
    // `high` is not zero, the power being at most `x`.
    write_decimal(&high, &powers, powers.len(), false, &mut out);
    drop(high);
    write_decimal(&low, &powers, powers.len(), true, &mut out);
    out
}

/// Writes `x < 10^(L 2^level)` to `out`, padded to `L 2^level` digits when `pad`.
fn write_decimal(x: &BigUint, powers: &[Divisor], level: usize, pad: bool, out: &mut String) {
    if level == 0 {
        let s = x.to_string();
        if pad {
            out.extend(std::iter::repeat_n('0', PRINT_LEAF - s.len()));
        }
        out.push_str(&s);
        return;
    }
    let (high, low) = powers[level - 1].div_rem(x);
    if !pad && high.is_zero() {
        return write_decimal(&low, powers, level - 1, false, out);
    }
    write_decimal(&high, powers, level - 1, pad, out);
    drop(high);
    write_decimal(&low, powers, level - 1, true, out);
}

#[cfg(test)]
mod tests {
    use super::*;

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
    }
}
