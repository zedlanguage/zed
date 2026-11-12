//! The product of two naturals by a number-theoretic transform, for the reading of long integers
//! (`read_digits`). The references do not use the kernel, whose products are the fast
//! ones (lib.rs: the outputs must not come from the compiler), and num-bigint's product is at
//! best Toom-3, about n^1.46, which made the reading of n digits cost about n^1.46 too.
//!
//! The transform works modulo the prime P = 29 * 2^57 + 1, below 2^62, which has roots of unity
//! of every order 2^k up to 2^57. A factor is cut into coefficients of `w` bits, `w` the widest
//! (at most 31) for which a coefficient of the product, a sum of at most `count` products of two
//! coefficients below 2^w, `count` the shorter factor's number of coefficients, stays below P:
//! 26 bits up to 754 words, 25 up to 2,900, 24 up to 11,136, 23 up to 42,688, against 16 bits at
//! every length for the prime 2^64 - 2^32 + 1, so the transforms are 1.4 to 1.6 times shorter.
//!
//! Each twiddle factor `w` is stored with `floor(w * 2^64 / P)` (Shoup's multiplication), so a
//! product by it is two multiplications and a subtraction with no division, and its result is
//! below 2P; sums and differences are kept below 2P too, and reduced below P only when read. The
//! pointwise products, whose factors are both data, are by Montgomery's reduction, which gives
//! `a * b / 2^64`; the factor 2^-64 is taken off with the division by the length.
//!
//! The forward transform is by decimation in frequency (natural order in, bit-reversed order
//! out), skipping the arithmetic on the zero padding, and the inverse by decimation in time with
//! the same twiddles (bit-reversed in, natural out), so neither reorders the coefficients; both
//! do two stages to a pass (radix 4), which halves the passes over the array.

use num_bigint::BigUint;

/// The prime the transform works modulo, 29 * 2^57 + 1, below 2^62.
const P: u64 = 29 * (1 << 57) + 1;

/// A generator of the multiplicative group modulo P.
const GENERATOR: u64 = 3;

/// 2^64 modulo P.
const R: u64 = ((1u128 << 64) % P as u128) as u64;

/// -1/P modulo 2^64. Newton's step `x (2 - P x)` doubles the low bits of 1/P that are right; 1
/// is right in one bit (P is odd), so six steps give 64.
const P_NEG_INV: u64 = {
    let mut inv = 1u64;
    let mut step = 0;
    while step < 6 {
        inv = inv.wrapping_mul(2u64.wrapping_sub(P.wrapping_mul(inv)));
        step += 1;
    }
    inv.wrapping_neg()
};

/// The fewer 32-bit words of two factors from which [`mul`] uses the transform.
//
// Complexity tradeoff: a timed crossover of two algorithms with identical results, nothing given
// up: num-bigint's product (schoolbook, Karatsuba, Toom-3; about n^1.46 at these sizes) below,
// the transform above, O(n log n) for n words. The transform's cost doubles where its length
// passes a power of two while num-bigint's grows smoothly, so the two cross again past it: two
// factors of 6,144 words, num-bigint 14.03 M, transform 9.84 M; 6,145 words 14.04 M, 19.46 M;
// 9,000 words 25.00 M, 20.29 M, and the transform cheaper at every length measured above, to
// 24,577 words. This is the crossover of the products the reading sends here, its last power
// times the high part. Instructions, test profile, 2026-11-12 (load 40 to 43 on 32 cores), each
// product with its own twiddles: 5^65536 (4,756 words) times a factor of 4,096 words, num-bigint
// 9.13 M, transform 9.34 M; 4,352 words 9.31 M, 9.38 M; 4,608 words 9.52 M, 9.42 M; 5,120 words
// 10.34 M, 9.49 M; break-even about 4,450 words. Two factors of 4,608 words: 9.32 M, 9.39 M;
// 5,120 words 10.49 M, 9.54 M.
pub const TRANSFORM_WORDS: u64 = 4450;

/// The fewest 32-bit words of a factor of a reading that keeps its transform ([`Factor::new`]).
//
// Complexity tradeoff: a timed crossover of two methods with identical results, nothing given up:
// below, num-bigint's square and products by the factor, about n^1.46 each; above, one forward
// transform kept (O(n log n) time, `len` coefficients of bytes) and one inverse transform for the
// square and each product. The reading's powers have 74 * 2^i words, so any value from 595 to
// 1,189 words gives the same reading. Instructions, test profile, 2026-11-12 (load 43 on 32
// cores), the square and one product by a factor 1.43 times longer (a part of as many digits),
// twiddles built once: 1,024 words, num-bigint 2.53 M, kept 2.75 M; 1,200 words 3.06 M, 2.89 M;
// break-even about 1,120 words. With more products by it, as in the reading, the kept
// transform gains more.
pub const KEPT_WORDS: u64 = 1120;

/// `a * b`: num-bigint's product when either factor has fewer than [`TRANSFORM_WORDS`] words,
/// else [`transform_mul`].
pub fn mul(a: &BigUint, b: &BigUint) -> BigUint {
    match words(a).min(words(b)) < TRANSFORM_WORDS {
        true => a * b,
        false => transform_mul(a, b),
    }
}

/// `a * b` by the transform, O(n log n) time and O(n) bytes for factors of n words together. A
/// square takes two transforms in place of three.
pub fn transform_mul(a: &BigUint, b: &BigUint) -> BigUint {
    product(&twiddles(transform_len(a.bits(), b.bits())), a, b)
}

/// A twiddle factor: a power of a root of unity modulo P, with `floor(value * 2^64 / P)`.
#[derive(Clone, Copy)]
pub struct Twiddle {
    value: u64,
    quotient: u64,
}

impl Twiddle {
    /// The twiddle factor of `value`, below P.
    fn new(value: u64) -> Twiddle {
        let quotient = ((u128::from(value) << 64) / u128::from(P)) as u64;
        Twiddle { value, quotient }
    }
}

/// A factor of a reading, with its transform kept or not: the powers of five the reading of long
/// integers multiplies by (`read_digits`).
//
// Complexity tradeoff: the reading multiplies by `5^(LEAF_DIGITS * 2^i)` 2^(top - i) times and
// squares it once; transforming it in each product costs a third of the product's work and a
// third of its bytes (a second array of `len` coefficients), keeping its transform costs `len`
// coefficients once. Its square, the next power, is then one inverse transform, in place of two
// transforms.
pub struct Factor {
    value: BigUint,
    /// The width of the coefficients of `spectrum`, in bits.
    width: u32,
    /// The transform of `value`, empty when it is not kept.
    spectrum: Vec<u64>,
}

impl Factor {
    /// `value` as a factor whose transform is not kept.
    pub fn plain(value: BigUint) -> Factor {
        Factor {
            width: width(value.bits()),
            value,
            spectrum: Vec::new(),
        }
    }

    /// `value` as a factor with its transform kept, at the length of its product by a natural of
    /// `partner_bits` bits, `partner_bits` at least the bits of `value` (the length then holds
    /// its square too); `roots` from [`twiddles`] of at least [`transform_len`] of the two.
    pub fn new(value: BigUint, partner_bits: u64, roots: &[Twiddle]) -> Factor {
        let width = width(value.bits());
        let used = count(value.bits(), width);
        let len = (used + count(partner_bits, width)).next_power_of_two();
        let mut spectrum = coefficients(&value, width, len);
        forward(&mut spectrum, roots, used);
        Factor {
            value,
            width,
            spectrum,
        }
    }

    /// The factor's value.
    pub fn value(&self) -> &BigUint {
        &self.value
    }

    /// The factor's square; `roots` as for [`Factor::new`].
    pub fn square(&self, roots: &[Twiddle]) -> BigUint {
        let used = 2 * count(self.value.bits(), self.width);
        if self.spectrum.len() < used {
            return mul(&self.value, &self.value);
        }
        let x = self.spectrum.iter().map(|u| pointwise(*u, *u)).collect();
        inverse(x, used, self.width, roots)
    }

    /// `a * value`: by the kept transform when `a` is as long as it was kept for, else as [`mul`]
    /// takes it; `roots` from [`twiddles`] of at least the product's [`transform_len`].
    pub fn times(&self, a: &BigUint, roots: &[Twiddle]) -> BigUint {
        let used = count(a.bits(), self.width) + count(self.value.bits(), self.width);
        let shorter = words(a).min(words(&self.value));
        if shorter < KEPT_WORDS || used.next_power_of_two() != self.spectrum.len() {
            return match shorter < TRANSFORM_WORDS {
                true => a * &self.value,
                false => product(roots, a, &self.value),
            };
        }
        let mut x = coefficients(a, self.width, self.spectrum.len());
        forward(&mut x, roots, count(a.bits(), self.width));
        for (u, v) in x.iter_mut().zip(&self.spectrum) {
            *u = pointwise(*u, *v);
        }
        inverse(x, used, self.width, roots)
    }
}

/// The 32-bit words of `x`.
fn words(x: &BigUint) -> u64 {
    x.bits().div_ceil(32)
}

/// The widest coefficient, of at most 31 bits, for which every coefficient of a product stays
/// below P, `bits` being the shorter factor's: such a coefficient is a sum of at most
/// `count(bits, w)` products of two coefficients below 2^w.
fn width(bits: u64) -> u32 {
    (16..32)
        .rev()
        .find(|w| u128::from(bits.div_ceil(u64::from(*w))) << (2 * w) < u128::from(P))
        .expect("a factor of fewer than 2^33 bits")
}

/// The coefficients of `width` bits of a natural of `bits` bits.
fn count(bits: u64, width: u32) -> usize {
    bits.div_ceil(u64::from(width)) as usize
}

/// The length of the transform of the product of naturals of `a_bits` and `b_bits` bits: the
/// table of [`twiddles`] a product needs.
pub fn transform_len(a_bits: u64, b_bits: u64) -> usize {
    let w = width(a_bits.min(b_bits));
    (count(a_bits, w) + count(b_bits, w)).next_power_of_two()
}

/// `a * b` by the transform, `roots` being [`twiddles`] of at least the product's
/// [`transform_len`].
fn product(roots: &[Twiddle], a: &BigUint, b: &BigUint) -> BigUint {
    let w = width(a.bits().min(b.bits()));
    let used = count(a.bits(), w) + count(b.bits(), w);
    let len = used.next_power_of_two();
    let mut x = coefficients(a, w, len);
    forward(&mut x, roots, count(a.bits(), w));
    if a == b {
        for u in x.iter_mut() {
            *u = pointwise(*u, *u);
        }
    } else {
        let mut y = coefficients(b, w, len);
        forward(&mut y, roots, count(b.bits(), w));
        for (u, v) in x.iter_mut().zip(&y) {
            *u = pointwise(*u, *v);
        }
    }
    inverse(x, used, w, roots)
}

/// The coefficients of `width` bits of `a`, the lowest first, then zeros up to `len` in all.
fn coefficients(a: &BigUint, width: u32, len: usize) -> Vec<u64> {
    let mut out = Vec::with_capacity(len);
    // `acc` holds the `bits` bits of `a` not yet cut, fewer than `width` before a word is added.
    let (mut acc, mut bits) = (0u64, 0);
    for word in a.iter_u32_digits() {
        acc |= u64::from(word) << bits;
        bits += 32;
        while bits >= width {
            out.push(acc & ((1 << width) - 1));
            acc >>= width;
            bits -= width;
        }
    }
    if bits > 0 {
        out.push(acc);
    }
    out.resize(len, 0);
    out
}

/// The natural whose coefficients of `width` bits, the lowest first, are the first `used` entries
/// of the inverse transform of `x`, each carrying into the next, for `x` a product of transforms
/// by [`pointwise`] (so times 2^-64) of factors of `used` coefficients together.
fn inverse(mut x: Vec<u64>, used: usize, width: u32, roots: &[Twiddle]) -> BigUint {
    backward(&mut x, roots);
    // The inverse transform is `backward` divided by the length; and times 2^64, for the
    // factor 2^-64 of the pointwise products.
    let scale = Twiddle::new(mul_mod(pow(x.len() as u64, P - 2), R));
    // `backward` gives entry `k` of the inverse transform at `-k` modulo the length.
    let (first, rest) = x.split_at(1);
    let entries = first
        .iter()
        .chain(rest[rest.len() + 1 - used.max(1)..].iter().rev());
    let mut words = Vec::with_capacity((used * width as usize).div_ceil(32) + 1);
    // `carry` holds the sum not yet cut into coefficients, `acc` the `bits` bits of output not
    // yet a word, fewer than 32.
    let (mut carry, mut acc, mut bits) = (0u128, 0u64, 0);
    for entry in entries {
        carry += u128::from(reduce(mul_twiddle(*entry, scale)));
        acc |= ((carry as u64) & ((1 << width) - 1)) << bits;
        carry >>= width;
        bits += width;
        if bits >= 32 {
            words.push(acc as u32);
            acc >>= 32;
            bits -= 32;
        }
    }
    // Factors of `k` and `m` coefficients have a product below 2^(width * (k + m)).
    debug_assert_eq!(carry, 0, "the product fits its coefficients");
    words.push(acc as u32);
    BigUint::new(words)
}

/// The twiddle factors of every stage of a transform of length `len`, a power of two: entries
/// `h..2h` are the powers `0..h` of the root of order `2h`, for `h` = 1, 2, 4, ..., `len / 2`;
/// `len` entries in all, entry 0 unused. Each stage reads its factors in order, and a transform
/// of any length up to `len` reads its factors from the same table. About 30 instructions an
/// entry.
pub fn twiddles(len: usize) -> Vec<Twiddle> {
    assert!(
        len as u64 <= 1 << 57,
        "a product of {len} coefficients is past the transform's length 2^57"
    );
    let root = pow(GENERATOR, (P - 1) / len as u64);
    let mut out = vec![Twiddle::new(0); len.max(1)];
    let mut half = len / 2;
    let mut w = 1;
    for t in out.get_mut(half..).unwrap_or_default() {
        *t = Twiddle::new(w);
        w = mul_mod(w, root);
    }
    // The root of order 2h is the square of the root of order 4h, so its j-th power is entry
    // 2h + 2j.
    while half > 1 {
        half /= 2;
        for j in 0..half {
            out[half + j] = out[2 * (half + j)];
        }
    }
    out
}

/// The transform of `xs`, in bit-reversed order: decimation in frequency, two stages to a pass,
/// `roots` being [`twiddles`] of at least `xs.len()`. Only the first `used` entries of `xs` may be
/// nonzero.
fn forward(xs: &mut [u64], roots: &[Twiddle], used: usize) {
    let mut half = xs.len() / 2;
    // While each block's upper half is zero, the stage writes the lower half's nonzero entries
    // times the twiddles into the upper half and leaves the lower half as it is.
    while half >= used.max(1) {
        let w = &roots[half..2 * half];
        for block in xs.chunks_exact_mut(2 * half) {
            let (low, high) = block.split_at_mut(half);
            for j in 0..used {
                high[j] = mul_twiddle(low[j], w[j]);
            }
        }
        half /= 2;
    }
    // Two stages, of blocks of `4q` and of `2q`: the root of order `2q` is the square of that of
    // order `4q`.
    while half >= 2 {
        let q = half / 2;
        let (w, v) = (&roots[half..2 * half], &roots[q..half]);
        for block in xs.chunks_exact_mut(4 * q) {
            let (ab, cd) = block.split_at_mut(2 * q);
            let ((a, b), (c, d)) = (ab.split_at_mut(q), cd.split_at_mut(q));
            for j in 0..q {
                let (s, u) = (add_mod(a[j], c[j]), mul_twiddle(sub_mod(a[j], c[j]), w[j]));
                let (t, z) = (
                    add_mod(b[j], d[j]),
                    mul_twiddle(sub_mod(b[j], d[j]), w[q + j]),
                );
                (a[j], b[j]) = (add_mod(s, t), mul_twiddle(sub_mod(s, t), v[j]));
                (c[j], d[j]) = (add_mod(u, z), mul_twiddle(sub_mod(u, z), v[j]));
            }
        }
        half /= 4;
    }
    // An odd number of stages leaves one, whose twiddle is 1.
    if half == 1 {
        for [x, y] in xs.as_chunks_mut::<2>().0 {
            (*x, *y) = (add_mod(*x, *y), sub_mod(*x, *y));
        }
    }
}

/// The transform of `xs`, from bit-reversed order to natural order: decimation in time with the
/// same [`twiddles`] as [`forward`], two stages to a pass. With the forward root, entry `k` of the
/// result is the length times entry `-k` (modulo the length) of the inverse transform, so the
/// inverse needs no table of its own.
fn backward(xs: &mut [u64], roots: &[Twiddle]) {
    let mut half = 1;
    // Two stages, of blocks of `2h` and of `4h`.
    while 4 * half <= xs.len() {
        let (v, w) = (&roots[half..2 * half], &roots[2 * half..4 * half]);
        for block in xs.chunks_exact_mut(4 * half) {
            let (ab, cd) = block.split_at_mut(2 * half);
            let ((a, b), (c, d)) = (ab.split_at_mut(half), cd.split_at_mut(half));
            for j in 0..half {
                let (t, z) = (mul_twiddle(b[j], v[j]), mul_twiddle(d[j], v[j]));
                let (s, u) = (
                    (add_mod(a[j], t), sub_mod(a[j], t)),
                    (add_mod(c[j], z), sub_mod(c[j], z)),
                );
                let (t, z) = (mul_twiddle(u.0, w[j]), mul_twiddle(u.1, w[half + j]));
                (a[j], c[j]) = (add_mod(s.0, t), sub_mod(s.0, t));
                (b[j], d[j]) = (add_mod(s.1, z), sub_mod(s.1, z));
            }
        }
        half *= 4;
    }
    // An odd number of stages leaves one.
    if half < xs.len() {
        let w = &roots[half..2 * half];
        for block in xs.chunks_exact_mut(2 * half) {
            let (low, high) = block.split_at_mut(half);
            for j in 0..half {
                let t = mul_twiddle(high[j], w[j]);
                (low[j], high[j]) = (add_mod(low[j], t), sub_mod(low[j], t));
            }
        }
    }
}

/// `x^e` modulo P.
fn pow(mut x: u64, mut e: u64) -> u64 {
    let mut out = 1;
    while e > 0 {
        if e & 1 == 1 {
            out = mul_mod(out, x);
        }
        x = mul_mod(x, x);
        e >>= 1;
    }
    out
}

// The arithmetic below uses `wrapping_` operations where the comments show no overflow can
// happen: the test profile checks every `+`, `-` and `*` for overflow, which in the transform's
// loops cost more than the arithmetic (a checked `u128` product most of all). The values in the
// transforms are below 2P, below 2^63.

/// `a * w` modulo P, below 2P, for any `a` (Shoup's multiplication): `q` is `a * w / P` rounded
/// down or one less, so `a * w - q * P` is below 2P, and is exact modulo 2^64.
#[inline]
fn mul_twiddle(a: u64, w: Twiddle) -> u64 {
    let q = (u128::from(a).wrapping_mul(u128::from(w.quotient)) >> 64) as u64;
    a.wrapping_mul(w.value).wrapping_sub(q.wrapping_mul(P))
}

/// `a` modulo P, for `a < 2P`.
#[inline]
fn reduce(a: u64) -> u64 {
    match a >= P {
        true => a.wrapping_sub(P),
        false => a,
    }
}

/// `a + b` modulo P, below 2P, for `a, b < 2P`; the sum is below 4P, below 2^64.
#[inline]
fn add_mod(a: u64, b: u64) -> u64 {
    let s = a.wrapping_add(b);
    match s >= 2 * P {
        true => s.wrapping_sub(2 * P),
        false => s,
    }
}

/// `a - b` modulo P, below 2P, for `a, b < 2P`.
#[inline]
fn sub_mod(a: u64, b: u64) -> u64 {
    match a >= b {
        true => a.wrapping_sub(b),
        false => a.wrapping_add(2 * P).wrapping_sub(b),
    }
}

/// `a * b / 2^64` modulo P, below 2P, for `a, b < 2P` (Montgomery's reduction): `m` makes
/// `a * b + m * P` a multiple of 2^64, and the sum is below 4P^2 + 2^64 P, below 2^64 * 2P since
/// 4P < 2^64.
#[inline]
fn pointwise(a: u64, b: u64) -> u64 {
    let t = u128::from(a).wrapping_mul(u128::from(b));
    let m = (t as u64).wrapping_mul(P_NEG_INV);
    (t.wrapping_add(u128::from(m).wrapping_mul(u128::from(P))) >> 64) as u64
}

/// `a * b` modulo P, by division: for the tables and the scale, not the transforms.
fn mul_mod(a: u64, b: u64) -> u64 {
    (u128::from(a) * u128::from(b) % u128::from(P)) as u64
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The generator's powers give a root of order exactly 2^57, `P_NEG_INV` and `R` are right,
    /// and each operation gives its value modulo P, below its bound, at the edges of its inputs.
    #[test]
    fn the_root_the_constants_and_the_operations_are_right() {
        let root = pow(GENERATOR, (P - 1) >> 57);
        assert_eq!(pow(root, 1 << 56), P - 1);
        assert_eq!(pow(root, 1 << 57), 1);
        assert_eq!(P.wrapping_mul(P_NEG_INV), u64::MAX);
        assert_eq!(u128::from(R), (1u128 << 64) % u128::from(P));
        let p = u128::from(P);
        let inv_r = u128::from(pow(R, P - 2));
        let edges = [0, 1, P - 1, P, P + 1, 2 * P - 1];
        for a in edges {
            assert_eq!(u128::from(reduce(a)), u128::from(a) % p, "reduce {a}");
            for b in edges {
                let (a128, b128) = (u128::from(a), u128::from(b));
                let checks = [
                    ("add", add_mod(a, b), (a128 + b128) % p),
                    ("sub", sub_mod(a, b), (a128 + 2 * p - b128) % p),
                    ("pointwise", pointwise(a, b), a128 * b128 % p * inv_r % p),
                ];
                for (what, got, expected) in checks {
                    assert!(got < 2 * P, "{what} {a} {b}: {got} not below 2P");
                    assert_eq!(u128::from(got) % p, expected, "{what} {a} {b}");
                }
            }
        }
        for a in [0, 1, P - 1, 2 * P - 1, u64::MAX] {
            for w in [0, 1, 2, P - 2, P - 1] {
                let got = mul_twiddle(a, Twiddle::new(w));
                assert!(got < 2 * P, "{a} times twiddle {w}: {got} not below 2P");
                assert_eq!(
                    u128::from(got) % p,
                    u128::from(a) * u128::from(w) % p,
                    "{a} times {w}"
                );
            }
        }
    }
}
