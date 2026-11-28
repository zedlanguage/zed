//! The solver's integers (DESIGN.md sec:domains, "exact, over unbounded integers"): unbounded,
//! with `i128` arithmetic while a value fits, since nearly all of them do. Zed's `int` is
//! unbounded, so this module goes at the port (ZED_PORT_GAPS.md).

use std::borrow::Cow;
use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::ops::{Add, BitAnd, Mul, Neg, Sub};
use std::sync::{Arc, Mutex};

use num_bigint::{BigInt, BigUint, Sign};
use num_integer::Integer;
use num_traits::{One, Zero};
use zed_bignum::approx::{Approx, below_zero, floor_shr, scaled_cmp};
use zed_bignum::coprime::coprime_base_exponents;
use zed_bignum::fast::{
    div_floor as div_floor_int, gcd_uint, inverse_mod as inverse_mod_uint,
    mod_floor as mod_floor_int, mul as mul_uint, mul_int, pow as pow_uint, to_decimal,
};
use zed_bignum::least_root::{least_root, nth_root_rem_uint};
use zed_bignum::trees::{crt_coprime, product_of};
use zed_collections::sorted::{Joined, merge_join, merge_with};
use zed_kernel::bits::BitLen;
use zed_kernel::num::{TooLarge, read_digits, room};
use zed_numtheory::{
    bezout_i128, gcd_big_u64, gcd_u64, gcd_u128, inverse_mod_u64, log2_bounds, next_prime, pow_mod,
};

/// An integer. A value that fits in `i128` is always `Small`, so that two equal values have
/// one form.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
enum Repr {
    Small(i128),
    Big(Arc<BigInt>),
}

/// An unbounded integer.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Int(Repr);

impl Default for Int {
    fn default() -> Int {
        Int::ZERO
    }
}

/// For the offsets of `zed_graph::UnionFind` (`Diff<Int>`, `Signed<Int>`), which skip adding
/// a zero.
impl zed_graph::IsZero for Int {
    #[inline]
    fn is_zero(&self) -> bool {
        Int::is_zero(self)
    }
}

impl From<i32> for Int {
    fn from(v: i32) -> Int {
        Int(Repr::Small(v.into()))
    }
}

impl From<i64> for Int {
    fn from(v: i64) -> Int {
        Int(Repr::Small(v.into()))
    }
}

impl From<usize> for Int {
    fn from(v: usize) -> Int {
        Int(Repr::Small(v as i128))
    }
}

impl From<i128> for Int {
    fn from(v: i128) -> Int {
        Int(Repr::Small(v))
    }
}

impl From<BigInt> for Int {
    fn from(v: BigInt) -> Int {
        Int(match i128::try_from(&v) {
            Ok(s) => Repr::Small(s),
            Err(_) => Repr::Big(Arc::new(v)),
        })
    }
}

impl Int {
    /// Zero.
    pub const ZERO: Int = Int(Repr::Small(0));
    /// One.
    pub const ONE: Int = Int(Repr::Small(1));

    /// The value as a `BigInt`, for the routines over `BigInt` (`zed_numtheory::floor_sum`):
    /// borrowed when it is big, made when it fits in `i128`.
    pub fn big(&self) -> Cow<'_, BigInt> {
        match &self.0 {
            Repr::Small(v) => Cow::Owned(BigInt::from(*v)),
            Repr::Big(v) => Cow::Borrowed(v),
        }
    }

    /// `|self|` as a `BigUint`, for the kernel's routines over `BigUint` (its product and
    /// remainder trees, `zed_kernel::num::trees`). O(n) for `n` words, a copy.
    pub fn magnitude(&self) -> BigUint {
        match &self.0 {
            Repr::Small(v) => BigUint::from(v.unsigned_abs()),
            Repr::Big(v) => v.magnitude().clone(),
        }
    }

    /// The value, when it fits in `i128`.
    pub fn to_i128(&self) -> Option<i128> {
        match self.0 {
            Repr::Small(v) => Some(v),
            Repr::Big(_) => None,
        }
    }

    /// Whether the value is below zero.
    pub fn is_negative(&self) -> bool {
        match &self.0 {
            Repr::Small(v) => *v < 0,
            Repr::Big(v) => v.sign() == Sign::Minus,
        }
    }

    /// Whether the value is above zero.
    pub fn is_positive(&self) -> bool {
        match &self.0 {
            Repr::Small(v) => *v > 0,
            Repr::Big(v) => v.sign() == Sign::Plus,
        }
    }

    /// Whether the value is zero.
    pub fn is_zero(&self) -> bool {
        self.0 == Repr::Small(0)
    }

    /// Whether the value is odd, in O(1) time whatever its size.
    pub fn is_odd(&self) -> bool {
        match &self.0 {
            Repr::Small(v) => v & 1 == 1,
            Repr::Big(v) => v.is_odd(),
        }
    }

    /// The number of binary digits of `|self|`: `0` for zero, and `floor(log2(|self|)) + 1`
    /// otherwise, in O(1) time with no heap allocation.
    pub fn bits(&self) -> u64 {
        match &self.0 {
            Repr::Small(v) => u64::from(v.unsigned_abs().bit_len()),
            Repr::Big(v) => v.bits(),
        }
    }

    /// Whether the value is 1 or -1.
    pub fn is_unit(&self) -> bool {
        matches!(self.0, Repr::Small(1 | -1))
    }

    /// The product of `xs`, 1 for none: a running `i128` product while it fits, else the
    /// magnitudes by pairs, then pairs of those (zed-bignum `trees::product_of`, O(M(B) log m)
    /// for `m` factors of `B` words in all, where a running product is O(m B)), with the sign
    /// of the count of negative factors. Was zedc-presburger `prod_slice`
    /// (DRY-bignum-crate-2026-11-26). Test: `tests::products_agree_with_a_running_product`.
    pub fn product(xs: &[Int]) -> Int {
        let small = (xs.iter()).try_fold(1i128, |p, x| x.to_i128().and_then(|v| p.checked_mul(v)));
        if let Some(p) = small {
            return Int::from(p);
        }
        if xs.iter().any(Int::is_zero) {
            return Int::ZERO;
        }
        let m = BigInt::from(product_of(
            &xs.iter().map(Int::magnitude).collect::<Vec<_>>(),
        ));
        match xs.iter().filter(|x| x.is_negative()).count() % 2 {
            1 => Int::from(-m),
            _ => Int::from(m),
        }
    }

    /// The absolute value.
    pub fn abs(&self) -> Int {
        if self.is_negative() {
            -self
        } else {
            self.clone()
        }
    }

    /// The least common multiple of two nonnegative integers, not both zero: `self / gcd(self,
    /// other) * other`, dividing first so no product is larger than the answer. The lcm with 0 is
    /// 0; both zero divides by `gcd(0, 0) = 0`. Cost: one gcd, one exact division and one
    /// product. Test: `tests::lcm_of_positive_integers`.
    pub fn lcm(&self, other: &Int) -> Int {
        &self.div_floor(&self.gcd(other)) * other
    }

    /// The greatest common divisor, never negative.
    pub fn gcd(&self, other: &Int) -> Int {
        match (&self.0, &other.0) {
            (Repr::Small(a), Repr::Small(b)) => {
                let (a, b) = (a.unsigned_abs(), b.unsigned_abs());
                // In 64 bits when both fit, where each step is one instruction.
                let g = match (u64::try_from(a), u64::try_from(b)) {
                    (Ok(a), Ok(b)) => u128::from(gcd_u64(a, b)),
                    _ => gcd_u128(a, b),
                };
                i128::try_from(g).map_or_else(|_| BigInt::from(g).into(), Int::from)
            }
            (Repr::Small(0), _) => other.abs(),
            (_, Repr::Small(0)) => self.abs(),
            (Repr::Small(1 | -1), _) | (_, Repr::Small(1 | -1)) => Int::ONE,
            // Complexity tradeoff: naive `self.big()` on a `Small` operand against `Big`
            // heap-allocates a `BigInt` and runs wide division even when the small operand is one
            // word (as in `Q::new` on small coefficients against `2^k` constants); streaming the
            // wide operand's words modulo an odd `u64` part finishes in registers in O(words)
            // with zero heap allocations. Past one odd word, `gcd_uint` takes out powers of 2 by
            // shifts, reduces the wider odd part modulo the narrower by `fast::rem`, O(M(n)), and
            // runs the half gcd (with in-place word-buffer Stein below `GCD_LEAF`) at the
            // narrower width, O(M(n) log n), instead of num-bigint's O(n^2) whole-width Stein
            // (LOAD-max-div-xr I25). Test: `int::tests::the_big_gcd_agrees_with_num_bigint`.
            // Stein's binary gcd is J. Stein, J. Comput. Phys. 1(3):397-405, 1967,
            // doi:10.1016/0021-9991(67)90047-2, cited with its rules, departures and check in
            // zed-numtheory's `word.rs` (the doc of `gcd_u64`).
            (Repr::Small(s), Repr::Big(b)) | (Repr::Big(b), Repr::Small(s)) => {
                let u = s.unsigned_abs();
                let zs = u.trailing_zeros();
                if let Ok(d) = u64::try_from(u >> zs) {
                    let bm = b.magnitude();
                    let zb = bm.trailing_zeros().unwrap_or(0);
                    let z = u64::from(zs).min(zb);
                    let g = u128::from(gcd_big_u64(bm, d)) << z;
                    return i128::try_from(g).map_or_else(|_| BigInt::from(g).into(), Int::from);
                }
                BigInt::from(gcd_uint(self.big().magnitude(), other.big().magnitude())).into()
            }
            (Repr::Big(a), Repr::Big(b)) => {
                BigInt::from(gcd_uint(a.magnitude(), b.magnitude())).into()
            }
        }
    }

    /// The extended gcd. Machine integers use the word extended Euclid of zed-numtheory
    /// ([`bezout_i128`]), the same steps and cofactors as the loop over `Int` it replaced,
    /// with no allocation; wider integers, and an operand `i128::MIN`, use the kernel's binary
    /// half-GCD.
    pub fn extended_gcd(&self, b: &Int) -> Option<(Int, Int, Int)> {
        if let (Repr::Small(x), Repr::Small(y)) = (&self.0, &b.0)
            && let Some((g, s, t)) = bezout_i128(*x, *y)
        {
            return Some((g.into(), s.into(), t.into()));
        }
        zed_kernel::num::bezout_int(&self.big(), &b.big())
            .map(|(g, s, t)| (g.into(), s.into(), t.into()))
    }

    /// [`Int::extended_gcd`] for callers that need the factors: `(g, s, t)` with
    /// `s self + t b = g = gcd(self, b) >= 0`. On machine integers the factors are extended
    /// Euclid's, `|s| <= max(1, |b| / g)` and `|t| <= max(1, |self| / g)`; wider, the half
    /// gcd's, reduced to the same bounds but not always the same pair (test
    /// `bezout_agrees_with_euclid_on_words_and_is_valid_when_wide` in zedc-presburger).
    ///
    /// Total: where [`Int::extended_gcd`] is `None`, the factors come from [`Int::euclid_bezout`].
    /// `extended_gcd` is never `None` (an `i128::MIN` operand makes [`bezout_i128`] `None`, but
    /// that case falls through to the kernel): the kernel's half gcd (`num/fast.rs`
    /// `bezout_with`) counts its halvings in u128, below `4 N < 2^68` for operands of `N` bits
    /// on every target, since no Rust allocation exceeds `isize::MAX` bytes (proof, every
    /// step, at `bezout_with`, step 6; PROOF-bezout-halvings-address-width). So the fallback is
    /// unreachable; it stays until `extended_gcd` drops its `Option`.
    pub fn bezout(&self, b: &Int) -> (Int, Int, Int) {
        self.bezout_or_euclid(b, self.extended_gcd(b))
    }

    /// [`Int::bezout`] given `found`, the answer of [`Int::extended_gcd`]: `found` itself, or
    /// for `None` the Euclid fallback, [`Int::euclid_bezout`] on `|self|` with the factor of
    /// `self` negated for a negative `self` (`s |self| = (-s) self`). Apart from `bezout` so the
    /// tests can reach the fallback, which no input held in memory is expected to reach
    /// (`the_euclid_fallback_of_bezout_gives_the_gcd_for_every_sign`).
    fn bezout_or_euclid(&self, b: &Int, found: Option<(Int, Int, Int)>) -> (Int, Int, Int) {
        found.unwrap_or_else(|| {
            let (g, s, t) = self.abs().euclid_bezout(b);
            (g, if self.is_negative() { -&s } else { s }, t)
        })
    }

    /// `(g, s, t)` with `s self + t b = g = gcd(self, b)`, for `self >= 0`, by the extended
    /// Euclidean algorithm over `Int`: O(n^2) on n-word values. It is the fallback of
    /// [`Int::bezout`] and the reference its tests compare against (zedc-presburger
    /// `bezout_agrees_with_euclid_on_words_and_is_valid_when_wide`). The remainder sequence is
    /// `r_{k+1} = r_{k-1} - q_k r_k`, `q_k = floor(r_{k-1} / r_k)`, from `(self, |b|)`, with the
    /// factors updated by the same `q_k`; the last nonzero remainder is the gcd.
    pub fn euclid_bezout(&self, b: &Int) -> (Int, Int, Int) {
        let (mut r, mut next) = (self.clone(), b.abs());
        let (mut s, mut ns) = (Int::ONE, Int::ZERO);
        let (mut t, mut nt) = (Int::ZERO, Int::ONE);
        while !next.is_zero() {
            let q = r.div_floor(&next);
            let rem = &r - &(&q * &next);
            r = std::mem::replace(&mut next, rem);
            let ns2 = &s - &(&q * &ns);
            s = std::mem::replace(&mut ns, ns2);
            let nt2 = &t - &(&q * &nt);
            t = std::mem::replace(&mut nt, nt2);
        }
        if b.is_negative() {
            t = -&t;
        }
        (r, s, t)
    }

    /// `self^-1 mod m` for `m` above zero, in `0..m`, or `None` when `gcd(self, m) != 1`;
    /// `Some(0)` modulo 1. The one inverse modulo an unbounded integer
    /// (DRY-int-crt-inverse-2026-11-26): moved from zedc-presburger `modular.rs`
    /// `inverse_mod`, it replaced the extended Euclid over `Num` of zedc-lattice
    /// `lattice.rs` `inverse` and over `Int` of zedc-presburger `extend/images.rs`
    /// `congruence`. Panics with "a modulus above 0" for `m` not above zero.
    ///
    /// Complexity tradeoff: the Euclidean algorithm over unbounded integers is O(n^2) on
    /// `n`-bit moduli, two Fibonacci neighbors being its slowest case
    /// (`pncx_fibonacci_crt_scale`, 77.9 times the work for 8 times the width, R6-CLAUDE-7);
    /// the kernel's binary half gcd with its steps kept (`zed_kernel::num::inverse_mod_uint`)
    /// is O(M(n) log n). Below that, a modulus of one word takes zed-numtheory's word Euclid
    /// (`inverse_mod_u64`, one 64-bit division a step) and one of two words the `i128`
    /// extended Euclid ([`bezout_i128`] through [`Int::extended_gcd`]): O(log m) steps on
    /// registers, with no allocation. The inverse is the same on every path, being unique in
    /// `0..m`. Tests: `tests::inverses_modulo_an_integer_at_every_width`.
    pub fn inverse_mod(&self, m: &Int) -> Option<Int> {
        assert!(m.is_positive(), "a modulus above 0");
        let a = self.mod_floor(m);
        if let (Repr::Small(x), Repr::Small(y)) = (&a.0, &m.0) {
            if let (Ok(x), Ok(y)) = (u64::try_from(*x), u64::try_from(*y)) {
                return inverse_mod_u64(x, y).map(|v| Int::from(i128::from(v)));
            }
            // `a` is in `0..m` and `m` is above 0, so neither is `i128::MIN` and
            // `extended_gcd` is `Some`.
            let (g, u, _) = a.extended_gcd(m)?;
            return (g == Int::ONE).then(|| u.mod_floor(m));
        }
        inverse_mod_uint(&a.magnitude(), &m.magnitude()).map(|x| Int::from(BigInt::from(x)))
    }

    /// The integers in both `r1 mod m1` and `r2 mod m2`, for `m1` and `m2` above zero, as one
    /// class `(r, lcm(m1, m2))` with `r` in `0..lcm`, or `None` when no integer is in both:
    /// the Chinese remainder theorem for two moduli that may share factors
    /// (DRY-int-crt-inverse-2026-11-26: moved from zedc-presburger `modular.rs`
    /// `combine_crt_pair`; zedc-lattice `Congruence::meet` calls it too).
    ///
    /// With `g = gcd(m1, m2)`, `x = r1 + m1 k` is in `r2 mod m2` exactly when
    /// `m1 k == r2 - r1 (mod m2)`. That needs `g | r2 - r1`; then dividing by `g`,
    /// `(m1 / g) k == (r2 - r1) / g (mod m2 / g)`, and `m1 / g` is coprime to `m2 / g`, so
    /// `k == (r2 - r1) / g · (m1 / g)^-1 (mod m2 / g)`: one class of `k` modulo `m2 / g`, so
    /// one class of `x` modulo `m1 m2 / g = lcm(m1, m2)`. One gcd and one inverse
    /// ([`Int::inverse_mod`]): O(M(n) log n). Tests: `tests::crt_pairs_agree_with_a_scan`.
    pub fn crt_pair(r1: &Int, m1: &Int, r2: &Int, m2: &Int) -> Option<(Int, Int)> {
        let g = m1.gcd(m2);
        let diff = r2 - r1;
        if !diff.mod_floor(&g).is_zero() {
            return None;
        }
        let m2_g = m2.div_floor(&g);
        let u = m1
            .div_floor(&g)
            .inverse_mod(&m2_g)
            .expect("m1 / g and m2 / g are coprime");
        let lcm = m1 * &m2_g;
        let step = (&diff.div_floor(&g) * &u).mod_floor(&m2_g);
        let r = (r1 + &(m1 * &step)).mod_floor(&lcm);
        Some((r, lcm))
    }

    /// The solution `(r, m)` of `x == r_i (mod m_i)` for all `(r_i, m_i)` in `pairs`, `m` the lcm
    /// of the `m_i`, or `None` when the congruences conflict. When the moduli are pairwise coprime
    /// (always so for the bases of zedc-presburger `solve_regime_step`), by the product and
    /// remainder trees:
    /// `x = sum_i c_i M / m_i mod M` with `c_i = r_i (M / m_i)^-1 mod m_i`, the sum built up the
    /// product tree as `v = v_left P_right + v_right P_left`, O(M(N) log k) for `k` moduli of `N`
    /// bits, plus one inverse modulo each `m_i` ([`Int::inverse_mod`], O(M(n) log n) for `n` bits).
    ///
    /// When one modulus is not coprime to the product of the others, the pairs are combined two
    /// at a time up a tree, each by a gcd, exact quotients and an inverse on the merged moduli
    /// ([`Int::crt_pair`]), O(M(N) log N) at each level of the tree. Tests:
    /// zedc-presburger `modular::r4_tests::the_crt_tree_solves_its_congruences` and
    /// `tests::crts_agree_with_pairs`; bench `pncx_fibonacci_crt_scale`
    /// (tests/steps/l01_38_presburger/bench/pncx_probe.rs).
    ///
    /// The coprime path (PERF-crt-tree-scaled-remainder, 2026-11-21): the cofactors
    /// `(M / m_i) mod m_i` come from the kernel's `trees::cofactors_mod_leaves` (the cofactor sum
    /// `S = sum_i M / m_i` up the tree, then Bernstein's scaled remainder tree down it, handing
    /// over
    /// to the exact descent at nodes of 128 words), the inverses are one word inverse each, and the
    /// sum goes up by `trees::linear_combination_up`. Every phase is O(M(N) log k).
    ///
    /// Cost argument and its limit: each level of the product tree holds at most `N + k` bits, so
    /// any method that builds the tree costs at least one multiplication of the level's width a
    /// level, `sum_levels M(N) = M(N) log k`. Only the output size, Omega(N), is a proved lower
    /// bound
    /// for CRT; no O(M(N)) method for `k` moduli of similar size is known. Searched 2026-11-21 with
    /// allpapers (keyword and semantic, `-n 250`, saved and read): R. P. Brent and P. Zimmermann,
    /// *Modern Computer Arithmetic*, arXiv:1004.4710, §2.7 (CRT by subproduct tree, O(M(N) log k));
    /// D. Harvey and A. V. Sutherland, arXiv:1402.3246 and arXiv:1410.5222 (the remainder forest,
    /// which lowers the memory and not the order); D. J. Bernstein, "Scaled remainder trees" (2004)
    /// and "Fast multiplication and its applications" (2008), §§12, 18, 23 (not in the corpus,
    /// read from the author's PDFs); van der Hoeven's "Faster Chinese remaindering" (2016) saves a
    /// factor `log log` for fixed moduli and is not in the corpus. Conditional lower bounds
    /// Omega(n log n) for multiplication itself (Afshani, Freksen, Kamma and Larsen, "Lower bounds
    /// for multiplication via network coding", ICALP 2019, arXiv:1902.10935; Harvey and van der
    /// Hoeven, "Integer multiplication is at least as hard as matrix transposition") bound below
    /// even one product of the root's width.
    ///
    /// Measured on the first 2,048 / 16,384 odd primes (`N` 25,546 / 259,803 bits, 10.17 times;
    /// remainders 0 and 1; release constants, instructions, load 56; the deferred bench
    /// `pncx_crt_tree_scale`): 20.45 M / 335.8 M, 16.42x, bytes 1.63 MB / 25.1 MB, 15.44x; on main
    /// before this change 23.28x and 31.10x. By phase (load 10 to 29): the product tree 1.24 M /
    /// 30.2 M (24.4x), the cofactors 10.2 M / 188.1 M (18.4x), the step up 2.93 M / 61.3 M (20.9x),
    /// the last remainder 0.10 M / 1.04 M (10.4x). The model with `M(N) = N log N` predicts
    /// `10.17 * (ln 259,803 / ln 25,546) * (14 / 11) = 15.9`; the larger phase ratios come from
    /// the multiplication, whose balanced products cost 3.1x a doubling from 64 to 256 words
    /// (num-bigint's Karatsuba and Toom-3, below `MUL_LEAF`, then 459 words and 400 since
    /// 2026-11-22, where the transforms cost more) and 2.0x to 2.2x from 1,024 words on: the
    /// tree's top node is 400 words at 2,048 primes and 4,059 at 16,384, so the two sizes sit on
    /// different parts of that curve. So the
    /// limit 10.5 at these sizes is out of reach of every known method; the bench stays in the
    /// deferred file (the author decision BENCH-crt-tree-size-by-bits holds the sizing).
    ///
    /// Above the crossover (PERF-crt-tree-bytes-growth, 2026-11-21, load 75 to 114): at 16,384 and
    /// 131,072 primes the top node is 4,059 words and more, past `MUL_LEAF`, and one product of two
    /// equal numbers measured n log n there (1.596 M instructions at 1,024 words, 13.66 M at
    /// 4,096, 119.3 M at 32,768 and 258.1 M at 65,536: 8.73x and 9.44x at 8 times the words). Still
    /// 335.3 M / 5,579 M instructions, 16.64x, and 25.1 MB / 362.5 MB, 14.43x; by phase the tree
    /// 18.16x (bytes 13.31x), the cofactors 17.97x (14.62x), the step up 18.87x (15.13x), the leaf
    /// inverses 9.12x (8.00x), the last remainder 22.6x (20.96x). So the excess is not a fixed
    /// crossover: it is the method's `M(N) log k` with `N` growing 9.5 times for 8 times the primes
    /// (the `n`-th prime has about `log2(n ln n)` bits) and three more levels, at the top where the
    /// cost of a level is highest. With `c(s) = M(s) / s` the cost of a level is `N c(s_l)`, and
    /// with `c(s) = log s` the ratio is `8 (N'/8N) ((L + 3) / L)^2`, 11.1 at `L` = 17 and under
    /// 10.5 only from `L` about 20.6, so the ratio of `N log^2 N` passes 10.5 at every size the
    /// tests can run.
    ///
    /// The bytes, proved for every method that keeps the levels of the product tree (the remainder
    /// tree reads every level on its way down, so all are held at once): a level's nodes multiply
    /// to `M`, and `bits(a b) <= bits(a) + bits(b)`, so a level holds at least `bits(M)` bits, and
    /// the `L` levels above the leaves at least `L bits(M)`. On this bench, sized by the count of
    /// primes, `bits(M)` grows 10.12 times (26,537 to 268,427) and `L` from 11 to 14, so the held
    /// levels alone grow at least `10.12 * 14 / 11 = 12.9` times, over 10.5, whatever the code
    /// around them does. Sized by bits instead (2,048 to 13,266 primes, `bits(M)` 8 times, 14
    /// levels), the same bound is `8 * 14 / 11 = 10.18`, under 10.5 and over 9, so it does not rule
    /// out a pass there; that sizing is the author decision BENCH-crt-tree-size-by-bits.
    /// A method that does not keep the levels recomputes them, which costs time
    /// (the remainder forest of Harvey and Sutherland, cited above, trades in that way); none is
    /// known that keeps the order `M(N) log k` and holds `o(N log k)` bits. Not proved: that every
    /// method in `O(M(N) log k)` time must hold `Omega(N log k)` bits.
    ///
    /// No refusal (PROOF-crt-refusal-exact-class, 2026-11-21). The author's order allows a refusal
    /// only for a class of inputs that provably degrades, defined by the moduli. To prove that a
    /// class needs more than O(n log n) work one needs a lower bound above `n log n` for CRT on
    /// that
    /// class. None is known in any model: the only proved lower bound is the output, Omega(N), and
    /// the conditional Omega(N log N) bounds cited above are for one multiplication, which every
    /// method also pays. So no nonempty class can be shown to degrade, the exact refusal class is
    /// empty, and every input is solved, at O(M(N) log k). This is a limit of what is known, not a
    /// proof that no faster method exists: the gap between Omega(N) and O(M(N) log k) is open in
    /// the literature searched above. A class defined by the moduli where a linear method is proved
    /// is taken instead where one exists: moduli that are all prime words, for the coprime base
    /// (zed-kernel `num::coprime::prime_words`, PERF-private-quotient-wide-moduli); for CRT itself
    /// the product `M` is the output, so no such class lowers its order.
    ///
    /// Moved from zedc-presburger `modular.rs` `combine_crt_tree` (DRY-bignum-crate-2026-11-26);
    /// the coprime path is zed-bignum `trees::crt_coprime`.
    pub fn crt(mut pairs: Vec<(Int, Int)>) -> Option<(Int, Int)> {
        pairs.retain(|(_, m)| *m != Int::ONE);
        if pairs.is_empty() {
            return Some((Int::ZERO, Int::ONE));
        }
        // The moduli are above 1 here, so their magnitudes are the moduli, and `mod_floor` by
        // `m > 0` is in `[0, m)`, so its magnitude is the residue.
        let moduli: Vec<BigUint> = pairs.iter().map(|(_, m)| m.magnitude()).collect();
        let residues: Vec<BigUint> = (pairs.iter())
            .map(|(r, m)| r.mod_floor(m).magnitude())
            .collect();
        if let Some((x, m)) = crt_coprime(&residues, &moduli) {
            return Some((Int::from(BigInt::from(x)), Int::from(BigInt::from(m))));
        }
        while pairs.len() > 1 {
            let mut next = Vec::with_capacity(pairs.len().div_ceil(2));
            let mut it = pairs.into_iter();
            while let Some((r1, m1)) = it.next() {
                next.push(match it.next() {
                    Some((r2, m2)) => Int::crt_pair(&r1, &m1, &r2, &m2)?,
                    None => (r1, m1),
                });
            }
            pairs = next;
        }
        pairs.pop()
    }

    /// The least `t >= 0` with `self · t == b (mod m)`, for `m` above zero, and the period
    /// `m / gcd(self, m)` of all solutions; `None` when there is none
    /// (DRY-int-crt-inverse-2026-11-26: it replaced the solves of zedc-presburger
    /// `extend/images.rs` `congruence` and `exact/projection.rs` `project`).
    ///
    /// With `g = gcd(self, m)`, a solution needs `g | b`; then `self / g` is coprime to
    /// `p = m / g` and the solutions are `t == (b / g) · (self / g)^-1 (mod p)`. For
    /// `self == 0 (mod m)`, `g = m` and `p = 1`: every `t` when `m | b`, so `t = 0`. One gcd
    /// and one inverse ([`Int::inverse_mod`]). Tests:
    /// `tests::linear_congruences_agree_with_a_scan`.
    pub fn solve_linear_congruence(&self, b: &Int, m: &Int) -> Option<(Int, Int)> {
        let g = self.gcd(m);
        if !b.mod_floor(&g).is_zero() {
            return None;
        }
        let period = m.div_floor(&g);
        let inv = self
            .div_floor(&g)
            .inverse_mod(&period)
            .expect("self / g and m / g are coprime");
        Some(((&b.div_floor(&g) * &inv).mod_floor(&period), period))
    }

    /// `self / m` rounded down, for `m` of either sign and not zero. Past `i128` the division
    /// of the magnitudes is the kernel's (`zed_kernel::num::div_floor_int`): num-bigint's own
    /// below its measured crossover and O(M(n)) by a reciprocal above it, where num-bigint's
    /// `div_floor` alone grows as n^1.52 where measured (Burnikel and Ziegler over Toom-3).
    /// Tests:
    /// `l01_38_presburger::pncx_probe::floor_division_of_wide_solver_integers_is_exact`; the
    /// growth by `bench::pncx_probe::pncx_wide_floor_division_scales` (COMPLEXITY.md S48).
    // num-bigint 0.4.8 (src/biguint/division.rs) divides operands above 64 words by
    // C. Burnikel and J. Ziegler, "Fast Recursive Division", Max-Planck-Institut für Informatik
    // report MPI-I-98-1-022, 1998,
    // https://pure.mpg.de/rest/items/item_1819444_4/component/file_2599480/content,
    // Algorithm 1. Its section 2.2 sums the cost as
    // D(n) = sum_i 2^i M(n/2^i) + O(n log n), and Theorem 1 gives "2K(n) + O(n log n) steps"
    // for 2n digits by n over Karatsuba. Over Toom-3 (A. L. Toom, Soviet Math. Doklady 3, 1963;
    // S. A. Cook, PhD thesis, Harvard, 1966, pp. 51-53; R. P. Brent and P. Zimmermann, "Modern
    // Computer Arithmetic", v0.5.1, arXiv:1004.4710, section 1.3.3, p. 8, "O(n^ν) with
    // ν = log(2r − 1)/ log r" at r = 3 parts; all three read 2026-11-20 and quoted in
    // zed-kernel `num::fast`, module doc, "Sources"), M(n) = n^log3(5) = n^1.465, and the sum
    // is O(M(n)) since its terms 2^i M(n/2^i) = M(n) (2/2^1.465)^i fall geometrically; the
    // 1.52 above is the slope measured over the sizes tried, where Karatsuba's n^1.585 still
    // takes part (zed-kernel `num::fast::DIV_POWER`, 2.79 to 2.90 times per doubling).
    // Checked 2026-11-20: num-bigint's source read for which methods it uses; the report read
    // (section 2.2, Theorem 1). The tests named above check the
    // quotients and the growth, not which method num-bigint runs.
    pub fn div_floor(&self, m: &Int) -> Int {
        match (&self.0, &m.0) {
            // In 64 bits when both fit, where a 128-bit division is many times slower; the
            // one quotient that overflows, `MIN / -1`, is left to the next width.
            (Repr::Small(a), Repr::Small(b)) => match (i64::try_from(*a), i64::try_from(*b)) {
                (Ok(a), Ok(b)) if (a, b) != (i64::MIN, -1) => Integer::div_floor(&a, &b).into(),
                _ if (*a, *b) != (i128::MIN, -1) => Integer::div_floor(a, b).into(),
                _ => div_floor_int(&self.big(), &m.big()).into(),
            },
            _ => div_floor_int(&self.big(), &m.big()).into(),
        }
    }

    /// `self / m` rounded up, for `m` of either sign and not zero: `-((-self) div_floor m)`,
    /// since `ceil(x) = -floor(-x)`; one division, as [`Int::div_floor`].
    pub fn div_ceil(&self, m: &Int) -> Int {
        -&(-self).div_floor(m)
    }

    /// The integer nearest zero in `[lo, hi]`, a missing end being unbounded: 0 where the
    /// range holds it, else the end nearer zero; `max(lo, 0)` then `min(hi)`, so on an empty
    /// range (`lo > hi`) the answer is `hi` or 0, never past `hi`. The shared copy of seven
    /// in the Presburger solver (DRY-numeric-shared, REPORT-dryA5 row 19); before it, three
    /// of them answered `lo` instead on an empty range with `lo > 0`.
    pub fn nearest_zero(lo: Option<&Int>, hi: Option<&Int>) -> Int {
        let v = match lo {
            Some(l) if l.is_positive() => l.clone(),
            _ => Int::ZERO,
        };
        match hi {
            Some(h) if *h < v => h.clone(),
            _ => v,
        }
    }

    /// The remainder of [`Int::div_floor`], which has the sign of `m`, by the kernel's
    /// division past `i128` as there (`zed_kernel::num::mod_floor_int`).
    pub fn mod_floor(&self, m: &Int) -> Int {
        match (&self.0, &m.0) {
            // `MIN mod -1` is 0, but `rem` overflows computing it, as `MIN / -1` does.
            (Repr::Small(_), Repr::Small(-1)) => Int::ZERO,
            (Repr::Small(a), Repr::Small(b)) => match (i64::try_from(*a), i64::try_from(*b)) {
                (Ok(a), Ok(b)) => Integer::mod_floor(&a, &b).into(),
                _ => Integer::mod_floor(a, b).into(),
            },
            _ => mod_floor_int(&self.big(), &m.big()).into(),
        }
    }

    /// The symmetric remainder of `self` by `m` (Pugh's `a mod^ m` from the Omega test), for `m`
    /// not zero, with the sign of `m` ignored: `r == self (mod m)` and
    /// `-|m|/2 <= r <= |m|/2`. At exactly half of `|m|` it takes the sign opposite to `self`,
    /// so the function is odd, `(-a).mod_hat(m) == -(a.mod_hat(m))`, and an equality solved
    /// with its sign turned gives the same definition. Pugh's `a - m floor(a/m + 1/2)` lies in
    /// `[-m/2, m/2)` and is not odd at the tie (`-1 mod^ 2 == -1 == 1 mod^ 2`); both satisfy
    /// the two facts the Omega test's equality step needs, the congruence and `|r| <= m/2`.
    ///
    /// Source: W. Pugh, "A practical algorithm for exact array dependence analysis", Commun.
    /// ACM 35(8):102-114, 1992, doi:10.1145/135226.135233. Its "Equality Constraints"
    /// section (p. 103) takes `m = |a_k| + 1` for the coefficient `a_k` of least absolute
    /// value and defines "a mod^ b = a - b floor(a/b + 1/2)"; then `a_k mod^ m = -sign(a_k)`,
    /// a new variable `σ` gets the constraint `m σ = Σ (a_i mod^ m) x_i`, which is solved for
    /// `x_k`. Checked 2026-11-20 against Crossref and the paper's text. The Omega test was first
    /// published as W. Pugh, "The Omega test: a fast and practical integer programming
    /// algorithm for dependence analysis", Supercomputing '91, pp. 4-13, 1991,
    /// doi:10.1145/125826.125848 (Crossref checked; read 2026-11-21 in a scanned copy). Its
    /// sec. 2.2, "Equality constraints" (p. 5), gives the same step with the definition
    /// "a mod^ b = if a mod b < b/2 then a mod b else (a mod b) - b", the same function as the
    /// CACM floor form (a tie goes to `-b/2`), and bounds the work: each step "changes the
    /// absolute value of each coefficient by a multiplicative factor of at most 1/m + 1/2.
    /// Since m >= 3", the step is needed only O(log max |a_i|) times before a unit coefficient
    /// appears. Tested in
    /// `int::completeness`: `floor_and_ceiling_division_agree_with_num_integer_for_every_sign`
    /// checks the congruence, `|r| <= |m|/2` and oddness on machine and wide values of every
    /// sign, and `the_symmetric_remainder_at_half_the_modulus_is_odd` checks the tie. Neither
    /// checks Pugh's own tie rule, which this function departs from on purpose.
    pub fn mod_hat(&self, m: &Int) -> Int {
        let m = m.abs();
        let r = self.mod_floor(&m);
        match (&r + &r).cmp(&m) {
            Ordering::Less => r,
            Ordering::Greater => &r - &m,
            Ordering::Equal if self.is_negative() => r,
            Ordering::Equal => &r - &m,
        }
    }

    /// `ceil(log2 self)`, the least `k` with `2^k >= self`: 0 for `self <= 1`, as
    /// `zed_kernel::bits::BitLen::ceil_log2` is for a machine word. It is `bits(self - 1)` for
    /// `self >= 1`, O(1) past the subtraction; doubling a power until it reaches `self`, as
    /// negsssp did, takes `k` additions of up to `k` bits, O(k^2 / 64) word operations.
    pub fn ceil_log2(&self) -> u64 {
        if *self <= Int::ONE {
            0
        } else {
            (self - &Int::ONE).bits()
        }
    }

    /// `2^k`: one shift, O(k / 64) words, where doubling from 1 takes O(k^2 / 64).
    pub fn pow2(k: u64) -> Int {
        // 126 is the highest exponent whose power fits an `i128`, which `Small` holds.
        if k <= 126 {
            Int::from(1i128 << k)
        } else {
            Int::from(BigInt::one() << k)
        }
    }
}

impl Add for &Int {
    type Output = Int;

    fn add(self, other: &Int) -> Int {
        if let (Repr::Small(a), Repr::Small(b)) = (&self.0, &other.0)
            && let Some(v) = a.checked_add(*b)
        {
            return v.into();
        }
        (&*self.big() + &*other.big()).into()
    }
}

impl Sub for &Int {
    type Output = Int;

    fn sub(self, other: &Int) -> Int {
        if let (Repr::Small(a), Repr::Small(b)) = (&self.0, &other.0)
            && let Some(v) = a.checked_sub(*b)
        {
            return v.into();
        }
        (&*self.big() - &*other.big()).into()
    }
}

impl Mul for &Int {
    type Output = Int;

    fn mul(self, other: &Int) -> Int {
        if let (Repr::Small(a), Repr::Small(b)) = (&self.0, &other.0) {
            // Two values of 64 bits have a product that fits in 128, with no overflow test.
            if let (Ok(x), Ok(y)) = (i64::try_from(*a), i64::try_from(*b)) {
                return (i128::from(x) * i128::from(y)).into();
            }
            if let Some(v) = a.checked_mul(*b) {
                return v.into();
            }
        }
        mul_int(&self.big(), &other.big()).into()
    }
}

/// The bitwise and of two integers, each read as an infinite two's-complement word: a
/// negative integer has every bit set above its width (`-1 & 5 == 5`, `-4 & -3 == -4`).
impl BitAnd for &Int {
    type Output = Int;

    fn bitand(self, other: &Int) -> Int {
        if let (Repr::Small(a), Repr::Small(b)) = (&self.0, &other.0) {
            return (a & b).into();
        }
        (&*self.big() & &*other.big()).into()
    }
}

impl Neg for &Int {
    type Output = Int;

    fn neg(self) -> Int {
        if let Repr::Small(a) = self.0
            && let Some(v) = a.checked_neg()
        {
            return v.into();
        }
        (-&*self.big()).into()
    }
}

/// `floor(n / d)` in `i128`, for `d` of either sign: `None` when `d` is 0 or the quotient
/// does not fit (only `MIN / -1`). From the Euclidean quotient `q`, with `n = q·d + r` and
/// `0 <= r < |d|`: `n/d = q + r/d`, so the floor is `q` for `d > 0` and `q - [r != 0]` for
/// `d < 0`. `q - 1` cannot overflow, as `r != 0` needs `|d| >= 2`, so `|q| <= |n|/2 + 1`.
/// It negates nothing, so `n = MIN` gives every quotient that fits; the form
/// `-((-n) div d)` answers `None` there. The shared copy of the checked integer division
/// that several `i128` paths of the solvers wrote out by hand (DRY-numeric-shared).
pub fn i128_div_floor(n: i128, d: i128) -> Option<i128> {
    let q = n.checked_div_euclid(d)?;
    let exact = n.checked_rem_euclid(d)? == 0;
    Some(if d < 0 && !exact { q - 1 } else { q })
}

/// `ceil(n / d)` in `i128`, for `d` of either sign, as [`i128_div_floor`]: the ceiling of
/// `q + r/d` is `q + [r != 0]` for `d > 0` (where `r != 0` needs `d >= 2`, so `q + 1` fits)
/// and `q` for `d < 0`.
pub fn i128_div_ceil(n: i128, d: i128) -> Option<i128> {
    let q = n.checked_div_euclid(d)?;
    let exact = n.checked_rem_euclid(d)? == 0;
    Some(if d > 0 && !exact { q + 1 } else { q })
}

/// An integer range `[lo, hi]`, an end `None` when unbounded; empty when `lo > hi`.
pub type IntRange = (Option<Int>, Option<Int>);

/// The integers `x` with `a·x + k >= 0`, or `a·x + k == 0` when `eq`, for `a` not zero, and
/// whether `eq` has no integer root. `a·x + k >= 0` is `x >= ⌈-k / a⌉` for `a > 0` and
/// `x <= ⌊k / -a⌋` for `a < 0`; an equality is the point `⌈-k / a⌉`, the root when `a`
/// divides `k` (with the flag set, a caller reads the row as empty). Shared by the readings
/// of single-atom rows in `zedc-presburger` (DRY-numeric-shared; one copy per reader before).
/// One or two floor divisions, O(M(n)) each above the kernel's crossover.
pub fn row_range(a: &Int, k: &Int, eq: bool) -> (IntRange, bool) {
    if eq {
        let v = -&k.div_floor(a);
        ((Some(v.clone()), Some(v)), !k.mod_floor(a).is_zero())
    } else if a.is_positive() {
        ((Some(row_bound(a, k)), None), false)
    } else {
        ((None, Some(row_bound(a, k))), false)
    }
}

/// The one finite end of [`row_range`]`(a, k, false)`, for `a` not zero: the least `x` with
/// `a·x + k >= 0`, `⌈-k / a⌉`, for `a > 0`, and the greatest, `⌊k / -a⌋`, for `a < 0`. For a
/// caller that branches on the sign of `a` itself (DRY-numeric-shared-rest). Why the ends: for
/// `a > 0`, `a·x + k >= 0` is `x >= -k / a`, so the least int is `⌈-k / a⌉`; for `a < 0` it is
/// `x <= k / -a`, so the greatest is `⌊k / -a⌋`. One floor division and at most one negation,
/// since `⌈-y⌉ = -⌊y⌋` for every rational `y` gives `⌈-k / a⌉ = -⌊k / a⌋`.
pub fn row_bound(a: &Int, k: &Int) -> Int {
    if a.is_positive() {
        -&k.div_floor(a)
    } else {
        k.div_floor(&-a)
    }
}

/// `cur` narrowed to its meet with `add`; whether the meet is empty (`lo > hi`).
pub fn meet_range(cur: &mut IntRange, add: IntRange) -> bool {
    if let Some(lo) = add.0
        && cur.0.as_ref().is_none_or(|v| lo > *v)
    {
        cur.0 = Some(lo);
    }
    if let Some(hi) = add.1
        && cur.1.as_ref().is_none_or(|v| hi < *v)
    {
        cur.1 = Some(hi);
    }
    range_is_empty(cur)
}

/// The meet of `a` and `b`, as [`meet_range`] but by value.
pub fn range_meet(a: &IntRange, b: &IntRange) -> IntRange {
    let mut out = a.clone();
    meet_range(&mut out, b.clone());
    out
}

/// Whether `r` holds no integer (`lo > hi`).
pub fn range_is_empty(r: &IntRange) -> bool {
    matches!(r, (Some(l), Some(h)) if l > h)
}

impl Ord for Int {
    fn cmp(&self, other: &Int) -> Ordering {
        match (&self.0, &other.0) {
            (Repr::Small(a), Repr::Small(b)) => a.cmp(b),
            (Repr::Big(a), Repr::Big(b)) => a.cmp(b),
            // A big value lies outside every small one.
            (Repr::Big(a), Repr::Small(_)) => {
                if a.sign() == Sign::Minus {
                    Ordering::Less
                } else {
                    Ordering::Greater
                }
            }
            (Repr::Small(_), Repr::Big(b)) => {
                if b.sign() == Sign::Minus {
                    Ordering::Greater
                } else {
                    Ordering::Less
                }
            }
        }
    }
}

impl PartialOrd for Int {
    fn partial_cmp(&self, other: &Int) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Unbounded, so every value has a next and a previous one: the interval lists of
/// `zed_collections::intervals` run over `Int` ends.
impl zed_collections::intervals::Discrete for Int {
    #[inline]
    fn succ(&self) -> Option<Int> {
        Some(self + &Int::ONE)
    }

    #[inline]
    fn pred(&self) -> Option<Int> {
        Some(self - &Int::ONE)
    }

    #[inline]
    fn at_most_succ(&self, other: &Int) -> bool {
        // Without forming `other + 1` where the order alone answers, or where both are wide.
        self <= other
            || match (&self.0, &other.0) {
                (Repr::Big(a), Repr::Big(b)) => is_succ(a, b),
                _ => *self <= other + &Int::ONE,
            }
    }
}

/// Whether `a == b + 1`, read from the digits of both without forming `b + 1`. The sum of two
/// wide ends allocated as many bytes as the ends hold at each merge of two intervals that do not
/// meet, `Θ(k²)` bytes over the `k` merges of a chain whose ends grow to `Θ(k)` bits; it was the
/// largest share of the bytes that grew faster than `n log n` in `l01_25_preimage_catalog`
/// `bench::s22::chain_t3_gaps_five_no_scales` (0.73 MB at 256 and 21.8 MB at 2048, under DHAT;
/// S22-scaling-10_5). The work is that of the sum, `O(w)` for ends of `w` words.
///
/// Proof: for `b >= 0`, `b + 1 = |b| + 1 > 0`, so `a == b + 1` exactly when `a > 0` and
/// `|a| == |b| + 1`. For `b < 0`, `b + 1 = -(|b| - 1) <= 0`, so `a == b + 1` exactly when
/// `a <= 0` and `|a| == |b| - 1`, that is `|b| == |a| + 1` (`b = -1` gives `a = 0`, `|a| + 1 =
/// 1 = |b|`).
fn is_succ(a: &BigInt, b: &BigInt) -> bool {
    match b.sign() {
        Sign::Minus => a.sign() != Sign::Plus && magnitude_is_succ(b.magnitude(), a.magnitude()),
        Sign::NoSign | Sign::Plus => {
            a.sign() == Sign::Plus && magnitude_is_succ(a.magnitude(), b.magnitude())
        }
    }
}

/// Whether `x == y + 1`. Adding 1 to `y` adds it to its lowest 64-bit digit and carries through
/// each digit that was `u64::MAX`, turning it to 0, so the digits of `y + 1` are made one at a
/// time from those of `y` and compared with those of `x`; a carry out of the top digit is one
/// more digit, 1. `BigUint` keeps no leading zero digits, and neither has `y + 1` (its top digit
/// is that of `y` or more, or the carried 1), so equal values have equal digit lists. `y = 0`
/// has no digits and `y + 1` is the one digit 1.
fn magnitude_is_succ(x: &BigUint, y: &BigUint) -> bool {
    let mut xs = x.iter_u64_digits();
    let mut carry = true;
    for d in y.iter_u64_digits() {
        let (sum, out) = d.overflowing_add(u64::from(carry));
        if xs.next() != Some(sum) {
            return false;
        }
        carry = out;
    }
    match carry {
        true => xs.next() == Some(1) && xs.next().is_none(),
        false => xs.next().is_none(),
    }
}

/// Unbounded, so the sum cannot overflow: the binary searches of
/// `zed_collections::search` run over `Int`.
impl zed_collections::search::Midpoint for Int {
    #[inline]
    fn mid_down(lo: &Int, hi: &Int) -> Int {
        (lo + hi).div_floor(&Int::from(2))
    }

    #[inline]
    fn mid_up(lo: &Int, hi: &Int) -> Int {
        (&(lo + hi) + &Int::ONE).div_floor(&Int::from(2))
    }
}

impl fmt::Display for Int {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.0 {
            Repr::Small(v) => write!(f, "{v}"),
            Repr::Big(v) => write_decimal(f, v),
        }
    }
}

/// The form of a [`Num`]. A value that fits in `i64` is always `Small`; a value outside `i64`
/// is `Big`, or `Kept` when it was made from a power and lies outside `i128`. A `Big` and a
/// `Kept` may hold the same value, so equality and hashing go by value, not by form.
#[derive(Clone, Debug)]
enum Word {
    Small(i64),
    Big(Arc<BigInt>),
    Kept(Box<Kept>),
}

/// `(c_1 * core_1 + ... + c_n * core_n + d) / den`, kept unexpanded, where each core is a
/// product of powers of integers and of floor roots. A bound such as that of
/// `x ^ 100000000 + 1`, `3 ^ 100000000 + 5 ^ 99999999` or `floor(2 ^ (100000000 / 3))` is
/// then built and compared in time polynomial in the bits of the numbers written here, not in
/// the bits of the value. Invariants: `n >= 1`; the cores are in decreasing order of value and
/// no two are equal by [`Core::same`]; no `c_i` is zero; the terms whose cores are powers of
/// one integer are folded ([`fold`]); `den >= 1` divides the numerator; the `c_i`, `d` and
/// `den` have no common factor; the value lies outside `i128`, and `negative` is its sign.
/// Equal values may have different forms.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Kept {
    terms: Vec<(BigInt, Core)>,
    d: BigInt,
    den: BigUint,
    negative: bool,
}

/// A factor of a [`Core`].
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Atom {
    /// An integer at least 2.
    Int(BigUint),
    /// `floor(rad ^ (1 / k))`, with `k >= 2`, `rad` above zero with cores of `Int` atoms only,
    /// and the root at least `2^127`. A root of a root is one root of the first radicand, so
    /// the nesting stops here.
    Root {
        rad: Box<Kept>,
        k: BigUint,
        memo: Memo,
    },
}

/// The finest approximation of a root found so far, with its precision in bits. A root is
/// approximated by bisection, at a cost of `O(bits)` products per call, and one root is met by
/// many comparisons and sums, so each approximation is kept, shared by every copy of the atom,
/// and a coarser one is its truncation. It takes no part in the order or equality of atoms.
#[derive(Clone, Debug, Default)]
struct Memo(Arc<Mutex<Option<(u64, Approx)>>>);

impl Memo {
    fn get(&self) -> std::sync::MutexGuard<'_, Option<(u64, Approx)>> {
        self.0
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
    }
}

impl PartialEq for Memo {
    fn eq(&self, _: &Memo) -> bool {
        true
    }
}

impl Eq for Memo {}

impl PartialOrd for Memo {
    fn partial_cmp(&self, o: &Memo) -> Option<Ordering> {
        Some(self.cmp(o))
    }
}

impl Ord for Memo {
    fn cmp(&self, _: &Memo) -> Ordering {
        Ordering::Equal
    }
}

/// `a_1 ^ e_1 * ... * a_m ^ e_m`, with `m >= 1`, the atoms distinct and in increasing order,
/// and every `e_i >= 1`.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Core(Vec<(Atom, BigUint)>);

/// `base ^ exp`, written out by zed-bignum `fast::pow` (DRY-bignum-crate-2026-11-26: this was a
/// second power by squaring with the same product): its cost is that of the value's digits.
/// For a base above 1 an exponent of 2^64 or more makes a value of more than 2^64 bits, which no
/// memory holds, so the panic stops only a build that could not finish.
fn expand_pow(base: &BigUint, exp: &BigUint) -> BigUint {
    match (u64::try_from(exp), base.bits()) {
        (Ok(e), _) => pow_uint(base, e),
        (Err(_), 0 | 1) => base.clone(),
        (Err(_), _) => panic!("a power of more than 2^64 bits written out"),
    }
}

impl Atom {
    /// The value to `bits` bits.
    fn approx(&self, bits: u64) -> Approx {
        match self {
            Atom::Int(b) => Approx::of(&BigInt::from(b.clone()), bits),
            Atom::Root { rad, k, memo } => {
                if let Some((have, a)) = &*memo.get()
                    && *have >= bits
                {
                    return a.clone().truncate(bits);
                }
                let a = root_approx(rad, k, bits).0;
                *memo.get() = Some((bits, a.clone()));
                a
            }
        }
    }

    /// The value, written out: for a root, its cost is that of a root of the radicand's
    /// digits.
    fn expand(&self) -> BigUint {
        match self {
            Atom::Int(b) => b.clone(),
            // By the kernel's `nth_root_rem_uint`, O(M(n)) for a fixed `k`, where num-bigint's
            // `nth_root` is above it (item PERF-wide-odd-base-ratio-9).
            Atom::Root { rad, k, .. } => {
                nth_root_rem_uint(
                    &rad.expand().into_parts().1,
                    u64::try_from(k)
                        .expect("a root of at least 2^127 of a radicand held in memory"),
                )
                .0
            }
        }
    }

    /// Bounds on the bits of the value and of the widest number [`Atom::expand`] builds.
    fn widths(&self) -> (BigUint, BigUint) {
        match self {
            Atom::Int(b) => (BigUint::from(b.bits()), BigUint::from(b.bits())),
            Atom::Root { rad, k, .. } => {
                let (value, widest) = rad.widths();
                (value / k + 1u32, widest)
            }
        }
    }
}

impl Core {
    /// `base ^ exp`, for `base >= 2`, over the least integer of which `base` is a power
    /// ([`least_root`]): `9 ^ e` is `3 ^ (2 * e)`, so that equal powers of integers are
    /// equal in form, and powers of one integer fold ([`fold`]).
    fn power(base: BigUint, exp: BigUint) -> Core {
        let (base, m) = least_root(base);
        Core(vec![(Atom::Int(base), exp * m)])
    }

    /// The base and exponent of a power of one integer.
    fn int_power(&self) -> Option<(&BigUint, &BigUint)> {
        match self.0.as_slice() {
            [(Atom::Int(b), e)] => Some((b, e)),
            _ => None,
        }
    }

    /// Whether every atom is an integer, so that the value has residues without its digits.
    fn is_int(&self) -> bool {
        self.0.iter().all(|(a, _)| matches!(a, Atom::Int(_)))
    }

    /// The greatest common divisor of the exponents: the value is a perfect power of it.
    fn exps_gcd(&self) -> BigUint {
        self.0
            .iter()
            .fold(BigUint::ZERO, |g, (_, e)| gcd_uint(&g, e))
    }

    /// Whether two cores have one value. The atoms on which they differ in form are taken
    /// from both by one merge of their atom lists, with exponents less those of the other;
    /// the integers among them are written over their natural coprime base (zed-kernel's
    /// `num::coprime::coprime_base_exponents`), on which a product of powers has one form, so
    /// `6 ^ e * 5 ^ f` and `2 ^ e * 3 ^ e * 5 ^ f` are found equal by 6, 2 and 3 alone. The
    /// cost is that of the coprime base of the integers written differently, nothing for the
    /// atoms the cores share; for a few roots of one word each (6, 2 and 3) the kernel's word
    /// path, O(k^2) word gcds for `k` roots up to its measured switchover `WORD_INPUTS`; for
    /// one wide root among a few small ones (`3^n * 2` against 3 and 2) the kernel's one-wide
    /// path, O(M(n)) at a fixed width of the small ones.
    // Complexity tradeoff: two cores whose roots differ in form are taken to differ here,
    // though two roots of different radicands may have one value (the floor cube roots of
    // `2 ^ (3 * e + 1)` and of `2 ^ (3 * e + 1) + 1`), so such cores are found equal only by
    // `value_cmp_at` once the approximations are exact, at the bits of the value; the answer
    // stays exact. Why: whether two floor roots are equal is whether a `k`-th power lies
    // between their radicands, which needs the roots' digits. Trigger: a sum, difference or
    // comparison of kept values holding roots of different radicands with one floor. Test:
    // `l01_24_refinement_lattices::ends::kept_values_with_no_kept_form_are_written_out`
    // (the two cube roots above); COMPLEXITY.md S33. A complete solution would keep a root in
    // a form that a floor determines, as the least radicand with that floor, found as a kept
    // value: the open case of a root of a sum at `Kept::root`. Naive version: every pair of
    // cores compared by `value_cmp_at`, at the bits of the value; used: a form comparison at
    // the cost of the coprime base, with `value_cmp_at` only for roots of differing radicands.
    fn same(&self, o: &Core) -> bool {
        if self == o {
            return true;
        }
        let mut l: Vec<(&Atom, Cow<'_, BigUint>)> = Vec::new();
        let mut r = Vec::new();
        for j in merge_join(&self.0, &o.0, |x, y| x.0.cmp(&y.0)) {
            match j {
                Joined::Left((a, e)) => l.push((a, Cow::Borrowed(e))),
                Joined::Right((b, f)) => r.push((b, Cow::Borrowed(f))),
                Joined::Both((a, e), (b, f)) => match e.cmp(f) {
                    Ordering::Less => r.push((b, Cow::Owned(f - e))),
                    Ordering::Greater => l.push((a, Cow::Owned(e - f))),
                    Ordering::Equal => {}
                },
            }
        }
        fn ints<'a>(
            v: &'a [(&'a Atom, Cow<'a, BigUint>)],
        ) -> Option<Vec<(&'a BigUint, &'a BigUint)>> {
            v.iter()
                .map(|(a, e)| match a {
                    Atom::Int(b) => Some((b, &**e)),
                    Atom::Root { .. } => None,
                })
                .collect()
        }
        let (Some(l), Some(r)) = (ints(&l), ints(&r)) else {
            return false;
        };
        // A product of powers of integers at least 2 is 1 only when it is empty.
        if l.is_empty() || r.is_empty() {
            return false;
        }
        // The roots of both sides in one list, `l` first, so that the multiplicities of the
        // first `l.len()` are those of `l`.
        let roots: Vec<&BigUint> = l.iter().chain(&r).map(|(b, _)| *b).collect();
        let base = coprime_base_exponents(&roots);
        let (kl, kr) = base.exponents.split_at(l.len());
        // The exponent of each element in `prod b ^ e`: the sum of `e * k` over the roots `b`
        // in which the element has multiplicity `k`.
        let over = |side: &[(&BigUint, &BigUint)], ks: &[Vec<(u32, u64)>]| {
            let mut out = vec![BigUint::ZERO; base.elements.len()];
            for ((_, e), k) in side.iter().zip(ks) {
                for &(c, k) in k {
                    out[c as usize] += *e * k;
                }
            }
            out
        };
        over(&l, kl) == over(&r, kr)
    }

    /// The order of the values, given `a = self.approx(64)` and `b = o.approx(64)`: equal in
    /// form, else at 64 bits, else for two powers of one integer by their exponents, else by
    /// [`Core::same`], else by bounds on their binary logarithms ([`Core::log2_bounds`]), else
    /// at twice as many bits and more until they are apart. Equal values agree at 64 bits, so
    /// `same` runs only for cores that do. The caller
    /// (`collect`) computes each core's `approx(64)` once for all its comparisons.
    // Complexity tradeoff: the powers and the logarithms' bounds are tried only once the 64-bit
    // approximations overlap, so a sum whose cores those part (`kept_sum`) pays nothing more.
    // They are needed for a power `b ^ e` of an exponent of more than about 64 bits: its
    // approximation at `p` bits is off by a factor of about `2^(e 2^-p)`, so its lower end
    // stays above 0 only once `p` passes the bits of `e`, and `approx_cmp` doubled `p` to
    // there, about `bits(e)` products of `bits(e)`-bit numbers a round (item
    // PERF-num-kept-multi-term-precision); the bounds of `e log2(b)` cost one product of `e` by
    // a 72-bit word. Cores whose logarithms differ by less than the bounds' width, about `e
    // 2^-64`, still go to the doubling, since no bound used here says how near two such
    // logarithms can be without being equal; the answer is exact either way. Test:
    // `l01_24_refinement_lattices::past_i64::bench::differences_of_powers_by_an_exponent_of_n_bits_scale_with_its_bits`;
    // COMPLEXITY.md row PERF-num-kept-multi-term-precision.
    fn value_cmp_at(&self, a: &Approx, o: &Core, b: &Approx) -> Ordering {
        if self == o {
            return Ordering::Equal;
        }
        if a.below(b) {
            return Ordering::Less;
        }
        if b.below(a) {
            return Ordering::Greater;
        }
        // `b ^ e` against `b ^ f` for `b >= 2`: `b ^ x` rises with `x`.
        if let (Some((b1, e1)), Some((b2, e2))) = (self.int_power(), o.int_power())
            && b1 == b2
        {
            return e1.cmp(e2);
        }
        // Equal values agree at 64 bits and their logarithms' bounds always overlap, so `same`
        // runs first and spares them the bounds.
        if self.same(o) {
            return Ordering::Equal;
        }
        // Bounds `l <= 2^64 log2(value) <= h` that are apart order the values, `log2` being
        // increasing.
        if let (Some((l1, h1)), Some((l2, h2))) = (self.log2_bounds(), o.log2_bounds()) {
            if h1 < l2 {
                return Ordering::Less;
            }
            if h2 < l1 {
                return Ordering::Greater;
            }
        }
        approx_cmp(128, |bits| self.approx(bits), |bits| o.approx(bits))
    }

    /// The product.
    fn times(&self, o: &Core) -> Core {
        if let (Some((b1, e1)), Some((b2, e2))) = (self.int_power(), o.int_power())
            && e1 == e2
            && b1 != b2
        {
            return Core::power(b1 * b2, e1.clone());
        }
        // Both factor lists are in the order of their atoms: merge them, adding the exponents
        // of an atom both hold.
        Core(merge_with(
            &self.0,
            &o.0,
            |x, y| x.0.cmp(&y.0),
            |j| match j {
                Joined::Left(x) | Joined::Right(x) => Some(x.clone()),
                Joined::Both((a, e), (_, f)) => Some((a.clone(), e + f)),
            },
        ))
    }

    /// `self ^ k`.
    fn pow(&self, k: &BigUint) -> Core {
        Core(self.0.iter().map(|(a, e)| (a.clone(), e * k)).collect())
    }

    /// `self ^ (1 / k)`, when `k` divides every exponent.
    fn exact_root(&self, k: &BigUint) -> Option<Core> {
        self.0
            .iter()
            .map(|(a, e)| e.is_multiple_of(k).then(|| (a.clone(), e / k)))
            .collect::<Option<Vec<_>>>()
            .map(Core)
    }

    /// The value to `bits` bits.
    fn approx(&self, bits: u64) -> Approx {
        #[cfg(test)]
        tests::CORE_APPROXES.with(|n| n.set(n.get() + 1));
        #[cfg(test)]
        tests::CORE_APPROX_BITS.with(|n| n.set(n.get().max(bits)));
        self.0
            .iter()
            .map(|(a, e)| a.approx(bits).pow(e, bits))
            .reduce(|p, q| p.mul(&q, bits))
            .expect("a core has a factor")
    }

    /// The value, written out: its cost is that of the value's digits, and for a root that of
    /// a root of the radicand's digits.
    fn expand(&self) -> BigUint {
        // The powers multiplied by pairs (`product_of`), not in turn (DRY-bignum-crate-2026-11-26).
        let powers: Vec<BigUint> = (self.0.iter())
            .map(|(a, e)| expand_pow(&a.expand(), e))
            .collect();
        product_of(&powers)
    }

    /// Bounds on the bits of the value and of the widest number [`Core::expand`] builds: each
    /// power and each partial product is at most the value, every factor being at least 1.
    fn widths(&self) -> (BigUint, BigUint) {
        let (mut value, mut widest) = (BigUint::ZERO, BigUint::ZERO);
        for (a, e) in &self.0 {
            let (v, w) = a.widths();
            value += e * v;
            widest = widest.max(w);
        }
        let widest = widest.max(value.clone());
        (value, widest)
    }

    /// A lower bound `L` on `floor(log2(value))`, so `value >= 2^L`: an integer atom `a` is at
    /// least `2^(bits(a) - 1)`, and a root at least `2^127` by the invariant of [`Atom::Root`],
    /// so `a ^ e` is at least `2^(e * (bits(a) - 1))` or `2^(e * 127)`, and the product of
    /// the powers at least `2` to the sum. O(m) products of an exponent by a word.
    fn least_log2(&self) -> BigUint {
        self.0
            .iter()
            .map(|(a, e)| match a {
                Atom::Int(b) => e * (b.bits() - 1),
                Atom::Root { .. } => e * 127u32,
            })
            .sum()
    }

    /// Integers `(l, h)` with `l <= 2^64 log2(value) <= h`, or `None` when a factor is a root:
    /// the sum over the factors `b ^ e` of `e` times the bounds of `log2_bounds(b, 64)`
    /// (zed-numtheory), since `log2` of a product is the sum of the logarithms of its factors
    /// and `log2(b ^ e) = e log2(b)` with `e >= 0`. The width is the sum of `e` times 1 or 2.
    /// O(m) logarithms of words to 64 bits and products of an exponent by a word, for `m`
    /// factors.
    fn log2_bounds(&self) -> Option<(BigInt, BigInt)> {
        let (mut l, mut h) = (BigInt::ZERO, BigInt::ZERO);
        for (a, e) in &self.0 {
            let Atom::Int(b) = a else { return None };
            let (lb, hb) = log2_bounds(b, LOG2_BITS);
            l += BigInt::from(e * lb);
            h += BigInt::from(e * hb);
        }
        Some((l, h))
    }

    /// The value modulo `n >= 1`, by `modpow`, or `None` when a factor is a root, whose
    /// digits are not known.
    fn residue(&self, n: &BigUint) -> Option<BigUint> {
        self.0
            .iter()
            .try_fold(BigUint::from(1u32) % n, |r, (a, e)| {
                let Atom::Int(b) = a else { return None };
                Some(r * b.modpow(e, n) % n)
            })
    }
}

/// `v = q * b ^ g + r` with `r` in `(-b ^ g / 2, b ^ g / 2]`, as `(r, q)`. When the bits of
/// `b` and `g` show that `b ^ g` exceeds `2 * |v|`, then `r = v` and `q = 0` with no power
/// computed, so a power is computed only when it has at most about twice the bits of `v`.
fn balance(v: BigInt, b: &BigUint, g: &BigUint) -> (BigInt, BigInt) {
    // 2 * |v| < 2^lim, and b ^ g >= 2^(g * (bits(b) - 1)).
    let lim = v.bits() + 1;
    let Some(g) = u64::try_from(g)
        .ok()
        .filter(|g| g.saturating_mul(b.bits() - 1) < lim)
    else {
        return (v, BigInt::ZERO);
    };
    let m = BigInt::from(pow_uint(b, g));
    let mut r = Integer::mod_floor(&v, &m);
    if (&r << 1u32) > m {
        r -= &m;
    }
    let q = (v - &r) / m;
    (r, q)
}

/// Folds the terms whose cores are powers of one integer `b`: in increasing order of exponent,
/// each coefficient but the last is brought into `(-b ^ g / 2, b ^ g / 2]`, with `g` the gap
/// to the next exponent, and the rest carried to the next. The lower terms of such a group
/// then add to less than its top term in magnitude, so the group is zero exactly when it has
/// no terms left, has the sign of its top coefficient, and is at least a quarter of its top
/// term for `b >= 3` (for `b = 2`, at least `2^-n` of it with `n` terms). `3 ^ (e + 1) -
/// 3 * 3 ^ e` folds to nothing, and `3 ^ (e + 1) - 3 ^ e - 2 * 3 ^ e` likewise, so a
/// difference of equal values in such forms is found to be zero with no digits written out.
/// A power of an integer is kept as a power of its least root (`Core::power`), so `3 * 9 ^ e`
/// and `3 ^ (2 * e + 1)` are one group. The cost is one sort of the terms and, per term, a
/// power of `b` of at most about twice the bits of its coefficient.
// Complexity tradeoff: only powers of one integer are folded. Terms over products of powers of
// several integers, as `2 ^ (e + 1) * 5 ^ e` against `2 * 10 ^ e`, or over roots stay apart,
// so a sum of them that cancels in their high bits is found small, or zero, only once the
// approximations are exact, at the bits of the value; the answer stays exact. Why: a carry
// between two such terms runs along each integer of a coprime base of their cores at once,
// and the coefficients of a group then form a polynomial in several powers, not a number in
// one base; for a power of a root, the root's digits. Trigger: a sum or difference of kept
// values whose cores are products of powers of several integers, or powers of roots, and whose
// high bits cancel. Test:
// `l01_24_refinement_lattices::ends::kept_values_with_no_kept_form_are_written_out`;
// COMPLEXITY.md S33. A complete solution would write the cores of a sum over one coprime base
// of their integers (as `Core::same` does for two cores) and carry between terms along each
// base element, as `fold` does along one; a bound on the carries for terms whose exponents
// differ along several elements at once, which would make it exact, is not worked out.
fn fold(terms: &mut Vec<(BigInt, Core)>) {
    let mut idx: Vec<usize> = (0..terms.len())
        .filter(|&i| terms[i].1.int_power().is_some())
        .collect();
    idx.sort_by(|&i, &j| terms[i].1.int_power().cmp(&terms[j].1.int_power()));
    fn base(terms: &[(BigInt, Core)], i: usize) -> Option<&BigUint> {
        terms[i].1.int_power().map(|(b, _)| b)
    }
    let mut s = 0;
    while s < idx.len() {
        let mut t = s + 1;
        while t < idx.len() && base(terms, idx[t]) == base(terms, idx[s]) {
            t += 1;
        }
        let mut carry = BigInt::ZERO;
        for w in s..t {
            let i = idx[w];
            let v = std::mem::take(&mut terms[i].0) + carry;
            if w + 1 == t {
                terms[i].0 = v;
                carry = BigInt::ZERO;
                continue;
            }
            let (b, e) = terms[i].1.int_power().expect("a power");
            let (_, f) = terms[idx[w + 1]].1.int_power().expect("a power");
            let (r, q) = balance(v, b, &(f - e));
            terms[i].0 = r;
            carry = q;
        }
        s = t;
    }
    terms.retain(|(c, _)| !c.is_zero());
}

/// The bits after the point of the bounds on binary logarithms that order cores and place
/// sums ([`Core::log2_bounds`], [`Kept::dominant_sign`]). Why 64: the bounds of `e log2(b)`
/// are `e` units of `2^-64` wide, so they part powers whose logarithms differ by more than about
/// `e 2^-63`, which for exponents below `2^60` is any two that the 64-bit approximations do
/// not already part; a larger value would narrow the bounds for larger exponents at the cost
/// of `2 k` squarings per logarithm. Any value gives exact answers, since a case the bounds do
/// not decide goes to the approximations.
const LOG2_BITS: u32 = 64;

/// The terms in decreasing order of the values of their cores, with the coefficients of equal
/// cores added and zero ones dropped: `O(n log n)` comparisons of cores for `n` terms, and
/// one approximation of each core to 64 bits.
// Complexity tradeoff: each core is approximated to 64 bits once, before the sort, and the
// comparisons read those approximations (`Core::value_cmp_at`). Comparing by the former
// `Core::value_cmp` computed both approximations again at each comparison, about 5 per term
// for a sum of two collected sums (the merge of their two runs, the test of neighbors for
// equal cores); for a power `b ^ e` each is a power by `e` at 64 bits, `O(log e)` products.
// Both are `O(n log n)` comparisons; this lowers the constant. Measured on `kept_sum(0,
// 48000)`, a sum of sums built by halves (item FAIL-l0124-kept-sum-benches-rising-load,
// 2026-11-20): the setup of
// `l01_24_refinement_lattices::boundary::bench::negating_a_kept_sum_scales_with_its_terms`
// took about 14.9 s of its 15.0 s at load 29 before, and the whole bench 4.4 s at load 58
// after (COMPLEXITY.md row FAIL-l0124-kept-sum-benches-rising-load). Test:
// `tests::a_sum_of_kept_sums_approximates_each_core_once_in_collect`.
fn collect(mut terms: Vec<(BigInt, Core)>) -> Vec<(BigInt, Core)> {
    // One term has no order to find and no equal core to meet: no approximation, so one
    // kept power times a number is placed with none (`Num::kept`; item
    // PERF-fold-power-of-huge-exponent).
    if terms.len() <= 1 {
        terms.retain(|(c, _)| !c.is_zero());
        return terms;
    }
    let mut terms: Vec<(BigInt, Core, Approx)> = terms
        .into_iter()
        .map(|(c, core)| {
            let a = core.approx(64);
            (c, core, a)
        })
        .collect();
    terms.sort_by(|x, y| y.1.value_cmp_at(&y.2, &x.1, &x.2));
    let mut out: Vec<(BigInt, Core, Approx)> = Vec::with_capacity(terms.len());
    for (c, core, a) in terms {
        match out.last_mut() {
            Some((c0, core0, a0)) if core0.value_cmp_at(a0, &core, &a) == Ordering::Equal => {
                *c0 += c
            }
            _ => out.push((c, core, a)),
        }
    }
    out.into_iter()
        .filter(|(c, _, _)| !c.is_zero())
        .map(|(c, core, _)| (c, core))
        .collect()
}

/// `floor(rad ^ (1 / k))` to `bits` bits, for `rad` above zero, with whether `rad` is a
/// perfect `k`-th power when that is decided at this precision. The root `y` is found to
/// `bits` bits as `r * 2^t` by bisection on `r`, each step comparing `(r * 2^t) ^ k` with
/// `rad` at `bits` bits, so the cost is `O(bits * bits of k)` products of `bits`-bit numbers,
/// whatever the size of `rad` or `k`. Only a step that both bounds certify moves a bound, so
/// the range always holds `y`. Once `bits` reaches the bits of `rad`, every comparison is
/// exact and `t` is 0, so the floor is found exactly.
// Complexity tradeoff: bisection takes `O(bits)` steps, so a root to `bits` bits costs
// `O(bits * bits of k)` products of `bits`-bit numbers, quadratic in `bits` where Newton's
// method would take `O(log bits)` steps; the answer is exact. Why: each bisection step needs
// only a power and a comparison, both certified in interval arithmetic, while a Newton step
// on intervals needs a division and a proof that the step keeps the root inside its range.
// Trigger: comparing a kept root with a value that agrees with it in many leading bits, as
// `5 ^ (k / 2)` against the square root of `3 ^ k + 5 ^ k`, which needs about `0.26 * k`
// bits. Test: `l01_24_refinement_lattices::ends::kept_forms_compute_as_their_values_written_out`
// (roots compared with their neighbors one apart); COMPLEXITY.md S33. A complete solution
// would refine the root by interval Newton steps from the bisection bracket, doubling the
// bits each step.
fn root_approx(rad: &Kept, k: &BigUint, bits: u64) -> (Approx, Option<bool>) {
    let a = rad.approx(bits);
    let k_int = BigInt::from(k.clone());
    // rad >= 2^l_min, and rad >= 1 since it is an integer above zero.
    let l_min = if a.lo.sign() == Sign::Plus {
        (&a.shift + (a.lo.bits() - 1)).max(BigInt::ZERO)
    } else {
        BigInt::ZERO
    };
    // rad < 2^l_max.
    let l_max = &a.shift + a.hi.bits();
    // 2^q_min <= y < 2^q_max.
    let q_min = Integer::div_floor(&l_min, &k_int);
    let q_max = Integer::div_ceil(&l_max, &k_int);
    let t = (&q_min - bits).max(BigInt::ZERO);
    // `at` is called with `q_min` and `q_max` only. `q - t >= 0`: `l_min >= 0`, so `q_min >= 0`
    // and `q_max >= q_min` (`l_max >= l_min`, since `rad < 2^l_max` and `rad >= 2^l_min`);
    // when `t == 0` this is `q >= 0`, and when `t > 0`, `q - t >= q_min - t == bits >= 0`.
    // That `q - t` fits a `u64`: when `t > 0`, `q_max - t <= bits + (l_max - l_min) / k + 2`,
    // and `l_max - l_min` is the difference of the bits of `a.hi` and `a.lo` plus 1, both
    // held in memory. Not proved: the case `t == 0` with `a.lo <= 0` (the interval of `rad`
    // reaches 0, as a kept sum of large terms that nearly cancel can), where `l_min` is 0 and
    // `q_max` is bounded only by `l_max = a.shift + a.hi.bits()`, the bits of the upper end of
    // `rad`, which for a kept power could exceed `2^64` with `k` small; no test reaches it.
    let at = |q: &BigInt| {
        BigInt::from(1u32) << u64::try_from(&(q - &t)).expect("at most the bits of the bound")
    };
    let pow = |r: &BigInt| {
        Approx {
            lo: r.clone(),
            hi: r.clone(),
            shift: t.clone(),
        }
        .pow(k, bits)
    };
    // The largest r with (r * 2^t) ^ k <= rad certified: r_lo = at(q_min) holds by the
    // bound, and at(q_max) is past y.
    let (mut lo, mut hi) = (at(&q_min), at(&q_max));
    while &hi - &lo > BigInt::from(1u32) {
        let mid: BigInt = (&lo + &hi) >> 1u32;
        if pow(&mid).hi_at_most(&a.lo, &a.shift) {
            lo = mid;
        } else {
            hi = mid;
        }
    }
    let r_lo = lo;
    // The least r with (r * 2^t) ^ k > rad certified.
    let (mut lo, mut hi) = (at(&q_min), at(&q_max));
    while &hi - &lo > BigInt::from(1u32) {
        let mid: BigInt = (&lo + &hi) >> 1u32;
        if a.below(&pow(&mid)) {
            hi = mid;
        } else {
            lo = mid;
        }
    }
    let r_hi = hi;
    if t.is_zero() && r_hi == &r_lo + 1u32 {
        let p = pow(&r_lo);
        let perfect = if p.is_exact()
            && a.is_exact()
            && scaled_cmp(&p.lo, &p.shift, &a.lo, &a.shift) == Ordering::Equal
        {
            Some(true)
        } else if p.below(&a) {
            Some(false)
        } else {
            None
        };
        return (Approx::exact(r_lo), perfect);
    }
    (
        Approx {
            lo: r_lo,
            hi: r_hi,
            shift: t,
        },
        None,
    )
}

impl Kept {
    /// The value to `bits` bits.
    fn approx(&self, bits: u64) -> Approx {
        self.terms
            .iter()
            .fold(Approx::of(&self.d, bits), |s, (c, core)| {
                s.add(&Approx::of(c, bits).mul(&core.approx(bits), bits), bits)
            })
            .div(&self.den, bits)
    }

    /// Whether the value is negative, when one term `c_j * core_j` outweighs the others and
    /// `d` so far that the value lies outside `i128` with the sign of `c_j`; `None` when the
    /// bounds below do not show that, or a core holds a root. For the term it picks the one
    /// whose lower bound on `log2 |c * core|` is largest; any choice is sound.
    ///
    /// Proof. Write `K = 2^64`, `lo(x)` and `hi(x)` for the ends of `log2_bounds(x, 64)`, so
    /// `lo(x) <= K log2(x) <= hi(x)`, and `(l_i, h_i)` for `core_i.log2_bounds()`. For each
    /// `i != j`, `D_i` below satisfies `|c_i core_i| <= 2^(D_i / K) core_j`:
    /// - `core_i = b ^ e_i` and `core_j = b ^ e_j` for one integer `b`: `core_i / core_j =
    ///   2^((e_i - e_j) log2(b))`, and `(e_i - e_j) log2(b) <= (e_i - e_j) lo(b) / K` when
    ///   `e_i < e_j`, `<= (e_i - e_j) hi(b) / K` otherwise; so `D_i = hi(|c_i|) + (e_i - e_j)
    ///   lo(b)` or `hi(|c_i|) + (e_i - e_j) hi(b)`. Measured from the difference of the
    ///   exponents, this stays narrow for exponents of any size, which the case below does not.
    /// - otherwise `|c_i core_i| <= 2^((hi(|c_i|) + h_i) / K)` and `core_j >= 2^(l_j / K)`, so
    ///   `D_i = hi(|c_i|) + h_i - l_j`.
    /// - for `d != 0`, likewise `D_d = hi(|d|) - l_j`.
    ///
    /// With `m >= 1` such others and `W` the largest `D`, their sum is at most `m 2^(W / K)
    /// core_j <= 2^((hi(m) + W) / K) core_j`. The test `hi(m) + W <= lo(|c_j|) - K` makes this
    /// at most `|c_j| core_j / 2`, so the numerator `c_j core_j + rest` has the sign of `c_j`
    /// and magnitude at least `|c_j| core_j / 2 >= 2^((lo(|c_j|) + l_j - K) / K)`. Divided by
    /// `den <= 2^(hi(den) / K)`, the value is at least `2^((lo(|c_j|) + l_j - K - hi(den)) /
    /// K)` in magnitude, and the test that this exponent is at least `128 K` puts it past
    /// `2^127`, outside `i128`. There the loop of [`Num::kept`] returns this form with
    /// `negative` set to the sign of the value, which is the sign of `c_j`: the same answer.
    ///
    /// Cost: O(n) logarithms of the coefficients, `d`, `den` and the cores' integers to 64 bits,
    /// each O(bits + 64 M(72)), and O(n) products of exponents by words, for `n` terms; none
    /// depends on the value's bits.
    fn dominant_sign(&self) -> Option<bool> {
        let unit = BigInt::from(1u32) << LOG2_BITS;
        let bounds = |x: &BigUint| {
            let (l, h) = log2_bounds(x, LOG2_BITS);
            (BigInt::from(l), BigInt::from(h))
        };
        let logs = (self.terms.iter())
            .map(|(_, core)| core.log2_bounds())
            .collect::<Option<Vec<_>>>()?;
        let coefficients: Vec<_> = (self.terms.iter())
            .map(|(c, _)| bounds(c.magnitude()))
            .collect();
        let low: Vec<BigInt> = (coefficients.iter().zip(&logs))
            .map(|((lc, _), (l, _))| lc + l)
            .collect();
        let j = (0..low.len()).max_by(|&x, &y| low[x].cmp(&low[y]))?;
        let (c_j, core_j) = &self.terms[j];
        let l_j = &logs[j].0;
        let mut worst: Option<BigInt> = None;
        let mut others = 0u64;
        for (i, (((_, core), (_, h)), (_, hc))) in
            (self.terms.iter().zip(&logs).zip(&coefficients)).enumerate()
        {
            if i == j {
                continue;
            }
            let d_i = match (core.int_power(), core_j.int_power()) {
                (Some((b, e)), Some((bj, ej))) if b == bj => {
                    let gap = BigInt::from(e.clone()) - BigInt::from(ej.clone());
                    let (lb, hb) = bounds(b);
                    hc + gap.clone() * if gap.sign() == Sign::Minus { lb } else { hb }
                }
                _ => hc + h - l_j,
            };
            worst = Some(worst.map_or(d_i.clone(), |w| w.max(d_i)));
            others += 1;
        }
        if !self.d.is_zero() {
            let d_d = bounds(self.d.magnitude()).1 - l_j;
            worst = Some(worst.map_or(d_d.clone(), |w| w.max(d_d)));
            others += 1;
        }
        let lead = &coefficients[j].0;
        if let Some(w) = worst
            && bounds(&BigUint::from(others)).1 + w > lead - &unit
        {
            return None;
        }
        (lead + l_j - &unit - bounds(&self.den).1 >= BigInt::from(128u32) * &unit)
            .then(|| below_zero(c_j))
    }

    /// The value, written out: its cost is that of the value's digits.
    fn expand(&self) -> BigInt {
        let num = self.terms.iter().fold(self.d.clone(), |s, (c, core)| {
            s + mul_int(c, &BigInt::from(core.expand()))
        });
        num / BigInt::from(self.den.clone())
    }

    /// Bounds on the bits of the value and of the widest number [`Kept::expand`] builds: a
    /// term `c * core` has at most the bits of both, and the sum of the terms and `d` at most
    /// the widest of them and one bit for each doubling of their count.
    fn widths(&self) -> (BigUint, BigUint) {
        let mut sum = BigUint::from(self.d.bits());
        let mut widest = BigUint::ZERO;
        for (c, core) in &self.terms {
            let (v, w) = core.widths();
            sum = sum.max(v + c.bits());
            widest = widest.max(w);
        }
        let count = self.terms.len() as u64 + 1;
        sum += u64::from(count.bit_len());
        let widest = widest.max(sum.clone());
        (sum, widest)
    }

    /// The negation of the form. Its value lies outside `i128` except when `self` is `2^127`,
    /// whose negation `i128::MIN` is a big value: so only `Neg for &Num`, which gives that
    /// value its form, calls this.
    fn neg(&self) -> Kept {
        Kept {
            terms: self
                .terms
                .iter()
                .map(|(c, core)| (-c, core.clone()))
                .collect(),
            d: -&self.d,
            den: self.den.clone(),
            negative: !self.negative,
        }
    }

    /// The core, when the value is `±core` alone.
    fn bare(&self) -> Option<&Core> {
        match self.terms.as_slice() {
            [(c, core)] if self.d.is_zero() && self.den.is_one() && c.magnitude().is_one() => {
                Some(core)
            }
            _ => None,
        }
    }

    /// Whether every core has integer atoms only, so that the value has residues.
    fn is_int(&self) -> bool {
        self.terms.iter().all(|(_, core)| core.is_int())
    }

    /// The value modulo `n >= 1`, in `0..n`, without its digits: each core modulo `den * n`
    /// by `modpow`. `None` when a core has a root, whose digits are not known.
    fn residue(&self, n: &BigUint) -> Option<BigUint> {
        let m = &self.den * n;
        let mut x = self.d.clone();
        for (c, core) in &self.terms {
            x += c * BigInt::from(core.residue(&m)?);
        }
        // The numerator is a multiple of den, and so is its residue modulo den * n.
        let x = Integer::mod_floor(&x, &BigInt::from(m));
        Some((x / BigInt::from(self.den.clone())).into_parts().1)
    }

    /// `floor(self / n)` for `n >= 1`, without the digits of `self`, or `None` when a core has
    /// a root.
    fn div_floor_by(&self, n: &BigUint) -> Option<Num> {
        let r = self.residue(n)?;
        Some(Num::kept(
            self.terms.clone(),
            &self.d - BigInt::from(r * &self.den),
            &self.den * n,
        ))
    }

    /// `floor(self ^ (1 / k))` or, when `up`, the ceiling, for `self` above zero and
    /// `k >= 2`.
    fn root(&self, k: &BigUint, up: bool) -> Num {
        if let Some(core) = self.bare() {
            if let Some(r) = core.exact_root(k) {
                return Num::kept(
                    vec![(BigInt::from(1u32), r)],
                    BigInt::ZERO,
                    BigUint::from(1u32),
                );
            }
            match core.0.as_slice() {
                [(Atom::Int(base), exp)] => {
                    // b ^ (e / k) = b ^ (e' / k') in lowest terms, with k' >= 2 since k does
                    // not divide e; b is not a perfect power (`Core::power`), so this is
                    // irrational, and its ceiling is one past its floor.
                    let g = gcd_uint(exp, k);
                    let (e, k) = (exp / &g, k / &g);
                    let r = Num::power(false, base.clone(), e).root_floor(&k);
                    return if up { &r + &Num::ONE } else { r };
                }
                [(Atom::Root { rad, k: k1, .. }, exp)] if exp.is_one() && !up => {
                    // floor(floor(y) ^ (1 / k)) = floor(y ^ (1 / k)) for y >= 0.
                    return Num(Word::Kept(rad.clone())).root_floor(&(k1 * k));
                }
                _ => {}
            }
        }
        if self.is_int() {
            let r = Num(Word::Kept(Box::new(self.clone()))).root_floor(k);
            return if up && !is_perfect_power(self, k) {
                &r + &Num::ONE
            } else {
                r
            };
        }
        // Complexity tradeoff: a root of a kept value with a root among its cores, other than
        // an exact root or the floor root of a bare root, is the root of the value written
        // out, at the cost of its digits and a root of them; the answer is exact. Why: the
        // kept root needs the radicand's residues, which a root's digits decide, and the
        // ceiling of a root of a root needs to know whether a root is itself a perfect power.
        // Trigger: `floor_root` or `ceil_root` of a sum, multiple or product holding a kept
        // root, or the ceiling root of a bare root. Test:
        // `l01_24_refinement_lattices::ends::kept_forms_compute_as_their_values_written_out`
        // (roots 2 to 5 of multiples of kept roots); COMPLEXITY.md S33. A complete solution
        // would keep nested roots `floor(floor(r ^ (1 / k)) * c + d) ^ (1 / j)` as their own
        // atoms, compared by approximation as roots are now.
        Num::from(self.expand()).root_big(k, up)
    }

    /// The number of trailing zero binary digits, or `None` when a core holds a root, whose
    /// digits are not known. The numerator is a sum of parts `2^v * u` with `u` odd: for a term
    /// `c * core`, `v` is the trailing zeros of `c` plus those of each atom times its exponent,
    /// and `u` the product of the odd parts; `d` is one more part. With `m` the least `v`, the
    /// numerator over `2^m` is found modulo `2^j` from the residues of the odd parts (`modpow`),
    /// for `j` = 64 and then twice as many until it is not 0 there; a part with `v - m >= j` is 0
    /// modulo `2^j` and is not read, so no power of 2 past `2^j` is built. Less the trailing
    /// zeros of `den`, which divides the numerator, that is the answer, exact. For a bare power
    /// `b ^ e` it is `e` times the trailing zeros of `b`, found at `j` = 64. The cost is
    /// `O(n log e)` products of `j` bits for `n` terms and exponents of `log e` bits, with `j`
    /// at most twice the trailing zeros of the numerator over `2^m`: the low bits in which its
    /// parts cancel, not the bits of the value.
    fn trailing_zeros(&self) -> Option<BigUint> {
        /// A part `2^v * c * product(b ^ e)` of the numerator, with `c` and each `b` odd.
        struct Part<'a> {
            v: BigUint,
            c: BigInt,
            odd: Vec<(BigUint, &'a BigUint)>,
        }
        let mut parts = Vec::with_capacity(self.terms.len() + 1);
        for (c, core) in &self.terms {
            let tc = c.trailing_zeros().expect("no coefficient is zero");
            let mut v = BigUint::from(tc);
            let mut odd = Vec::with_capacity(core.0.len());
            for (a, e) in &core.0 {
                let Atom::Int(b) = a else { return None };
                let tb = b.trailing_zeros().expect("an atom is at least 2");
                v += e * tb;
                odd.push((b >> tb, e));
            }
            parts.push(Part { v, c: c >> tc, odd });
        }
        if let Some(td) = self.d.trailing_zeros() {
            parts.push(Part {
                v: BigUint::from(td),
                c: &self.d >> td,
                odd: Vec::new(),
            });
        }
        let m = parts
            .iter()
            .map(|p| &p.v)
            .min()
            .expect("a kept value has a term")
            .clone();
        let den_zeros = self.den.trailing_zeros().expect("den is at least 1");
        let mut j = 64u64;
        loop {
            let unit = BigUint::from(1u32) << j;
            let mask = &unit - 1u32;
            let modulus = BigInt::from(unit.clone());
            let mut r = BigUint::ZERO;
            for Part { v, c, odd } in &parts {
                let s = u64::try_from(&(v - &m)).ok().filter(|&s| s < j);
                let Some(s) = s else { continue };
                let u = odd.iter().fold(
                    Integer::mod_floor(c, &modulus).into_parts().1,
                    |x, (b, e)| (x * b.modpow(e, &unit)) & &mask,
                );
                r = (r + (u << s)) & &mask;
            }
            if let Some(z) = r.trailing_zeros() {
                return Some(m + z - den_zeros);
            }
            j *= 2;
        }
    }

    /// The exponent `k` when the value is `2 ^ k`.
    fn pow2_exponent(&self) -> Option<&BigUint> {
        match self.bare()?.int_power() {
            Some((b, k)) if !self.negative && *b == BigUint::from(2u32) => Some(k),
            _ => None,
        }
    }

    /// `floor(self / 2^k)`, for `den == 1`, when a term has `2^k` as a factor of its coefficient
    /// and its atom 2. Such a term over `2^k` is a term again, its exponent of 2 or its
    /// coefficient lowered, or a part of `d` when no atom is left; the other terms and `d` make
    /// `L`, and the answer is those terms plus `floor(L / 2^k)`, which is `floor(d / 2^k)` when
    /// no other term is left, by a shift. `None` when `den > 1` or no term has `2^k` as a
    /// factor. The cost is that of the terms, not of the value's digits.
    fn shr(&self, k: &BigUint) -> Option<Num> {
        if !self.den.is_one() {
            return None;
        }
        let two = Atom::Int(BigUint::from(2u32));
        let (mut high, mut low) = (Vec::new(), Vec::new());
        let mut d_high = BigInt::ZERO;
        for (c, core) in &self.terms {
            // The atoms are in increasing order, so 2 is the first when it is one.
            let f = match core.0.first() {
                Some((a, e)) if *a == two => e.clone(),
                _ => BigUint::ZERO,
            };
            let t = BigUint::from(c.trailing_zeros().expect("no coefficient is zero"));
            if &f + &t < *k {
                low.push((c.clone(), core.clone()));
                continue;
            }
            let (c, atoms) = if f >= *k {
                let mut atoms = core.0.clone();
                let left = &f - k;
                if left.is_zero() {
                    atoms.remove(0);
                } else {
                    atoms[0].1 = left;
                }
                (c.clone(), atoms)
            } else {
                let s = u64::try_from(&(k - &f)).expect("at most the trailing zeros of c");
                let rest = if f.is_zero() {
                    &core.0[..]
                } else {
                    &core.0[1..]
                };
                (c >> s, rest.to_vec())
            };
            if atoms.is_empty() {
                d_high += c;
            } else {
                high.push((c, Core(atoms)));
            }
        }
        if high.is_empty() && d_high.is_zero() {
            return None;
        }
        let rest = if low.is_empty() {
            Num::from(floor_shr(&self.d, &BigInt::from(k.clone())))
        } else {
            Num::kept(low, self.d.clone(), BigUint::from(1u32)).div_floor(&Num::power(
                false,
                BigUint::from(2u32),
                k.clone(),
            ))
        };
        Some(&Num::kept(high, d_high, BigUint::from(1u32)) + &rest)
    }
}

/// Whether `x`, above zero with integer atoms only, is a perfect `k`-th power. Each round
/// tests one more prime `p` with `g = gcd(k, p - 1) > 1`: a `k`-th power `a` not divisible by
/// `p` has `a ^ ((p - 1) / g) == 1` modulo `p`, so a failure proves `x` is not one, and for a
/// value that is not a `k`-th power about `1 - 1/g` of such primes show it. When the number
/// of primes tested reaches a power of two, `x` is also compared with the `k`-th power of its
/// root at twice the last precision, which decides a perfect power once the precision reaches
/// the bits of `x`. Each comparison then costs a constant factor more than the last, and the
/// residue tests cost one per prime. Doubling the precision for every prime instead reached
/// `2 ^ n` bits by the `n`-th prime, while a `k` whose prime factors are all large
/// (`2 ^ 32 + 1 = 641 * 6700417`) gets no residue test below the prime `2 * 641 + 1`, so
/// `3 ^ (2 ^ 32 + 1) + 1` did not finish.
// Complexity tradeoff: a value that is a perfect `k`-th power passes every prime, so it is
// decided only when the precision reaches the bits of `x`, at the cost of its digits and of
// one residue test for each 64 bits of `x`; the answer is exact. Why: a proof that a number
// given as a sum of powers is a perfect power needs its root in a closed form, and no general
// closed form is known for a root of a sum.
// Trigger: the ceiling root (`ceil_root`) of a kept value that is not a bare power and is a
// perfect `k`-th power, such as `(2 ^ 200 + 1) ^ 2` read as a sum. Test:
// `l01_24_refinement_lattices::ends::kept_values_with_no_kept_form_are_written_out`;
// COMPLEXITY.md S33. A complete solution would find the root as a kept value (a sum of
// powers whose `k`-th power is `x`, by matching the leading terms) and check it exactly.
fn is_perfect_power(x: &Kept, k: &BigUint) -> bool {
    let mut p: u64 = 2;
    let mut bits = 64;
    let mut tested: u64 = 0;
    loop {
        // Unreachable: `root_approx` decides once `bits` reaches the bits of `x`, and `bits`
        // doubles at each power of two of `tested`, so `tested` stays below twice the bits of
        // `x` over 64 and `p`, the `tested`-th prime, far below `2^64`.
        p = next_prime(p).expect("a prime below 2^64 for a value held in memory");
        tested += 1;
        let g = gcd_big_u64(k, p - 1);
        if g != 1 {
            let a = x
                .residue(&BigUint::from(p))
                .expect("integer atoms have residues");
            let a = u64::try_from(a).expect("a residue below p");
            if a != 0 && pow_mod(a, (p - 1) / g, p) != 1 {
                return false;
            }
        }
        if tested.is_power_of_two() {
            if let (_, Some(perfect)) = root_approx(x, k, bits) {
                return perfect;
            }
            bits *= 2;
        }
    }
}

/// An unbounded integer held in one machine word while it fits in `i64`: an interval end
/// (`interval::End`). It is two words, as the kernel's `Value::Int` and `Value::Big` are, so
/// an end costs no more than an `i64` one did while every value fits, and no end is rounded
/// or dropped past `i64`. Arithmetic on two small values is done in `i128`, which holds every
/// sum, difference and product of two `i64` values.
#[derive(Clone, Debug)]
pub struct Num(Word);

impl From<i64> for Num {
    fn from(v: i64) -> Num {
        Num(Word::Small(v))
    }
}

impl From<i32> for Num {
    fn from(v: i32) -> Num {
        Num(Word::Small(i64::from(v)))
    }
}

impl From<u64> for Num {
    fn from(v: u64) -> Num {
        Num::from(i128::from(v))
    }
}

impl From<i128> for Num {
    fn from(v: i128) -> Num {
        Num(match i64::try_from(v) {
            Ok(s) => Word::Small(s),
            Err(_) => Word::Big(Arc::new(BigInt::from(v))),
        })
    }
}

impl From<&BigInt> for Num {
    fn from(v: &BigInt) -> Num {
        Num(match i64::try_from(v) {
            Ok(s) => Word::Small(s),
            Err(_) => Word::Big(Arc::new(v.clone())),
        })
    }
}

impl From<BigInt> for Num {
    fn from(v: BigInt) -> Num {
        Num(match i64::try_from(&v) {
            Ok(s) => Word::Small(s),
            Err(_) => Word::Big(Arc::new(v)),
        })
    }
}

impl From<&Int> for Num {
    fn from(v: &Int) -> Num {
        match &v.0 {
            Repr::Small(s) => Num::from(*s),
            Repr::Big(b) => Num::from((**b).clone()),
        }
    }
}

/// An integer of the kernel, kept as a power of each of its primes, which may be far past
/// what can be written out, and as a power of each of its wide atoms (`Rat::wide`). It must
/// be an integer, so every exponent is positive.
impl From<&zed_kernel::num::Rat> for Num {
    fn from(v: &zed_kernel::num::Rat) -> Num {
        let (coeff, pows) = v.integer_factors();
        let n = pows.iter().fold(Num::from(coeff), |n, (p, e)| {
            &n * &Num::power(false, BigUint::from(*p), e.magnitude().clone())
        });
        v.wide().iter().fold(n, |n, (q, f)| {
            &n * &Num::power(false, q.clone(), f.magnitude().clone())
        })
    }
}

impl From<&Num> for zed_kernel::Value {
    fn from(v: &Num) -> zed_kernel::Value {
        match &v.0 {
            Word::Small(s) => zed_kernel::Value::Int(*s),
            Word::Big(b) => zed_kernel::Value::int((**b).clone()),
            Word::Kept(k) => zed_kernel::Value::int(k.expand()),
        }
    }
}

impl From<&Num> for Int {
    fn from(v: &Num) -> Int {
        match &v.0 {
            Word::Small(s) => Int::from(*s),
            Word::Big(b) => Int::from((**b).clone()),
            Word::Kept(k) => Int::from(k.expand()),
        }
    }
}

impl Num {
    /// Zero.
    pub const ZERO: Num = Num(Word::Small(0));
    /// One.
    pub const ONE: Num = Num(Word::Small(1));

    /// The int `v` of either width, exact at any size (a kept power stays kept, as
    /// `From<&Rat>`); `None` for a value that is no int. The shared reading of an int
    /// constant as an interval end, in place of a match on `Value::Int` and `Value::Big` at
    /// each reader (DRY-numeric-shared-rest).
    pub fn of_integer(v: &zed_kernel::Value) -> Option<Num> {
        match v {
            zed_kernel::Value::Int(n) => Some(Num::from(*n)),
            zed_kernel::Value::Big(n) => Some(Num::from(&**n)),
            _ => None,
        }
    }

    /// The value, written out when kept, once the system gives a byte for each bit of the
    /// widest number the writing builds (`Kept::widths`); [`TooLarge`] names that memory when
    /// it refuses. A value not kept is borrowed, or built from its one word.
    // Complexity tradeoff: the memory asked for is a byte for each bit of a bound on the widest
    // number built (each power, product, sum and radicand), the factor `Rat::built_parts`
    // asks. Measured on its own
    // (`kept_serial::a_kept_value_built_takes_less_memory_than_it_asks_for`,
    // item NATIVE-shape-test, one thread, growth of `VmHWM`): 2^(2^30) peaks at 2.51 times the
    // value's bytes against an ask of 16.0 times, 3^(2^27) (squaring) at 8.08 times against
    // 10.1, 3^(2^26) + 5^(2^26) at 6.51 times against 10.3; every peak lies below its ask. So a
    // value needing less is refused when the free memory lies
    // between the two, and none aborts. Trigger: the canonical serialization of an interval end
    // or a class past `i64` (`canon::serial`). Test:
    // `l01_24_refinement_lattices::kept_serial` (refused at two widths, exact when given);
    // COMPLEXITY.md S33. A complete solution would ask each allocation of the build for its
    // own memory.
    pub fn built(&self) -> Result<Cow<'_, BigInt>, TooLarge> {
        if let Word::Kept(k) = &self.0 {
            let (value, widest) = k.widths();
            room(value, widest << 3u32)?;
        }
        Ok(self.big())
    }

    /// The value, written out when kept: its cost is then that of the value's digits.
    fn big(&self) -> Cow<'_, BigInt> {
        match &self.0 {
            Word::Small(v) => Cow::Owned(BigInt::from(*v)),
            Word::Big(v) => Cow::Borrowed(v),
            Word::Kept(k) => Cow::Owned(k.expand()),
        }
    }

    /// The value to `bits` bits.
    fn approx(&self, bits: u64) -> Approx {
        match &self.0 {
            Word::Kept(k) => k.approx(bits),
            _ => Approx::of(&self.big(), bits),
        }
    }

    /// The value, when it is not kept.
    fn scalar(&self) -> Option<Cow<'_, BigInt>> {
        match &self.0 {
            Word::Small(v) => Some(Cow::Owned(BigInt::from(*v))),
            Word::Big(v) => Some(Cow::Borrowed(v)),
            Word::Kept(_) => None,
        }
    }

    /// `(sum of c * core + d) / den` in its one form for a value inside `i128`, else kept. The
    /// terms are collected and folded first. The place of the value against `i128` is found at
    /// 64 bits and then at twice as many until it is decided; a value inside `i128` is then
    /// written out.
    // Complexity tradeoff: a value inside `i128` whose terms remain after collecting and
    // folding, because they cancel in forms that neither relates (see `Core::same` and
    // `fold`), is placed only once the approximations are exact, and written out, at the
    // cost of the digits of its cores; the answer is exact. Why: the terms cancel only by
    // carries between products of powers of several integers, or between roots, which `fold`
    // does not make. Trigger: a sum or difference of kept values in such forms whose value is
    // small, as `2 ^ (e + 1) * 5 ^ e + 1 - 2 * 10 ^ e`. Test:
    // `l01_24_refinement_lattices::ends::kept_values_with_no_kept_form_are_written_out`;
    // COMPLEXITY.md S33. A complete solution is that of `fold`, which would cancel these terms.
    fn kept(terms: Vec<(BigInt, Core)>, d: BigInt, den: BigUint) -> Num {
        let mut terms = collect(terms);
        fold(&mut terms);
        if terms.is_empty() {
            return Num::from(d / BigInt::from(den));
        }
        let g = terms
            .iter()
            .fold(BigInt::from(gcd_uint(d.magnitude(), &den)), |g, (c, _)| {
                BigInt::from(gcd_uint(g.magnitude(), c.magnitude()))
            });
        let (terms, d, den) = if g.is_one() {
            (terms, d, den)
        } else {
            let gu = g.magnitude();
            (
                terms.into_iter().map(|(c, core)| (c / &g, core)).collect(),
                d / &g,
                den / gu,
            )
        };
        let mut k = Kept {
            terms,
            d,
            den,
            negative: false,
        };
        // One term placed by the least size of its core, before any approximation (item
        // PERF-fold-power-of-huge-exponent): the approximation of `3 ^ e` loses its lower end
        // to 0 after about `bits` squarings, since each rounds the ends apart, so the loop
        // below doubled `bits` until it neared the `b` bits of `e`, O(b * M(b)) a round, and
        // `3 ^ (2^(2^20)) > 0` did not finish in 30 s. Proof that the shortcut gives the value
        // the loop gives: write the value `(c * core + d) / den` with `c != 0`, `den >= 1`,
        // and `L = core.least_log2()`, so `|c * core| >= core >= 2^L`. When `L >= bits(d) +
        // bits(den) + 128`, then `|d| < 2^bits(d) <= 2^(L - 1)`, so `|c * core + d| >= 2^L -
        // 2^(L - 1) = 2^(L - 1)` and its sign is that of `c`; with `den < 2^bits(den)`, the
        // value is past `2^(L - 1 - bits(den)) >= 2^127` in magnitude. So it lies outside
        // `i128` with the sign of `c`, which is the kept form the loop returns. Tested by
        // `tests::a_kept_power_of_a_huge_exponent_is_placed_by_its_least_size`; what the test
        // cannot catch: a sum of several terms, which still goes to the loop.
        if let [(c, core)] = &k.terms[..]
            && core.least_log2() >= BigUint::from(k.d.bits() + k.den.bits() + 128)
        {
            k.negative = below_zero(c);
            return Num(Word::Kept(Box::new(k)));
        }
        let edge = BigInt::from(1u32) << 127u32;
        let zero = BigInt::ZERO;
        let mut bits = 64;
        loop {
            let a = k.approx(bits);
            if scaled_cmp(&a.lo, &a.shift, &edge, &zero) != Ordering::Less {
                return Num(Word::Kept(Box::new(k)));
            }
            if scaled_cmp(&a.hi, &a.shift, &-&edge, &zero) == Ordering::Less {
                k.negative = true;
                return Num(Word::Kept(Box::new(k)));
            }
            if scaled_cmp(&a.lo, &a.shift, &-&edge, &zero) != Ordering::Less
                && scaled_cmp(&a.hi, &a.shift, &edge, &zero) == Ordering::Less
            {
                return Num::from(k.expand());
            }
            // Several terms, one of which outweighs the rest past `i128` (item
            // PERF-num-kept-multi-term-precision): placed by the bounds on the logarithms of
            // the terms once 64 bits leave the value undecided, rather than by doubling `bits`
            // to past those of the cores' exponents. `Kept::dominant_sign` proves it gives the
            // sign the loop gives, for a value the loop finds outside `i128`; a sum it does not
            // decide goes on in the loop.
            if bits == 64
                && let Some(negative) = k.dominant_sign()
            {
                k.negative = negative;
                return Num(Word::Kept(Box::new(k)));
            }
            bits *= 2;
        }
    }

    /// A bare kept value `±core`, for a core whose value is at least `2^127`.
    fn bare(negative: bool, core: Core) -> Num {
        Num(Word::Kept(Box::new(Kept {
            terms: vec![(BigInt::from(if negative { -1 } else { 1 }), core)],
            d: BigInt::ZERO,
            den: BigUint::from(1u32),
            negative,
        })))
    }

    /// The value, when it fits in `i64`.
    pub fn to_i64(&self) -> Option<i64> {
        match self.0 {
            Word::Small(v) => Some(v),
            _ => None,
        }
    }

    /// The value as an [`Int`], when it is written out: a kept power is not built, since that
    /// costs time and memory in its digits.
    pub fn to_int(&self) -> Option<Int> {
        self.scalar().map(|v| Int::from(v.into_owned()))
    }

    /// Whether the value is kept as a power rather than written out: then [`Num::to_int`] is
    /// `None`, and a written-out `Num` of the same value may exist, equal and of one hash.
    pub fn is_kept(&self) -> bool {
        matches!(self.0, Word::Kept(_))
    }

    /// The value, when it fits in `i128`.
    pub fn to_i128(&self) -> Option<i128> {
        match &self.0 {
            Word::Small(v) => Some(*v as i128),
            Word::Big(v) => i128::try_from(&**v).ok(),
            Word::Kept(_) => None,
        }
    }

    /// The sign: -1, 0 or 1.
    pub fn signum(&self) -> i8 {
        match &self.0 {
            Word::Small(v) => v.signum() as i8,
            Word::Big(v) => match v.sign() {
                Sign::Minus => -1,
                Sign::NoSign => 0,
                Sign::Plus => 1,
            },
            Word::Kept(k) => {
                if k.negative {
                    -1
                } else {
                    1
                }
            }
        }
    }

    /// Whether the value is zero.
    pub fn is_zero(&self) -> bool {
        matches!(self.0, Word::Small(0))
    }

    /// Whether the value is odd. A kept value is read by its residue modulo 2
    /// ([`Num::mod_floor`]), not written out.
    pub fn is_odd(&self) -> bool {
        match &self.0 {
            Word::Small(v) => v & 1 == 1,
            Word::Big(v) => v.is_odd(),
            Word::Kept(_) => !self.mod_floor(&Num::from(2)).is_zero(),
        }
    }

    /// The absolute value.
    pub fn abs(&self) -> Num {
        if self.signum() < 0 {
            -self
        } else {
            self.clone()
        }
    }

    /// The number of binary digits of `abs(self)`: the least `b >= 0` with `abs(self) < 2^b`.
    /// A kept value is not written out (`Num::kept_bits`).
    pub fn bits(&self) -> Num {
        match &self.0 {
            Word::Small(v) => Num::from(i64::from(v.unsigned_abs().bit_len())),
            Word::Big(v) => Num::from(i128::from(v.bits())),
            Word::Kept(k) => Num::from(self.kept_bits(k)),
        }
    }

    /// The most one binary digits of a value in `lo ..= self`, for `0 <= lo <= self`: the
    /// popCount of `self` when `lo == self`. Above the highest digit `p` where `lo` and `self`
    /// differ, every value in the range has the digits of `self`; at `p`, `self` has 1 and `lo`
    /// 0, so the range holds those high digits followed by `p` ones, and `self` itself, which
    /// has one more one exactly when its low `p` digits are all ones. No value beats these two:
    /// one with 0 at `p` has at most `p` ones below it; one with 1 at `p` is at most `self`, so
    /// it has `p + 1` ones from `p` down only when its low `p` digits are all ones, and then so
    /// are those of `self`, which it does not exceed. (The value with 0 at `p` and ones below is
    /// at least `lo`, whose digits below `p` are at most all ones, and below `self`.) So the
    /// answer is the ones of `self` above `p`, plus `p`, plus 1 when the low `p` digits of
    /// `self` are ones.
    // Complexity tradeoff: naive, the popCount of each value in the range, O(range * digits);
    // here one pass over the words from the highest and a count of the trailing ones, O(digits),
    // with nothing allocated past a machine word. A kept end is not written out:
    // the answer is then that of the range `0 ..= self`, the digits of `self`, less one unless
    // `self + 1` is a power of 2, which bounds the answer from above and is exact when `lo` has
    // fewer digits than `self` (so for the masks `0 ..= h`). Why: the digits of a kept value
    // cost its full width to write out. Trigger: `pext` with a mask interval with an end kept
    // as a power or root past `i128`. Test:
    // `l01_39f_int_machine_ops::pext_popcount::a_kept_mask_bounds_pext_by_its_digits`;
    // COMPLEXITY.md S33. A complete solution would read the popCount of a kept power from its
    // cores (a bare power of 2 has one one digit).
    pub fn most_ones_from(&self, lo: &Num) -> Num {
        match (&lo.0, &self.0) {
            (Word::Small(l), Word::Small(h)) => {
                let (l, h) = (l.unsigned_abs(), h.unsigned_abs());
                let x = l ^ h;
                if x == 0 {
                    return Num::from(i64::from(h.count_ones()));
                }
                let p = x.ilog2();
                let top = (h >> p >> 1).count_ones();
                let low = u32::from(h.trailing_ones() >= p);
                Num::from(i64::from(top + p + low))
            }
            (Word::Kept(_), _) | (_, Word::Kept(_)) => {
                let d = self.bits();
                if (self + &Num::ONE) == Num::pow2(&d) {
                    d
                } else {
                    &d - &Num::ONE
                }
            }
            _ => {
                // The words of both from the highest, `lo`'s padded with zeros to the length of
                // `self`'s, read in place: no xor or shift is built.
                let (l, h) = (lo.big(), self.big());
                let (l, h) = (l.magnitude(), h.magnitude());
                let (lw, hw) = (l.iter_u64_digits(), h.iter_u64_digits());
                let at = hw.len();
                let lw = std::iter::repeat_n(0, at - lw.len()).chain(lw.rev());
                let mut top = 0;
                for (i, (a, b)) in (0..at).rev().zip(lw.zip(hw.rev())) {
                    let x = a ^ b;
                    if x != 0 {
                        let d = u64::from(x.ilog2());
                        let p = 64 * i as u64 + d;
                        top += u64::from((b >> d >> 1).count_ones());
                        let low = u64::from(h.trailing_ones() >= p);
                        return Num::from(top + p + low);
                    }
                    top += u64::from(b.count_ones());
                }
                Num::from(top)
            }
        }
    }

    /// The bits of the kept value `self`, whose form is `k`, from its approximation at 64 bits
    /// and then at twice as many. When the bounds `lo * 2^s` and `hi * 2^s` of `abs(self)`
    /// have one bit count, that is the answer: so for a bare power of 2 at once, since its
    /// approximation is exact, and for any other bare power `b ^ e` once the precision passes
    /// the bits of `e` and those on which `e * log2(b)` agrees with an integer. When the counts
    /// are `l` and `l + 1`, as for `2 ^ k - 1`, whose bounds lie on both sides of `2^k` at
    /// every precision short of its digits, one comparison of `abs(self)` with `2^l` decides,
    /// as the sign of a kept difference whose equal cores cancel. The answer is exact; the cost
    /// is that of the approximations and of that comparison, not of the value's digits.
    fn kept_bits(&self, k: &Kept) -> BigInt {
        let mut bits = 64;
        loop {
            let Approx { lo, hi, shift } = k.approx(bits);
            let (lo, hi) = if k.negative { (-hi, -lo) } else { (lo, hi) };
            if lo.sign() == Sign::Plus {
                let low = &shift + lo.bits();
                let high = &shift + hi.bits();
                if low == high {
                    return high;
                }
                if high == &low + 1u32 {
                    // abs(self) >= 2^(low - 1) and abs(self) < 2^high.
                    let edge = Num::power(false, BigUint::from(2u32), low.magnitude().clone());
                    let past = if k.negative {
                        *self <= -&edge
                    } else {
                        *self >= edge
                    };
                    return if past { high } else { low };
                }
            }
            bits *= 2;
        }
    }

    /// The number of trailing zero binary digits of a value other than 0. A kept value with
    /// integer cores is not written out (`Kept::trailing_zeros`).
    pub fn trailing_zeros(&self) -> Num {
        match &self.0 {
            Word::Small(v) => Num::from(i64::from(v.trailing_zeros())),
            Word::Big(v) => Num::from(i128::from(v.trailing_zeros().unwrap_or(0))),
            Word::Kept(k) => match k.trailing_zeros() {
                Some(z) => Num::from(BigInt::from(z)),
                // Complexity tradeoff: the trailing zeros of a kept value with a root among its
                // cores are those of the value written out, at the cost of its digits; the
                // answer is exact. Why: a floor root's low digits need the root to unit
                // precision, and so the radicand's digits. Trigger: `trailingZeros`, or a bit
                // word's rule reading one, on an end holding a kept root. Test:
                // `l01_39a_bit_words::kept_ends::the_trailing_zeros_of_a_kept_root_are_those_written_out`;
                // COMPLEXITY.md S33. A complete solution would keep the residue of a root modulo
                // a power of 2 in its atom's memo, found from the radicand's residue by a 2-adic
                // root where one exists.
                None => Num::from(i128::from(
                    self.big().trailing_zeros().expect("a kept value is not 0"),
                )),
            },
        }
    }

    /// `2 ^ e` for `e >= 0`, kept as a power when it does not fit in `i128`.
    // Complexity tradeoff: a kept `e` is written out, at the cost of its digits, since the
    // exponents of a core are written out; the answer is exact, and `2 ^ e` stays kept. Why:
    // a power whose exponent is itself kept needs an atom with a kept exponent, whose
    // approximation, residues and comparisons are not built. Trigger: `shl`, `bitNot`, `rotl`
    // or `rotr` with a count or width outside `i128`, or `bitOr`, `bitXor` or `trailingZeros`
    // on an operand of more than about `2^127` bits. Test:
    // `l01_39a_bit_words::kept_ends::a_power_of_2_by_a_kept_exponent_stays_kept`; COMPLEXITY.md
    // S33. A complete solution would keep `b ^ x` for a kept `x` as an atom, approximated by
    // `Approx::pow` on an approximation of `x`.
    pub fn pow2(e: &Num) -> Num {
        Num::power(false, BigUint::from(2u32), e.big().magnitude().clone())
    }

    /// `base ^ exp`, negated when `negative`, in its one form: in `i128` arithmetic when it
    /// fits there, else kept as a power. Finding whether it fits stops at the first product
    /// past `i128`, so it costs `O(bits of exp)` word operations.
    fn power(negative: bool, base: BigUint, exp: BigUint) -> Num {
        let sign = if negative { Sign::Minus } else { Sign::Plus };
        match exp.bits() {
            0 => return Num::ONE,
            1 => return BigInt::from_biguint(sign, base).into(),
            _ => {}
        }
        if let (Ok(b), Ok(e)) = (u128::try_from(&base), u32::try_from(&exp))
            && let Some(m) = b.checked_pow(e)
            && let Some(v) = if negative {
                0i128.checked_sub_unsigned(m)
            } else {
                i128::try_from(m).ok()
            }
        {
            return v.into();
        }
        Num::bare(negative, Core::power(base, exp))
    }

    /// `self ^ k`. A value that does not fit in `i128` is kept: a bare power or root as one
    /// with its exponents times `k`, other kept values by squaring, so the cost is that of
    /// the terms of the result (up to `C(n + k, k)` for `n` terms), not of its digits.
    pub fn pow(&self, k: u32) -> Num {
        if let Word::Small(a) = self.0
            && let Some(v) = (a as i128).checked_pow(k)
        {
            return v.into();
        }
        match k {
            0 => return Num::ONE,
            1 => return self.clone(),
            _ => {}
        }
        let negative = self.signum() < 0 && k % 2 == 1;
        match &self.0 {
            Word::Kept(x) => {
                if let Some(core) = x.bare() {
                    return match core.int_power() {
                        Some((base, exp)) => Num::power(negative, base.clone(), exp * k),
                        None => Num::bare(negative, core.pow(&BigUint::from(k))),
                    };
                }
                // Complexity tradeoff: a power of a kept value that is not bare is expanded into
                // its terms, up to `C(n + k - 1, k)` of them for `n` terms, so `(x ^ e + 1) **
                // 1000000` holds a million terms with coefficients of up to a million bits; the
                // answer is exact. Why: a kept power of a sum needs a new atom, a power of a kept
                // value, with its own approximation (`Approx::pow`), residues (`modpow` of the
                // sum's residue) and rules for collecting it with expanded terms. Trigger: an
                // exponent `k` on an interval whose end is a kept sum, as the bound of
                // `(x ^ e + 1) ^ k`. Test:
                // `l01_24_refinement_lattices::ends::kept_forms_compute_as_their_values_written_out`
                // (squares of sums) and `ends::sums_of_unrelated_large_powers_keep_their_form`
                // (a cube of `2 ^ k + 1`); COMPLEXITY.md S33. A complete solution would keep
                // `s ^ k` as an atom for a kept sum `s`.
                let mut r = Num::ONE;
                for i in (0..k.bit_len()).rev() {
                    r = &r * &r;
                    if (k >> i) & 1 == 1 {
                        r = &r * self;
                    }
                }
                r
            }
            Word::Small(_) | Word::Big(_) => {
                Num::power(negative, self.big().magnitude().clone(), BigUint::from(k))
            }
        }
    }

    /// `self ^ k` for `k >= 0` of any size, or `None` when no form holds it: when `k` is
    /// kept, or `self` is a kept value that is not bare and `k` is past `u32`. A power of a
    /// value that is not kept is kept as a power, with its exponent `k`, never written out.
    pub fn pow_by(&self, k: &Num) -> Option<Num> {
        if let Some(k) = k.to_i64().and_then(|k| u32::try_from(k).ok()) {
            return Some(self.pow(k));
        }
        let negative = self.signum() < 0 && k.is_odd();
        if self.abs() <= Num::ONE {
            // 0, 1 and -1 are read by the parity of `k`.
            return Some(if negative { Num::from(-1) } else { self.abs() });
        }
        let exp = k.scalar()?.magnitude().clone();
        match &self.0 {
            Word::Small(_) | Word::Big(_) => {
                Some(Num::power(negative, self.big().magnitude().clone(), exp))
            }
            // Complexity tradeoff: a kept value that is not bare raised past `u32` has no form;
            // it is `None` and the caller bounds outward. Why: expanding it squares its terms
            // about 32 times, past any memory. Trigger: `(2 ^ 200 + 1) ^ (2 ^ 40)`. Test:
            // `l01_24_refinement_lattices::past_i64::an_exponent_with_no_exact_form_bounds_outward`;
            // COMPLEXITY.md S36. A complete solution would keep `s ^ k` as an atom for a kept
            // sum `s`.
            Word::Kept(x) => {
                let core = x.bare()?;
                Some(match core.int_power() {
                    Some((base, e)) => Num::power(negative, base.clone(), e * exp),
                    None => Num::bare(negative, core.pow(&exp)),
                })
            }
        }
    }

    /// [`Num::floor_root`] with `k >= 1` of any size, or `None` when `k` is kept.
    pub fn floor_root_by(&self, k: &Num) -> Option<Num> {
        self.root_by(k, false)
    }

    /// [`Num::ceil_root`] with `k >= 1` of any size, or `None` when `k` is kept.
    pub fn ceil_root_by(&self, k: &Num) -> Option<Num> {
        self.root_by(k, true)
    }

    fn root_by(&self, k: &Num, up: bool) -> Option<Num> {
        if let Some(k) = k.to_i64().and_then(|k| u32::try_from(k).ok()) {
            return Some(self.root(k, up));
        }
        let k = k.scalar()?.magnitude().clone();
        Some(match &self.0 {
            Word::Small(_) | Word::Big(_) => self.root_big(&k, up),
            Word::Kept(x) => x.root(&k, up),
        })
    }

    /// The greatest `r >= 0` with `r ^ k <= self`, for `self >= 0` and `k >= 1`. The root of
    /// a kept value is kept, exact when the value is a power whose exponent `k` divides.
    pub fn floor_root(&self, k: u32) -> Num {
        self.root(k, false)
    }

    /// The least `r >= 0` with `r ^ k >= self`, for `self >= 0` and `k >= 1`.
    pub fn ceil_root(&self, k: u32) -> Num {
        self.root(k, true)
    }

    fn root(&self, k: u32, up: bool) -> Num {
        if k == 1 {
            return self.clone();
        }
        match &self.0 {
            Word::Small(_) | Word::Big(_) => self.root_big(&BigUint::from(k), up),
            Word::Kept(x) => x.root(&BigUint::from(k), up),
        }
    }

    /// The floor or ceiling of the `k`-th root of a value that is not kept, for `self >= 0`
    /// and `k >= 2`.
    fn root_big(&self, k: &BigUint, up: bool) -> Num {
        let v = self.big();
        if v.bits() <= 1 {
            // 0 and 1 are their own roots.
            return self.clone();
        }
        // For v >= 2 and k at least its bits, 1 ^ k <= v < 2 ^ k. An index below the bits is
        // a `u64`, whatever its size against a `u32` (ledger FAIL-roots-binomial-u32-narrowing:
        // every index past a `u32` took this answer, wrong for a value of more bits; test
        // `a_root_whose_index_is_past_a_u32_of_a_value_wider_than_it`).
        let Some(k) = u64::try_from(k).ok().filter(|k| *k < v.bits()) else {
            return Num::from(if up { 2 } else { 1 });
        };
        // O(M(n)) for a fixed `k` by the kernel's root, whose remainder also says whether the
        // root is exact, where num-bigint's `nth_root` is above it (item
        // PERF-wide-odd-base-ratio-9, at `nth_root_rem_uint`).
        let (r, rem) = nth_root_rem_uint(v.magnitude(), k);
        Num::from(BigInt::from(r + u32::from(up && !rem.is_zero())))
    }

    /// `floor(self ^ (1 / k))` for `self` above zero with integer atoms only or not kept, and
    /// `k >= 2`: kept as a root when it is at least `2^127`, which holds exactly when
    /// `self >= 2 ^ (127 * k)`, else found by bisection on the 127 bits of the root.
    fn root_floor(&self, k: &BigUint) -> Num {
        let Word::Kept(x) = &self.0 else {
            return self.root_big(k, false);
        };
        if *self >= Num::power(false, BigUint::from(2u32), k * 127u32) {
            let root = Atom::Root {
                rad: x.clone(),
                k: k.clone(),
                memo: Memo::default(),
            };
            return Num::bare(false, Core(vec![(root, BigUint::from(1u32))]));
        }
        let (mut lo, mut hi) = (BigUint::ZERO, BigUint::from(1u32) << 127u32);
        while &hi - &lo > BigUint::from(1u32) {
            let mid: BigUint = (&lo + &hi) >> 1u32;
            if Num::power(false, mid.clone(), k.clone()) <= *self {
                lo = mid;
            } else {
                hi = mid;
            }
        }
        BigInt::from(lo).into()
    }

    /// Whether `self <= other + 1`: whether no integer lies strictly between them, with
    /// `self` past `other`. It does not expand a kept value.
    pub fn at_most_succ(&self, other: &Num) -> bool {
        if self <= other {
            return true;
        }
        let perfect = |x: &Kept| {
            x.bare()
                .is_some_and(|c| c.exps_gcd() >= BigUint::from(2u32))
        };
        match (&self.0, &other.0) {
            // Two bare kept cores whose exponents share a factor are perfect powers with
            // exponents at least 2, both outside i128; by Mihailescu's theorem (Catalan's
            // conjecture) the only two such powers that differ by 1 are 8 and 9, so these
            // never do.
            (Word::Kept(a), Word::Kept(b)) if perfect(a) && perfect(b) => false,
            (Word::Big(a), Word::Big(b)) => is_succ(a, b),
            _ => *self <= other + &Num::ONE,
        }
    }

    /// `self / d` rounded down, for `d` not zero. A kept value over a value that is not kept
    /// uses residues of its cores and keeps its form; a value smaller in magnitude than a kept
    /// divisor gives 0 or -1 by one comparison.
    pub fn div_floor(&self, d: &Num) -> Num {
        match (&self.0, &d.0) {
            (Word::Small(a), Word::Small(b)) => {
                return Integer::div_floor(&(*a as i128), &(*b as i128)).into();
            }
            // floor(x / d) = floor(-x / -d), so a negative divisor is turned around by negating
            // both in their one forms: the negation of a kept 2^127 is i128::MIN, a big value,
            // and no kept form ever holds a value inside i128.
            (Word::Kept(_), Word::Small(_) | Word::Big(_)) if d.signum() < 0 => {
                return (-self).div_floor(&-d);
            }
            (Word::Kept(x), _) if let Some(s) = d.scalar() => {
                if let Some(q) = x.div_floor_by(s.magnitude()) {
                    return q;
                }
            }
            (_, Word::Kept(_)) if self.abs() < d.abs() => {
                return if self.is_zero() || self.signum() == d.signum() {
                    Num::ZERO
                } else {
                    Num::from(-1)
                };
            }
            // A shift right (`interval::bit_word`'s `shr`) by a count of at least 127.
            (Word::Kept(x), Word::Kept(y))
                if let Some(k) = y.pow2_exponent()
                    && let Some(q) = x.shr(k) =>
            {
                return q;
            }
            _ => {}
        }
        // Complexity tradeoff: the quotient of a kept value by a kept value at most its size,
        // and of a kept value with a root among its cores by any value, is that of the values
        // written out, at the cost of their digits; the answer is exact. By a power of 2, the
        // terms that have it as a factor are divided in their form (`Kept::shr`), and only the
        // other terms, when any is kept, are written out. Why: a quotient of two
        // sums of powers is not a sum of powers in general, and keeping it needs a new form
        // (a floor of a ratio) whose comparisons need its own approximation and residues; a
        // root has no residues without its digits. Trigger: `div` with a kept divisor no
        // larger than the dividend, or a dividend holding a kept root. Test:
        // `l01_24_refinement_lattices::ends::kept_forms_compute_as_their_values_written_out`
        // (every pair of 156 kept values) and, by a power of 2,
        // `l01_39a_bit_words::kept_ends::a_shift_right_of_a_kept_end_keeps_its_form`;
        // COMPLEXITY.md S33. A complete solution would keep `floor(a / b)` as an atom,
        // approximated as the quotient of the approximations. The digits are divided by the
        // kernel's division, as at `Int::div_floor` (COMPLEXITY.md S48).
        div_floor_int(&self.big(), &d.big()).into()
    }

    /// The remainder of [`Num::div_floor`], which has the sign of `d`.
    pub fn mod_floor(&self, d: &Num) -> Num {
        match (&self.0, &d.0) {
            (Word::Small(a), Word::Small(b)) => {
                return Integer::mod_floor(&(*a as i128), &(*b as i128)).into();
            }
            (Word::Kept(x), _) if let Some(s) = d.scalar() => {
                if let Some(r) = x.residue(s.magnitude()) {
                    let r = BigInt::from(r);
                    return if below_zero(&s) && !r.is_zero() {
                        (r + &*s).into()
                    } else {
                        r.into()
                    };
                }
            }
            (_, Word::Kept(_)) if self.abs() < d.abs() => {
                return if self.is_zero() || self.signum() == d.signum() {
                    self.clone()
                } else {
                    self + d
                };
            }
            _ => {}
        }
        // Complexity tradeoff: the remainder of a kept value by a kept value at most its size,
        // and of a kept value with a root among its cores by any value, is that of the values
        // written out, at the cost of their digits; the answer is exact. Why: the remainder is
        // the dividend less the divisor times the quotient, with the cost of the quotient at
        // `div_floor`. Trigger: `mod` with a kept divisor no larger than the dividend, or a
        // dividend holding a kept root. Test:
        // `l01_24_refinement_lattices::ends::kept_forms_compute_as_their_values_written_out`;
        // COMPLEXITY.md S33. A complete solution would follow from a kept quotient, as at
        // `div_floor`. The digits are divided by the kernel's division (COMPLEXITY.md S48).
        mod_floor_int(&self.big(), &d.big()).into()
    }

    /// The greatest common divisor, at least 0. With one kept operand and one that is not,
    /// it is the gcd of the latter with the former's residue modulo it.
    pub fn gcd(&self, other: &Num) -> Num {
        match (&self.0, &other.0) {
            (Word::Small(a), Word::Small(b)) => {
                return i128::from(gcd_u64(a.unsigned_abs(), b.unsigned_abs())).into();
            }
            (Word::Kept(_), _) if other.scalar().is_some() => {
                if other.is_zero() {
                    return self.abs();
                }
                let s = other.abs();
                if let Word::Kept(x) = &self.0
                    && let Some(r) = x.residue(s.big().magnitude())
                {
                    return BigInt::from(gcd_uint(&r, s.big().magnitude())).into();
                }
            }
            (_, Word::Kept(_)) if self.scalar().is_some() => return other.gcd(self),
            _ => {}
        }
        // Complexity tradeoff: the gcd of two kept values, and of a kept value with a root
        // among its cores and any value, is that of the values written out, at the cost of
        // their digits; the answer is exact. Why: Euclid's algorithm on two kept values takes
        // remainders of kept values by kept values (see `mod_floor`), and the gcd of two
        // powers of unrelated bases has no form other than its value. Trigger: `gcd` of two
        // kept values, or of a kept value holding a root. Test:
        // `l01_24_refinement_lattices::ends::kept_forms_compute_as_their_values_written_out`;
        // COMPLEXITY.md S33. A complete solution would factor out the common part of the cores
        // over a coprime base (as at `Core::value_cmp_at`) and take the gcd of the remaining
        // coefficients by residues.
        BigInt::from(gcd_uint(self.big().magnitude(), other.big().magnitude())).into()
    }

    /// The Euclidean quotient: `self = q * d + r` with `r` in `0..abs(d)`, for `d` not zero.
    pub fn div_euclid(&self, d: &Num) -> Num {
        let q = self.div_floor(&d.abs());
        if d.signum() < 0 { -&q } else { q }
    }

    /// The Euclidean remainder, in `0..abs(d)`, for `d` not zero.
    pub fn rem_euclid(&self, d: &Num) -> Num {
        self.mod_floor(&d.abs())
    }
}

impl Add for &Num {
    type Output = Num;

    /// A sum with a kept value is kept: the terms of both, over the least common multiple of
    /// their denominators, collected and folded.
    fn add(self, other: &Num) -> Num {
        match (&self.0, &other.0) {
            (Word::Small(a), Word::Small(b)) => (*a as i128 + *b as i128).into(),
            (Word::Kept(x), Word::Kept(y)) => {
                let den = Integer::lcm(&x.den, &y.den);
                let (sx, sy) = (BigInt::from(&den / &x.den), BigInt::from(&den / &y.den));
                let terms = x
                    .terms
                    .iter()
                    .map(|(c, core)| (c * &sx, core.clone()))
                    .chain(y.terms.iter().map(|(c, core)| (c * &sy, core.clone())))
                    .collect();
                Num::kept(terms, &x.d * &sx + &y.d * &sy, den)
            }
            (Word::Kept(x), _) if let Some(s) = other.scalar() => Num::kept(
                x.terms.clone(),
                &x.d + &*s * BigInt::from(x.den.clone()),
                x.den.clone(),
            ),
            (_, Word::Kept(_)) => other + self,
            // Neither is kept.
            _ => (&*self.big() + &*other.big()).into(),
        }
    }
}

impl Sub for &Num {
    type Output = Num;

    fn sub(self, other: &Num) -> Num {
        match (&self.0, &other.0) {
            (Word::Small(a), Word::Small(b)) => (*a as i128 - *b as i128).into(),
            // Complexity tradeoff: `self + &-other` on two values that are not kept builds the
            // negation as a new `BigInt` and `Arc` before the sum makes its own, four heap
            // allocations for one difference; one `BigInt` subtraction makes the two of the sum
            // alone, with the same value and form (`From<BigInt>` picks `Small` or `Big` as the
            // sum does). 1640 instructions a difference of two values past `i64` before, in a
            // debug build (callgrind, dry-hash, hm3); the l01_24 bench
            // `the_least_class_of_points_past_i64_scales_linearly`, whose points are past `i64`,
            // went from 1,901,924,582 to 1,751,925,918 instructions at n = 200,000 (-7.89%, on
            // 912bb65e2). A kept value keeps the sum, which collects and folds its terms. Test:
            // `tests::differences_agree_with_sums_of_negations`.
            (Word::Small(_) | Word::Big(_), Word::Small(_) | Word::Big(_)) => {
                (&*self.big() - &*other.big()).into()
            }
            _ => self + &-other,
        }
    }
}

impl Mul for &Num {
    type Output = Num;

    /// A product with a kept value is kept: with a value that is not kept, each coefficient
    /// times it; with a kept value, each pair of terms, a product of cores being one core.
    fn mul(self, other: &Num) -> Num {
        match (&self.0, &other.0) {
            (Word::Small(a), Word::Small(b)) => (*a as i128 * *b as i128).into(),
            (Word::Kept(x), _) if let Some(s) = other.scalar() => {
                if s.is_zero() {
                    return Num::ZERO;
                }
                let terms = x
                    .terms
                    .iter()
                    .map(|(c, core)| (c * &*s, core.clone()))
                    .collect();
                Num::kept(terms, &x.d * &*s, x.den.clone())
            }
            (_, Word::Kept(_)) if self.scalar().is_some() => other * self,
            (Word::Kept(x), Word::Kept(y)) => {
                let mut terms = Vec::with_capacity((x.terms.len() + 1) * (y.terms.len() + 1));
                for (a, p) in &x.terms {
                    for (b, q) in &y.terms {
                        terms.push((mul_int(a, b), p.times(q)));
                    }
                    if !y.d.is_zero() {
                        terms.push((mul_int(a, &y.d), p.clone()));
                    }
                }
                if !x.d.is_zero() {
                    for (b, q) in &y.terms {
                        terms.push((mul_int(&x.d, b), q.clone()));
                    }
                }
                Num::kept(terms, mul_int(&x.d, &y.d), mul_uint(&x.den, &y.den))
            }
            // Neither is kept.
            _ => mul_int(&self.big(), &other.big()).into(),
        }
    }
}

impl Neg for &Num {
    type Output = Num;

    fn neg(self) -> Num {
        match &self.0 {
            Word::Small(a) => (-(*a as i128)).into(),
            Word::Big(a) => (-&**a).into(),
            // A kept value is at least 2^127 or below -2^127, so its negation lies outside
            // i128 too, except for that of 2^127, which is i128::MIN and must be Big.
            Word::Kept(k) if !k.negative && *self == Num::from(BigInt::from(1u32) << 127u32) => {
                Num::from(i128::MIN)
            }
            Word::Kept(k) => Num(Word::Kept(Box::new(k.neg()))),
        }
    }
}

impl Ord for Num {
    /// Values of one sign outside `i64` compare by the sign of their difference, a kept value
    /// whose terms are collected and folded, so equal cores cancel; a root against the power
    /// it came from by `root_power_cmp`. The sign of a kept difference is found at 64 bits
    /// and then at twice as many until it is decided; for values that differ in their leading
    /// bits, as bounds nearly always do, the first pass decides. Equal values in forms that
    /// neither collecting nor folding relates are found equal only at the bits of the value
    /// (the tradeoffs at `Core::same` and `fold`).
    fn cmp(&self, other: &Num) -> Ordering {
        match (&self.0, &other.0) {
            (Word::Small(a), Word::Small(b)) => return a.cmp(b),
            (Word::Big(a), Word::Big(b)) => return a.cmp(b),
            // A value outside i64 lies outside every small one.
            (_, Word::Small(_)) => {
                return if self.signum() < 0 {
                    Ordering::Less
                } else {
                    Ordering::Greater
                };
            }
            (Word::Small(_), _) => return other.cmp(self).reverse(),
            _ => {}
        }
        match self.signum().cmp(&other.signum()) {
            Ordering::Equal => {}
            o => return o,
        }
        if let (Word::Kept(x), Word::Kept(y)) = (&self.0, &other.0)
            && x == y
        {
            return Ordering::Equal;
        }
        if let Some(o) = root_power_cmp(self, other) {
            return o;
        }
        if let Some(o) = root_power_cmp(other, self) {
            return o.reverse();
        }
        // One pass at 64 bits decides values that differ in their leading bits, as bounds nearly
        // always do; the sign of the difference decides the rest.
        let (a, b) = (self.approx(64), other.approx(64));
        if a.below(&b) {
            return Ordering::Less;
        }
        if b.below(&a) {
            return Ordering::Greater;
        }
        (self - other).signum().cmp(&0)
    }
}

/// `a` against `b`, of one sign, when `a` is `±floor(rad ^ (1 / k)) ^ (m * k)` and `b` lies
/// at or past `±rad ^ m`: that power is at most `rad ^ m`, and below it unless `rad` is a
/// perfect `k`-th power, so no digits of the root are needed. This is the comparison of an
/// image of a root bound with the bound it came from, where approximations would agree to
/// every bit of the root.
fn root_power_cmp(a: &Num, b: &Num) -> Option<Ordering> {
    let Word::Kept(x) = &a.0 else {
        return None;
    };
    let [(Atom::Root { rad, k, .. }, exp)] = x.bare()?.0.as_slice() else {
        return None;
    };
    if !exp.is_multiple_of(k) {
        return None;
    }
    let m = exp / k;
    let bound = if m.is_one() {
        Num(Word::Kept(rad.clone()))
    } else {
        Num::bare(false, rad.bare()?.pow(&m))
    };
    let b = if x.negative { -b } else { b.clone() };
    let o = match bound.cmp(&b) {
        Ordering::Less => Ordering::Less,
        // A root of a bare power of one integer is kept only when it is irrational.
        Ordering::Equal
            if rad.bare().and_then(Core::int_power).is_some() || !is_perfect_power(rad, k) =>
        {
            Ordering::Less
        }
        Ordering::Equal => Ordering::Equal,
        Ordering::Greater => return None,
    };
    Some(if x.negative { o.reverse() } else { o })
}

/// Two values given to any precision, in order: at `bits` bits and then at twice as many
/// until their ranges are apart or both are exact.
fn approx_cmp(mut bits: u64, x: impl Fn(u64) -> Approx, y: impl Fn(u64) -> Approx) -> Ordering {
    loop {
        let (a, b) = (x(bits), y(bits));
        if a.below(&b) {
            return Ordering::Less;
        }
        if b.below(&a) {
            return Ordering::Greater;
        }
        if a.is_exact() && b.is_exact() {
            return scaled_cmp(&a.lo, &a.shift, &b.lo, &b.shift);
        }
        bits *= 2;
    }
}

impl PartialOrd for Num {
    fn partial_cmp(&self, other: &Num) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for Num {
    fn eq(&self, other: &Num) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl Eq for Num {}

impl Hash for Num {
    /// A value inside `i128` hashes as itself, and a value outside it by its sign alone. This
    /// agrees with equality for every pair of equal values, whatever their forms: a value in
    /// `i64` is always `Small`, a value in `i128` past `i64` always `Big` (a kept value lies
    /// outside `i128`), so a value inside `i128` has one form and hashes as itself; and two
    /// equal values outside `i128`, `Big` or kept, a sum of cores or a root, have one sign.
    // Complexity tradeoff: a hash table keyed by many values outside i128 puts them in one
    // bucket per sign, so a lookup among n of them costs n comparisons; the answers stay
    // exact. Why: a hash that agrees on equal values must be a function of the value alone,
    // computed alike from every form, and a big value may equal a kept root
    // (`floor(3 ^ (901 / 3))` written out and kept), whose residues, leading bits and bit
    // count each need the root's digits or, near a power of 2, the value's. Trigger: a hash
    // map or set holding many interval ends outside i128. Test:
    // `l01_24_refinement_lattices::ends::equal_values_in_different_forms_hash_alike`;
    // COMPLEXITY.md S33. A complete solution would hash every value outside `i128` by its
    // residue modulo a fixed prime: a big value by `%`, a kept value with integer cores by
    // `Kept::residue`, and a kept value holding a root by the residue of each root written
    // out once and kept in the atom's memo, at the cost of the root's digits; equal values
    // have one residue whatever their forms, so this agrees with equality. Standard version: a
    // hash of the value, O(1) expected per lookup but at the cost of a root's digits; used: one
    // bucket per sign, O(1) to hash and O(n) comparisons per lookup among n such values.
    fn hash<H: Hasher>(&self, h: &mut H) {
        match &self.0 {
            Word::Small(v) => v.hash(h),
            Word::Big(v) if let Ok(s) = i128::try_from(&**v) => s.hash(h),
            Word::Big(_) | Word::Kept(_) => self.signum().hash(h),
        }
    }
}

impl std::str::FromStr for Num {
    type Err = num_bigint::ParseBigIntError;

    /// Decimal text, of any length, read as num-bigint reads it: an optional `-` or `+`, then a
    /// digit, then digits and `_`. The digits are read by halves (`zed_kernel::num::read_digits`),
    /// O(n log^2 n) for `n` digits, where num-bigint's reading is O(n^2).
    fn from_str(s: &str) -> Result<Num, Self::Err> {
        if let Ok(v) = s.parse::<i64>() {
            return Ok(Num::from(v));
        }
        // num-bigint takes off a `-` not followed by `+`, then a `+` not followed by `+`.
        let (sign, body) = match s.strip_prefix('-') {
            Some(tail) if !tail.starts_with('+') => (Sign::Minus, tail),
            _ => (Sign::Plus, s),
        };
        let body = match body.strip_prefix('+') {
            Some(tail) if !tail.starts_with('+') => tail,
            _ => body,
        };
        let digits = body.as_bytes().first().is_some_and(u8::is_ascii_digit)
            && body.bytes().all(|b| b.is_ascii_digit() || b == b'_');
        if !digits {
            // Not decimal digits: num-bigint finds the error, in one pass over the text.
            return s.parse::<BigInt>().map(Num::from);
        }
        let n = match body.contains('_') {
            true => read_digits(&body.replace('_', "")),
            false => read_digits(body),
        };
        Ok(Num::from(BigInt::from_biguint(sign, n)))
    }
}

impl fmt::Display for Num {
    // Complexity tradeoff: a kept value is shown in decimal, written out, at the cost of its
    // digits and their conversion to decimal. Why: a kept value has no shorter decimal text,
    // and the printed value must be one a user can write back. Trigger: printing or
    // serializing an interval end outside i128 made from a power (`canon::serial` writes ends
    // past i64 with this). Test:
    // `l01_24_refinement_lattices::ends::kept_forms_compute_as_their_values_written_out`
    // (each value against its text); COMPLEXITY.md S33. A complete solution would print a
    // kept value in its own form, as Zed text such as `3 ^ 100000000 + 1`, which parses
    // back to the same value.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.0 {
            Word::Small(v) => write!(f, "{v}"),
            Word::Big(v) => write_decimal(f, v),
            Word::Kept(k) => write_decimal(f, &k.expand()),
        }
    }
}

/// `v` in decimal, as num-bigint writes it, the digits by [`to_decimal`]: O(n log^2 n) for `n`
/// words, against num-bigint's `n^1.5` (COMPLEXITY.md K81).
fn write_decimal(f: &mut fmt::Formatter<'_>, v: &BigInt) -> fmt::Result {
    if v.sign() == Sign::Minus {
        f.write_str("-")?;
    }
    f.write_str(&to_decimal(v.magnitude()))
}

#[cfg(test)]
mod completeness;

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::Cell;

    thread_local! {
        /// The calls of `Core::approx` on this thread.
        pub(super) static CORE_APPROXES: Cell<u64> = const { Cell::new(0) };
        /// The largest `bits` of those calls.
        pub(super) static CORE_APPROX_BITS: Cell<u64> = const { Cell::new(0) };
    }

    /// A crate above zed-bignum takes the measured leaves in its own unit tests: zed-bignum's
    /// small leaves come only from its own `cfg(test)` and from the package zed-bignum-small,
    /// which only zed-kernel's unit tests link (zed-bignum `fast::SMALL_LEAVES`;
    /// TEST-kernel-small-leaves-after-bignum-move). zed-kernel's
    /// `num::tests::the_unit_tests_take_the_small_leaves` checks the other side.
    #[test]
    fn the_unit_tests_of_another_crate_take_the_measured_leaves() {
        use zed_bignum::fast::crossover;
        const { assert!(!crossover::SMALL_LEAVES) };
        assert_eq!(crossover::MUL_LEAF, 400);
        assert!(crossover::TOOM_COST.is_finite());
        assert!(crossover::DIV_COST.is_finite());
    }

    /// `is_succ` and the two `at_most_succ` that use it agree with `a == b + 1` and `a <= b + 1`
    /// formed by num-bigint, on every pair of: 0, ±1, ±2, the values next to ±2^63, ±2^64 (one
    /// 64-bit digit full, a carry into a new digit), ±2^128, ±2^192 and 2^128 + 2^64 (a carry
    /// through one and through two full digits, and a full digit in the middle), and random
    /// values of up to 300 bits each with its successor and predecessor (S22-scaling-10_5).
    #[test]
    fn successors_of_wide_values_are_found_without_the_sum() {
        let (mut rng, _) =
            crate::seed::Rng::fresh("successors_of_wide_values_are_found_without_the_sum");
        let one = BigInt::from(1);
        let mut centers = vec![BigInt::from(0), BigInt::from(2)];
        for e in [63u32, 64, 128, 192] {
            centers.push(&one << e);
        }
        centers.push((&one << 128u32) + (&one << 64u32));
        for _ in 0..12 {
            let bits = 1 + rng.below(300);
            let words: Vec<u32> = (0..bits.div_ceil(32))
                .map(|_| rng.next_u64() as u32)
                .collect();
            centers.push(BigInt::from(
                BigUint::new(words) >> (32 * bits.div_ceil(32) - bits),
            ));
        }
        let mut values = Vec::new();
        for c in centers {
            for v in [&c - 1, c.clone(), &c + 1] {
                values.push(-&v);
                values.push(v);
            }
        }
        for a in &values {
            for b in &values {
                let succ = *a == b + 1;
                assert_eq!(is_succ(a, b), succ, "{a} {b}");
                let at_most = *a <= b + 1;
                let (na, nb) = (Num::from(a.clone()), Num::from(b.clone()));
                assert_eq!(na.at_most_succ(&nb), at_most, "Num {a} {b}");
                let (ia, ib) = (Int::from(a.clone()), Int::from(b.clone()));
                assert_eq!(
                    zed_collections::intervals::Discrete::at_most_succ(&ia, &ib),
                    at_most,
                    "Int {a} {b}"
                );
            }
        }
    }

    /// A root whose index `k = 2^32` does not fit a `u32`, of a value of more than `k` bits
    /// (ledger FAIL-roots-binomial-u32-narrowing): the floor root of `2^k` is 2 and the
    /// ceiling root of `2^k + 1` is 3. Before, every index past a `u32` gave 1 and 2, right
    /// only for values of at most `k` bits.
    #[test]
    fn a_root_whose_index_is_past_a_u32_of_a_value_wider_than_it() {
        let k = 1u64 << 32;
        let index = Num::from(BigInt::from(k));
        let power = BigInt::from(1u8) << k;
        let floor = Num::from(power.clone()).floor_root_by(&index);
        assert_eq!(floor, Some(Num::from(BigInt::from(2))));
        let ceil = Num::from(power + 1).ceil_root_by(&index);
        assert_eq!(ceil, Some(Num::from(BigInt::from(3))));
    }

    /// `floor_root(k)` and `ceil_root(k)` of values not kept, for `k` 2, 3 and 7, by the
    /// kernel's `nth_root_rem_uint` (item PERF-wide-odd-base-ratio-9), against num-bigint's
    /// `nth_root`: 0 to 3, `k`-th powers, one below and one above them, and random values of 1
    /// to 300 and 20,000 bits.
    #[test]
    fn roots_of_values_not_kept_agree_with_num_bigint() {
        let (mut rng, _) =
            crate::seed::Rng::fresh("roots_of_values_not_kept_agree_with_num_bigint");
        for k in [2u32, 3, 7] {
            let check = |v: BigUint| {
                let s = v.nth_root(k);
                let exact = s.pow(k) == v;
                let n = Num::from(BigInt::from(v.clone()));
                assert_eq!(
                    n.floor_root(k),
                    Num::from(BigInt::from(s.clone())),
                    "{k} {v}"
                );
                let up = s + u32::from(!exact);
                assert_eq!(n.ceil_root(k), Num::from(BigInt::from(up)), "{k} {v}");
            };
            for v in 0u32..4 {
                check(BigUint::from(v));
            }
            for bits in (1..=300u64).chain([20_000]) {
                let words: Vec<u64> = (0..bits.div_ceil(64)).map(|_| rng.next_u64()).collect();
                let mut v = BigUint::from_slice(
                    &words
                        .iter()
                        .flat_map(|w| [*w as u32, (w >> 32) as u32])
                        .collect::<Vec<_>>(),
                ) >> (64 * bits.div_ceil(64) - bits);
                v.set_bit(bits - 1, true);
                let pk = v.nth_root(k).pow(k);
                if !pk.is_zero() {
                    check(&pk - 1u32);
                }
                check(pk.clone());
                check(pk + 1u32);
                check(v);
            }
        }
    }

    /// `kept_sum(lo, hi)`: the sum of `(3 + 2 i) ^ 200` for `i` in `lo..hi`, built by halves.
    fn kept_sum(lo: usize, hi: usize) -> Num {
        if hi - lo == 1 {
            return Num::from(3 + 2 * lo as i64).pow(200);
        }
        let mid = (lo + hi) / 2;
        &kept_sum(lo, mid) + &kept_sum(mid, hi)
    }

    /// A sum of two kept sums of `n` terms each approximates each of the `2 n` cores to 64 bits
    /// once in `collect`, and once more in `Kept::approx` when `Num::kept` places the value,
    /// so `4 n` approximations in all; computing both approximations again at each comparison
    /// in `collect`, as before, made 764 for n = 64, about 12 n (item
    /// FAIL-l0124-kept-sum-benches-rising-load).
    #[test]
    fn a_sum_of_kept_sums_approximates_each_core_once_in_collect() {
        let n = 64;
        let (x, y) = (kept_sum(0, n), kept_sum(n, 2 * n));
        CORE_APPROXES.with(|c| c.set(0));
        let s = &x + &y;
        let calls = CORE_APPROXES.with(|c| c.get());
        assert!(s.signum() > 0);
        assert_eq!(
            s,
            kept_sum(0, 2 * n),
            "the sum does not depend on how it is built"
        );
        assert!(
            calls <= 4 * n as u64,
            "{calls} approximations of cores for 2 n = {} terms",
            2 * n
        );
    }

    /// A product or sum of one kept power by small numbers is placed past `i128` by the least
    /// size of its core, with no approximation: before, `-7 * 3^(2^4096)` approximated the
    /// core at 64, 128, ... bits until the lower end stayed above 0, and `3 ^ (2^(2^20))` did
    /// not finish in 30 s (item PERF-fold-power-of-huge-exponent). Values on both sides of the
    /// shortcut's bound, `3^300` (least size 300) and `3^81` (least size 81, under the bound
    /// of 128 plus the bits of `d` and `den`), equal their values written out.
    #[test]
    fn a_kept_power_of_a_huge_exponent_is_placed_by_its_least_size() {
        let x = Num::power(false, BigUint::from(3u32), BigUint::one() << 4096u32);
        CORE_APPROXES.with(|c| c.set(0));
        let y = &x * &Num::from(-7);
        let z = &x + &Num::from(11);
        let calls = CORE_APPROXES.with(|c| c.get());
        assert_eq!(calls, 0, "approximations of cores to place one kept term");
        assert!(y.is_kept() && y.signum() < 0);
        assert!(z.is_kept() && z.signum() > 0);
        for e in [81u32, 300] {
            let x = Num::power(false, BigUint::from(3u32), BigUint::from(e));
            let v = BigInt::from(3u32).pow(e);
            for (c, d) in [(-7i64, 11i64), (1, -1), (5, 0), (-1, 1 << 40)] {
                let got = &(&x * &Num::from(c)) + &Num::from(d);
                let want = Num::from(&v * c + d);
                assert_eq!(got, want, "{c} * 3^{e} + {d}");
                assert_eq!(got.signum(), want.signum(), "{c} * 3^{e} + {d}");
            }
        }
    }

    /// Sums of two to four powers of 2, 3, 5 and 6 of about one size (300 to 600 bits), with
    /// coefficients -3 to 3 and an added `d`, so that some cancel in their high bits: where
    /// `Kept::dominant_sign` decides, the value written out lies outside `i128` with that
    /// sign, and every sum built by `+` equals its value written out, in value and sign
    /// (item PERF-num-kept-multi-term-precision).
    #[test]
    fn sums_placed_by_the_logarithms_of_their_terms_equal_their_values_written_out() {
        let (mut rng, _) = crate::seed::Rng::fresh(
            "sums_placed_by_the_logarithms_of_their_terms_equal_their_values_written_out",
        );
        let edge = BigInt::one() << 127u32;
        let (mut decided, mut undecided) = (0, 0);
        for _ in 0..400 {
            let size = 300 + rng.next_u64() % 300;
            let d = (rng.next_u64() % 2001) as i64 - 1000;
            let mut terms = Vec::new();
            let (mut got, mut want) = (Num::from(d), BigInt::from(d));
            for _ in 0..1 + rng.next_u64() % 4 {
                let b = [2u32, 3, 5, 6][(rng.next_u64() % 4) as usize];
                let e = (size as f64 / f64::from(b).log2()) as u32 + (rng.next_u64() % 3) as u32;
                let c = (rng.next_u64() % 7) as i64 - 3;
                let power = Num::power(false, BigUint::from(b), BigUint::from(e));
                got = &got + &(&power * &Num::from(c));
                want += BigInt::from(b).pow(e) * c;
                terms.push((
                    BigInt::from(c),
                    Core::power(BigUint::from(b), BigUint::from(e)),
                ));
            }
            assert_eq!(got, Num::from(want.clone()), "the sum {terms:?} + {d}");
            assert_eq!(
                got.signum(),
                Num::from(want.clone()).signum(),
                "{terms:?} + {d}"
            );
            let mut terms = collect(terms);
            fold(&mut terms);
            if terms.is_empty() {
                continue;
            }
            let k = Kept {
                terms,
                d: BigInt::from(d),
                den: BigUint::one(),
                negative: false,
            };
            match k.dominant_sign() {
                Some(negative) => {
                    decided += 1;
                    assert!(want.magnitude() > edge.magnitude(), "{k:?} is past i128");
                    assert_eq!(negative, want.sign() == Sign::Minus, "the sign of {k:?}");
                }
                None => undecided += 1,
            }
        }
        assert!(
            decided > 0 && undecided > 0,
            "{decided} decided, {undecided} not"
        );
    }

    /// Sums of powers by an exponent of 4097 bits, `3^e - 3^(e - 1)`, `2^e - 3^e` and `5^e -
    /// 3^e + 2^e`, are ordered and placed with no core approximated past 64 bits. Before
    /// PERF-num-kept-multi-term-precision `collect` and `Num::kept` approximated them at 128,
    /// 256, ... bits until past the 4097 bits of `e`.
    #[test]
    fn sums_of_powers_of_a_huge_exponent_are_placed_by_their_logarithms() {
        let e = BigUint::one() << 4096u32;
        let power = |b: u32, e: BigUint| Num::power(false, BigUint::from(b), e);
        let (three, below) = (power(3, e.clone()), power(3, &e - 1u32));
        let (two, five) = (power(2, e.clone()), power(5, e.clone()));
        CORE_APPROX_BITS.with(|c| c.set(0));
        let x = &three - &below;
        let y = &two - &three;
        let z = &(&five - &three) + &two;
        let widest = CORE_APPROX_BITS.with(|c| c.get());
        assert!(x.is_kept() && x.signum() > 0);
        assert!(y.is_kept() && y.signum() < 0);
        assert!(z.is_kept() && z.signum() > 0);
        assert_eq!(widest, 64, "the most bits a core was approximated to");
        assert!((&x - &(&below * &Num::from(2))).is_zero());
        assert!(y < x && x < z);
    }

    #[test]
    fn bit_and_reads_each_sign_as_twos_complement_at_every_size() {
        // Small values agree with `i128`'s `&`, every sign.
        for a in -40i128..=40 {
            for b in -40i128..=40 {
                assert_eq!(&Int::from(a) & &Int::from(b), Int::from(a & b), "{a} & {b}");
            }
        }
        // Shifted past 128 bits, the and is the shifted and: `(a·2^k) & (b·2^k) = (a & b)·2^k`
        // for every sign, so a big value on either side, or both, keeps its sign's bits.
        let k = Int::from(BigInt::from(1) << 200u32);
        for (a, b) in [
            (-1i128, 5i128),
            (5, -1),
            (-4, -3),
            (12, 10),
            (-12, 10),
            (i128::MIN, -1),
        ] {
            let (x, y) = (&Int::from(a) * &k, &Int::from(b) * &k);
            assert_eq!(&x & &y, &Int::from(a & b) * &k, "({a}·2^200) & ({b}·2^200)");
        }
        // One big and one small: `-1` keeps the other whole, a nonnegative small one masks.
        let big = &k + &Int::from(13);
        assert_eq!(&Int::from(-1) & &big, big);
        assert_eq!(&big & &Int::from(-1), big);
        assert_eq!(&big & &Int::from(7), Int::from(5));
        assert_eq!(&(-&big) & &Int::from(7), Int::from(3));
    }

    #[test]
    fn values_past_i128_keep_their_order_and_come_back_small() {
        let max = Int::from(i128::MAX);
        let min = Int::from(i128::MIN);
        let past = &max + &Int::ONE;
        assert_eq!(past.to_i128(), None);
        assert_eq!((&past - &Int::ONE).to_i128(), Some(i128::MAX));
        assert!(past > max && min > &min - &Int::ONE);
        assert_eq!(-&past, min);
        assert!(past > min && &min - &Int::ONE < -&past);
        // -i128::MIN is past i128; negated again it is the small value, one form for one value.
        assert_eq!(-&(-&min), min);
        assert_eq!(min.abs(), &max + &Int::ONE);
        assert_eq!((&max * &max).div_floor(&max), max);
        assert_eq!((&(&max * &max) + &Int::from(5)).mod_floor(&max), 5.into());
    }

    #[test]
    fn division_rounds_down_and_the_gcd_is_never_negative() {
        let (a, m) = (Int::from(-7), Int::from(2));
        assert_eq!(a.div_floor(&m), Int::from(-4));
        assert_eq!(a.mod_floor(&m), Int::ONE);
        assert_eq!(Int::from(-12).gcd(&Int::from(18)), Int::from(6));
        // Both are powers of two, so the gcd of i128::MIN with itself does not fit in i128.
        let min = Int::from(i128::MIN);
        assert_eq!(min.gcd(&min), -&min);
        assert_eq!(Int::ZERO.gcd(&Int::from(-5)), Int::from(5));
    }

    /// `Int::lcm` against num-bigint's lcm, on small operands, a common factor, one operand
    /// dividing the other, and operands past i128 whose product is past i128 too.
    #[test]
    fn lcm_of_positive_integers() {
        let big: BigInt = BigInt::from(3u8).pow(100) * 1_000_003;
        let cases: Vec<(BigInt, BigInt)> = vec![
            (BigInt::from(1), BigInt::from(1)),
            (BigInt::from(4), BigInt::from(6)),
            (BigInt::from(6), BigInt::from(12)),
            (BigInt::from(7), BigInt::from(13)),
            (BigInt::from(i128::MAX), BigInt::from(i128::MAX - 1)),
            (big.clone(), BigInt::from(9)),
            (
                big.clone(),
                BigInt::from(999_983) * BigInt::from(3u8).pow(120),
            ),
        ];
        for (a, b) in cases {
            let want = Int::from(Integer::lcm(&a, &b));
            assert_eq!(Int::from(a.clone()).lcm(&Int::from(b.clone())), want);
            assert_eq!(Int::from(b).lcm(&Int::from(a)), want);
        }
    }

    /// `Int::product` against a running product of num-bigint's, on no factor, one, products
    /// within i128, products that pass i128 by one factor, zeros, signs, and 1 to 40 random
    /// factors of up to 320 bits.
    #[test]
    fn products_agree_with_a_running_product() {
        let running = |xs: &[Int]| Int::from(xs.iter().fold(BigInt::from(1), |p, x| p * &*x.big()));
        let big = Int::from(BigInt::from(3u8).pow(100));
        let mut cases: Vec<Vec<Int>> = vec![
            vec![],
            vec![Int::from(-7)],
            vec![Int::from(6), Int::from(-7), Int::from(11)],
            vec![Int::from(i128::MAX), Int::from(2)],
            vec![Int::from(i128::MIN), Int::from(-1)],
            vec![Int::from(i64::MAX), Int::from(i64::MAX), Int::from(-3)],
            vec![big.clone(), Int::ZERO, Int::from(5)],
            vec![-&big, big.clone(), Int::from(-1)],
        ];
        let mut x = 0x9e37_79b9_7f4a_7c15u64;
        let mut next = || {
            x = x
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            x
        };
        for len in 1..=40 {
            let xs = (0..len)
                .map(|_| {
                    let words = (next() % 5) as usize;
                    let mag = (0..=words).fold(BigInt::from(next() >> (next() % 64)), |m, _| {
                        (m << 64) + next()
                    });
                    Int::from(if next() & 1 == 1 { -mag } else { mag })
                })
                .collect();
            cases.push(xs);
        }
        for xs in cases {
            assert_eq!(Int::product(&xs), running(&xs), "{xs:?}");
        }
    }

    /// `Int::gcd` past i128 agrees with num-bigint's for every sign, for operands of one word
    /// against many, with shared powers of 2 and odd factors, and with zero.
    #[test]
    fn the_big_gcd_agrees_with_num_bigint() {
        let big: BigInt = BigInt::from(3u8).pow(200) * BigInt::from(2u8).pow(70) * 1_000_003;
        let other: BigInt = BigInt::from(3u8).pow(150) * BigInt::from(2u8).pow(90) * 999_983;
        let cases: Vec<(BigInt, BigInt)> = vec![
            (BigInt::ZERO, BigInt::ZERO),
            (big.clone(), other.clone()),
            (big.clone(), BigInt::from(1)),
            (big.clone(), BigInt::from(6)),
            (big.clone(), BigInt::from(35)),
            (big.clone(), BigInt::from(u64::MAX)),
            (BigInt::from(i128::MIN), big.clone()),
            (BigInt::from(i128::MIN), BigInt::from(1u8) << 200),
            (BigInt::from(1u8) << 300, BigInt::from(3u8) << 200),
            (big.clone(), BigInt::ZERO),
            (big.clone(), big.clone()),
            (big.clone(), BigInt::from(i128::MAX) * 7),
        ];
        for (a, b) in cases {
            for (sa, sb) in [(1i8, 1i8), (-1, 1), (1, -1), (-1, -1)] {
                let (x, y): (BigInt, BigInt) = (&a * sa, &b * sb);
                let want = Int::from(Integer::gcd(&x, &y));
                assert_eq!(Int::from(x.clone()).gcd(&Int::from(y.clone())), want);
                assert_eq!(Int::from(y).gcd(&Int::from(x)), want);
            }
        }
    }

    /// The 64-bit, 128-bit and big paths of `div_floor` and `mod_floor` give the floor quotient
    /// and remainder of `BigInt` for every sign of each operand, at and across the ends of
    /// `i64` and `i128`, including `MIN / -1`, whose quotient does not fit.
    #[test]
    fn floor_division_agrees_on_every_path_for_every_sign() {
        let mut ends: Vec<BigInt> = [1, 2, 3, 7]
            .map(BigInt::from)
            .into_iter()
            .chain([i128::from(i64::MAX), i128::MAX].into_iter().flat_map(|v| {
                let v = BigInt::from(v);
                [&v - 1, v.clone(), &v + 1, &v + 2]
            }))
            .chain([BigInt::from(1) << 200])
            .collect();
        ends.extend(ends.clone().into_iter().map(|v| -v));
        let zero = BigInt::zero();
        for a in ends.iter().chain([&zero]) {
            for m in &ends {
                let (x, y) = (Int::from(a.clone()), Int::from(m.clone()));
                let want = (Int::from(a.div_floor(m)), Int::from(a.mod_floor(m)));
                assert_eq!((x.div_floor(&y), x.mod_floor(&y)), want, "{a} by {m}");
            }
        }
    }

    /// A random integer of `0..2^bits`, `bits` drawn from [`WIDTHS`].
    fn random_int(rng: &mut crate::seed::Rng) -> Int {
        let bits = rng.pick(&WIDTHS);
        let words: Vec<u64> = (0..bits.div_ceil(64)).map(|_| rng.next_u64()).collect();
        let mut v = BigUint::from(0u8);
        for w in words.iter().rev() {
            v = (v << 64u32) + BigUint::from(*w);
        }
        Int::from(BigInt::from(v >> (64 * bits.div_ceil(64) - bits)))
    }

    /// The widths the tests of the modular routines draw from: one word (zed-numtheory's word
    /// Euclid), two words (`i128` extended Euclid), and past `i128` (the kernel's half gcd).
    const WIDTHS: [usize; 6] = [3, 20, 64, 100, 127, 400];

    /// `Int::inverse_mod` against a scan of `0..m` for every `m` up to 40 and `a` in
    /// `-50..50`, and at random widths against the definition (`a x == 1 (mod m)`, `x` in
    /// `0..m`) and Euclid over `Int` (`euclid_bezout`, the O(n^2) copy it replaced), whose
    /// cofactor reduced modulo `m` is the unique inverse; `None` exactly when the gcd is not 1.
    #[test]
    fn inverses_modulo_an_integer_at_every_width() {
        for m in 1..=40i128 {
            for a in -50..50i128 {
                let want = (0..m).find(|x| (a * x).rem_euclid(m) == 1 % m);
                let got = Int::from(a).inverse_mod(&Int::from(m));
                assert_eq!(got, want.map(Int::from), "{a}^-1 mod {m}");
            }
        }
        let (mut rng, _) = crate::seed::Rng::fresh("inverses_modulo_an_integer_at_every_width");
        let mut found = 0;
        for _ in 0..600 {
            let m = &random_int(&mut rng) + &Int::ONE;
            let mut a = random_int(&mut rng);
            if rng.coin() {
                a = -&a;
            }
            let (g, s, _) = a.mod_floor(&m).euclid_bezout(&m);
            match a.inverse_mod(&m) {
                Some(x) => {
                    found += 1;
                    assert_eq!(g, Int::ONE, "{a} mod {m}");
                    assert!(!x.is_negative() && x < m, "{a}^-1 mod {m} = {x}");
                    assert_eq!((&a * &x).mod_floor(&m), Int::ONE.mod_floor(&m));
                    assert_eq!(x, s.mod_floor(&m));
                }
                None => assert_ne!(g, Int::ONE, "{a} mod {m}"),
            }
        }
        assert!(found >= 200, "only {found} inverses found");
    }

    /// `Int::crt_pair` against a scan of `0..lcm(m1, m2)` for every `m1, m2` up to 12 and
    /// residues in `-13..13`; at random widths, the class found lies in both classes, its
    /// modulus is the lcm, and `None` exactly when `gcd(m1, m2)` does not divide `r2 - r1`.
    #[test]
    fn crt_pairs_agree_with_a_scan() {
        for m1 in 1..=12i128 {
            for m2 in 1..=12i128 {
                let lcm = Int::from(m1).lcm(&Int::from(m2));
                let l = lcm.to_i128().expect("small");
                for r1 in -13..13i128 {
                    for r2 in (-13..13i128).step_by(3) {
                        let want = (0..l)
                            .find(|x| (x - r1).rem_euclid(m1) == 0 && (x - r2).rem_euclid(m2) == 0)
                            .map(|x| (Int::from(x), lcm.clone()));
                        let got = Int::crt_pair(&r1.into(), &m1.into(), &r2.into(), &m2.into());
                        assert_eq!(got, want, "{r1} mod {m1} and {r2} mod {m2}");
                    }
                }
            }
        }
        let (mut rng, _) = crate::seed::Rng::fresh("crt_pairs_agree_with_a_scan");
        let mut solved = 0;
        for _ in 0..400 {
            // A shared factor half the time, so both answers are common.
            let common = &random_int(&mut rng) + &Int::ONE;
            let mut m1 = &random_int(&mut rng) + &Int::ONE;
            let mut m2 = &random_int(&mut rng) + &Int::ONE;
            if rng.coin() {
                (m1, m2) = (&m1 * &common, &m2 * &common);
            }
            let r1 = random_int(&mut rng);
            let mut r2 = random_int(&mut rng);
            if rng.coin() {
                // `r2 == r1 (mod gcd)`, so there is an answer.
                r2 = &r1 + &(&m1.gcd(&m2) * &r2);
            }
            let g = m1.gcd(&m2);
            match Int::crt_pair(&r1, &m1, &r2, &m2) {
                Some((r, l)) => {
                    solved += 1;
                    assert_eq!(l, m1.lcm(&m2));
                    assert!(!r.is_negative() && r < l);
                    assert_eq!(r.mod_floor(&m1), r1.mod_floor(&m1));
                    assert_eq!(r.mod_floor(&m2), r2.mod_floor(&m2));
                }
                None => assert!(!(&r2 - &r1).mod_floor(&g).is_zero()),
            }
        }
        assert!(solved >= 100, "only {solved} pairs solved");
    }

    /// `Int::crt` against a left fold of `Int::crt_pair`, on no pair, moduli of 1, coprime
    /// moduli (the tree path), moduli that share factors (the pairwise path), conflicts, and
    /// negative residues.
    #[test]
    fn crts_agree_with_pairs() {
        let fold = |pairs: &[(Int, Int)]| {
            (pairs.iter()).try_fold((Int::ZERO, Int::ONE), |(r, m), (r2, m2)| {
                Int::crt_pair(&r, &m, r2, m2)
            })
        };
        let p = |r: i64, m: i64| (Int::from(r), Int::from(m));
        let big = Int::from(BigInt::from(2u8).pow(127) - 1);
        let cases: Vec<Vec<(Int, Int)>> = vec![
            vec![],
            vec![p(5, 1), p(0, 1)],
            vec![p(2, 3), p(3, 5), p(2, 7)],
            vec![p(-1, 4), p(4, 9), p(-7, 25), p(1, 1)],
            vec![p(2, 6), p(5, 9)],
            vec![p(1, 6), p(5, 9), p(1, 4)],
            vec![p(3, 12), p(7, 8), p(1, 18)],
            vec![(Int::from(-5), big.clone()), p(10, 1 << 40), p(3, 5)],
            vec![(Int::from(9), big.clone()), (Int::from(10), big.clone())],
        ];
        for pairs in cases {
            assert_eq!(Int::crt(pairs.clone()), fold(&pairs), "{pairs:?}");
        }
    }

    /// `Int::solve_linear_congruence` against a scan of `0..m` for every `m` up to 30 and `a`,
    /// `b` in `-31..31`: the least solution and the period `m / gcd(a, m)`; at random widths,
    /// the solution solves, lies below the period, and `None` exactly when `gcd(a, m)` does not
    /// divide `b`.
    #[test]
    fn linear_congruences_agree_with_a_scan() {
        for m in 1..=30i128 {
            for a in -31..31i128 {
                for b in -31..31i128 {
                    let want = (0..m).find(|t| (a * t - b).rem_euclid(m) == 0).map(|t| {
                        let p = m / Int::from(a).gcd(&Int::from(m)).to_i128().expect("small");
                        (Int::from(t), Int::from(p))
                    });
                    let got = Int::from(a).solve_linear_congruence(&b.into(), &m.into());
                    assert_eq!(got, want, "{a} t == {b} mod {m}");
                }
            }
        }
        let (mut rng, _) = crate::seed::Rng::fresh("linear_congruences_agree_with_a_scan");
        for _ in 0..400 {
            let m = &random_int(&mut rng) + &Int::ONE;
            let a = random_int(&mut rng);
            let mut b = random_int(&mut rng);
            if rng.coin() {
                b = &a * &b;
            }
            let g = a.gcd(&m);
            match a.solve_linear_congruence(&b, &m) {
                Some((t, p)) => {
                    assert_eq!(p, m.div_floor(&g));
                    assert!(!t.is_negative() && t < p);
                    assert!(
                        (&(&a * &t) - &b).mod_floor(&m).is_zero(),
                        "{a} t == {b} mod {m}"
                    );
                }
                None => assert!(!b.mod_floor(&g).is_zero()),
            }
        }
    }

    /// `a - b` is `a + (-b)` in value and in form (`Small`, `Big` or kept, read from `Debug`),
    /// and the num-bigint difference for values not kept, on every pair of: 0, ±1, the values
    /// next to ±2^63, ±2^64 and ±2^127, random values of up to 300 bits, and `3^(2^40)` and
    /// its negation (kept, the path of the sum).
    #[test]
    fn differences_agree_with_sums_of_negations() {
        let (mut rng, _) = crate::seed::Rng::fresh("differences_agree_with_sums_of_negations");
        let one = BigInt::from(1);
        let mut centers = vec![BigInt::from(0)];
        for e in [63u32, 64, 127] {
            centers.push(&one << e);
        }
        for _ in 0..12 {
            let bits = 1 + rng.below(300);
            let words: Vec<u32> = (0..bits.div_ceil(32))
                .map(|_| rng.next_u64() as u32)
                .collect();
            centers.push(BigInt::from(
                BigUint::new(words) >> (32 * bits.div_ceil(32) - bits),
            ));
        }
        let mut values = Vec::new();
        for c in centers {
            for v in [&c - 1, c.clone(), &c + 1] {
                values.push(Num::from(-&v));
                values.push(Num::from(v));
            }
        }
        let kept = Num::from(3).pow_by(&Num::from(1i64 << 40)).unwrap();
        assert!(kept.is_kept());
        values.push(-&kept);
        values.push(kept);
        for a in &values {
            for b in &values {
                let d = a - b;
                let s = a + &-b;
                assert_eq!(format!("{d:?}"), format!("{s:?}"), "{a:?} - {b:?}");
                if !a.is_kept() && !b.is_kept() {
                    assert_eq!(*d.big(), &*a.big() - &*b.big(), "{a:?} - {b:?}");
                }
            }
        }
    }
}
