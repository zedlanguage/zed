//! Exact numbers (step L1.17): unbounded integers, rationals, and the order of numbers by
//! value across `int`, `rat` and floats (DESIGN.md sec:order, the natural order).
//!
//! The semantic `int` and `rat` are unbounded (sec:domains), and the evaluator sets no size
//! limit on them. An integer inside the 64-bit range is a [`Value::Int`](crate::Value::Int);
//! one outside it is a `Value::Big` holding a [`Rat`], so every integer has one representation
//! and the fast path stays a machine word.
//!
//! A [`Rat`] is `n/d * prod p^e`: a reduced rational, and powers of primes with unbounded
//! exponents that are kept as exponents, not built. A decimal literal with an exponent is the
//! case of the primes 2 and 5, so `1.345e932` is `269 * 2^929 * 5^930` and costs its digits
//! and the exponent's, not the value's 3100 bits; `2 ^ 2 ^ 40` is `2^(2^40)`. Products,
//! quotients and powers add and multiply exponents. Order is decided by bounds on the two
//! values (`bound`), equality by the normal form, and a sum builds only the part of the
//! operands above their common powers. Printing builds the digits, at a cost proportional to
//! them. A value with no prime powers is a plain reduced rational, whose arithmetic is what it
//! was before the powers.

mod bound;
pub mod coprime;
pub mod dec;
mod digit_text;
mod fast;
pub mod float_mod;
mod float_text;
mod least_root;
mod room;
pub mod trees;

use std::borrow::Cow;
use std::cell::Cell;
use std::cmp::Ordering;
use std::fmt;
use std::sync::OnceLock;
use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering::Relaxed;

use num_bigint::{BigInt, BigUint, Sign};
use num_integer::Integer;
use num_traits::{One, Pow, Signed, ToPrimitive, Zero};
use zed_collections::sorted::sorted_get;

use crate::machine_int::BitLen;
use bound::{Format, Product};
use dec::Dec;
#[doc(hidden)]
pub use fast::crossover;
#[cfg(feature = "method-counts")]
pub use fast::method_counts;
use fast::{LEAF_DIGITS, built, read_digits_by};
pub use fast::{
    PRINT_HANDOFF, PRINT_WHOLE, mul as mul_uint, mul_int, pow as pow_uint, to_decimal,
    to_decimal_split, to_decimal_split_at,
};
pub(crate) use fast::{mul_cost, squares_by_transform};
pub use float_text::{FloatFormat, read_f32_ieee, read_f64_ieee, read_float, show_f32, show_f64};
pub use least_root::{least_root, remainders, sqrt_rem_uint};
pub use room::{
    LiteralRounding, TooLarge, about, bits_of_digits, bytes_of, bytes_text, digits_of_bits,
    fixed_room, machine_memory, memory_clause, room,
};
use room::{least_bits, least_log2};
use zed_numtheory::m61::{self, P as MERSENNE_61};
use zed_numtheory::{factor, gcd_big_u64, is_prime, mul_mod, pow_mod_big, rem_big_u64};

/// How [`Rat::round_whole`] rounds a number to a whole one: the rules of `round` (ties to
/// even), `round(x, ties: #away)`, `floor`, `ceil`, `trunc` and `awayFromZero` (DESIGN.md
/// sec:facets, "Rounding to a whole number").
// Source of the two names to the nearest: IEEE Std 754-2019, "IEEE Standard for Floating-Point
// Arithmetic", IEEE, 2019, doi:10.1109/IEEESTD.2019.8766229, section 4.3, "Rounding-direction
// attributes". Sketch: roundTiesToEven delivers the representable value nearest the exact
// result and, of two equally near, the one with an even least significant digit;
// roundTiesToAway delivers, of two equally near, the one larger in magnitude. Here the
// "representable values" are the whole numbers, so even means an even whole number. Read
// 2026-11-20 in the 2019 text (the copy named at the `sqrt` rule in `eval.rs`), 4.3.1,
// "Rounding-direction attributes to nearest", p. 27: roundTiesToEven, "the floating-point
// number nearest to the infinitely precise result shall be delivered; if the two nearest
// floating-point numbers bracketing an unrepresentable infinitely precise result are equally
// near, the one with an even least significant digit shall be delivered; if that is not
// possible, the one larger in magnitude shall be delivered"; roundTiesToAway, "if the two
// nearest ... are equally near, the one with larger magnitude shall be delivered". The case
// "if that is not possible" (two odd neighbors, for one-digit precision) cannot happen for
// whole numbers, of which one of any two neighbors is even. And 4.3.2, "Directed rounding
// attributes", p. 27: roundTowardPositive gives the number "closest to and no less than the
// infinitely precise result", roundTowardNegative the one "closest to and no greater than"
// it, roundTowardZero the one "closest to and no greater in magnitude than" it; these are
// `ceil`, `floor` and `trunc` here.
//
// Every one of these rules is monotone: x <= y gives round(x) <= round(y). The standard
// states this only for conversions to and from character sequences (5.12.2, NOTE 1, p. 46,
// "Conversions are monotonic"), so here is the proof from the definitions above, for any
// set of representable values (floats with their infinities, or whole numbers). Directed:
// roundTowardNegative(x) is the greatest value <= x, and every value <= x is <= y, so it is
// <= roundTowardNegative(y); roundTowardPositive is the mirror image, and roundTowardZero is
// roundTowardNegative on x >= 0 and roundTowardPositive on x <= 0, both monotone and both 0
// at 0. To nearest: let r = round(x), s = round(y), x <= y, and suppose s < r. Let f(t) =
// |t - s| - |t - r|; for s < r it is -(r - s) up to s, 2t - r - s between, r - s from r on,
// so f does not decrease. r nearest to x gives f(x) >= 0, s nearest to y gives f(y) <= 0, so
// 0 <= f(x) <= f(y) <= 0 and f(x) = f(y) = 0, which forces x = y = (r + s) / 2: one tie
// broken two ways. But both tie rules pick one of the two neighbors by a fixed property (even
// digit, or larger magnitude), so they pick the same one, r = s, a contradiction. Overflow:
// 4.3.1 sends every result of magnitude at least b^emax (b - b^(1-p) / 2) to the infinity of
// its sign. If y is at or past that bound, round(y) = +inf is above every value; if x is at
// or past its negative, round(x) = -inf is below every value; otherwise x and y both lie
// inside, where the nearest values are finite and the proof above applies. (Whole numbers
// have no largest one, so this case does not arise for `Rat::round_whole`.) zedc-lattice
// `grade.rs` relies on this proof.
// Departure: the
// standard rounds to a float format; `Rat::round_whole` rounds an exact rational to an integer,
// so no precision or overflow enters. Tests: `l01_18_scalar_interpreter::rounding`, which
// checks ties at both signs under both rules (it catches a tie sent the wrong way, not a
// misreading of the standard shared by the test and the code). Other sites that name these
// rules point here.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Rounding {
    /// To the nearest, a tie to the even neighbor (IEEE 754 roundTiesToEven).
    TiesEven,
    /// To the nearest, a tie away from zero (IEEE 754 roundTiesToAway).
    TiesAway,
    /// Toward −∞.
    Floor,
    /// Toward +∞.
    Ceil,
    /// Toward zero.
    Trunc,
    /// Away from zero.
    AwayFromZero,
}

/// An exact number `num/den * prod p^e`: `num/den` reduced with `den` positive, the primes
/// `p` distinct and in increasing order, each `e` nonzero, and `num` and `den` divisible by
/// none of the `p`. Zero has no powers.
///
/// A value read from a decimal literal whose exponent does not fit an `i64`, such as `1eNr`
/// with `N` of thousands of digits, holds that exponent as its decimal digits in `ten`: the
/// value is then `num/den * prod p^e * 10^t` (see `Ten`).
#[derive(Clone)]
pub struct Rat {
    num: BigInt,
    den: BigInt,
    pows: Box<[(u64, BigInt)]>,
    ten: Option<Box<Ten>>,
}

/// The factor `10^t` of a [`Rat`], `t` held as its decimal digits (DESIGN.md sec:domains,
/// "Kept powers", and step L1.17b; plan rows KEPT-power-form and PERF-rat-literal-text-length).
/// The `Rat` holding it keeps these invariants: `t` does not fit an `i64` (a smaller one is
/// folded into the exponents of 2 and 5, at no conversion of note); 2 and 5 divide neither
/// `num` nor `den`; and the exponents of 2 and 5 in `pows` are positive with at most one of the
/// two listed, so the common power of ten of the value is all in `t`. The operations of
/// [`Rat::decimal`], [`Rat::literal_text`], equality, order, [`Rat::mul`], [`Rat::div`],
/// [`Rat::pow`] by an exponent of one word, [`Rat::neg`], [`Rat::residues`] and
/// [`Rat::integer_residues`] work on the digits of `t` in O(n); every other operation works on
/// `bin`, the same value with `t` converted to binary and folded into the exponents of 2 and
/// 5, made once at O(n log^2 n) and kept (the conversion [`dec::conversions`] counts).
#[derive(Clone, Debug)]
struct Ten {
    t: Dec,
    bin: OnceLock<Rat>,
}

impl Rat {
    /// `num / den`, reduced; `None` when `den` is zero.
    pub fn new(num: BigInt, den: BigInt) -> Option<Self> {
        if den.is_zero() {
            return None;
        }
        let (num, den) = reduce(num, den);
        Some(Rat::plain(num, den))
    }

    /// `num / den` when it is already in lowest terms with `den` above 1, the form `String`
    /// writes for a rational that is not an integer; `None` otherwise, so `0/5`, `2/4`, `3/1`
    /// and a negative `den` are `None`. The test is one gcd and nothing is divided.
    pub fn in_lowest_terms(num: BigInt, den: BigInt) -> Option<Self> {
        (den > BigInt::one() && gcd(&num, &den).is_one()).then(|| Rat::plain(num, den))
    }

    fn plain(num: BigInt, den: BigInt) -> Rat {
        Rat {
            num,
            den,
            pows: Box::default(),
            ten: None,
        }
    }

    /// It with the decimal exponent `t` of its [`Ten`] converted to binary and folded into the
    /// exponents of 2 and 5: itself when it holds none, else the form made at the first call,
    /// at O(n log^2 n) on the `n` digits of `t`, and kept. Every operation that does not read
    /// the digits works on this.
    fn bin(&self) -> &Rat {
        match &self.ten {
            None => self,
            Some(ten) => ten.bin.get_or_init(|| {
                let t = ten.t.to_bigint();
                self.rest().times_ten(&t)
            }),
        }
    }

    /// It without its factor `10^t`: a copy of the coefficients and powers.
    fn rest(&self) -> Rat {
        Rat {
            num: self.num.clone(),
            den: self.den.clone(),
            pows: self.pows.clone(),
            ten: None,
        }
    }

    /// It times `10^k`, `k` in binary; it holds no [`Ten`]. The exponents of 2 and 5 gain `k`,
    /// listed if they were not, and [`Rat::extract`] moves any 2 or 5 of the coefficients
    /// into them, so the result is in normal form.
    fn times_ten(&self, k: &BigInt) -> Rat {
        debug_assert!(self.ten.is_none());
        if self.is_zero() {
            return self.clone();
        }
        let mut pows = self.pows.to_vec();
        for p in [2u64, 5] {
            match pows.binary_search_by_key(&p, |(q, _)| *q) {
                Ok(i) => pows[i].1 += k,
                Err(i) => pows.insert(i, (p, k.clone())),
            }
        }
        Rat::extract(self.num.clone(), self.den.clone(), pows)
    }

    /// `rest * 10^t`, `rest` holding no [`Ten`] and nonzero: a [`Ten`] of `t` when it stays
    /// beyond an `i64` once the common power of ten of `rest` is moved into it, else the
    /// binary form. Its cost is that of `rest` and O(n) on the digits of `t`, unless the
    /// common power of ten of `rest` is itself beyond an `i64`, where `t` is converted (a value
    /// that only a binary computation, never a literal, makes).
    fn with_ten(rest: Rat, t: Dec) -> Rat {
        debug_assert!(rest.ten.is_none() && !rest.is_zero());
        if let Some(k) = t.to_i64() {
            return rest.times_ten(&BigInt::from(k));
        }
        // 2 and 5 moved out of the coefficients into the exponents.
        let rest = rest.times_ten(&BigInt::zero());
        let exp = |p: u64| sorted_get(&rest.pows, &p).cloned().unwrap_or_default();
        let m = exp(2).min(exp(5));
        let Some(k) = m.to_i64() else {
            return rest.times_ten(&t.to_bigint());
        };
        let t = t.add_i64(k);
        let rest = rest.times_ten(&-m);
        if let Some(k) = t.to_i64() {
            return rest.times_ten(&BigInt::from(k));
        }
        Rat {
            ten: Some(Box::new(Ten {
                t,
                bin: OnceLock::new(),
            })),
            ..rest
        }
    }

    /// The decimal exponent `t` of its [`Ten`], when it holds one.
    fn t(&self) -> Option<&Dec> {
        self.ten.as_ref().map(|ten| &ten.t)
    }

    /// The integer `n` as a rational.
    pub fn int(n: BigInt) -> Self {
        Rat::plain(n, BigInt::one())
    }

    /// `num/den * prod pows`, `den` nonzero, `pows` by prime and in normal form.
    fn build(num: BigInt, den: BigInt, pows: Vec<(u64, BigInt)>) -> Rat {
        let (num, den) = if den.is_one() {
            (num, den)
        } else {
            reduce(num, den)
        };
        Rat::extract(num, den, pows)
    }

    /// `num/den * prod pows` from a reduced `num/den`: each listed prime is moved out of
    /// `num` and `den` into its exponent.
    fn extract(mut num: BigInt, mut den: BigInt, pows: Vec<(u64, BigInt)>) -> Rat {
        if num.is_zero() {
            return Rat::int(num);
        }
        let mut out = Vec::with_capacity(pows.len());
        for (p, mut e) in pows {
            let (v, n) = valuation(num, p);
            num = n;
            e += v;
            let (v, d) = valuation(den, p);
            den = d;
            e -= v;
            if !e.is_zero() {
                out.push((p, e));
            }
        }
        Rat {
            num,
            den,
            pows: out.into_boxed_slice(),
            ten: None,
        }
    }

    /// The exact value of a decimal literal's text, such as `0.1`, `2.5e-3` or `1e400000`;
    /// `Ok(None)` when it is not decimal digits with an optional sign, fraction and exponent
    /// (the exponent with an optional sign). A written exponent is kept as powers of 2 and 5, so
    /// the text's length bounds the cost. [`TooLarge`] when the system refuses the memory for
    /// reading the digits, asked before anything is built.
    pub fn decimal(text: &str) -> Result<Option<Self>, TooLarge> {
        match decimal_syntax(text) {
            Some((sign, whole, frac, exp)) => Rat::decimal_parts(sign, whole, frac, exp).map(Some),
            None => Ok(None),
        }
    }

    /// Whether [`Rat::decimal`] reads `text` as a number, given the memory: one pass over the
    /// text, reading none of its digits into a number.
    pub fn is_decimal(text: &str) -> bool {
        decimal_syntax(text).is_some()
    }

    /// The exact value of a decimal whose parts were checked: `whole` and `frac` decimal digits,
    /// not both empty, and `exp`, when present, a sign and decimal digits, not empty. Each digit
    /// is read once. [`TooLarge`] as for [`Rat::decimal`].
    pub(crate) fn decimal_parts(
        sign: Sign,
        whole: &str,
        frac: &str,
        exp: Option<(Sign, &str)>,
    ) -> Result<Self, TooLarge> {
        // Complexity tradeoff: the memory asked for is 64 bits for each digit of the text, a
        // measured bound, not a proved one, on the copy of the mantissa's digits, their reading
        // by halves, and the division by a power of ten in lowest terms or the powers of 2 and
        // 5 moved out into exponents: the peak heap was at most 42.7 bits per digit (12.8 times
        // the `3.32 n` bits of the number) over texts of 2^12 to 2^24 digits, all nines, a long
        // fraction, a run of zeros and an exponent, measured on 2026-11-06 with glibc's mmap
        // threshold fixed at 128 KiB; with its default, which keeps freed blocks of up to 32 MiB
        // on the heap, 49.1. Since RAT-parse-scale reads the powers of 2 and 5 by their binary
        // digits, decimals whose digits hold a high power of 2, of 5 or of both, of 13,000 to
        // 1,280,000 digits, peaked at most at 42.1 bits per digit (allocator bytes, 2026-11-07,
        // `l01_18_scalar_interpreter::scaling`'s families). So a literal needing less is refused
        // when the free memory lies between the two, and none aborts. Tested by
        // `a_long_decimal_literal_is_refused_when_memory_is_short` (COMPLEXITY.md K30). A
        // complete solution would ask each allocation of the reading for its own memory.
        let len = whole.len() + frac.len() + exp.map_or(0, |(_, e)| e.len());
        let len = BigUint::from(len);
        room(bits_of_digits(&len), len << 6u32)?;
        let mantissa = match frac.is_empty() {
            true => BigInt::from_biguint(sign, read_digits(whole)),
            false => BigInt::from_biguint(sign, read_digits(&[whole, frac].concat())),
        };
        // Unreachable: a `usize` is at most 64 bits on every target Rust supports, so a length
        // always fits in a `u64`.
        let shift = u64::try_from(frac.len()).expect("a text's length fits in 64 bits");
        Ok(match exp {
            None => Rat::over_ten_to(mantissa, shift),
            // An exponent of more than 18 digits stays in its digits (`Ten`), so this costs
            // O(n) on them where reading them into binary costs O(n log^2 n). Zero has no
            // powers.
            Some((s, e)) if e.len() > 18 && !mantissa.is_zero() => {
                let t = Dec::read(s == Sign::Minus, e);
                // `shift` is a text's length, so it fits an `i64` (lengths are below
                // `isize::MAX`).
                let shift = i64::try_from(shift).expect("a text's length fits an i64");
                Rat::with_ten(Rat::int(mantissa), t.add_i64(-shift))
            }
            Some((s, e)) => {
                let e = BigInt::from_biguint(s, read_digits(e)) - shift;
                Rat::extract(mantissa, BigInt::one(), vec![(2, e.clone()), (5, e)])
            }
        })
    }

    /// `digits / 10^k` as a plain reduced rational. `10^k` is `2^k 5^k`, so the common factor
    /// is `2^min(v2, k) 5^min(v5, k)` for the valuations `v2` and `v5` of `digits`, found with
    /// the cap `k` ([`valuation_upto`]) and divided out, where num-bigint's gcd of the two wide
    /// numbers is O(n^2).
    fn over_ten_to(digits: BigInt, k: u64) -> Rat {
        if digits.is_zero() {
            return Rat::int(digits);
        }
        let (t, rest) = valuation_upto(digits, 2, k);
        let (f, num) = valuation_upto(rest, 5, k);
        let den = BigInt::from(fast::pow(&BigUint::from(5u32), k - f) << (k - t));
        Rat::plain(num, den)
    }

    /// Whether it is zero.
    pub fn is_zero(&self) -> bool {
        self.num.is_zero()
    }

    /// Whether it is below zero.
    pub fn is_negative(&self) -> bool {
        self.num.is_negative()
    }

    /// The integer it is as a coefficient and its prime powers, `coeff * prod p^e`, each `e`
    /// positive. It must be an integer.
    pub fn integer_factors(&self) -> (&BigInt, &[(u64, BigInt)]) {
        let b = self.bin();
        (&b.num, &b.pows)
    }

    /// The form it is kept in, `num/den * prod p^e`: `num/den` reduced with `den` positive,
    /// and the prime powers by increasing prime, each exponent nonzero, none of the primes
    /// dividing `num` or `den`. Equal numbers can be kept in different forms (`1e3r` holds
    /// `2^3 5^3`, the `1000r` written out holds none); [`Rat::from_kept`] reads this form back.
    pub fn kept(&self) -> (&BigInt, &BigInt, &[(u64, BigInt)]) {
        // A `Ten` is given in binary (`Rat::bin`), the form this names.
        let b = self.bin();
        (&b.num, &b.den, &b.pows)
    }

    /// The number kept as `num/den * prod pows`, when the parts are in the form [`Rat::kept`]
    /// gives; `None` otherwise. Nothing is built: the checks are a primality test of each
    /// prime, the product of the primes, and three gcds, of `num` with `den` and of each with
    /// the product, which is 1 exactly when no listed prime divides it (zero included); so the
    /// cost is that of the parts as written, not of the number's digits.
    ///
    /// Complexity tradeoff: the product by halves and the half gcd (`fast::gcd`) cost
    /// O(M(n) log n) in the bits n of the parts, where a remainder of `num` and `den` by each
    /// prime costs O(n) a prime, O(n^2) for n/64 primes. Nothing is given up.
    pub fn from_kept(num: BigInt, den: BigInt, pows: Vec<(u64, BigInt)>) -> Option<Rat> {
        /// The product of `ps`, by halves.
        fn product(ps: &[u64]) -> BigUint {
            match ps {
                [] => BigUint::one(),
                [p] => BigUint::from(*p),
                _ => {
                    let (a, b) = ps.split_at(ps.len() / 2);
                    fast::mul(&product(a), &product(b))
                }
            }
        }
        let primes: Vec<u64> = pows.iter().map(|(p, _)| *p).collect();
        let listed = product(&primes);
        let form_ok = den.is_positive()
            && primes.windows(2).all(|w| w[0] < w[1])
            // `is_prime` is exact on every u64 (Miller 1976 and Rabin 1980 with deciding bases;
            // the full comment is in zed-numtheory `factor.rs`, at its head and fn `is_prime`).
            && pows.iter().all(|(p, e)| !e.is_zero() && is_prime(*p))
            && gcd(&num, &den).is_one()
            && gcd_uint(num.magnitude(), &listed).is_one()
            && gcd_uint(den.magnitude(), &listed).is_one();
        form_ok.then(|| Rat {
            num,
            den,
            pows: pows.into_boxed_slice(),
            ten: None,
        })
    }

    /// Whether it is an integer.
    pub fn is_integer(&self) -> bool {
        // With a `Ten`, the exponents of 2 and 5 in `pows` are positive and one of them is
        // absent, so the value's exponent of that prime is `t`: an integer needs `t >= 0`.
        self.t().is_none_or(|t| !t.is_negative())
            && self.den.is_one()
            && self.pows.iter().all(|(_, e)| !e.is_negative())
    }

    /// Whether it holds no prime powers: a plain reduced rational.
    fn is_plain(&self) -> bool {
        self.pows.is_empty() && self.ten.is_none()
    }

    /// The integer it is, built, or [`TooLarge`] when the system refuses the memory for it.
    /// It must be an integer.
    pub fn to_integer(&self) -> Result<BigInt, TooLarge> {
        if self.ten.is_some() {
            return self.bin().to_integer();
        }
        // Complexity tradeoff: the memory asked for is eight times the integer's width, a
        // measured bound, not a proved one, on building it power by power (each power by
        // squaring with `num::fast::mul`, and the running product by it): the peak heap was at
        // most 3.85 times the width over integers of 2^14 to 2^24 bits, one prime, several
        // primes, and a wide coefficient times a power (2026-11-06, glibc's mmap threshold
        // fixed at 128 KiB, the powers then by num-bigint's squaring). With the powers by
        // `num::fast::pow` (2026-11-07) a power alone peaked at 6.43 times its width, below the
        // ask; the whole build was not measured again. So an integer needing less is refused
        // when the free memory lies between the two, and none aborts. Tested by
        // `building_a_kept_power_is_refused_when_memory_is_short` (COMPLEXITY.md K30). A
        // complete solution would ask each allocation of the build for its own memory.
        // The refusal names a lower bound on the integer's bits and asks by the upper bound
        // (row CONST-least-refusal-size): `5^k` has about 2.32k bits, where `width` says 3k.
        let pows = || self.pows.iter().map(|(p, e)| (*p, e.magnitude()));
        room(
            least_bits(&self.num, pows()),
            width(&self.num, pows()) << 3u32,
        )?;
        self.integer_built()
    }

    /// The integer it is, built, with no check of its size but the exponents' ([`built`]). It
    /// must be an integer.
    fn integer_built(&self) -> Result<BigInt, TooLarge> {
        if self.ten.is_some() {
            return self.bin().integer_built();
        }
        let pows: Vec<(u64, BigUint)> = self
            .pows
            .iter()
            .map(|(p, e)| (*p, e.magnitude().clone()))
            .collect();
        Ok(fast::mul_int(&self.num, &built(&pows)?))
    }

    /// Whether the integer it is is even: a positive power of 2, or an even coefficient. It
    /// must be an integer.
    pub fn is_even(&self) -> bool {
        // A `Ten` of an integer has `t >= 2^63`, a positive power of 2.
        self.ten.is_some()
            || self.num.is_even()
            || self
                .pows
                .first()
                .is_some_and(|(p, e)| *p == 2 && e.is_positive())
    }

    /// Twice this integer, without building its kept powers.
    // Complexity tradeoff: expanding powers then doubling can require
    // exponentially many bits in their written exponent length. Copy the
    // coefficient and exponents and shift the coefficient or increment the
    // exponent of 2, O(n) in the encoded size, with no answer given up.
    // No general product or memory estimate is needed. Test:
    // setop::cofinite_integer_points_keep_large_powers_symbolic.
    pub(crate) fn twice_integer(&self) -> Rat {
        debug_assert!(self.is_integer());
        if self.ten.is_some() {
            return self.bin().twice_integer();
        }
        let mut twice = self.clone();
        if let Some((2, e)) = twice.pows.first_mut() {
            *e += 1;
        } else {
            twice.num <<= 1;
        }
        twice
    }

    /// The integer it is, built, unless it is surely beyond 64 bits. It must be an integer.
    pub(crate) fn small_integer(&self) -> Option<BigInt> {
        // A `Ten` of an integer is at least `10^(2^63)`.
        if self.ten.is_some() {
            return None;
        }
        // `|n| >= 2^(bits(n) - 1)` and `p^e >= 2^((bits(p) - 1) e)`, so past this bound the
        // value is beyond `2^63`; within it, it has at most about 128 bits.
        let mut low = BigInt::from(self.num.bits()) - 1;
        for (p, e) in self.pows.iter() {
            low += e * p.ilog2();
        }
        // Within the bound every exponent is below 64, so the build is never refused.
        match low <= BigInt::from(63) {
            true => self.integer_built().ok(),
            false => None,
        }
    }

    /// The numerator's digits, with its sign, or [`TooLarge`] when a kept exponent is too large
    /// for any memory to hold the digits (`built`). The memory is not asked for here; a
    /// caller that writes a wide number asks first with [`Rat::text_room`].
    pub fn numer_text(&self) -> Result<String, TooLarge> {
        if self.ten.is_some() {
            return self.bin().numer_text();
        }
        let sign = if self.is_negative() { "-" } else { "" };
        let pows = self
            .pows
            .iter()
            .filter(|(_, e)| e.is_positive())
            .map(|(p, e)| (*p, e.magnitude().clone()));
        Ok(format!(
            "{sign}{}",
            digits(self.num.magnitude(), pows.collect())?
        ))
    }

    /// `Ok` when the system gives the memory to write its digits (`Rat::text_ask`); else
    /// [`TooLarge`] naming that memory, before anything is built.
    pub fn text_room(&self) -> Result<(), TooLarge> {
        room(self.least_size(), self.text_ask())
    }

    /// At most the bits of its numerator and denominator together, built: the size a refusal
    /// to build or write them names, a lower bound, where [`Rat::text_size`] bounds them from
    /// above for the memory asked (row CONST-least-refusal-size).
    fn least_size(&self) -> BigUint {
        if self.ten.is_some() {
            return self.bin().least_size();
        }
        let side = |coef: &BigInt, sign: Sign| {
            let pows = self.pows.iter().filter(move |(_, e)| e.sign() == sign);
            least_bits(coef, pows.map(|(p, e)| (*p, e.magnitude())))
        };
        side(&self.num, Sign::Plus) + side(&self.den, Sign::Minus)
    }

    /// The memory writing its digits asks for, in bits.
    pub(crate) fn text_ask(&self) -> BigUint {
        let (bits, text) = self.text_size();
        // Complexity tradeoff: the memory asked for is eight times the number's width and its
        // text together, a measured bound, not a proved one, on building the number, the
        // conversion to decimal by halves (`num::fast::to_decimal`, its powers of ten and their
        // reciprocals held at once), the zeros of a kept power of ten, and the copy of the text
        // into the value: the peak heap was at most 4.53 times that over numbers of 2^12 to
        // 2^20 bits, plain, kept powers and rationals (2026-11-06, glibc's mmap threshold
        // fixed at 128 KiB), and with the printer of NUM-print-fast, whose levels keep their
        // transforms, at most 6.11 times over plain numbers of 2^14 to 2^19 words and 5.50 over
        // `3 ^ k` to 6.4 million (2026-11-08). So a text needing less is refused when the free
        // memory lies between the two, and none aborts. Tested by
        // `printing_a_wide_number_is_refused_when_memory_is_short` (COMPLEXITY.md K30). A
        // complete solution would write the digits by halves into memory reserved once.
        (bits + (text << 3u32)) << 3u32
    }

    /// What writing its digits builds: the number, of at most the first many bits, and its
    /// digits, numerator's and denominator's, at most the second many bytes.
    pub fn text_size(&self) -> (BigUint, BigUint) {
        if self.ten.is_some() {
            return self.bin().text_size();
        }
        let side = |coef: &BigInt, sign: Sign| {
            let pows = self.pows.iter().filter(move |(_, e)| e.sign() == sign);
            width(coef, pows.map(|(p, e)| (*p, e.magnitude())))
        };
        let bits = side(&self.num, Sign::Plus) + side(&self.den, Sign::Minus);
        // `log10(2) < 1234 / 4096`; a digit is one byte.
        let text = ((&bits * 1234u32) >> 12u32) + 2u32;
        (bits, text)
    }

    /// At most the bytes of its text: the digits of the numerator and, when it is above 1, of
    /// the denominator, without the sign. [`Rat::text_size`] bounds the text from above, for
    /// asking for memory; this bounds it from below, for a claim that writing the text needs
    /// at least this much (the checker's, sec:checking_in_zed).
    pub fn text_least(&self) -> BigUint {
        if self.ten.is_some() {
            return self.bin().text_least();
        }
        let side = |coef: &BigInt, sign: Sign| {
            let pows = self.pows.iter().filter(move |(_, e)| e.sign() == sign);
            least_log2(coef, pows.map(|(p, e)| (*p, e.magnitude())))
        };
        // `x >= 2^l` has at least `floor(l log10 2) + 1` digits, and `1233 / 4096 < log10 2`.
        let digits = |l: BigUint| ((l * 1233u32) >> 12u32) + 1u32;
        let den = match self.den.is_one() && self.pows.iter().all(|(_, e)| e.is_positive()) {
            true => BigUint::zero(),
            false => digits(side(&self.den, Sign::Minus)),
        };
        digits(side(&self.num, Sign::Plus)) + den
    }

    /// The denominator's digits, or [`TooLarge`] as for [`Rat::numer_text`].
    pub fn denom_text(&self) -> Result<String, TooLarge> {
        if self.ten.is_some() {
            return self.bin().denom_text();
        }
        let pows = self
            .pows
            .iter()
            .filter(|(_, e)| e.is_negative())
            .map(|(p, e)| (*p, e.magnitude().clone()));
        digits(self.den.magnitude(), pows.collect())
    }

    /// `|N|` and `D` for the value `±N/D` in lowest terms, built: the same two numbers for
    /// every form of one value, as the digits are, so a content address can be taken over
    /// their binary form, in time linear in their bits, where the digits cost more than linear
    /// time to convert. A side with no powers is its coefficient, borrowed; a power of 2 is a
    /// shift, and a power of another prime is built by squaring. A side with powers is built
    /// only after the system gives the memory for it; [`TooLarge`] names that memory when it
    /// refuses.
    pub fn built_parts(&self) -> Result<(Cow<'_, BigUint>, Cow<'_, BigUint>), TooLarge> {
        if self.ten.is_some() {
            return self.bin().built_parts();
        }
        if !self.is_plain() {
            // Complexity tradeoff: the memory asked for is eight times the width of the two
            // sides together, the factor `to_integer` asks for the same build (powers by
            // squaring, the product by `num::fast::mul`), whose peak it measured at
            // 5.49 times the width; this build was not measured on its own (the same ask in
            // `zedc_int::Num::built` peaked at 8.08 times the value for a power of 3 built by
            // squaring, below its ask: item NATIVE-shape-test), and a power of 2 here is a
            // shift, which needs less. So a number needing less is refused when the
            // free memory lies between the two, and none aborts. Tested by
            // `l01_17_value_representation::asks::addressing_a_wide_constant_is_refused_when_memory_is_short`
            // (COMPLEXITY.md K30). A complete solution would ask each allocation of the build
            // for its own memory.
            let (bits, _) = self.text_size();
            room(self.least_size(), bits << 3u32)?;
        }
        fn side<'s>(
            coef: &'s BigInt,
            pows: &[(u64, BigInt)],
            sign: Sign,
        ) -> Result<Cow<'s, BigUint>, TooLarge> {
            let pows: Vec<(u64, BigUint)> = pows
                .iter()
                .filter(|(_, e)| e.sign() == sign)
                .map(|(p, e)| (*p, e.magnitude().clone()))
                .collect();
            Ok(match pows.is_empty() {
                true => Cow::Borrowed(coef.magnitude()),
                false => Cow::Owned(fast::mul(coef.magnitude(), built(&pows)?.magnitude())),
            })
        }
        Ok((
            side(&self.num, &self.pows, Sign::Plus)?,
            side(&self.den, &self.pows, Sign::Minus)?,
        ))
    }

    /// The value's residues, the same for every form of it: whether it is negative, and
    /// `|N| mod M` and `D mod M` for the value `N/D` in lowest terms, `M = 2^61 - 1`. The
    /// form `num/den * prod p^e` is in lowest terms as it stands, since `num/den` is reduced,
    /// no listed prime divides either, and each prime lies on one side, so `N` and `D` are the
    /// same whatever powers a form lists; each `p^e` is reduced by Fermat's little theorem,
    /// so the cost is the size of the coefficients and exponents, never of the value.
    pub fn residues(&self) -> (bool, u64, u64) {
        let t = self.t();
        // With a `Ten`, 2 and 5 are read below with it.
        let ten_prime = |p: u64| t.is_some() && (p == 2 || p == 5);
        let side = |coef: &BigInt, sign: Sign| {
            let mut r = rem_big_u64(coef.magnitude(), MERSENNE_61);
            for (p, e) in self
                .pows
                .iter()
                .filter(|(p, e)| e.sign() == sign && !ten_prime(*p))
            {
                r = m61::mul(r, m61::pow(*p, e.magnitude()));
            }
            r
        };
        let (mut n, mut d) = (side(&self.num, Sign::Plus), side(&self.den, Sign::Minus));
        if let Some(t) = t {
            // The value's exponent of `p` in {2, 5} is `t + e_p`, `e_p >= 0` its exponent in
            // `pows` (zero when absent); `|t| >= 2^63`. For `t > 0` it is positive and `p^(t +
            // e_p)` lies in `N`. For `t < 0` and `e_p < 2^63` it is negative and `p^(|t| - e_p)`
            // lies in `D`; a wider `e_p`, which no literal makes, is read from the binary form.
            // Each power is reduced modulo `M` by Fermat's little theorem, `p` coprime to `M`,
            // with `|t| mod (M - 1)` read from its digits in O(n) ([`Dec::rem_u64`]).
            let q = MERSENNE_61 - 1;
            let k = t.rem_u64(q);
            for p in [2u64, 5] {
                let e = sorted_get(&self.pows, &p).cloned().unwrap_or_default();
                if t.is_negative() && e.to_i64().is_none() {
                    return self.bin().residues();
                }
                let e = rem_big_u64(e.magnitude(), q);
                match t.is_negative() {
                    false => n = m61::mul(n, m61::pow_word(p, (k + e) % q)),
                    true => d = m61::mul(d, m61::pow_word(p, (k + q - e) % q)),
                }
            }
        }
        (self.is_negative(), n, d)
    }

    /// The integer's residues `n mod M` and `n mod (M - 1)`, each in `0 .. modulus`, for
    /// `M = 2^61 - 1`: a family's hash weighs the entry of key `n` by `R^n` (`value::family_sum`),
    /// where `R^(M - 1) = 1`. It must be an integer. Each `p^e` is reduced by squaring over the
    /// bits of `e`, so the cost is the size of the coefficient and exponents, never of the value.
    pub fn integer_residues(&self) -> (u64, u64) {
        debug_assert!(self.is_integer(), "residues of an integer");
        let (negative, n, _) = self.residues();
        let q = MERSENNE_61 - 1;
        let mut e = rem_big_u64(self.num.magnitude(), q);
        for (p, k) in self.pows.iter() {
            e = mul_mod(e, pow_mod_big(*p, k.magnitude(), q), q);
        }
        // A `Ten` of an integer has `t > 0`; `M - 1` is even, so 2 has no inverse modulo it and
        // Fermat does not apply: `10^t` is reduced by a power over the decimal digits of `t`,
        // O(n) ([`Dec::pow_mod`]), times the `p^e_p` of `pows` above.
        if let Some(t) = self.t() {
            e = mul_mod(e, t.pow_mod(10, q), q);
        }
        match negative {
            true => ((MERSENNE_61 - n) % MERSENNE_61, (q - e) % q),
            false => (n, e),
        }
    }

    /// Its text as a literal type writes it: when it is a decimal, `m * 10^K` with `m` an
    /// integer not divisible by 10, as the one literal `meKr` (`1e400000r`, `5e-1r`, `-25e9r`,
    /// `7r`), which is the form the type syntax has (`SignedLit` in DESIGN.md sec:grammar).
    /// Equal values print alike whatever form they hold. Of a value read from a decimal literal
    /// `d e k`, `m` is `d` less its trailing zeros, so the text is no longer than the literal
    /// and the power of 10 is never built.
    pub fn literal_text(&self) -> String {
        if self.is_zero() {
            return "0r".to_string();
        }
        let sign = if self.is_negative() { "-" } else { "" };
        // With a `Ten`, `10^t` is the value's whole power of ten (`Ten`'s invariants), so the
        // literal is `m e t` with `m` the rest, an integer when `den` is 1 (the exponents in
        // `pows` of a `Ten` are positive for 2 and 5); `t` is written from its digits, O(n).
        if let Some(t) = self.t() {
            if !self.den.is_one() || self.pows.iter().any(|(_, e)| e.is_negative()) {
                return self.to_string();
            }
            let pows: Vec<(u64, BigUint)> = (self.pows.iter())
                .map(|(p, e)| (*p, e.magnitude().clone()))
                .collect();
            let Ok(m) = built(&pows) else {
                return self.to_string();
            };
            let m = fast::to_decimal(&fast::mul(self.num.magnitude(), m.magnitude()));
            return format!("{sign}{m}e{t}r");
        }
        // The signed exponents of 2 and 5 in the value, and the coefficients without them.
        let (mut num, mut den) = (self.num.abs(), self.den.clone());
        let [two, five] = [2, 5].map(|p| match sorted_get(&self.pows, &p) {
            Some(e) => e.clone(),
            None => {
                let (up, n) = valuation(std::mem::take(&mut num), p);
                let (down, d) = valuation(std::mem::take(&mut den), p);
                (num, den) = (n, d);
                BigInt::from(up) - BigInt::from(down)
            }
        });
        let others = |sign: Sign| -> Vec<(u64, BigUint)> {
            self.pows
                .iter()
                .filter(|(p, e)| *p != 2 && *p != 5 && e.sign() == sign)
                .map(|(p, e)| (*p, e.magnitude().clone()))
                .collect()
        };
        let below: Vec<(u64, BigUint)> = others(Sign::Minus);
        // Complexity tradeoff: the part `m` that is not a power of 10, and every number that is
        // not a decimal, is built and written in full, at a cost proportional to its digits,
        // since the type syntax has no power to write it with. Of a literal, `m` is the
        // literal's digits; only a computed constant such as `2r ^ 400000`, `1r / 2r ^ 400000`
        // or `1r / 3r` has an `m` beyond its source, and printing its type then costs the
        // digits of `m`, the size of the output. A number that is not a decimal has no literal
        // and prints as the quotient `nr/dr`, which the type syntax cannot write. Nothing is
        // refused. Tested by `a_computed_power_prints_its_digits` (COMPLEXITY.md K30). A
        // complete solution would give types a written power and quotient, such as
        // `2r ^ 400000` and `1r / 3r`, and print the kept powers as they are.
        if !den.is_one() || !below.is_empty() {
            return self.to_string();
        }
        let tens = (&two).min(&five).clone();
        let mut pows = others(Sign::Plus);
        // Unreachable: `tens` is the smaller of `two` and `five`, so neither difference is
        // negative and each converts to a `BigUint`.
        pows.extend([(2, &two - &tens), (5, &five - &tens)].map(|(p, e)| {
            (
                p,
                e.to_biguint()
                    .expect("an exponent less its least is not negative"),
            )
        }));
        // An exponent of 2^64 or more has digits no memory holds; the value is written as
        // `Display` writes it then, by its powers.
        let Ok(m) = built(&pows) else {
            return self.to_string();
        };
        let m = fast::to_decimal(&fast::mul(num.magnitude(), m.magnitude()));
        match tens.is_zero() {
            true => format!("{sign}{m}r"),
            false => format!("{sign}{m}e{tens}r"),
        }
    }

    /// Its text as a literal type writes an integer (DESIGN.md L1.26a, `LitType` in
    /// sec:grammar): its digits, or the powers it holds where their text is shorter, so
    /// `3^200000`, `-5*3^200000` and `12^100000` print so, and `2^10` prints `1024`. It must
    /// be an integer.
    ///
    /// Complexity tradeoff (LIT-power-values): the text is chosen without the digits. They are
    /// no longer than the power's text, of `L` characters, exactly when `|self| < 10^L`, which
    /// the bounds of `Rat::magnitude_order` decide in O(L) word operations; only then are
    /// they built, at the cost of a text of at most `L` characters. So the cost is that of the
    /// shorter text, never of a power's digits: `3^200000` costs its 8 characters where its
    /// 95,425 digits cost about 105 million instructions (two decimal conversions of about 95
    /// million each and the power's 9 million, measured 2026-11-13 in the message of
    /// MSG-literal-type-huge-power). This compares two lengths of one value and is no size
    /// threshold. The alternative, a power always printed as a power, writes `2^3` for 8 and
    /// gives `2^3` and `2 * 2 * 2` different texts; the one before, digits always, cost the
    /// digits. A value held as plain digits, such as the sum `3^200000 + 1`, prints its digits
    /// (DESIGN.md L1.26a).
    ///
    /// The powers are read from the value by `Rat::text_atoms`, not from the way it is held, so
    /// a product such as `4294967296 * 4294967296`, held as digits, prints `2^64` as `2 ^ 64`
    /// does (DESIGN.md sec:diagnostics, "Types in a message"; plan row KEPT-power-form-print),
    /// and `q * 3^50` prints one text whether `3^50` is kept or the product is digits (plan row
    /// KEPT-print-value-canonical).
    pub fn integer_text(&self) -> String {
        if self.ten.is_some() {
            return self.bin().integer_text();
        }
        debug_assert!(self.is_integer());
        if self.num.is_zero() {
            return "0".to_string();
        }
        let sign = if self.is_negative() { "-" } else { "" };
        let atoms = self.text_atoms();
        if atoms.iter().all(|(_, e)| e.is_one()) {
            // Every atom is written in the coefficient, which is then the value: its digits.
            let c = (atoms.iter()).fold(BigUint::one(), |c, (b, _)| fast::mul(&c, b));
            return format!("{sign}{}", fast::to_decimal(&c));
        }
        let power = powers_text(&atoms);
        // Unreachable: `Rat::pow` returns `TooLarge` only for a numerator or denominator wider
        // than 64 bits, and 10 is factored into `2^L * 5^L`, so nothing is asked or built.
        let ten = Rat::int(BigInt::from(10))
            .pow(&BigUint::from(power.len()))
            .expect("10 is factored and nothing is built");
        // Below `10^L` every exponent is small, so the digits are never refused; a refusal
        // would leave the powers, which are the value too.
        let digits = match self.magnitude_order(&ten, false) {
            Ok(Ordering::Less) => self.numer_text().ok(),
            _ => None,
        };
        digits.unwrap_or_else(|| format!("{sign}{power}"))
    }

    /// The atoms `(b, e)` of `|self|` that its text writes as `b^e` ([`powers_text`]), sorted by
    /// base, their product `|self|`: a function of the value alone, not of the way it is held
    /// (plan row KEPT-print-value-canonical), but for the gap below. It must be a nonzero
    /// integer, held in binary. The steps, for `V = |self| = c * prod p^e`, `c` the coefficient:
    ///
    /// 1. Each prime `t` of [`TEXT_PRIMES`] with its power `v_t(V)`: from `c` by
    ///    [`valuation`] when `t` divides it, else the listed exponent (zero when unlisted).
    /// 2. What is left, `R = V / prod t^(v_t(V))`, as its least root `R = r^m`, `r` no perfect
    ///    power, computed without building `R`: `c'`, the `c` of step 1 divided by its primes of
    ///    the set, is `s^k` by [`fn@least_root`] (`s = 1`, `k = 0` when `c' = 1`); then
    ///    `m = gcd(k, e_p)` over the listed primes `p` outside the set, and
    ///    `r = s^(k/m) * prod p^(e_p/m)`, built.
    /// 3. `r` factored by `zed_numtheory::factor` when `r < 2^44`, each prime with `m` times its
    ///    power; else `(r, m)`, a prime word or a wider number this cannot factor. An atom with
    ///    exponent 1 is written in the coefficient.
    ///
    /// Proof that the atoms are a function of `V` (when `r` is built): step 1 reads `v_t(V)`
    /// exactly, since a listed prime divides no coefficient (the form's invariant), so `t` is in
    /// `c` or listed, not both, and [`valuation`] takes all of it from `c`; so `R` is a function
    /// of `V`. Every integer `R > 1` is `r^m` for one `r` that is no perfect power and one `m`,
    /// the gcd of the exponents of its primes (write `R = prod q^(a_q)`; `R = y^j` exactly when
    /// `j` divides every `a_q`). Step 2 finds that pair: `s` is no perfect power, so the gcd of
    /// its primes' exponents is 1 and that of `c' = s^k` is `k`; the listed `p` divide neither
    /// `c` nor so `s`; so the exponents of `R` are `k a_q` for the primes `q` of `s` and `e_p`
    /// for the listed `p`, with gcd `gcd(k gcd(a_q), e_p) = gcd(k, e_p) = m` (`gcd(0, x) = x`
    /// covers `c' = 1`), and `R^(1/m) = s^(k/m) prod p^(e_p/m)` (`m` divides `k` and each `e_p`).
    /// Step 3 is a function of `(r, m)`, and factoring is unique. So the text, a function of the
    /// sorted atoms and of `|V|` against powers of ten, is one per value.
    ///
    /// Gap (not proved away): when the system refuses the memory to build `r`, the atoms are read
    /// from the held form instead (`(s, k)` and the listed primes outside the set, each with its
    /// exponent), which can differ between two holds of one value. Since `r <= V`, no form of
    /// such a value holds it as digits; two holds differ only in a prime with exponent above 1,
    /// outside the set, that one keeps in `c` and the other lists.
    ///
    /// Complexity tradeoff: for `n` the bits of `c`, step 1 costs one remainder by a word per
    /// group of the set's primes whose product fits a word ([`text_prime_groups`], 6 groups),
    /// O(n) each, and a [`valuation`] for each prime of the set that divides, O(M(n)) and at
    /// most O(n log^2 n) each (proved there); [`fn@least_root`] costs O(M(n) log n) (proved there);
    /// `factor` below 2^44 is O(1), a constant proved at `zed_numtheory::factor`. The build of `r`
    /// asks the system for its memory first ([`Rat::text_room`]) and costs O(M(b) log b) for `b`
    /// its bits ([`built`] and [`fast::mul_int`]). When `r >= 2^44` its digits are in the text, as
    /// coefficient or base, at O(M(b) log b) ([`fast::to_decimal`]), so the build costs at most a
    /// constant times the text it serves; when `r < 2^44`, `b < 44`. So the whole is at most a
    /// constant times the cost of the digits of `c` and of the text written, and only a printed
    /// number pays it; arithmetic never calls it, so `*` costs no factoring (decision of
    /// 2026-11-23, plan row KEPT-power-form-print). The one before, at origin/main 80c93acf5,
    /// reduced the coefficient alone and wrote the listed powers as held: no build of `r`, but
    /// `q * 3^50` with `q` a wide prime printed `q*3^50` held with `3^50` and its digits held as
    /// digits. The price of this one: a value that lists a prime outside the set beside a
    /// coefficient that makes `R` no perfect power, such as `q * 1009^50`, prints its digits
    /// where the held form printed `q*1009^50`, since its digits held as digits have no prime
    /// that a method of proved cost finds. Methods with no proved bound are not used: Pollard's
    /// rho on a word above 2^44 is unproved and cost about 0.85 ms on a product of two primes near
    /// 2^31 (measured 2026-11-23 on Colab when `Rat::mul` factored words, against 61 ns for the
    /// product), so such a word prints as digits.
    fn text_atoms(&self) -> Vec<(BigUint, BigInt)> {
        debug_assert!(self.ten.is_none() && !self.num.is_zero());
        let mut atoms: Vec<(BigUint, BigInt)> = Vec::new();
        let mut c = self.num.magnitude().clone();
        for t in text_primes_dividing(&c) {
            let (v, rest) = valuation(BigInt::from(c), t);
            c = rest.into_parts().1;
            atoms.push((BigUint::from(t), BigInt::from(v)));
        }
        let mut others: Vec<(u64, BigInt)> = Vec::new();
        for (p, e) in self.pows.iter() {
            match TEXT_PRIMES.binary_search(p).is_ok() {
                true => atoms.push((BigUint::from(*p), e.clone())),
                false => others.push((*p, e.clone())),
            }
        }
        let (s, k) = match c.is_one() {
            true => (c, BigUint::zero()),
            false => least_root(c),
        };
        let m = (others.iter()).fold(BigInt::from(k.clone()), |g, (_, e)| g.gcd(e));
        if !m.is_zero() {
            // `m` divides `k`, a bit count of `c`, so `k / m` fits a word.
            let km = (&k / m.magnitude()).to_u64().expect("below the bits of c");
            let root = Rat {
                num: BigInt::from(fast::pow(&s, km)),
                den: BigInt::one(),
                pows: (others.iter()).map(|(p, e)| (*p, e / &m)).collect(),
                ten: None,
            };
            match root.text_room().and_then(|()| root.integer_built()) {
                Ok(r) => push_root(&mut atoms, r.magnitude(), &m),
                Err(_) => {
                    push_root(&mut atoms, &s, &BigInt::from(k));
                    atoms.extend(others.into_iter().map(|(p, e)| (BigUint::from(p), e)));
                }
            }
        }
        atoms.sort_unstable_by(|a, b| a.0.cmp(&b.0));
        atoms
    }

    /// `a + b`, or [`TooLarge`] when the system refuses the memory for the part of the
    /// operands it builds.
    pub fn add(&self, b: &Rat) -> Result<Rat, TooLarge> {
        self.sum(b, false)
    }

    /// `a - b`, by the rule of [`Rat::add`]. `b` is read with its sign flipped, not negated
    /// into a copy, so `1 - x` builds only the difference.
    pub fn sub(&self, b: &Rat) -> Result<Rat, TooLarge> {
        self.sum(b, true)
    }

    /// At most the bits `a + b` or `a - b` builds in full (`Rat::sum`), found without building
    /// the sum: the wider operand for two integers, the cross products for two plain
    /// rationals, and, beside kept powers, the wider side of the part above the powers the
    /// operands share, its powers at `log2` bounded from below (`least_log2`). [`TooLarge`]
    /// where moving a shared prime out of a coefficient is refused, as in the sum itself.
    /// Complexity: O(primes kept), plus the copy of the coefficients that alignment makes.
    pub fn sum_least(&self, b: &Rat) -> Result<BigUint, TooLarge> {
        if self.ten.is_some() || b.ten.is_some() {
            return self.bin().sum_least(b.bin());
        }
        if self.is_plain() && b.is_plain() {
            let [na, da, nb, db] = [&self.num, &self.den, &b.num, &b.den].map(|x| x.bits());
            return Ok(BigUint::from(match self.den.is_one() && b.den.is_one() {
                true => na.max(nb),
                false => (na + db).max(nb + da) + da + db - 2,
            }));
        }
        if self.is_zero() || b.is_zero() {
            return Ok(BigUint::zero());
        }
        let a = self.aligned(&b.pows, true)?;
        let b = b.aligned(&self.pows, true)?;
        let mut rest_a = Vec::new();
        let mut rest_b = Vec::new();
        for (p, ea, eb) in zip_pows(&a.pows, &b.pows) {
            let g = (&ea).min(&eb).clone();
            rest_a.push((p, (ea - &g).magnitude().clone()));
            rest_b.push((p, (eb - &g).magnitude().clone()));
        }
        // `n * prod p^e * d >= 2^(l + bits(d) - 1)`, which has at least `l + bits(d)` bits.
        let [x, y] = [(&a.num, &rest_a, &b.den), (&b.num, &rest_b, &a.den)]
            .map(|(n, rest, d)| least_log2(n, rest.iter().map(|(p, e)| (*p, e))) + d.bits());
        Ok(x.max(y))
    }

    /// `a + b`, or `a - b` when `minus`.
    fn sum(&self, b: &Rat, minus: bool) -> Result<Rat, TooLarge> {
        // Complexity tradeoff: a sum with a `Ten` converts its exponent, O(n log^2 n), where a
        // sum of two whose exponents differ by a word could stay in digits; a sum is built in
        // full beyond its shared powers anyway (DESIGN.md "Kept powers", *Sums*).
        if self.ten.is_some() || b.ten.is_some() {
            return self.bin().sum(b.bin(), minus);
        }
        let signed = |x: BigInt, y: BigInt| match minus {
            true => x - y,
            false => x + y,
        };
        if self.is_plain() && b.is_plain() {
            if self.den.is_one() && b.den.is_one() {
                // num-bigint builds the result once, at most one bit wider than the wider
                // operand.
                let size = BigUint::from(self.num.bits().max(b.num.bits()) + 1);
                room(size.clone(), size)?;
                return Ok(Rat::int(match minus {
                    true => &self.num - &b.num,
                    false => &self.num + &b.num,
                }));
            }
            // Complexity tradeoff: the memory asked for a sum of two plain rationals is
            // sixteen times the unreduced result's width, a measured bound, not a proved one,
            // on the two cross products, their sum and the reduction by the gcd (a remainder of
            // the wider by the narrower, the half gcd and two exact divisions by it, all in
            // `num::fast`): the peak heap was at most 9.24 times that width over numerators
            // and denominators of 3 to 2^16 words, and the gcd alone of two parts with a common
            // factor at most 8.83 times their sum (2026-11-06, glibc's mmap threshold fixed at
            // 128 KiB). The products have been by `num::fast::mul_int` since BIGINT-fast-mul
            // (2026-11-07), at most 5.00 times a product's width; the sum was not measured
            // again. So a sum needing less is refused when the free memory lies between the
            // two, and none aborts. Tested by `a_wide_
            // rational_difference_is_refused_when_memory_is_short` (COMPLEXITY.md K30). A
            // complete solution would ask each allocation of the reduction for its own memory,
            // which needs a reduction written here rather than num-bigint's.
            let n = (self.num.bits() + b.den.bits()).max(b.num.bits() + self.den.bits()) + 1;
            let d = self.den.bits() + b.den.bits();
            room(BigUint::from(n + d), BigUint::from(n + d) << 4u32)?;
            // Unreachable: both denominators are positive, so their product is not zero and
            // `Rat::new` returns `Some`.
            return Ok(Rat::new(
                signed(
                    fast::mul_int(&self.num, &b.den),
                    fast::mul_int(&b.num, &self.den),
                ),
                fast::mul_int(&self.den, &b.den),
            )
            .expect("den > 0"));
        }
        if self.is_zero() {
            return match minus {
                true => b.try_neg(),
                false => b.try_copy(),
            };
        }
        if b.is_zero() {
            return self.try_copy();
        }
        // The common powers `g`, each prime at the lesser exponent, factor out; the rest of
        // each operand is built, at the cost of its size.
        // Complexity tradeoff: a sum is kept as one rational times powers, so the part of each
        // operand above the common powers is built, at a cost proportional to the size of the
        // sum's coefficient; `10 ^ 10 ^ 9 + 1` builds the billion digits, while
        // `10 ^ 10 ^ 9 + 10 ^ 10 ^ 9` builds nothing. This is the cost of the output in this
        // form, and no input is refused for its size; a part that does not fit in memory is
        // `TooLarge`, found before building it. Tested by
        // `kept_powers_agree_with_the_built_value`, `close_products_compare_exactly` and
        // `a_sum_too_large_to_build_is_an_error_naming_its_size` (COMPLEXITY.md K30).
        // So the cost grows with the value and not with its text: `3 ^ 2 ^ k + 1` builds
        // `1.6 * 2^k` bits, 0.78 s at k = 25 and about 4 minutes at k = 33, O(n log n) in the
        // bits (item KERNEL-sum-tower; whether to keep such a sum unbuilt or refuse it is
        // QUESTIONS.md A28). Tested by `a_kept_power_beside_its_built_successor_costs_n_log_n`.
        // A complete solution would keep a sum of terms unbuilt, ordered and projected by
        // bounds as products are.
        // Complexity tradeoff: the memory asked for is eight times the wider side's width, a
        // measured bound, not a proved one, on building both sides' powers, the cross products,
        // the sum, and its reduction and the primes moved out into exponents: the peak heap was
        // at most 4.97 times that width over sums of 2^14 to 2^24 bits, an integer and a power,
        // two powers, a common power, a wide coefficient, and rationals. So a sum needing less
        // is refused when the free memory lies between the two, and none aborts. Tested by
        // `a_sum_of_kept_powers_is_refused_when_memory_is_short` (COMPLEXITY.md K30).
        let a = self.aligned(&b.pows, true)?;
        let b = b.aligned(&self.pows, true)?;
        let mut common = Vec::new();
        let mut rest_a = Vec::new();
        let mut rest_b = Vec::new();
        for (p, ea, eb) in zip_pows(&a.pows, &b.pows) {
            let g = (&ea).min(&eb).clone();
            rest_a.push((p, (ea - &g).magnitude().clone()));
            rest_b.push((p, (eb - &g).magnitude().clone()));
            common.push((p, g));
        }
        let sizes = [(&a.num, &rest_a, &b.den), (&b.num, &rest_b, &a.den)]
            .map(|(n, rest, d)| width(n, rest.iter().map(|(p, e)| (*p, e))) + d.bits());
        let [x, y] = sizes;
        let ask = (x.max(y) + 1u32) << 3u32;
        // The refusal names the bits of the wider cross product, a lower bound, by the formula
        // and proof of [`Rat::sum_least`], and asks by the upper bound (row
        // CONST-least-refusal-size).
        let [x, y] = [(&a.num, &rest_a, &b.den), (&b.num, &rest_b, &a.den)]
            .map(|(n, rest, d)| least_log2(n, rest.iter().map(|(p, e)| (*p, e))) + d.bits());
        room(x.max(y), ask)?;
        let ra = fast::mul_int(&a.num, &built(&rest_a)?);
        let rb = fast::mul_int(&b.num, &built(&rest_b)?);
        Ok(Rat::build(
            signed(fast::mul_int(&ra, &b.den), fast::mul_int(&rb, &a.den)),
            fast::mul_int(&a.den, &b.den),
            common,
        ))
    }

    /// `a * b`, or [`TooLarge`] when the system refuses the memory for the products of the
    /// coefficients and their reduction, asked before anything is built. The kept powers add
    /// their exponents and are not built.
    pub fn mul(&self, b: &Rat) -> Result<Rat, TooLarge> {
        if self.ten.is_some() || b.ten.is_some() {
            if self.is_zero() || b.is_zero() {
                return Ok(Rat::int(BigInt::zero()));
            }
            // `r_a 10^t_a * r_b 10^t_b = (r_a r_b) 10^(t_a + t_b)`, the exponents added by their
            // digits, O(n).
            let t = Rat::ten_sum(self, b, false);
            return Ok(Rat::with_ten(self.rest().mul(&b.rest())?, t));
        }
        if self.is_plain() && b.is_plain() && self.den.is_one() && b.den.is_one() {
            // Complexity tradeoff: the memory asked for a product of two integers is eight
            // times the product's width, a measured bound, not a proved one, on `num::fast::mul`
            // (num-bigint's Toom-3 or the three residue lists of the transform, held at once):
            // the peak heap was at most 5.00 times the product's width over operands of 2^8 to
            // 2^18 words, balanced, unbalanced, all ones and squares (2026-11-07, BIGINT-fast-mul;
            // 5.0 with num-bigint alone). So a product needing less is refused when the free
            // memory lies between the two, and none aborts. Tested by
            // `a_product_or_quotient_of_wide_numbers_is_refused_when_memory_is_short`
            // (COMPLEXITY.md K30).
            // A complete solution would be a multiplication whose scratch is allocated once,
            // its size known by construction.
            let size = BigUint::from(self.num.bits() + b.num.bits());
            room(size.clone(), size << 3u32)?;
            return Ok(Rat::int(fast::mul_int(&self.num, &b.num)));
        }
        self.scaled(&b.num, &b.den, &b.pows, |x, y| x + y)
    }

    /// `a / b`, by the rule of [`Rat::mul`]; `Ok(None)` when `b` is zero.
    pub fn div(&self, b: &Rat) -> Result<Option<Rat>, TooLarge> {
        if b.is_zero() {
            return Ok(None);
        }
        if self.ten.is_some() || b.ten.is_some() {
            if self.is_zero() {
                return Ok(Some(Rat::int(BigInt::zero())));
            }
            // As in `Rat::mul`, with the exponents subtracted.
            let t = Rat::ten_sum(self, b, true);
            let rest = self.rest().div(&b.rest())?;
            // Unreachable: `b` is not zero, so neither is its rest.
            let rest = rest.expect("a nonzero divisor");
            return Ok(Some(Rat::with_ten(rest, t)));
        }
        self.scaled(&b.den, &b.num, &b.pows, |x, y| x - y).map(Some)
    }

    /// `t_a + t_b`, or `t_a - t_b` when `minus`, of the decimal exponents of two numbers' `Ten`s,
    /// zero for one with none. O(n).
    fn ten_sum(a: &Rat, b: &Rat, minus: bool) -> Dec {
        let zero = Dec::from_i128(0);
        let (ta, tb) = (a.t().unwrap_or(&zero), b.t().unwrap_or(&zero));
        match minus {
            true => ta.sub(tb),
            false => ta.add(tb),
        }
    }

    /// `num * up / (den * down) * prod p^e`, the exponent of each prime `f` of this one's and
    /// `pows`', a missing one zero; `down` is not zero. [`TooLarge`] when the system refuses
    /// the memory for the two products and their reduction.
    fn scaled(
        &self,
        up: &BigInt,
        down: &BigInt,
        pows: &[(u64, BigInt)],
        f: impl Fn(&BigInt, &BigInt) -> BigInt,
    ) -> Result<Rat, TooLarge> {
        debug_assert!(
            self.ten.is_none(),
            "`Rat::mul` and `Rat::div` take a `Ten` apart"
        );
        // Complexity tradeoff: the memory asked for is sixteen times the sum of the four
        // coefficients' widths, a measured bound, not a proved one, on the two products, their
        // reduction by the gcd (a Burnikel-Ziegler remainder of the wider by the narrower,
        // Stein's gcd, cited in `num::fast`'s "Sources", and two divisions by it) and the
        // primes moved out into exponents
        // (`valuation`): the peak heap was at most 7.5 times that width for products and
        // quotients of rationals of 2^6 to 2^14 words, plain and with kept powers, at most 10.3
        // times when a kept prime divides a coefficient of 2^8 to 2^16 words, and the
        // reduction alone of an exact quotient at most 10.9 times (`exact_div`); the products
        // have been by `num::fast::mul_int` since 2026-11-07, not measured again here. So a product
        // or quotient needing less is refused when the free memory lies between the two, and
        // none aborts. Tested by
        // `a_product_or_quotient_of_wide_numbers_is_refused_when_memory_is_short`
        // and `an_exact_quotient_of_a_wide_number_is_refused_when_memory_is_short`
        // (COMPLEXITY.md K30). A complete solution would ask each allocation of the reduction
        // for its own memory, which needs a reduction written here rather than num-bigint's.
        let bits = self.num.bits() + self.den.bits() + up.bits() + down.bits();
        room(BigUint::from(bits), BigUint::from(bits) << 4u32)?;
        Ok(Rat::build(
            fast::mul_int(&self.num, up),
            fast::mul_int(&self.den, down),
            merge(&self.pows, pows, f),
        ))
    }

    /// `-a`.
    pub fn neg(&self) -> Rat {
        // A `Ten` is copied with its digits, O(n); its binary form, which holds the sign, is
        // made again when needed.
        Rat {
            num: -&self.num,
            den: self.den.clone(),
            pows: self.pows.clone(),
            ten: (self.t()).map(|t| {
                Box::new(Ten {
                    t: t.clone(),
                    bin: OnceLock::new(),
                })
            }),
        }
    }

    /// `-a`, or [`TooLarge`] when the system refuses the memory for its coefficients: negating
    /// copies them.
    pub fn try_neg(&self) -> Result<Rat, TooLarge> {
        let size = BigUint::from(self.num.bits() + self.den.bits());
        room(size.clone(), size)?;
        Ok(self.neg())
    }

    /// A copy, or [`TooLarge`] when the system refuses the memory for its coefficients.
    fn try_copy(&self) -> Result<Rat, TooLarge> {
        let size = BigUint::from(self.num.bits() + self.den.bits());
        room(size.clone(), size)?;
        Ok(self.clone())
    }

    /// `|a|`.
    pub fn abs(&self) -> Rat {
        match self.is_negative() {
            true => self.neg(),
            false => self.clone(),
        }
    }

    /// The bit lengths of the numerator and the denominator, each where [`Rat::pow`] builds
    /// its power: where it is wider than 64 bits. A narrower one is factored and kept as prime
    /// exponents, so its power builds nothing and it has `None`. `self ^ k` has at least
    /// `k * (L - 1) + 1` bits for each part of `L` bits, since the part is at least
    /// `2^(L - 1)` in magnitude (DESIGN.md sec:checking_in_zed).
    pub fn built_widths(&self) -> [Option<u64>; 2] {
        [&self.num, &self.den].map(|part| {
            let part = part.magnitude();
            part.to_u64().is_none().then(|| part.bits())
        })
    }

    /// `a^e`. Powers of primes multiply their exponents, and a numerator or denominator that
    /// fits in 64 bits is factored into primes, so `10 ^ 10 ^ 9` is `2^(10^9) * 5^(10^9)`.
    /// [`TooLarge`] when a wider part's power is built and the system refuses the memory.
    pub fn pow(&self, e: &BigUint) -> Result<Rat, TooLarge> {
        if e.is_zero() {
            return Ok(Rat::int(BigInt::one()));
        }
        if self.is_zero() {
            return Ok(self.clone());
        }
        if let Some(t) = self.t() {
            // `(r 10^t)^e = r^e 10^(t e)`: for `e` of one word, `t e` by its digits, O(n)
            // (DESIGN.md step L1.17b, `(1eNr)^3`); a wider `e` needs `t` in binary.
            return match e.to_u64() {
                Some(k) => Ok(Rat::with_ten(self.rest().pow(e)?, t.mul_u64(k))),
                None => self.bin().pow(e),
            };
        }
        let parts = [self.num.magnitude(), self.den.magnitude()];
        // Complexity tradeoff: the memory asked for is eight times the width of the built
        // powers together, a measured bound, not a proved one, on `num::fast::pow`,
        // by squaring (each square by `num::fast::mul`, the base and the running result held at
        // once), the numerator's power held while the denominator's is built: the peak heap of
        // a power was at most 6.43 times the width over bases of 2^10 to 2^22 bits and
        // exponents 2 to 31 (2026-11-07, BIGINT-fast-mul; 6.09 with num-bigint's power), and
        // 3.55 times it for a rational with both parts wide (measured with num-bigint's). So a
        // power needing less is refused when the free memory lies between the two, and none
        // aborts. Tested by
        // `a_power_of_a_wide_base_is_refused_when_memory_is_short` (COMPLEXITY.md K30). A
        // complete solution would ask each allocation of the power for its own memory.
        let widths = self.built_widths();
        let wide: u64 = widths.into_iter().flatten().sum();
        // The refusal of the wide parts' powers: their size in bits, and the memory asked,
        // eight times the width times `e`; asked of `room` here, and returned below when `e` is
        // too wide to raise a part to. The size is the least the powers have, `e * (L - 1) + 1`
        // bits for each part of `L` bits ([`Rat::built_widths`]), as a message reads it as what
        // the step needs (`least_bits`, row CONST-least-refusal-size); the width times `e`, an
        // upper bound, took 65 bits a factor for `(2^64 + 13) ^ (2^64)` and named 130 EiB where
        // the number has `64 * 2^64 + 19` bits, 128 EiB (plan row MSG-too-large-figure).
        let refusal = || {
            let size = (widths.into_iter().flatten())
                .map(|l| BigUint::from(l - 1) * e + 1u32)
                .sum();
            TooLarge {
                ask: (BigUint::from(wide) * e) << 3u32,
                size,
            }
        };
        if wide > 0 {
            let TooLarge { size, ask } = refusal();
            room(size, ask)?;
        }
        let times = BigInt::from(e.clone());
        let mut pows: Vec<(u64, BigInt)> = self
            .pows
            .iter()
            .map(|(p, x)| (*p, fast::mul_int(x, &times)))
            .collect();
        let mut raised = [BigInt::one(), BigInt::one()];
        for (i, part) in parts.into_iter().enumerate() {
            if part.is_one() {
                continue;
            }
            match part.to_u64() {
                Some(w) => {
                    for (p, k) in factor(w) {
                        let x = &times * k;
                        pows.push((p, if i == 0 { x } else { -x }));
                    }
                }
                // Complexity tradeoff: a numerator or denominator beyond 64 bits is raised to
                // the power by building it, at a cost proportional to the result's size,
                // where one within 64 bits is factored and kept as exponents; such a part only
                // arises from a value built before, so its power is the size of that value
                // times `e`; one that does not fit in memory is `TooLarge`, asked above. Tested
                // by `a_power_of_a_wide_base_is_built` (COMPLEXITY.md K30).
                // A complete solution would keep an opaque base `b^e` beside the primes, with
                // the bases made pairwise coprime by Bernstein's coprime-base algorithm (D. J.
                // Bernstein, "Factoring into coprimes in essentially linear time", J.
                // Algorithms 54(1):1-30, 2005, doi:10.1016/j.jalgor.2004.04.009; Crossref and
                // the text checked 2026-11-20). Its abstract: a coprime base for a set S is a
                // set P of pairwise coprime integers with each element of S a product of
                // powers of elements of P, and the paper computes the natural one "in
                // essentially linear time" using only products, exact divisions, gcds and
                // equality tests. Not implemented; no test.
                None => {
                    // An exponent of `2^64` or more is refused with the ask above. With a
                    // 64-bit `usize`, `room` has already refused it (this part is wider than
                    // 64 bits, so the ask is at least `65 * 2^67` bits, `65 * 2^61` words,
                    // more than a `usize` counts); on any other target this returns the same
                    // refusal, so the step holds by the code, not by that argument. Tested by
                    // `a_power_of_a_wide_base_to_an_exponent_beyond_64_bits_is_refused`.
                    let Some(e) = e.to_u64() else {
                        return Err(refusal());
                    };
                    raised[i] = BigInt::from(fast::pow(part, e));
                }
            }
        }
        pows.sort_unstable_by_key(|(p, _)| *p);
        let [mut num, den] = raised;
        if self.is_negative() && e.bit(0) {
            num = -num;
        }
        // The factored primes are new: `num` and `den` held none of the listed ones.
        Ok(Rat {
            num,
            den,
            pows: pows.into_boxed_slice(),
            ten: None,
        })
    }

    /// `a^e` for an integer `e` of either sign (DESIGN.md sec:lexical, `^` on a `rat`): a
    /// negative `e` gives `1 / a^|e|`, and `Ok(None)` for `0^e` with `e` negative, which is
    /// `#divByZero` as `1r / 0r` is. A base of `0`, `1` or `-1` is read from the exponent's
    /// sign and parity, so `1r ^ 2 ^ 2 ^ 33` builds no exponent; any other base builds `e` and
    /// is raised by [`Rat::pow`]. [`TooLarge`] when building `e` or the power is refused its
    /// memory.
    ///
    /// Complexity tradeoff (COMPLEXITY.md K108): naive is `|e|` products of the base, O(e)
    /// products. Used: a base of `0`, `1` or `-1` costs O(1) from `e`'s kept form; any other
    /// base costs [`Rat::pow`], O(log e) products with its kept prime exponents multiplied by
    /// `e`, plus O(bits of `e`) to build `e`; a negative `e` adds O(1) moves in `Rat::recip`.
    pub fn pow_int(&self, e: &Rat) -> Result<Option<Rat>, TooLarge> {
        let one = || Rat::int(BigInt::one());
        if e.is_zero() {
            return Ok(Some(one()));
        }
        if self.is_zero() {
            return Ok((!e.is_negative()).then(|| self.clone()));
        }
        if self.is_plain() && self.den.is_one() && self.num.magnitude().is_one() {
            return Ok(Some(match self.is_negative() && !e.is_even() {
                true => self.clone(),
                false => one(),
            }));
        }
        let k = e.to_integer()?;
        let p = self.pow(k.magnitude())?;
        Ok(Some(match k.is_negative() {
            true => p.recip(),
            false => p,
        }))
    }

    /// `1 / a` of a nonzero `a`: the numerator and denominator swapped, the sign kept on the
    /// numerator, and every exponent negated. It moves what it holds and builds nothing.
    fn recip(self) -> Rat {
        let Rat {
            num,
            den,
            mut pows,
            ten,
        } = self;
        for (_, e) in pows.iter_mut() {
            *e = -std::mem::take(e);
        }
        let (num, den) = match num.is_negative() {
            true => (-den, -num),
            false => (den, num),
        };
        let rest = Rat {
            num,
            den,
            pows,
            ten: None,
        };
        // `10^-t`: the exponents of 2 and 5 are now negative, so `with_ten` moves their
        // common part into the negated `t`, O(n).
        match ten {
            None => rest,
            Some(ten) => Rat::with_ten(rest, ten.t.neg()),
        }
    }

    /// The Euclidean remainder of two integers, in `0 ..< |m|`; `m` is not zero. An exact
    /// division gives `0` and a dividend in `0 ..< |m|` gives itself, without building either;
    /// otherwise a power of a prime is reduced by modular exponentiation, so `10 ^ 10 ^ 9 mod
    /// 7` builds no large number. [`TooLarge`] when the divisor is built, or the two are
    /// compared to more bits than the system gives memory for.
    pub fn rem_euclid(&self, m: &Rat) -> Result<Rat, TooLarge> {
        if self.ten.is_some() || m.ten.is_some() {
            return self.bin().rem_euclid(m.bin());
        }
        if self.is_plain() && m.is_plain() {
            let r = rem(self.num.magnitude(), m.num.magnitude())?;
            return euclid(r, self.is_negative(), m.num.magnitude());
        }
        if self.divides_by(m)? {
            return Ok(Rat::int(BigInt::zero()));
        }
        if !self.is_negative() && self.magnitude_order(m, true)? == Ordering::Less {
            return self.try_copy();
        }
        self.rem_built(m)
    }

    /// The Euclidean remainder by an `m` that does not divide this integer, found by building
    /// `m`.
    fn rem_built(&self, m: &Rat) -> Result<Rat, TooLarge> {
        if self.ten.is_some() || m.ten.is_some() {
            return self.bin().rem_built(m.bin());
        }
        // Complexity tradeoff: a remainder that is neither `0` nor the dividend itself is
        // found by building the divisor `m`, at a cost proportional to `m`'s size, which bounds
        // the remainder's; `3 ^ 10 ^ 9 mod 2 ^ 10 ^ 9` builds `2^(10^9)`, while
        // `10 ^ 10 ^ 12 mod 2 ^ 10 ^ 12` and `5 mod 2 ^ 10 ^ 12` build nothing. An input
        // is refused only when the memory asked for it is refused: its divisor built, the
        // remainder of its coefficient (`rem`, 24 times `m`'s width) or a modular-power step
        // (32 times, below), each a measured bound that can exceed the real need; any of these
        // refused is `TooLarge`. Tested by `an_exact_division_by_a_huge_power_builds_nothing`,
        // `kept_powers_agree_with_the_built_value` and
        // `a_kept_power_modulo_a_wide_number_is_refused_below_its_ask` (COMPLEXITY.md K30). A
        // complete solution would keep a residue modulo a kept power unbuilt, as `p^a mod p^b`
        // is, which needs modular arithmetic on the kept forms.
        let (_, m) = m.to_integer()?.into_parts();
        let mut r = rem(self.num.magnitude(), &m)?;
        if !self.pows.is_empty() {
            // Complexity tradeoff: the memory asked for the modular-power steps is 32 times
            // `m`'s width, a measured bound, not a proved one, on a step's peak: it holds `r`,
            // `p^e mod m` (num-bigint's Montgomery power, Montgomery 1985 as cited in
            // `num::fast`'s "Sources", for an odd `m`, square and multiply
            // for an even one), their product and its division by `m`, and the peak heap was
            // at most 25.2 times `m`'s width over divisors of 2^8 to 2^13 words, odd and even.
            // So a kept-power dividend modulo a wide divisor whose steps need less is
            // `TooLarge` when the free memory lies between the two, and none aborts. Tested by
            // `a_kept_power_modulo_a_wide_number_is_refused_below_its_ask` (COMPLEXITY.md K30).
            // A complete solution would ask each allocation of the power and the division for
            // its own memory, which needs a modular power written here rather than
            // num-bigint's.
            room(BigUint::from(m.bits()), BigUint::from(m.bits()) << 5u32)?;
        }
        for (p, e) in self.pows.iter() {
            r = r * BigUint::from(*p).modpow(e.magnitude(), &m) % &m;
        }
        euclid(r, self.is_negative(), &m)
    }

    /// The Euclidean quotient of two integers; `m` is not zero. An exact division keeps the
    /// powers, and a dividend smaller than `|m|` gives `0` or `±1`, building nothing; any
    /// other builds the remainder, by the rule of [`Rat::rem_euclid`], and the dividend's part
    /// above the powers it shares with the remainder, by the rule of [`Rat::add`].
    pub fn div_euclid(&self, m: &Rat) -> Result<Rat, TooLarge> {
        if self.ten.is_some() || m.ten.is_some() {
            return self.bin().div_euclid(m.bin());
        }
        if self.is_plain() && m.is_plain() {
            // Complexity tradeoff: the memory asked for is the quotient's width for a divisor
            // of one word, which num-bigint divides into a single copy of the dividend; for a
            // quotient wider than a divisor whose transforms `fast::Divisor` keeps
            // (`fast::reciprocal_points`), found block by block through it, `POINT_WORDS` words
            // a point and twice the dividend's width, the quotient written once and copied once
            // into its number; and sixteen times the dividend's width for any other divisor of
            // two or more words. These are measured, not proved: the peak heap of
            // `num::fast::div_euclid` (glibc's mmap threshold fixed at 128 KiB) was at most 14.5
            // times the dividend's width for a quotient no wider than a dense divisor, and 25.5
            // for `2w` words by a dense `w` just above a power of two (12.75 words a point),
            // over divisors of 2^12 - 1 to 2^16 + 1 words (2026-11-09); 7.94 over
            // dividends of 2^8 to 2^20 words with the earlier products (2026-11-06). So a
            // quotient by a wide divisor that needs less is refused when the free memory lies
            // between the two, and none aborts. No answer rests on these figures: they set the
            // memory asked for before the division, so a figure too low can only turn the
            // refusal into the allocator's abort, never give a wrong quotient. Tested by
            // `dividing_a_wide_number_is_refused_when_memory_is_short`,
            // `dividing_by_a_wide_divisor_answers_when_its_peak_is_given` and
            // `a_dense_divisor_asks_for_its_transforms` (COMPLEXITY.md K30). A complete
            // solution would be a division whose peak is known by construction, each
            // allocation asked for.
            let a = BigUint::from(self.num.bits());
            let b = m.num.magnitude();
            room(
                a.clone(),
                match (b.to_u64(), fast::reciprocal_points(b, self.num.bits())) {
                    (Some(_), _) => a,
                    // `k > n`: the quotient has more bits than the divisor (`fast::div_rem`).
                    (None, Some(points)) if self.num.bits() >= 2 * b.bits() => {
                        BigUint::from(points) * (64 * POINT_WORDS) + (a << 1u32)
                    }
                    (None, _) => a << 4u32,
                },
            )?;
            return Ok(Rat::int(fast::div_euclid(&self.num, &m.num)));
        }
        if self.divides_by(m)? {
            return self.exact_div(m);
        }
        if self.magnitude_order(m, true)? == Ordering::Less {
            // `0 <= a < |m|` gives `0`; `-|m| < a < 0` gives `-1` toward a positive `m`.
            let q = match (self.is_negative(), m.is_negative()) {
                (false, _) => 0,
                (true, false) => -1,
                (true, true) => 1,
            };
            return Ok(Rat::int(BigInt::from(q)));
        }
        // Complexity tradeoff: a quotient that is not exact and not `0` or `±1` is found by
        // building the remainder (`rem_built`) and the part of the dividend above the powers
        // it shares with the remainder (`Rat::add`), at a cost proportional to the dividend's
        // size, near the quotient's; `3 ^ 10 ^ 9 div 2 ^ 10 ^ 9` builds both, while
        // `10 ^ 10 ^ 12 div 2 ^ 10 ^ 12` builds nothing. An input is refused only when the
        // memory asked for its parts is refused, by the measured bounds of `rem_built` and
        // `exact_div`, which can exceed the real need; any of these refused is `TooLarge`.
        // Tested by `a_kept_power_modulo_a_wide_number_is_refused_below_its_ask`,
        // `an_exact_quotient_of_a_wide_number_is_refused_when_memory_is_short`,
        // `an_exact_division_by_a_huge_power_builds_nothing` and
        // `kept_powers_agree_with_the_built_value` (COMPLEXITY.md K30). A complete solution
        // would keep the floor of a quotient of kept powers unbuilt, which needs the same
        // modular arithmetic on kept forms as `rem_built`.
        let r = self.rem_built(m)?;
        self.sub(&r)?.exact_div(m)
    }

    /// Whether the integer `m` divides this integer, with no quotient built: once both are
    /// aligned to the primes either lists, each exponent of `m` is at most this one's and `m`'s
    /// coefficient divides this one's ([`rem`]). [`TooLarge`] when aligning copies a
    /// coefficient, or the remainder needs more memory, than the system gives.
    fn divides_by(&self, m: &Rat) -> Result<bool, TooLarge> {
        if self.ten.is_some() || m.ten.is_some() {
            return self.bin().divides_by(m.bin());
        }
        if self.is_zero() {
            return Ok(true);
        }
        let a = self.aligned(&m.pows, true)?;
        let b = m.aligned(&self.pows, true)?;
        if zip_pows(&a.pows, &b.pows).any(|(_, x, y)| y > x) {
            return Ok(false);
        }
        Ok(rem(a.num.magnitude(), b.num.magnitude())?.is_zero())
    }

    /// `a / m` for an `m` that divides this integer, or [`TooLarge`] when the system refuses
    /// the memory for it, by the rule of [`Rat::div`]: the reduction's peak heap was at most
    /// 10.9 times the coefficients' width, for products of 512 to 2^14 words reduced by
    /// factors of 66 words to their own length.
    fn exact_div(&self, m: &Rat) -> Result<Rat, TooLarge> {
        if self.ten.is_some() || m.ten.is_some() {
            return self.bin().exact_div(m.bin());
        }
        // Unreachable: `Rat::div` returns `None` only for a zero divisor, and an `m` that
        // divides is not zero; every caller passes a nonzero `m` (`div_euclid` requires it).
        Ok(self.div(m)?.expect("the divisor is not zero"))
    }

    /// The same number, with each prime of `others` moved out of `num` and `den` too. When one
    /// of them divides a coefficient, the coefficients are copied and divided; when `check`,
    /// [`TooLarge`] first if the system refuses the memory for that.
    fn aligned(&self, others: &[(u64, BigInt)], check: bool) -> Result<Cow<'_, Rat>, TooLarge> {
        if self.ten.is_some() {
            return self.bin().aligned(others, check);
        }
        let listed = |p: u64| sorted_get(&self.pows, &p).is_some();
        let divides = |p: u64| divides(self.num.magnitude(), p) || divides(self.den.magnitude(), p);
        let new: Vec<u64> = others
            .iter()
            .map(|(p, _)| *p)
            .filter(|&p| !listed(p) && divides(p))
            .collect();
        if new.is_empty() {
            return Ok(Cow::Borrowed(self));
        }
        if check {
            // Complexity tradeoff: the memory asked for is sixteen times the coefficients'
            // width, a measured bound, not a proved one, on the copy of both coefficients and,
            // while a power of `p` is divided out of one (`valuation`), its quotient, its
            // remainder and the powers of `p` up to the square of the widest that divides it:
            // the peak heap of `valuation` was at most 10.7 times its operand's width over
            // powers of 3 of 2^10 to 2^17 words. So an alignment that needs less is
            // `TooLarge` (for `==`, the `Watch` record `EqualityTooLarge`) when the free memory
            // lies between the two, and none aborts. Tested by
            // `equality_that_must_copy_a_wide_number_is_refused_when_memory_is_short`
            // (COMPLEXITY.md K30). A complete solution would ask each allocation of
            // `valuation` for its own memory, or divide the powers of `p` out in place.
            let size = BigUint::from(self.num.bits() + self.den.bits());
            room(size.clone(), size << 4u32)?;
        }
        let mut pows = self.pows.to_vec();
        pows.extend(new.into_iter().map(|p| (p, BigInt::zero())));
        pows.sort_unstable_by_key(|(p, _)| *p);
        Ok(Cow::Owned(Rat::extract(
            self.num.clone(),
            self.den.clone(),
            pows,
        )))
    }

    /// `|self|` as the quotient of two products of positive powers.
    fn split<'a>(&'a self) -> (Product<'a>, Product<'a>) {
        if self.ten.is_some() {
            return self.bin().split();
        }
        let side = |coef: &'a BigInt, sign: Sign| Product {
            coef: Cow::Borrowed(coef.magnitude()),
            pows: self
                .pows
                .iter()
                .filter(|(_, e)| e.sign() == sign)
                .map(|(p, e)| (*p, e.magnitude().clone()))
                .collect(),
        };
        (side(&self.num, Sign::Plus), side(&self.den, Sign::Minus))
    }

    /// The nearest number of the format, ties to even, as its sign, significand and the
    /// exponent of its leading place; `None` for zero.
    fn project(&self, f: &Format) -> Result<Option<(bool, u64, i64)>, LiteralRounding> {
        if self.ten.is_some() {
            return self.bin().project(f);
        }
        if self.is_zero() {
            return Ok(None);
        }
        let (n, d) = self.split();
        // `|self| * 2^s == w` is read as `self == ±w * 2^-s`: the side built is the small one,
        // and the power of 2 is kept.
        let is = |s: &BigInt, w: &BigUint| {
            let w = Rat::extract(BigInt::from(w.clone()), BigInt::one(), vec![(2, -s)]);
            match self.is_negative() {
                true => *self == w.neg(),
                false => *self == w,
            }
        };
        let (m, t) = bound::round(&n, &d, f, &is)?;
        Ok(Some((self.is_negative(), m, t)))
    }

    /// The whole number `rule` rounds it to (DESIGN.md sec:facets, "Rounding to a whole
    /// number"): an integer is itself, kept as it is, and any other number `N/D`, `D > 1`, is
    /// `q = N div D` (Euclidean, toward −∞) or `q + 1`, chosen by `rule` from the sign and from
    /// `2 (N mod D)` against `D`, which is never equal to `D` when `D` is odd. [`TooLarge`] when
    /// the system refuses the memory for the quotient or the remainder.
    ///
    /// Complexity tradeoff: none. The naive way rounds a float through `f64::floor` and the
    /// like, and a `rat` by building `N` and `D`; here every operand is one rational, so a
    /// float's exact value and a `rat` take one path. The cost is one Euclidean quotient and
    /// one remainder of `N` by `D` ([`Rat::div_euclid`], [`Rat::rem_euclid`], O(M(n)) in the
    /// bits of `N`, a kept power of a prime reduced without being built where they can), a
    /// doubling, a comparison and an addition of 1, each linear in the remainder's or the
    /// quotient's size. Scaling test:
    /// `l01_18_scalar_interpreter::bench::rounding::rounding_wide_rationals_scales`.
    pub fn round_whole(&self, rule: Rounding) -> Result<Rat, TooLarge> {
        if self.ten.is_some() {
            return self.bin().round_whole(rule);
        }
        if self.is_integer() {
            return Ok(self.clone());
        }
        // `N` and `D` as integers kept with their powers: the powers of positive exponent are
        // `N`'s and those of negative exponent `D`'s, so nothing is built.
        let (up, down): (Vec<_>, Vec<_>) = self
            .pows
            .iter()
            .cloned()
            .partition(|(_, e)| e > &BigInt::zero());
        let down = down.into_iter().map(|(p, e)| (p, -e)).collect();
        let n = Rat::extract(self.num.clone(), BigInt::one(), up);
        let d = Rat::extract(self.den.clone(), BigInt::one(), down);
        let q = n.div_euclid(&d)?;
        let r = n.rem_euclid(&d)?;
        let half = r.twice_integer().try_cmp(&d)?;
        let neg = self.is_negative();
        let up = match rule {
            Rounding::Floor => false,
            Rounding::Ceil => true,
            Rounding::Trunc => neg,
            Rounding::AwayFromZero => !neg,
            Rounding::TiesEven => match half {
                Ordering::Equal => !q.is_even(),
                o => o == Ordering::Greater,
            },
            Rounding::TiesAway => match half {
                Ordering::Equal => !neg,
                o => o == Ordering::Greater,
            },
        };
        match up {
            true => q.add(&Rat::int(BigInt::one())),
            false => Ok(q),
        }
    }

    /// The nearest `f64`, ties to even: correctly rounded from the exact value, without
    /// building it. [`LiteralRounding`] when it rounds to infinity, or to zero while not zero,
    /// or when the system refuses the memory to tell which way it rounds.
    pub fn to_f64(&self) -> Result<f64, LiteralRounding> {
        let f = Format {
            prec: 53,
            emin: -1022,
            emax: 1023,
        };
        Ok(match self.project(&f)? {
            None => 0.0,
            Some((neg, m, t)) => {
                let bits = if m >> 52 == 0 {
                    m
                } else {
                    (((t + 1023) as u64) << 52) | (m & ((1 << 52) - 1))
                };
                f64::from_bits(bits | (u64::from(neg) << 63))
            }
        })
    }

    /// The nearest `f32`, by the rule of [`Rat::to_f64`].
    pub fn to_f32(&self) -> Result<f32, LiteralRounding> {
        let f = Format {
            prec: 24,
            emin: -126,
            emax: 127,
        };
        Ok(match self.project(&f)? {
            None => 0.0,
            Some((neg, m, t)) => {
                let m = m as u32;
                let bits = if m >> 23 == 0 {
                    m
                } else {
                    (((t + 127) as u32) << 23) | (m & ((1 << 23) - 1))
                };
                f32::from_bits(bits | (u32::from(neg) << 31))
            }
        })
    }
}

/// `num / den` reduced, with `den` positive.
fn reduce(num: BigInt, den: BigInt) -> (BigInt, BigInt) {
    let g = gcd(&num, &den);
    let sign = if den.is_negative() { -1 } else { 1 };
    // `g` divides both and is positive, so each floor is the exact quotient.
    (
        sign * fast::div_floor(&num, &g),
        sign * fast::div_floor(&den, &g),
    )
}

/// The greatest common divisor of `a` and `b`, not negative.
fn gcd(a: &BigInt, b: &BigInt) -> BigInt {
    BigInt::from(gcd_uint(a.magnitude(), b.magnitude()))
}

/// `(a / b, a mod b)` for `b` not zero, O(M(n)) in the width of `a` (`num::fast::div_rem`), for
/// integers held outside a [`Rat`].
pub fn div_rem_uint(a: &BigUint, b: &BigUint) -> (BigUint, BigUint) {
    fast::div_rem(a, b)
}

/// `a mod b` for `b` not zero, the second of [`div_rem_uint`], with no quotient built when it
/// would be wider than `b` (`num::fast::rem`).
pub fn rem_uint(a: &BigUint, b: &BigUint) -> BigUint {
    fast::rem(a, b)
}

/// `(r, a - r^k)` with `r = floor(a^(1/k))`, for `k >= 1`, for integers held outside a
/// [`Rat`]: [`sqrt_rem_uint`] for `k = 2`; for `k >= 3`, `nth_root_near`, `r` or `r + 1`, and
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
    if wide <= u64::from(u32::BITS - k.leading_zeros()) + 64 {
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
    let c = u64::from(u32::BITS - (k - 1).leading_zeros());
    let h = (wide - c - 4) / 2;
    // Step 1.
    let s = nth_root_near(&(a >> (k64 * h)), k) + 1u32;
    // Steps 2 and 3.
    let big_a = a >> ((k64 - 1) * h);
    let p = pow_uint(&s, k64 - 1);
    let wq = (big_a.bits() + 1).saturating_sub(p.bits());
    let d = p.bits().saturating_sub(wq + 2);
    let (q, _) = div_rem_uint(&(big_a >> d), &(p >> d));
    // Steps 4 to 6.
    ((s << h) * (k - 1) + q) / k
}

/// `floor(a / m)` for `m` not zero, either sign, for integers held outside a [`Rat`]: the
/// division of the magnitudes by [`div_rem_uint`], O(M(n)) past its measured crossover with
/// num-bigint's division (`num::fast::div_rem`), where num-bigint's `div_floor` alone is
/// O(n^1.52) (Burnikel and Ziegler over Toom-3, both cited in `num::fast`'s "Sources").
pub fn div_floor_int(a: &BigInt, m: &BigInt) -> BigInt {
    fast::div_floor(a, m)
}

/// `a - m floor(a / m)` for `m` not zero, the remainder of [`div_floor_int`], which has the
/// sign of `m`, by [`rem_uint`] on the magnitudes.
pub fn mod_floor_int(a: &BigInt, m: &BigInt) -> BigInt {
    fast::mod_floor(a, m)
}

/// `a^-1 mod m` for `m` above zero, below `m`, or `None` when `a` and `m` have a common
/// factor, for integers held outside a [`Rat`]: the binary half gcd with its steps kept
/// (`num::fast::inverse_mod`), O(M(n) log n), where the extended Euclidean algorithm is
/// O(n^2). Panics with "a modulus above 0" for `m` zero.
pub fn inverse_mod_uint(a: &BigUint, m: &BigUint) -> Option<BigUint> {
    fast::inverse_mod(a, m)
}

/// The greatest common divisor of `a` and `b`, for integers held outside a [`Rat`].
///
/// One gcd (DRY-number-theory-wide item 3, dryN2, 2026-11-19): `gcd_uint_recursive`, the same
/// half gcd with no handoff to Stein's gcd at `GCD_LEAF` once what is left is narrow, was
/// removed. Measured in release (`gcd` against it, best of 5, load 52 to 88, random pairs and
/// pairs with a common factor): 0.97 to 1.21 times `gcd`'s time from 4 to 310 words, where the
/// two run the same steps (within the noise at that load), and 1.04 to 1.53 times from 512 to
/// 16384 words, where `gcd` hands the last 310 words to Stein's gcd; so no width favored it.
/// Its one client, `Int::gcd_recursive` in zedc-int, now calls `Int::gcd`. Tests:
/// `completeness::fast` (the gcd cases) and `crossover::gcd` against num-bigint.
pub fn gcd_uint(a: &BigUint, b: &BigUint) -> BigUint {
    let (Some(za), Some(zb)) = (a.trailing_zeros(), b.trailing_zeros()) else {
        return a | b;
    };
    let z = za.min(zb);
    // The powers of 2 come out first, by shifts, so that `2^m` against `2^n 3` costs O(m + n)
    // and not a division of `m` bits by `n`. When an odd part fits in 64 bits, the other
    // operand's remainder modulo it is streamed over its words with no shift or allocation (since
    // `gcd(2^za, d) == 1` for odd `d`) and finished in registers. Otherwise, equal odd parts
    // return at once, and the wider odd part is reduced modulo the narrower by `fast::rem` (with
    // no quotient built, O(M(n))) before the half gcd (`fast::gcd`) runs at the narrower width.
    fn odd_u64(x: &BigUint, zx: u64) -> Option<u64> {
        if x.bits() - zx > 64 {
            return None;
        }
        let w = (zx / 64) as usize;
        let sh = (zx % 64) as u32;
        let mut it = x.iter_u64_digits().skip(w);
        let lo = it.next().unwrap_or(0);
        let hi = it.next().unwrap_or(0);
        Some(if sh == 0 {
            lo
        } else {
            (lo >> sh) | (hi << (64 - sh))
        })
    }
    if let Some(da) = odd_u64(a, za) {
        return BigUint::from(gcd_big_u64(b, da)) << z;
    }
    if let Some(db) = odd_u64(b, zb) {
        return BigUint::from(gcd_big_u64(a, db)) << z;
    }
    fn odd(x: &BigUint, z: u64) -> Cow<'_, BigUint> {
        match z {
            0 => Cow::Borrowed(x),
            _ => Cow::Owned(x >> z),
        }
    }
    let (a, b) = (odd(a, za), odd(b, zb));
    if *a == *b {
        return a.into_owned() << z;
    }
    let g = match a.bits().cmp(&b.bits()) {
        Ordering::Greater => fast::gcd(&b, &fast::rem(&a, &b)),
        Ordering::Less => fast::gcd(&a, &fast::rem(&b, &a)),
        Ordering::Equal => fast::gcd(&a, &b),
    };
    g << z
}

/// `(g, s, t)` with `s a + t b = g = gcd(a, b) >= 0`.
// Complexity tradeoff: extended Euclid writes a quadratic total of remainders.
// Binary half-GCD accumulates one coefficient column in O(M(n) log n),
// then one exact division recovers the other coefficient. Always `Some`: `fast::bezout` is
// total, its halving count fitting in u128 on every target (proof at `num/fast.rs`
// `bezout_with`, step 6; PROOF-bezout-halvings-address-width). The `Option` stays only
// because zedc-int `Int::extended_gcd` and its users in zedc-presburger still read it; their
// `None` arms (zedc-int `Int::bezout_or_euclid`'s Euclid fallback) are unreachable.
// No input size changes the verdict. Tests in modular.rs:
// pncx_fast_bezout_matches_euclid, and pncx_fibonacci_scale, deferred to plan row
// PERF-negated-chain-unsolved in wt/scratch/deferred-tests/PERF-negated-chain-unsolved.rs.
pub fn bezout_int(a: &BigInt, b: &BigInt) -> Option<(BigInt, BigInt, BigInt)> {
    let (g, s, t) = fast::bezout(a.magnitude(), b.magnitude());
    let s = if a.is_negative() { -s } else { s };
    let t = if b.is_negative() { -t } else { t };
    Some((BigInt::from(g), s, t))
}

/// The sign of a text and the rest of it after an optional `-` or `+`.
pub(crate) fn sign_of(text: &str) -> (Sign, &str) {
    match (text.strip_prefix('-'), text.strip_prefix('+')) {
        (Some(rest), _) => (Sign::Minus, rest),
        (None, Some(rest)) => (Sign::Plus, rest),
        (None, None) => (Sign::Plus, text),
    }
}

/// A decimal literal's sign, whole digits, fraction digits and signed exponent digits.
type DecimalParts<'t> = (Sign, &'t str, &'t str, Option<(Sign, &'t str)>);

/// The parts of a decimal literal's text, as [`Rat::decimal_parts`] takes them: its sign, its
/// whole and fraction digits and its exponent; `None` when it is not decimal digits with an
/// optional sign, fraction and exponent.
fn decimal_syntax(text: &str) -> Option<DecimalParts<'_>> {
    let (mantissa, exp): (&str, Option<(Sign, &str)>) = match text.find(['e', 'E']) {
        Some(i) => (&text[..i], Some(sign_of(&text[i + 1..]))),
        None => (text, None),
    };
    let (sign, mantissa) = sign_of(mantissa);
    let (whole, frac): (&str, &str) = mantissa.split_once('.').unwrap_or((mantissa, ""));
    let digits = |t: &str| digit_text::all_digits(t.as_bytes());
    let read = !(whole.is_empty() && frac.is_empty()) && digits(whole) && digits(frac);
    if !read || exp.is_some_and(|(_, e)| e.is_empty() || !digits(e)) {
        return None;
    }
    Some((sign, whole, frac, exp))
}

/// The value of a text of ASCII decimal digits; `Ok(None)` when it is empty or holds anything
/// else, and [`TooLarge`] when the system refuses the memory for reading it, asked before
/// anything is built.
pub fn read_decimal(digits: &str) -> Result<Option<BigUint>, TooLarge> {
    if digits.is_empty() || !digit_text::all_digits(digits.as_bytes()) {
        return Ok(None);
    }
    // Complexity tradeoff: the memory asked for is 48 bits for each digit, a measured bound,
    // not a proved one, on the reading by halves (the powers of ten, the parts and their
    // products by `num::fast::mul` held at once): the peak heap was at most 34.7 bits per digit
    // (10.4 times the `3.32 n` bits of the number) over texts of 2^12 to 2^24 nines, and 45.3
    // with glibc's default mmap threshold, which keeps freed blocks of up to 32 MiB on the
    // heap (2026-11-06). So a text needing less is
    // refused when the free memory lies between the two, and none aborts. Tested by
    // `a_long_decimal_literal_is_refused_when_memory_is_short` (COMPLEXITY.md K30). A complete
    // solution would ask each allocation of the reading for its own memory.
    let len = BigUint::from(digits.len());
    room(bits_of_digits(&len), len * 48u32)?;
    Ok(Some(read_digits(digits)))
}

/// The value of a nonempty text of ASCII decimal digits, with no check of its size.
///
/// num-bigint reads a text one machine word of digits at a time into the whole number read so
/// far, O(n^2) for `n` digits. This reads the text in groups of `LEAF_DIGITS` digits from the
/// low end, then joins the groups in pairs, level by level, as `high * 10^(LEAF_DIGITS *
/// 2^j) + low` at level `j`, the top group carried up alone when it has no pair, with each
/// power `10^(LEAF_DIGITS * 2^j)` the square of the one below. Each level costs about one
/// widest product, O(M(n)) = O(n log n) with `fast::mul` and `fast::Factor`, and there are
/// `log2(n / LEAF_DIGITS)` levels, so the whole is O(n log^2 n). In full: with `h` =
/// `LEAF_DIGITS` and `L = log2(n / h)` levels, the leaves cost O(n h) in all (num-bigint's
/// reading of `n / h` texts of `h` digits, O(h^2) each), and level `j` joins pairs whose widths
/// sum to `n` digits, each pair one product of width `w = h 2^j` at `a w log2 w`, so the level
/// costs `a n (log2 h + j)` and the whole `a n (L log2 h + L^2 / 2 + L / 2) + O(n h)`. Under
/// author decision P300 that predicts the ratio from `n` to `8n` digits:
/// 8 * 234 / 165 = 11.35 at `n` = 2^21, read 9.54 (2026-11-18) and 10.07 (2026-11-20) by
/// `l01_17_value_representation::bench::asks::the_message_for_a_long_literal_costs_n_log_squared_n`.
/// A text of at most `LEAF_DIGITS` digits is read whole, with no power of ten built.
///
/// # Panics
///
/// When `digits` is empty or holds anything but ASCII decimal digits.
pub fn read_digits(digits: &str) -> BigUint {
    read_digits_by(digits, LEAF_DIGITS)
}

/// The power of the prime `p` in `n`, and `n` without it ([`valuation_upto`] with no cap).
fn valuation(n: BigInt, p: u64) -> (u64, BigInt) {
    valuation_upto(n, p, u64::MAX)
}

/// `v = min(v_p(n), cap)` for the power `v_p(n)` of the prime `p` in `n`, and `n / p^v`.
///
/// For `p = 2`, the trailing zero bits. Otherwise, after a check that `p` divides `n` (O(n)),
/// the powers `P_i = p^(2^i)` are built by squaring while `P_i` divides `n`, each tested by
/// the remainder `x = |n| mod P_(i+1)`, until `x` is not zero or `2^(i+1)` passes `cap`; let
/// `J` be the last `i`. (`P_(J+1)` above `|n|` is not divided by: `x` is `|n|`.) If `x` is
/// zero, `v_p(n) >= 2^(J+1) > cap`, so `v` is `cap`. Otherwise `v_p(x)` is `v_p(n)`, below
/// `2^(J+1)`, and its binary digits are read from the top: at step `i`, with `x < P_(i+1)`,
/// `x = q P_i + r`; when `r` is zero, `2^i` is a digit and `x` becomes `q`, otherwise `x`
/// becomes `r`, which has the same power of `p` as `x` since that is below `2^i`. Both are
/// below `P_i`, so the widths halve from step to step. Then `n` is divided once by `p^v`, the
/// product of the `P_i` of its digits.
///
/// The steps down, the powers and the last division cost O(M(n)) in all. The tests on the
/// way up divide `n`, of `N` bits, by powers of `s_i = 2^(i+1) log2 p` bits, `(N / s_i) M(s_i)`
/// each, so O(N log^2 v) in all: O(N) for a power `v` of a few factors, as most decimals have,
/// and O(M(N) log N) = O(N log^2 N) at most, the order of reading the digits.
///
/// With no cap, once the next power `P_(i+1)` passes [`WHOLE_TEST_BITS`], the tests from it on
/// are made from the top instead ([`valuation_from_the_top`]): the powers are squared up to the
/// last `P_T` of at most `N` bits, and `r_T = |n| mod P_T`, then `r_k = r_(k+1) mod P_k` for `k`
/// down from `T`, which is `|n| mod P_k` since `P_k` divides `P_(k+1)`. The `P_k` that divide
/// `n` are those below the least `k` with `r_k` not zero, as in the tests on the way up, so `J`
/// and `x` are the same.
fn valuation_upto(n: BigInt, p: u64, cap: u64) -> (u64, BigInt) {
    if n.is_zero() || cap == 0 {
        return (0, n);
    }
    if p == 2 {
        // Unreachable: a zero `n` returned above, and a nonzero one has a lowest set bit.
        let z = n.trailing_zeros().expect("n is not zero").min(cap);
        return (z, n >> z);
    }
    if !divides(n.magnitude(), p) {
        return (0, n);
    }
    // Complexity tradeoff: each test on the way up divides the whole of `n`, so a power `v` as
    // wide as `n` costs O(n log^2 n), a log above building every `P_i` to the width of `n`
    // first, O(M(n)); but that costs O(M(n)) for every `v`, and through long division of
    // balanced widths it was quadratic up to some 2000 words for the one factor of 5 most
    // decimals have, where the tests cost O(n). The reading of the digits is O(n log^2 n) as
    // well (COMPLEXITY.md K41).
    // `P_0 .. P_J`, each dividing `n`.
    let mut powers = vec![BigUint::from(p)];
    let mut x = loop {
        let i = powers.len() - 1;
        let next = fast::mul(&powers[i], &powers[i]);
        if next.bits() > n.bits() {
            break n.magnitude().clone();
        }
        if cap == u64::MAX && next.bits() > WHOLE_TEST_BITS {
            powers.push(next);
            break valuation_from_the_top(n.magnitude(), &mut powers);
        }
        let x = fast::div_rem(n.magnitude(), &next).1;
        if !x.is_zero() || i + 1 >= 64 || 2u64 << i > cap {
            break x;
        }
        powers.push(next);
    };
    let v = match x.is_zero() {
        // `p^(2^(J+1))` divides `n`, and `2^(J+1) > cap`.
        true => cap,
        false => {
            let mut v = 0u64;
            for (i, pw) in powers.iter().enumerate().rev() {
                let (q, r) = fast::div_rem(&x, pw);
                x = match r.is_zero() {
                    true => {
                        v += 1 << i;
                        q
                    }
                    false => r,
                };
            }
            // Below `2^(J+1)`, but it may pass a cap that is not a power of 2 less 1.
            v.min(cap)
        }
    };
    drop(x);
    if v == 0 {
        return (0, n);
    }
    // The smaller powers first, so that each product is of a number by a wider one.
    let pv = powers
        .iter()
        .enumerate()
        .filter(|(i, _)| v >> i & 1 == 1)
        .fold(BigUint::one(), |acc, (_, pw)| fast::mul(&acc, pw));
    drop(powers);
    // `pv` divides `n` and is positive, so the floor is the exact quotient.
    (v, fast::div_floor(&n, &BigInt::from(pv)))
}

/// The width in bits past which [`valuation_upto`] stops dividing the whole of `n` by each
/// power on the way up and takes the remainders from the top ([`valuation_from_the_top`]).
///
/// Complexity tradeoff: the tests on the way up cost `(N / s) M(s)` time each for a power of
/// `s` bits, below the O(M(N)) of the powers and remainders from the top, so they are kept
/// while the power is narrow, where most valuations end (one factor of 5 in a decimal); but
/// the bytes a test allocates grow faster than `N` once the divisor passes the division's
/// leaf: dividing `q 3^262144` (415,550 bits, `q = 2^61 - 1`) by `3^(2^i)` allocated at most
/// 4 times the dividend's bytes for divisors up to 3,247 bits, and 22 to 53 times them from
/// 6,493 bits up, against 0.45 to 4.5 times at 51,998 bits (2026-11-23, Colab, the
/// test of `zed_alloc_count::allocated` per step), so the text of `q * 3^n` allocated 18.6
/// times the bytes at `8n` (`the_text_of_a_prime_word_times_a_power_held_as_digits_scales`).
/// From the top, each remainder is of a number below the square of its divisor, and the
/// widths halve, so the method's own memory is O(N); but the remainder by the widest power
/// and the divisions by it and by `p^v` have short quotients, which `fast::div_rem` sends to
/// num-bigint, whose Burnikel-Ziegler recursion copies the divisor's halves (plan row
/// KERNEL-bz-short-quotient), so the valuation of `q 3^v` still allocated 10.9 times the
/// bytes from `v = 2^15` to `2^18` (1,094,432 and 11,947,280), against 18.2 on the way up;
/// not proved O(N) until that row is done. 4096 bits, 64 words, is the division's leaf
/// `fast::DIV_LEAF` and lies between the two measured groups. Both ways find the same `J` and
/// `x` (the proof at [`valuation_upto`]); tested by
/// `valuations_from_the_top_agree_with_the_tests_on_the_way_up`.
const WHOLE_TEST_BITS: u64 = 64 * 64;

/// For [`valuation_upto`]: `powers` holds `P_0 .. P_k` with `P_i = p^(2^i)`, each `P_i` for
/// `i < k` dividing `n` and `P_k` of at most the bits of `n`. The powers are squared on to the
/// last `P_T` of at most the bits of `n`; then the remainders `r_T = n mod P_T` and
/// `r_j = r_(j+1) mod P_j` for `j` from `T - 1` down to `k`, each `n mod P_j` since `P_j`
/// divides `P_(j+1)`, stop at the first zero. `P_j` divides `n` exactly when `r_j` is zero,
/// and if `P_j` divides `n` so does each `P_i` below it, so the `P_j` that divide `n` are
/// those below the least `j` with `r_j` not zero, the last one found. `powers` is cut to the
/// powers that divide `n`, `P_0 .. P_J`, and the result is `x = n mod P_(J+1)`, not zero; when
/// every `r_j` is zero, `J = T` and `x` is `n`, which is below `P_(T+1)`, wider than `n`.
///
/// Cost: the squarings O(M(N)) and the remainders, each of a number below the square of its
/// divisor, O(M(N)) as the widths halve, for `n` of `N` bits.
fn valuation_from_the_top(n: &BigUint, powers: &mut Vec<BigUint>) -> BigUint {
    let k = powers.len() - 1;
    loop {
        // Unreachable: `powers` is not empty.
        let last = powers.last().expect("P_0 at least");
        let next = fast::mul(last, last);
        // `p^(2^64)` has more than 2^64 bits, so the 64 powers bound no `n` held in memory.
        if next.bits() > n.bits() || powers.len() >= 64 {
            break;
        }
        powers.push(next);
    }
    let t = powers.len() - 1;
    let mut r = fast::rem(n, &powers[t]);
    if r.is_zero() {
        return n.clone();
    }
    let mut j = t;
    while j > k {
        let below = fast::rem(&r, &powers[j - 1]);
        if below.is_zero() {
            break;
        }
        (r, j) = (below, j - 1);
    }
    // `r` is `r_j`, not zero, and `r_(j-1)` is zero or `j` is `k`: `P_0 .. P_(j-1)` divide `n`.
    powers.truncate(j);
    r
}

/// The prime powers of two numbers merged by prime, `f` combining the exponents of a prime
/// both hold, a missing exponent being zero; zero exponents are left out.
fn merge(
    a: &[(u64, BigInt)],
    b: &[(u64, BigInt)],
    f: impl Fn(&BigInt, &BigInt) -> BigInt,
) -> Vec<(u64, BigInt)> {
    zip_pows(a, b)
        .map(|(p, x, y)| (p, f(&x, &y)))
        .filter(|(_, e)| !e.is_zero())
        .collect()
}

/// The primes below 2^8, which [`Rat::text_atoms`] takes out of a value before its least root.
///
/// Magic constant: any fixed set keeps the text a function of the value (the proof at
/// [`Rat::text_atoms`] holds for every set), so this is no size switch; it sets which kept primes
/// a value held as digits is found to hold beside a coefficient that is no perfect power, as
/// `q * 3^50` is. Each group of primes whose product fits a word costs one O(n) remainder of
/// the coefficient, so the 54 primes below 2^8 cost 6; the primes below 2^16 would cost about
/// 1,640 (6,542 primes of 16 bits or fewer, 4 to a word), for the few values that hold a prime
/// between 2^8 and 2^16 to a power beside such a coefficient. Checked by
/// `tests::the_text_primes_are_the_primes_below_256_in_six_words`.
const TEXT_PRIMES: [u64; 54] = [
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
    101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193,
    197, 199, 211, 223, 227, 229, 233, 239, 241, 251,
];

/// [`TEXT_PRIMES`] in runs, in order, each run as long as its product stays below 2^64.
fn text_prime_groups() -> Vec<&'static [u64]> {
    let mut groups = Vec::new();
    let (mut start, mut product) = (0, 1u64);
    for (i, &t) in TEXT_PRIMES.iter().enumerate() {
        match product.checked_mul(t) {
            Some(x) => product = x,
            None => {
                groups.push(&TEXT_PRIMES[start..i]);
                (start, product) = (i, t);
            }
        }
    }
    groups.push(&TEXT_PRIMES[start..]);
    groups
}

/// The primes of [`TEXT_PRIMES`] that divide `c`, in order: one remainder `x = c mod P` by a
/// word for the product `P` of each group, then `t | c` exactly when `t | x`, since `t | P`.
fn text_primes_dividing(c: &BigUint) -> Vec<u64> {
    let mut hits = Vec::new();
    for run in text_prime_groups() {
        let x = rem_big_u64(c, run.iter().product());
        hits.extend(run.iter().filter(|&&t| x.is_multiple_of(t)));
    }
    hits
}

/// The atoms of `r^m` for [`Rat::text_atoms`]: none for `r = 1`; for `r < 2^44` the primes of
/// `r` (`zed_numtheory::factor`), each with `m` times its power; else `(r, m)`.
fn push_root(atoms: &mut Vec<(BigUint, BigInt)>, r: &BigUint, m: &BigInt) {
    match r.to_u64() {
        Some(1) => {}
        Some(w) if w < 1 << 44 => atoms
            .extend((factor(w).into_iter()).map(|(p, a)| (BigUint::from(p), BigInt::from(a) * m))),
        _ => atoms.push((r.clone(), m.clone())),
    }
}

/// The atoms of an integer ([`Rat::text_atoms`]) as `c*b^e*…`, without the sign: the atoms of
/// exponent 1 multiplied into the coefficient `c`, written first, so `5*3^200000` prints alike
/// whether the 5 was kept as a prime or as digits; then the bases that share an exponent
/// multiplied into one, largest exponent first; or, where shorter, those bases under the gcd
/// `g` of their exponents, `c*(prod b^(e/g))^g`, which writes `12^100000` and not
/// `2^200000*3^100000`. That base is built only when a lower bound on its digits leaves room
/// for the form to be shorter, so it costs O(the text), as does every other base here. At
/// least one atom has an exponent above 1.
fn powers_text(atoms: &[(BigUint, BigInt)]) -> String {
    let coef = (atoms.iter().filter(|(_, e)| e.is_one()))
        .fold(BigUint::one(), |c, (b, _)| fast::mul(&c, b));
    let mut by_exp: Vec<(&BigInt, &BigUint)> = (atoms.iter())
        .filter(|(_, e)| !e.is_one())
        .map(|(b, e)| (e, b))
        .collect();
    by_exp.sort_unstable_by(|a, b| b.0.cmp(a.0).then(a.1.cmp(b.1)));
    let groups: Vec<String> = by_exp
        .chunk_by(|a, b| a.0 == b.0)
        .map(|run| {
            let base = (run.iter()).fold(BigUint::one(), |b, (_, p)| fast::mul(&b, p));
            format!("{}^{}", fast::to_decimal(&base), run[0].0)
        })
        .collect();
    let head = match coef.is_one() {
        true => String::new(),
        false => format!("{}*", fast::to_decimal(&coef)),
    };
    let grouped = format!("{head}{}", groups.join("*"));
    let g = (by_exp.iter()).fold(BigInt::zero(), |g, (e, _)| g.gcd(e));
    if groups.len() < 2 || g.is_one() {
        return grouped;
    }
    let reduced: Vec<(&BigUint, BigUint)> = (by_exp.iter())
        .map(|(e, b)| (*b, (*e / &g).magnitude().clone()))
        .collect();
    // `base >= 2^low`, so its digits are at least `low log10 2 > 0.30102 low`.
    let low: BigUint = (reduced.iter()).map(|(b, e)| e * (b.bits() - 1)).sum();
    let g_text = g.to_string();
    let least = BigUint::from(head.len() + 1 + g_text.len()) + low * 30102u32 / 100_000u32;
    if least >= BigUint::from(grouped.len()) {
        return grouped;
    }
    // The base's digits are fewer than the grouped text's characters, and each `e / g` is at
    // most the base's bits, so each fits a word.
    let base = reduced.iter().fold(BigUint::one(), |acc, (b, e)| {
        let e = e.to_u64().expect("below the grouped text's length");
        fast::mul(&acc, &fast::pow(b, e))
    });
    let gcd_form = format!("{head}{}^{g_text}", fast::to_decimal(&base));
    match gcd_form.len() < grouped.len() {
        true => gcd_form,
        false => grouped,
    }
}

/// Each prime of either list with its two exponents, zero where a list lacks it.
fn zip_pows<'a>(
    a: &'a [(u64, BigInt)],
    b: &'a [(u64, BigInt)],
) -> impl Iterator<Item = (u64, BigInt, BigInt)> + 'a {
    let (mut i, mut j) = (0, 0);
    std::iter::from_fn(move || {
        let x = a.get(i);
        let y = b.get(j);
        let (p, ex, ey) = match (x, y) {
            (None, None) => return None,
            (Some((p, e)), None) => {
                i += 1;
                (*p, e.clone(), BigInt::zero())
            }
            (None, Some((q, e))) => {
                j += 1;
                (*q, BigInt::zero(), e.clone())
            }
            (Some((p, e)), Some((q, f))) => match p.cmp(q) {
                Ordering::Less => {
                    i += 1;
                    (*p, e.clone(), BigInt::zero())
                }
                Ordering::Greater => {
                    j += 1;
                    (*q, BigInt::zero(), f.clone())
                }
                Ordering::Equal => {
                    i += 1;
                    j += 1;
                    (*p, e.clone(), f.clone())
                }
            },
        };
        Some((p, ex, ey))
    })
}

/// At least the number of bits of `coef * prod p^e`, from the exponents alone: the size of
/// building it.
fn width<'a>(coef: &BigInt, pows: impl Iterator<Item = (u64, &'a BigUint)>) -> BigUint {
    let mut bits = BigUint::from(coef.bits());
    for (p, e) in pows {
        // `p^e < 2^(e * ceil(log2 p))`.
        bits += e * p.ceil_log2();
    }
    bits
}

/// Whether `p` divides `m`, read one word at a time with no quotient built, so a wide `m` costs
/// no memory.
fn divides(m: &BigUint, p: u64) -> bool {
    match u32::try_from(p) {
        Ok(q) => (m % q).is_zero(),
        Err(_) => {
            let p = u128::from(p);
            let r = m
                .iter_u64_digits()
                .rev()
                .fold(0u128, |r, d| ((r << 64) | u128::from(d)) % p);
            r == 0
        }
    }
}

/// The memory of [`rem`] by a divisor wider than a word that `fast::Divisor` divides without
/// transforms (by num-bigint, or by long division over its few nonzero words), in multiples of
/// the divisor's width. The peak heap measured on 2026-11-06 over divisors of 2^8 to 2^20
/// words, then all divided through num-bigint's products, was at most 19.0 times the
/// divisor's width with glibc's mmap threshold fixed at 128 KiB, so that freed blocks go back
/// to the system, and 26.9 at 380,000 words with glibc's default threshold, which keeps freed
/// blocks of up to 32 MiB on the heap; 24 leaves a fifth to spare over the algorithm's own
/// peak. A divisor divided by transforms asks [`POINT_WORDS`] words a point instead.
const REM_STEP: u32 = 24;

/// The memory of a division through `fast::Divisor` by a divisor whose transforms it keeps
/// (`fast::reciprocal_points`), in words a point: the divisor, its reciprocal's and its own
/// spectra and the roots, built once, and a step's dividend, estimate and cyclic products.
/// The peak heap of [`rem`] measured on 2026-11-09 over dense and all-ones divisors of
/// `2^k - 1`, `2^k` and `2^k + 1` words, `k` = 12, 16 and 18, and dividends of one, two and
/// five blocks, was at most 13.5 words a point (27 times the divisor's width at a power of
/// two, whose transforms have twice its words as points, and 50 times just above one, where
/// they have four times), with glibc's mmap threshold fixed at 128 KiB; the cases at `k` = 20
/// that ran within 60 s gave the same. 16 leaves a sixth to spare.
const POINT_WORDS: u32 = 16;

/// `a mod m` for an `m` that is not zero, read from the top of `a` with no copy of it, so its
/// memory is that of `m` whatever the size of `a`. A one-word `m` folds the words of `a` into
/// a two-word remainder; a wider `m` folds blocks of as many words as `m` has, each step
/// dividing a number of twice `m`'s length by `m`. [`TooLarge`] when the system refuses the
/// memory for it, asked as [`POINT_WORDS`] words for each point of `m`'s transforms, or as
/// [`REM_STEP`] times `m`'s width when it has none.
fn rem(a: &BigUint, m: &BigUint) -> Result<BigUint, TooLarge> {
    if let Some(w) = m.to_u64() {
        return Ok(BigUint::from(rem_big_u64(a, w)));
    }
    // Complexity tradeoff: the memory is asked as `POINT_WORDS` words a point of `m`'s
    // transforms, or `REM_STEP` times `m`'s width, measured bounds on its peak (see each), not
    // proved ones, so a remainder that needs less is refused when the free memory lies between
    // the two. Tested by `a_wide_number_modulo_a_wide_one_answers_when_its_peak_is_given` and
    // `a_dense_divisor_asks_for_its_transforms` (COMPLEXITY.md K30). A complete solution would
    // ask each allocation of the division for its own memory.
    room(
        BigUint::from(m.bits()),
        match fast::reciprocal_points(m, a.bits()) {
            Some(points) => BigUint::from(points) * (64 * POINT_WORDS),
            None => BigUint::from(m.bits()) * REM_STEP,
        },
    )?;
    Ok(fast::Divisor::new(Cow::Borrowed(m), a.bits()).rem(a))
}

/// The Euclidean remainder from `r = |a| mod |m|`: `r` itself, or `|m| - r` for a negative
/// `a` and a nonzero `r`, built after asking for `m`'s width.
fn euclid(r: BigUint, negative: bool, m: &BigUint) -> Result<Rat, TooLarge> {
    if !negative || r.is_zero() {
        return Ok(Rat::int(BigInt::from(r)));
    }
    room(BigUint::from(m.bits()), BigUint::from(m.bits()))?;
    Ok(Rat::int(BigInt::from(m - r)))
}

/// `x * y`, borrowed when one is 1; when `check`, [`TooLarge`] if the system refuses the memory
/// for the product.
fn times<'a>(x: &'a BigUint, y: &'a BigUint, check: bool) -> Result<Cow<'a, BigUint>, TooLarge> {
    if y.is_one() {
        return Ok(Cow::Borrowed(x));
    }
    if x.is_one() {
        return Ok(Cow::Borrowed(y));
    }
    if check {
        let size = BigUint::from(x.bits() + y.bits());
        room(size.clone(), size)?;
    }
    Ok(Cow::Owned(fast::mul(x, y)))
}

/// The digits of `coef * prod pows`. The power of 10 they share is written as zeros, so a
/// decimal literal's digits cost their number. [`TooLarge`] when an exponent is 2^64 or
/// more ([`built`]), or the zeros are more than an address reaches, naming their bytes; the
/// memory is not asked for here.
fn digits(coef: &BigUint, pows: Vec<(u64, BigUint)>) -> Result<String, TooLarge> {
    let exp = |q: u64| {
        pows.iter()
            .find(|(p, _)| *p == q)
            .map_or(BigUint::zero(), |(_, e)| e.clone())
    };
    let tens = exp(2).min(exp(5));
    let zeros = match coef.is_zero() {
        true => 0,
        false => (tens.to_usize()).ok_or_else(|| TooLarge {
            size: bits_of_digits(&tens),
            ask: &tens << 3u32,
        })?,
    };
    let rest: Vec<(u64, BigUint)> = pows
        .iter()
        .map(|(p, e)| match p {
            2 | 5 => (*p, e - &tens),
            _ => (*p, e.clone()),
        })
        .collect();
    let mut out = fast::to_decimal(&fast::mul(coef, built(&rest)?.magnitude()));
    out.push_str(&"0".repeat(zeros));
    Ok(out)
}

thread_local! {
    /// Whether an evaluator run on this thread watches the comparisons made through [`Ord`],
    /// which cannot return an error, for a refused build ([`Watch`]).
    static WATCHED: Cell<bool> = const { Cell::new(false) };
    /// The first comparison in the watched run whose build the system refused, and its test.
    static REFUSED: Cell<Option<(Test, TooLarge)>> = const { Cell::new(None) };
}

/// While it lives, an [`Ord`] comparison of two numbers on this thread asks the system for the
/// memory of its bounds, as [`Rat::try_cmp`] does, and records the first refusal for
/// [`refused`] instead of building. A run makes one and reads the record after each step;
/// dropping it restores the watch it replaced, so a run nested in another keeps its own.
pub(crate) struct Watch {
    was: bool,
    outer: Option<(Test, TooLarge)>,
}

/// The test of two numbers whose build the system refused, so the error names it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Test {
    /// Their order ([`Ord`]).
    Order,
    /// Their equality ([`PartialEq`]).
    Equality,
}

impl Watch {
    pub(crate) fn start() -> Watch {
        Watch {
            was: WATCHED.replace(true),
            outer: replace_refused(None),
        }
    }
}

impl Drop for Watch {
    fn drop(&mut self) {
        WATCHED.set(self.was);
        replace_refused(self.outer.take());
    }
}

/// How many threads hold a refusal in [`REFUSED`]: every write of `REFUSED` goes through
/// [`replace_refused`], which keeps the count.
// Complexity tradeoff (KERNEL-eval-step-cost): the evaluator reads the record after every
// step (`Machine::run`), and a refusal is rare. The old read took `REFUSED` on each step: a
// thread-local access, which in this crate's dylib build is a call of `__tls_get_addr` and of
// `LocalKey::take`, about 80 instructions a step and 3% of a law test (callgrind, law_04). Used:
// one relaxed load of this count, about 2 instructions, and the thread-local only when some
// thread holds a refusal. A thread that sees 0 holds none: its own increment precedes the load
// in the count's modification order, and every other thread's decrement follows that thread's
// own increment, so the count it loads is at least 1 while it holds one. Cost: an atomic
// add or subtract on a refusal and on a `Watch` that saves or restores one, all rare.
static HOLDING: AtomicUsize = AtomicUsize::new(0);

/// Sets this thread's [`REFUSED`] to `new` and returns what it held, keeping [`HOLDING`].
fn replace_refused(new: Option<(Test, TooLarge)>) -> Option<(Test, TooLarge)> {
    let holds = new.is_some();
    let old = REFUSED.replace(new);
    match (old.is_some(), holds) {
        (false, true) => HOLDING.fetch_add(1, Relaxed),
        (true, false) => HOLDING.fetch_sub(1, Relaxed),
        _ => 0,
    };
    old
}

/// The first comparison refused since the last call, under a [`Watch`], and its test.
pub(crate) fn refused() -> Option<(Test, TooLarge)> {
    if HOLDING.load(Relaxed) == 0 {
        return None;
    }
    replace_refused(None)
}

/// Records the refusal `e` of the test `t` for [`refused`], after any recorded before it.
fn record(t: Test, e: TooLarge) {
    let first = replace_refused(None).unwrap_or((t, e));
    replace_refused(Some(first));
}

impl Rat {
    /// The order of the two by value, or [`TooLarge`] when they agree in so many leading bits
    /// that the system refuses the memory to tell them apart: each doubling of the precision
    /// of the bounds (`bound`) asks for it first, as does building the two in full.
    pub fn try_cmp(&self, other: &Rat) -> Result<Ordering, TooLarge> {
        self.order(other, true)
    }

    /// The order by value; [`TooLarge`] as for [`Rat::try_cmp`]. When not `check`, the copies of
    /// the coefficients it multiplies, of the size of values already held, are not asked for;
    /// the bounds and the build of two powers ([`bound::cmp`]) always are.
    fn order(&self, other: &Rat, check: bool) -> Result<Ordering, TooLarge> {
        if self.ten.is_some() || other.ten.is_some() {
            let sign = self.num.sign().cmp(&other.num.sign());
            if sign != Ordering::Equal {
                return Ok(sign);
            }
            return match Rat::ten_pair(self, other) {
                Tens::Binary(a, b) => a.order(&b, check),
                Tens::Apart(o) => Ok(match self.is_negative() {
                    true => o.reverse(),
                    false => o,
                }),
                Tens::Convert => self.bin().order(other.bin(), check),
            };
        }
        if self.is_plain() && other.is_plain() && self.den.is_one() && other.den.is_one() {
            return Ok(self.num.cmp(&other.num));
        }
        let sign = self.num.sign().cmp(&other.num.sign());
        if sign != Ordering::Equal || self.is_zero() {
            return Ok(sign);
        }
        let o = self.magnitude_order(other, check)?;
        Ok(match self.is_negative() {
            true => o.reverse(),
            false => o,
        })
    }

    /// The order of `|self|` and `|other|`, read from the coefficients' magnitudes with no
    /// copy of either; when `check`, [`TooLarge`] as for [`Rat::try_cmp`].
    fn magnitude_order(&self, other: &Rat, check: bool) -> Result<Ordering, TooLarge> {
        if self.ten.is_some() || other.ten.is_some() {
            return self.bin().magnitude_order(other.bin(), check);
        }
        if self.is_zero() || other.is_zero() {
            return Ok(other.is_zero().cmp(&self.is_zero()));
        }
        if self.is_plain() && other.is_plain() {
            let n = times(self.num.magnitude(), other.den.magnitude(), check)?;
            let d = times(other.num.magnitude(), self.den.magnitude(), check)?;
            return Ok(n.cmp(&d));
        }
        // With both coprime to every listed prime, the two are equal exactly when their
        // coefficients and exponents are, and otherwise one side holds a prime the other lacks.
        let a = self.aligned(&other.pows, check)?;
        let b = other.aligned(&self.pows, check)?;
        let n = times(a.num.magnitude(), b.den.magnitude(), check)?;
        let d = times(b.num.magnitude(), a.den.magnitude(), check)?;
        let f = merge(&a.pows, &b.pows, |x, y| x - y);
        let pows = |sign: Sign| {
            f.iter()
                .filter(|(_, e)| e.sign() == sign)
                .map(|(p, e)| (*p, e.magnitude().clone()))
                .collect()
        };
        Ok(match f.is_empty() {
            true => n.cmp(&d),
            false => {
                let up = Product {
                    pows: pows(Sign::Plus),
                    coef: n,
                };
                let down = Product {
                    pows: pows(Sign::Minus),
                    coef: d,
                };
                // Complexity tradeoff: each round of bounds and the build ask for their memory
                // with or without a `Watch`, one allocation of the size asked, O(1) beside the
                // round itself (NUM-huge-div); see [`bound::cmp`].
                bound::cmp(&up, &down)?
            }
        })
    }

    /// An order on the normal forms, for a pair whose order by value was refused: total, and
    /// building nothing, but not the order by value.
    fn form_cmp(&self, other: &Rat) -> Ordering {
        let (a, b) = (self.bin(), other.bin());
        (&a.num, &a.den, &a.pows).cmp(&(&b.num, &b.den, &b.pows))
    }

    /// At least `|log2 |x||` for the value `x` of its coefficients and powers (its `Ten` left
    /// out): the bits of `num` and `den`, and `|e| (floor(log2 p) + 1)` for each power, since
    /// `p < 2^(floor(log2 p) + 1)`. O(the count of words of the exponents).
    fn log2_span(&self) -> BigInt {
        let mut s = BigInt::from(self.num.bits() + self.den.bits());
        for (p, e) in self.pows.iter() {
            s += e.abs() * (p.ilog2() + 1);
        }
        s
    }

    /// Two nonzero numbers of one sign, at least one holding a [`Ten`], made comparable without
    /// converting a decimal exponent where that can be done. Write each as `r * 10^t`, `t` zero
    /// for one with no `Ten`, and `d = t_a - t_b`, by digits in O(n).
    ///
    /// When `d` fits an `i64`, `10^min(t_a, t_b)` is a common positive factor, so dividing it
    /// out keeps the order and the equality: the two become `r_a * 10^d` and `r_b`, or `r_a`
    /// and `r_b * 10^-d`, in binary, built at the cost of their coefficients ([`Tens::Binary`]).
    ///
    /// When `d` does not fit, `|d| >= 2^63`, and `log2 |a| - log2 |b| = d log2 10 + log2 |r_a|
    /// - log2 |r_b|`. With `s = log2_span(r_a) + log2_span(r_b)`, `|log2 |r_a| - log2 |r_b|| <= s`,
    /// and `|d| log2 10 > 3 * 2^63 > s` when `s < 2^63`; then the difference has the sign of
    /// `d`, so `|a| > |b|` exactly when `d > 0`, and the two are not equal ([`Tens::Apart`]).
    /// Otherwise, which only a value with an exponent beyond 2^63 made by binary operations
    /// meets, both are converted ([`Tens::Convert`]).
    fn ten_pair(a: &Rat, b: &Rat) -> Tens {
        let zero = Dec::from_i128(0);
        let (ta, tb) = (a.t().unwrap_or(&zero), b.t().unwrap_or(&zero));
        let d = ta.sub(tb);
        let (ra, rb) = (a.rest(), b.rest());
        if let Some(k) = d.to_i64() {
            return match k >= 0 {
                true => Tens::Binary(ra.times_ten(&BigInt::from(k)), rb),
                false => Tens::Binary(ra, rb.times_ten(&-BigInt::from(k))),
            };
        }
        match ra.log2_span() + rb.log2_span() < BigInt::from(i64::MAX) {
            true => Tens::Apart(match d.is_negative() {
                true => Ordering::Less,
                false => Ordering::Greater,
            }),
            false => Tens::Convert,
        }
    }
}

/// How [`Rat::ten_pair`] compares two numbers, at least one holding a [`Ten`].
enum Tens {
    /// The two with their common power of ten divided out, in binary.
    Binary(Rat, Rat),
    /// Their magnitudes differ, in this order, by more than any form of their rests spans.
    Apart(Ordering),
    /// Neither applies: compare the binary forms.
    Convert,
}

/// Equal exactly when the values are. Both sides are aligned to every prime either lists, and
/// then the two are equal exactly when their coefficients and exponents are, by unique
/// factorization. Aligning copies the coefficients when a prime the other lists divides one;
/// under a `Watch`, that copy asks the system for its memory first, and a refusal is
/// recorded for `refused` and the two are compared by their normal forms, as [`Ord`] does.
impl PartialEq for Rat {
    fn eq(&self, other: &Self) -> bool {
        if self.ten.is_some() || other.ten.is_some() {
            if self.num.sign() != other.num.sign() {
                return false;
            }
            return match Rat::ten_pair(self, other) {
                Tens::Binary(a, b) => a == b,
                Tens::Apart(_) => false,
                Tens::Convert => self.bin() == other.bin(),
            };
        }
        if self.is_plain() && other.is_plain() {
            return self.num == other.num && self.den == other.den;
        }
        if self.num.sign() != other.num.sign() {
            return false;
        }
        let check = WATCHED.get();
        match (
            self.aligned(&other.pows, check),
            other.aligned(&self.pows, check),
        ) {
            (Ok(a), Ok(b)) => a.num == b.num && a.den == b.den && a.pows == b.pows,
            (Err(e), _) | (_, Err(e)) => {
                record(Test::Equality, e);
                self.form_cmp(other) == Ordering::Equal
            }
        }
    }
}

impl Eq for Rat {}

/// The order by value. A pair the system refuses the memory to order is given the order of
/// their normal forms; under a `Watch` it is recorded for `refused`, and the run stops at its
/// next step.
impl Ord for Rat {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.order(other, WATCHED.get()) {
            Ok(o) => o,
            Err(e) => {
                if WATCHED.get() {
                    record(Test::Order, e);
                }
                self.form_cmp(other)
            }
        }
    }
}

impl PartialOrd for Rat {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// The fields, as a derived `Debug` writes them, with `ten` written only when it holds a
/// decimal exponent: a value with none writes `Rat { num: 1, den: 1, pows: [] }`, the text it
/// had before `ten` was added. Checker texts hold this (the R10 tests hash D's `Info` text
/// against `expected.out`), so a `ten: None` in every value would change every recorded hash.
impl fmt::Debug for Rat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut s = f.debug_struct("Rat");
        s.field("num", &self.num)
            .field("den", &self.den)
            .field("pows", &self.pows);
        if let Some(ten) = &self.ten {
            s.field("ten", ten);
        }
        s.finish()
    }
}

/// Written as its literal: `3r`, `-1r/3r`; or, when the system refuses the memory for the
/// digits (`Rat::digits_or_powers`), as each side's powers cast, `rat(2^K)` or
/// `rat(1)/rat(3^K)`.
impl fmt::Display for Rat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.digits_or_powers() {
            Ok((num, den)) if den == "1" => write!(f, "{num}r"),
            Ok((num, den)) => write!(f, "{num}r/{den}r"),
            Err((num, den)) if den == "1" => write!(f, "rat({num})"),
            Err((num, den)) => write!(f, "rat({num})/rat({den})"),
        }
    }
}

impl Rat {
    /// The digits of the integer it is, with its sign, as `String` writes them; or, when the
    /// system refuses the memory for them, its powers as [`Rat::integer_text`] writes them,
    /// `2^1267650600228229401496703205376`. It must be an integer.
    pub fn integer_digits(&self) -> String {
        match self.digits_or_powers() {
            Ok((num, _)) | Err((num, _)) => num,
        }
    }

    /// `Ok` with the digits of the numerator, with its sign, and of the denominator; or, when
    /// the system refuses the memory for them ([`Rat::text_room`]), `Err` with each side's
    /// text by [`Rat::integer_text`], its powers where they are shorter.
    ///
    /// Complexity tradeoff (NUM-no-panic-built): a number with kept powers asks the system
    /// for the memory of its digits before they are built, one allocation asked and freed,
    /// beside the digits' O(n log^2 n) in their bits n; a plain number is written as it is,
    /// its digits about its own size. The naive method, building the digits always, aborted
    /// the process on a refusal and stopped zedc at an `expect` on an exponent of 2^64 or more,
    /// as `2^2^100` in a message. Which text a value near the memory limit gets depends on the
    /// machine's free memory; the messages that name a number print its type's text
    /// ([`Rat::integer_text`]) and not this, so they do not.
    fn digits_or_powers(&self) -> Result<(String, String), (String, String)> {
        if self.ten.is_some() {
            return self.bin().digits_or_powers();
        }
        let room = match self.is_plain() {
            true => Ok(()),
            false => self.text_room(),
        };
        let digits = room.and_then(|()| Ok((self.numer_text()?, self.denom_text()?)));
        digits.map_err(|_| {
            let side = |num: &BigInt, sign: Sign| {
                let pows = (self.pows.iter())
                    .filter(|(_, e)| e.sign() == sign)
                    .map(|(p, e)| (*p, BigInt::from(e.magnitude().clone())));
                Rat {
                    num: num.clone(),
                    den: BigInt::one(),
                    pows: pows.collect(),
                    ten: None,
                }
                .integer_text()
            };
            (side(&self.num, Sign::Plus), side(&self.den, Sign::Minus))
        })
    }
}

/// A number placed on the extended line, for comparing numbers of different kinds.
#[derive(PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Exact<'a> {
    NegInf,
    /// Borrowed from a wide number, so placing one copies none of its digits.
    Finite(Cow<'a, Rat>),
    PosInf,
    /// After every number, as the canonical NaN is after `+inf` in a float's total order.
    NaN,
}

impl Exact<'_> {
    /// The exact value of a float: every finite double is a dyadic rational.
    pub(crate) fn float(x: f64) -> Exact<'static> {
        if x.is_nan() {
            return Exact::NaN;
        }
        if x.is_infinite() {
            return if x > 0.0 {
                Exact::PosInf
            } else {
                Exact::NegInf
            };
        }
        let bits = x.to_bits();
        let exp = ((bits >> 52) & 0x7ff) as i64;
        let frac = bits & ((1 << 52) - 1);
        let (mantissa, exp) = if exp == 0 {
            (frac, -1074)
        } else {
            (frac | (1 << 52), exp - 1075)
        };
        let mut m = BigInt::from(mantissa);
        if bits >> 63 == 1 {
            m = -m;
        }
        let two = BigInt::from(2);
        let r = if exp >= 0 {
            Rat::int(m * two.pow(exp as u32))
        } else {
            // Unreachable: the denominator `2^-exp` is positive.
            Rat::new(m, two.pow((-exp) as u32)).expect("den > 0")
        };
        Exact::Finite(Cow::Owned(r))
    }
}

/// The float literal `text` at `f64`: decimal digits with an optional fraction and exponent,
/// no sign and no `_`, as the lexer keeps it (`0.1`, `1e9`, `2.5E-3`), read straight to the
/// format by [`read_float`], correctly rounded, to nearest with ties to even; it is
/// [`LiteralRounding::Infinite`] when that rounds to infinity and [`LiteralRounding::Zero`] when
/// it rounds to zero while the literal is not zero, so `0e999` is zero and `1e-400` is an error.
/// `None` when `text` is not such a decimal (`abc`, `1e`, `0x1p3`): the lexer's digits of a
/// `Float` (`Decimal '.' Decimal Exponent? | Decimal Exponent`, zedc-syntax lex/number.rs) or
/// of a decimal `Integer`, with the `_` removed, are always one, which
/// `the_lexer_s_float_and_decimal_forms_are_read` tests; a caller passing other text is told
/// so here rather than reaching a panic (LIT-f64-pub-expect).
pub fn literal_f64(text: &str) -> Option<Result<f64, LiteralRounding>> {
    Some(read_float(text, FloatFormat::F64)?.map(f64::from_bits))
}

/// The float literal `text` at `f32`, by the rule of [`literal_f64`]: `1e39` rounds to
/// infinity and `1e-46` to zero; `None` when `text` is not a decimal.
pub fn literal_f32(text: &str) -> Option<Result<f32, LiteralRounding>> {
    // The cast keeps every bit: `read_float` at `F32` gives a 32-bit encoding in a `u64`.
    Some(read_float(text, FloatFormat::F32)?.map(|bits| f32::from_bits(bits as u32)))
}

#[cfg(test)]
mod bench;

#[cfg(test)]
mod units;

#[cfg(test)]
mod tests {
    use super::*;

    /// `b^k` for a small base, kept as exponents.
    pub(super) fn power(b: u64, k: u64) -> Rat {
        Rat::int(BigInt::from(b)).pow(&BigUint::from(k)).unwrap()
    }

    /// [`sqrt_rem_uint`] against num-bigint's `sqrt`: random values of every width from 1 to
    /// 640 bits (each residue of the width mod 4, so both of its branches, and the levels of
    /// its recursion down to 128 bits), the squares `s^2`, `s^2 + 1`, `s^2 + 2s - 1` and
    /// `(s + 1)^2 - 1 = s^2 + 2s` (the remainders 0, 1, `2s - 1` and `2s`), powers of 2 and
    /// all ones, and random values of 600 and 5,000 words, past the kernel's product and
    /// division leaves.
    #[test]
    fn square_roots_agree_with_num_bigint() {
        let (mut rng, _) = crate::seed::Rng::fresh("square_roots_agree_with_num_bigint");
        let mut random = |bits: u64| {
            let words = bits.div_ceil(64) as usize;
            let mut x = BigUint::from_slice(
                &(0..2 * words)
                    .map(|_| rng.next_u64() as u32)
                    .collect::<Vec<_>>(),
            );
            x >>= 64 * words as u64 - bits;
            x.set_bit(bits - 1, true);
            x
        };
        let check = |a: &BigUint| {
            let (s, r) = sqrt_rem_uint(a);
            assert_eq!(s, a.sqrt(), "a of {} bits", a.bits());
            assert_eq!(&s * &s + &r, *a, "a of {} bits", a.bits());
        };
        check(&BigUint::ZERO);
        for bits in 1..=640u64 {
            let a = random(bits);
            check(&a);
            let s = a.sqrt();
            let sq = &s * &s;
            for x in [
                &sq + 0u32,
                &sq + 1u32,
                &sq + (&s << 1u32) - 1u32,
                &sq + (&s << 1u32),
            ] {
                check(&x);
            }
            check(&(BigUint::one() << (bits - 1)));
            check(&((BigUint::one() << bits) - 1u32));
        }
        for words in [600u64, 5000] {
            let a = random(64 * words - 7);
            check(&a);
            let s = a.sqrt();
            check(&(&s * &s));
            check(&(&s * &s + (&s << 1u32)));
        }
    }

    /// [`nth_root_rem_uint`] against num-bigint's `nth_root`: `k` from 1 to 9 at every width
    /// from 1 to 1,500 bits (for `k = 3`, the recursion starts past 210 bits and has three
    /// levels at 1,500), `k = 64` at widths to 24,000 bits (its recursion starts past 5,440),
    /// `k = 1000` at 64,000 bits (only the bit-by-bit leaf), and at `r^k - 1`, `r^k` and
    /// `r^k + 1` for the root `r` of each random value.
    #[test]
    fn kth_roots_agree_with_num_bigint() {
        let (mut rng, _) = crate::seed::Rng::fresh("kth_roots_agree_with_num_bigint");
        let mut random = |bits: u64| {
            let words = bits.div_ceil(64) as usize;
            let mut x = BigUint::from_slice(
                &(0..2 * words)
                    .map(|_| rng.next_u64() as u32)
                    .collect::<Vec<_>>(),
            );
            x >>= 64 * words as u64 - bits;
            x.set_bit(bits - 1, true);
            x
        };
        let check = |a: &BigUint, k: u32| {
            let (r, rem) = nth_root_rem_uint(a, k);
            assert_eq!(r, a.nth_root(k), "k = {k}, a of {} bits", a.bits());
            assert_eq!(
                pow_uint(&r, u64::from(k)) + &rem,
                *a,
                "k = {k}, a of {} bits",
                a.bits()
            );
        };
        let widths = (1..=9u32)
            .flat_map(|k| (1..=1500u64).step_by(7).map(move |b| (k, b)))
            .chain((5000..=24_000u64).step_by(4111).map(|b| (64, b)))
            .chain([(1000, 64_000)]);
        for (k, bits) in widths {
            check(&BigUint::ZERO, k);
            let a = random(bits);
            check(&a, k);
            let r = a.nth_root(k);
            if !r.is_zero() {
                let p = pow_uint(&r, u64::from(k));
                check(&(&p - 1u32), k);
                check(&p, k);
                check(&(p + 1u32), k);
            }
        }
    }

    #[test]
    fn the_built_widths_are_the_parts_wider_than_64_bits() {
        // CONST-too-large: the checker's bound on `x ^ k` reads the bit lengths of the parts
        // `pow` builds; a part within 64 bits is kept as exponents and has none.
        let widths = |r: &Rat| r.built_widths();
        let b: BigInt = (BigInt::one() << 64u32) + 13;
        assert_eq!(widths(&Rat::int(b.clone())), [Some(65), None]);
        assert_eq!(widths(&Rat::int(-b)), [Some(65), None]);
        assert_eq!(widths(&Rat::int(BigInt::from(u64::MAX))), [None, None]);
        assert_eq!(widths(&power(3, 40)), [None, None]);
        assert_eq!(widths(&power(2, 100)), [None, None]);
        // `n / (n + 1)` for `n = 5 * 2^100 + 1`: both parts wide and coprime.
        let n: BigInt = (BigInt::from(5) << 100u32) + 1;
        assert_eq!(
            widths(&Rat::new(n.clone(), n + 1).unwrap()),
            [Some(103), Some(103)]
        );
        // A wide numerator over a narrow denominator, and the reverse.
        let r = Rat::new((BigInt::one() << 70u32) + 1, BigInt::from(3)).unwrap();
        assert_eq!(widths(&r), [Some(71), None]);
        let r = Rat::new(BigInt::from(3), (BigInt::one() << 70u32) + 1).unwrap();
        assert_eq!(widths(&r), [None, Some(71)]);
    }

    #[test]
    fn the_least_text_is_at_most_the_digits_written() {
        // CONST-too-large-kept-powers: the checker says writing a number needs at least
        // `text_least` bytes, so it must not pass the digits written; `text_size`, which asks
        // for the memory, must not fall below them. `5^1300000` has 908660 digits, which
        // `text_size` put above 1 MiB, is
        // `bench::five_to_the_1300000_has_text_bounds_around_its_digits`.
        let wide = Rat::int((BigInt::one() << 200u32) + 7);
        for r in [
            power(2, 1),
            power(2, 100_000),
            power(3, 77_777),
            power(10, 5_000),
            power(6, 3001).mul(&wide).unwrap(),
            Rat::int(BigInt::from(7))
                .div(&power(3, 9_999))
                .unwrap()
                .unwrap(),
            power(7, 12_345).div(&power(11, 2_345)).unwrap().unwrap(),
            Rat::int(-BigInt::from(999)),
            Rat::int(BigInt::zero()),
        ] {
            text_bounds_hold(&r);
        }
    }

    /// `r.text_least()` is at most the digits `r` writes, and `r.text_size()` at least.
    pub(super) fn text_bounds_hold(r: &Rat) {
        let mut digits = r.numer_text().unwrap().trim_start_matches('-').len();
        if !r.is_integer() {
            digits += r.denom_text().unwrap().len();
        }
        let digits = BigUint::from(digits);
        assert!(r.text_least() <= digits && digits <= r.text_size().1, "{r}");
    }

    #[test]
    fn the_least_sum_is_at_most_what_the_sum_builds() {
        // CONST-too-large-kept-powers: the checker says a sum needs at least `sum_least` bits,
        // so it must not pass the widest part `sum` builds: the wider integer, the cross
        // products and the denominators' product, or the parts above the shared powers.
        let bits = |x: &BigInt| BigUint::from(x.bits());
        let builds = |a: &Rat, b: &Rat| -> BigUint {
            if a.is_plain() && b.is_plain() {
                let cross = bits(&(&a.num * &b.den)).max(bits(&(&b.num * &a.den)));
                return match a.den.is_one() && b.den.is_one() {
                    true => cross,
                    false => cross + bits(&(&a.den * &b.den)),
                };
            }
            let (a, b) = (
                a.aligned(&b.pows, false).unwrap(),
                b.aligned(&a.pows, false).unwrap(),
            );
            let (mut rest_a, mut rest_b) = (Vec::new(), Vec::new());
            for (p, ea, eb) in zip_pows(&a.pows, &b.pows) {
                let g = (&ea).min(&eb).clone();
                rest_a.push((p, (ea - &g).magnitude().clone()));
                rest_b.push((p, (eb - &g).magnitude().clone()));
            }
            let part = |n: &BigInt, rest: &[(u64, BigUint)], d: &BigInt| {
                bits(&(n * built(rest).unwrap() * d))
            };
            part(&a.num, &rest_a, &b.den).max(part(&b.num, &rest_b, &a.den))
        };
        let third = Rat::int(BigInt::one())
            .div(&Rat::int(BigInt::from(3)))
            .unwrap()
            .unwrap();
        let wide = Rat::int((BigInt::one() << 300u32) - 1);
        let pairs = [
            (Rat::int(BigInt::from(5)), Rat::int(BigInt::from(-9))),
            (third.clone(), Rat::int(BigInt::zero())),
            (third.clone(), wide.clone()),
            (power(5, 3_000), Rat::int(BigInt::one())),
            (power(5, 3_000), power(3, 2_000)),
            (power(6, 1_000).mul(&wide).unwrap(), power(6, 999)),
            (
                power(7, 999).div(&power(2, 4_000)).unwrap().unwrap(),
                third.clone(),
            ),
            (power(11, 4_321).mul(&third).unwrap(), power(13, 1_234)),
        ];
        for (a, b) in pairs {
            let least = a.sum_least(&b).unwrap();
            assert!(least <= builds(&a, &b), "{a} + {b}");
            assert_eq!(least, b.sum_least(&a).unwrap(), "{a} + {b}");
        }
        // The bound is exact here: `5^3000 + 1` builds 6966 bits, `log2 5` read to 2^-27.
        assert_eq!(
            power(5, 3_000).sum_least(&Rat::int(BigInt::one())).unwrap(),
            BigUint::from(6966u32)
        );
    }

    /// Row CONST-least-refusal-size: each refusal of a build of kept powers names a size at most
    /// the bits the build makes, which a message reads as what it needs at least, and asks at
    /// least that many. Each value is refused under a bound of 64 bits ([`fixed_room`]) and then
    /// built outside it, and its bits compared: `5^k` (its `width` overstates it by 29%),
    /// `3^k * 7^j`, `5^k / 3^j` and `-(11^k)`, writing their digits and their parts, and the
    /// sums `5^k + 1` and `5^k + 3^j`, at `k` and `j` from 1,000 to 20,000.
    #[test]
    fn a_refusal_names_at_most_the_bits_built_and_asks_at_least() {
        let check = |what: &str, refused: TooLarge, bits: u64| {
            let TooLarge { size, ask } = refused;
            assert!(size <= BigUint::from(bits), "{what}: size {size} > {bits}");
            assert!(BigUint::from(bits) <= ask, "{what}: ask {ask} < {bits}");
        };
        for (k, j) in [(1_000u64, 1_000u64), (4_321, 777), (20_000, 13_001)] {
            let quotient = power(5, k).div(&power(3, j)).unwrap().unwrap();
            let values = [
                power(5, k),
                power(3, k).mul(&power(7, j)).unwrap(),
                quotient,
                power(11, k).neg(),
            ];
            for v in &values {
                let (n, d) = v.built_parts().unwrap();
                let parts = n.bits() + d.bits();
                if v.is_integer() {
                    let refused = fixed_room(64, || v.to_integer()).unwrap_err();
                    check(&format!("to_integer {v}"), refused, n.bits());
                }
                let refused = fixed_room(64, || v.built_parts().map(|_| ())).unwrap_err();
                check(&format!("built_parts {v}"), refused, parts);
                let refused = fixed_room(64, || v.text_room()).unwrap_err();
                check(&format!("text_room {v}"), refused, parts);
            }
            for (a, b) in [
                (power(5, k), Rat::int(BigInt::one())),
                (power(5, k), power(3, j)),
            ] {
                let refused = fixed_room(64, || a.add(&b)).unwrap_err();
                // The wider cross product the sum builds, `5^k * 1` or `5^k` beside `3^j`.
                let bits = |r: &Rat| r.built_parts().unwrap().0.bits();
                let built = bits(&a).max(bits(&b));
                check(&format!("{a} + {b}"), refused, built);
            }
        }
    }

    #[test]
    fn a_power_whose_digits_no_memory_holds_is_refused_and_written_by_its_powers() {
        // NUM-no-panic-built: an exponent of 2^64 or more has more bits than any memory holds.
        // Building the number is `TooLarge`, naming its bits, where `expect` stopped before,
        // and writing it gives its powers.
        let k = BigUint::one() << 100u32;
        let big = |b: u64| Rat::int(BigInt::from(b)).pow(&k).unwrap();
        let (two, three, ten) = (big(2), big(3), big(10));
        let k_text = "1267650600228229401496703205376";
        // `2^K` has `K + 1` bits, `3^K` about `1.585 K`, named from below, with `2K` asked;
        // `10^K` is its `K` zeros, a byte each (row CONST-least-refusal-size).
        assert_eq!(
            two.numer_text(),
            Err(TooLarge {
                size: &k + 1u32,
                ask: k.clone()
            })
        );
        // `log2 3 = 1.5849625007…`, read to within 33 units of 2^-32 from below.
        let three_bits = |r: Result<String, TooLarge>| {
            let TooLarge { size, ask } = r.unwrap_err();
            assert_eq!(ask, &k << 1u32);
            assert!(&k * 1_584_962u32 / 1_000_000u32 < size, "{size}");
            assert!(size < &k * 1_584_962_501u64 / 1_000_000_000u64, "{size}");
        };
        three_bits(three.numer_text());
        assert_eq!(
            ten.numer_text(),
            Err(TooLarge {
                size: bits_of_digits(&k),
                ask: &k << 3u32
            })
        );
        assert!(two.to_integer().is_err() && three.built_parts().is_err());
        assert_eq!(two.integer_digits(), format!("2^{k_text}"));
        assert_eq!(ten.integer_digits(), format!("10^{k_text}"));
        assert_eq!(three.to_string(), format!("rat(3^{k_text})"));
        assert_eq!(three.neg().integer_text(), format!("-3^{k_text}"));
        let third = Rat::int(BigInt::from(5)).div(&three).unwrap().unwrap();
        assert_eq!(third.to_string(), format!("rat(5)/rat(3^{k_text})"));
        three_bits(third.denom_text());
        // Building it refuses with the same lower bound and asks eight times the upper one.
        let TooLarge { size, ask } = three.to_integer().unwrap_err();
        // `width`: the coefficient 1's one bit and `ceil(log2 3) = 2` per factor.
        assert_eq!(ask, ((&k << 1u32) + 1u32) << 3u32);
        assert!(size < &k * 1_584_962_501u64 / 1_000_000_000u64, "{size}");
        assert!(third.literal_text().starts_with("rat(5)/"));
        // The order is told by the bit lengths, and nothing is built.
        assert_eq!(two.try_cmp(&three), Ok(Ordering::Less));
        // A power with an exponent below 2^64 still prints its digits.
        assert_eq!(power(2, 64).integer_digits(), "18446744073709551616");
        assert_eq!(power(10, 3).to_string(), "1000r");
    }

    #[test]
    fn doubling_an_integer_preserves_its_value_and_kept_powers() {
        let two = Rat::int(BigInt::from(2));
        for text in [
            "0",
            "1",
            "-1",
            "9223372036854775807",
            "1e100000000000000000000",
            "-1e100000000000000000000",
        ] {
            let n = Rat::decimal(text).unwrap().unwrap();
            let twice = n.twice_integer();
            assert_eq!(twice, n.mul(&two).unwrap());
            assert!(twice.is_integer());
            assert_eq!(twice.integer_factors().1.len(), n.integer_factors().1.len());
        }
    }

    /// `len` random digits from `seed`.
    fn digits(seed: u64, len: usize) -> String {
        let mut rng = crate::seed::Rng::new(seed);
        (0..len)
            .map(|_| char::from(b'0' + rng.below(10) as u8))
            .collect()
    }

    /// The reading by halves gives num-bigint's value whatever the leaf: leaf 1 splits down to
    /// single digits and `LEAF_DIGITS` reads the shortest texts whole. Random texts of every
    /// length from 1 to 1,200 and some on either side of `LEAF_DIGITS * 2^i`, with leading
    /// zeros, all nines and all zeros.
    #[test]
    fn the_leaf_does_not_change_the_value() {
        let edges = (1..=3).flat_map(|i| {
            let at = LEAF_DIGITS << i;
            [at - 1, at, at + 1]
        });
        // Leaf 1 reaches products by `fast::Factor`'s spectra from `10^1024`, 54 words, above
        // the unit tests' `MUL_LEAF` of 48: these lengths join two or more pairs at that level
        // and above, with the top group carried up alone or not.
        let spectra = (12..=14).flat_map(|i| [(1 << i) - 1, 1 << i, (1 << i) + 1, 3 << (i - 1)]);
        for (seed, len) in (1..=1200)
            .chain(edges)
            .chain([5000])
            .chain(spectra)
            .enumerate()
        {
            let random = digits(seed as u64, len);
            let padded = format!("{}{}", "0".repeat(seed % 7), random);
            for text in [random, padded, "9".repeat(len), "0".repeat(len)] {
                let expected: BigUint = text.parse().expect("ASCII decimal digits");
                assert_eq!(read_digits_by(&text, 1), expected, "leaf 1, {len} digits");
                assert_eq!(
                    read_digits(&text),
                    expected,
                    "leaf {LEAF_DIGITS}, {len} digits"
                );
            }
        }
    }

    /// `read_decimal` gives num-bigint's value at every length from 1 to 2,100 digits, across
    /// one leaf, two and three: random digits, the same after leading zeros, all nines, all
    /// zeros and a power of ten; and leaves of 19 and 20 digits, one chunk and one more,
    /// split the same texts.
    #[test]
    fn a_decimal_text_reads_as_num_bigint_reads_it() {
        for len in 1..=2100 {
            let random = digits(len as u64, len);
            let padded = format!("{}{}", "0".repeat(len % 23), &random[len % 23..]);
            let power = format!("1{}", "0".repeat(len - 1));
            for text in [random, padded, "9".repeat(len), "0".repeat(len), power] {
                let expected: BigUint = text.parse().expect("ASCII decimal digits");
                let read = read_decimal(&text).expect("room for a short text");
                assert_eq!(read.as_ref(), Some(&expected), "{len} digits");
                for leaf in [19, 20] {
                    assert_eq!(read_digits_by(&text, leaf), expected, "leaf {leaf}, {len}");
                }
            }
        }
    }

    /// A text that is not ASCII decimal digits alone is no number for `read_decimal` and no
    /// decimal for `Rat::decimal` (`Rat::is_decimal`), wherever the other character is: in the part
    /// checked eight bytes at a time and in the rest, at every place of texts of 1 to 40 digits.
    /// The other characters are `_` between digits, a sign, a space, the bytes either side of the
    /// digits (`/` and `:`), a letter, and digits of other scripts (Arabic-Indic, full-width),
    /// which are several bytes each.
    #[test]
    fn a_text_with_anything_but_ascii_digits_is_not_read() {
        assert_eq!(read_decimal(""), Ok(None));
        for len in 1..=40 {
            let text = digits(len as u64 + 7, len);
            for at in 0..=len {
                for other in ["_", "+", "-", " ", "/", ":", "a", "\u{663}", "\u{FF13}"] {
                    let bad = format!("{}{other}{}", &text[..at], &text[at..]);
                    assert_eq!(read_decimal(&bad), Ok(None), "{bad:?}");
                    assert!(!Rat::is_decimal(&format!("1.{bad}")), "{bad:?}");
                }
            }
        }
    }

    /// `read_digits` is for texts already checked: a `_`, which num-bigint's `parse` skipped
    /// inside a leaf, stops it.
    #[test]
    #[should_panic(expected = "ASCII decimal digits")]
    fn read_digits_stops_at_a_mark() {
        read_digits("1_000");
    }

    #[test]
    fn a_remainder_by_a_word_is_the_big_remainder() {
        let xs = [
            BigUint::from(0u8),
            BigUint::from(5u8),
            BigUint::from(u64::MAX),
            BigUint::from(3u8).pow(1000u32),
            (BigUint::from(1u8) << 4096u32) - 1u8,
        ];
        for x in &xs {
            for m in [1, 2, 7, MERSENNE_61 - 1, MERSENNE_61, u64::MAX] {
                assert_eq!(BigUint::from(rem_big_u64(x, m)), x % m, "{x} mod {m}");
            }
        }
    }

    /// `valuation` against division by `p` one at a time, on `c p^v` for powers `v` either side
    /// of the step from the tests on the way up to those from the top (`WHOLE_TEST_BITS`, at
    /// `v` of 2048 to 4096 for `p = 3`), cofactors `c` that `p` divides and does not, and with
    /// a cap, which keeps the tests on the way up; and the bytes it allocates for `q 3^v`
    /// against those of the tests on the way up.
    #[test]
    fn valuations_from_the_top_agree_with_the_tests_on_the_way_up() {
        fn by_one(mut n: BigInt, p: u64) -> (u64, BigInt) {
            let mut v = 0;
            while (&n % p).is_zero() {
                n /= p;
                v += 1;
            }
            (v, n)
        }
        let m61 = (1u64 << 61) - 1;
        let wide: BigInt = (BigInt::one() << 300u32) + 7;
        for p in [3u64, 5, 1009, m61] {
            for v in [
                0u32, 1, 2, 1000, 2047, 2048, 2049, 4095, 4096, 5000, 8191, 8192,
            ] {
                if p == m61 && v > 1000 {
                    continue;
                }
                for c in [
                    BigInt::one(),
                    BigInt::from(-2),
                    BigInt::from(p + 1),
                    BigInt::from(p) * (p + 1),
                    wide.clone(),
                    BigInt::from(7).pow(3000u32),
                ] {
                    let n = c * BigInt::from(p).pow(v);
                    let want = by_one(n.clone(), p);
                    assert_eq!(valuation(n.clone(), p), want, "p {p}, v {v}");
                    for cap in [0u64, 1, 2047, 2048, 4097] {
                        let (k, rest) = valuation_upto(n.clone(), p, cap);
                        let k_want = want.0.min(cap);
                        assert_eq!(k, k_want, "p {p}, v {v}, cap {cap}");
                        assert_eq!(rest * BigInt::from(p).pow(k as u32), n);
                    }
                }
            }
        }
        // The step it guards, against the tests on the way up on the same input (a cap of
        // `u64::MAX - 1` keeps them): `q 3^(2^18)`, `q = 2^61 - 1`, 415,550 bits, took
        // 11,947,280 bytes from the top and 21,410,592 on the way up (2026-11-23, Colab);
        // allocation counts are deterministic. Not held to 10.5 from `v` to `8v`: from `2^15`
        // to `2^18` it grows 10.9 times (1,094,432 to 11,947,280), all of it in divisions with
        // a short quotient (`r_T = n mod P_T` 10.4 times, the division of `n` by `P_T` and by
        // `p^v` 11.9 times each), which `fast::div_rem` sends to num-bigint, whose
        // Burnikel-Ziegler recursion copies the divisor's halves however short the quotient:
        // plan row KERNEL-bz-short-quotient, which owns that fix in num/fast.rs. The whole
        // text of such a number is held to 10.5 by
        // `bench::kept_powers::the_text_of_a_prime_word_times_a_power_held_as_digits_scales`
        // (9.8 times the bytes).
        let n = BigInt::from(m61) * BigInt::from(3).pow(1u32 << 18);
        let bytes = [u64::MAX, u64::MAX - 1].map(|cap| {
            let before = zed_alloc_count::allocated();
            let (k, _) = valuation_upto(n.clone(), 3, cap);
            assert_eq!(k, 1 << 18);
            zed_alloc_count::allocated() - before
        });
        assert!(bytes[0] * 3 < bytes[1] * 2, "{bytes:?}");
    }

    #[test]
    fn the_text_primes_are_the_primes_below_256_in_six_words() {
        let primes: Vec<u64> = (2..256).filter(|&n| is_prime(n)).collect();
        assert_eq!(TEXT_PRIMES.to_vec(), primes);
        let groups = text_prime_groups();
        assert_eq!(groups.len(), 6);
        assert_eq!(groups.concat(), primes);
        // Each run's product fits a word, and would not with the first prime of the next run.
        for (i, run) in groups.iter().enumerate() {
            let product = run.iter().try_fold(1u64, |a, &t| a.checked_mul(t));
            assert!(product.is_some(), "{run:?}");
            if let (Some(p), Some(next)) = (product, groups.get(i + 1)) {
                assert!(p.checked_mul(next[0]).is_none(), "{run:?}");
            }
        }
        let c = BigUint::from(3u32 * 251 * 7);
        assert_eq!(text_primes_dividing(&c), vec![3, 7, 251]);
    }

    #[test]
    fn the_kept_form_reads_back_and_nothing_out_of_it_does() {
        // ENGINE-one: the binary form of a number writes `kept` and reads it with `from_kept`.
        let k = BigUint::one() << 100u32;
        let big = |b: u64| Rat::int(BigInt::from(b)).pow(&k).unwrap();
        let frac = big(3).div(&big(7)).unwrap().unwrap().neg();
        let lit = Rat::decimal("1.345e932").unwrap().unwrap();
        for r in [
            big(2),
            frac,
            lit,
            Rat::int(BigInt::from(-5)),
            Rat::int(BigInt::zero()),
        ] {
            let (num, den, pows) = r.kept();
            let back = Rat::from_kept(num.clone(), den.clone(), pows.to_vec()).unwrap();
            assert_eq!(back.kept(), r.kept());
        }
        let i = BigInt::from;
        let e = || i(1) << 100u32;
        let bad = [
            (i(1), i(1), vec![(5, e()), (2, e())]), // primes out of order
            (i(1), i(1), vec![(2, e()), (2, e())]), // a prime twice
            (i(1), i(1), vec![(4, e())]),           // not a prime
            (i(1), i(1), vec![(2, i(0))]),          // a zero exponent
            (i(6), i(1), vec![(3, e())]),           // a prime dividing num
            (i(1), i(9), vec![(3, e())]),           // a prime dividing den
            (i(2), i(4), vec![]),                   // not reduced
            (i(0), i(1), vec![(2, e())]),           // zero with powers
        ];
        for (num, den, pows) in bad {
            let shown = format!("{num}/{den} {pows:?}");
            assert!(Rat::from_kept(num, den, pows).is_none(), "{shown}");
        }
        assert!(Rat::from_kept(i(1), i(-1), vec![]).is_none());
        assert!(Rat::from_kept(i(1), i(0), vec![]).is_none());
    }

    /// NUM-expect-audit: every form the lexer keeps of a `Float` (`Decimal '.' Decimal
    /// Exponent? | Decimal Exponent`, `_` removed) and of a decimal `Integer` is read, so a
    /// caller that `expect`s `literal_f64` or `literal_f32` on the lexer's text never panics;
    /// each value is the one std reads.
    #[test]
    fn the_lexer_s_float_and_decimal_forms_are_read() {
        let forms = [
            "0.5",
            "1.0",
            "0.0",
            "12.5e3",
            "1e9",
            "1E-9",
            "1e+9",
            "0e0",
            "007.250E+0010",
            "1e999",
            "1e-999",
            "123",
            "0",
            "000",
            "18446744073709551616",
        ];
        for text in forms {
            let want: f64 = text.parse().unwrap();
            match literal_f64(text).expect("a decimal") {
                Ok(x) => assert_eq!(x, want, "{text}"),
                Err(LiteralRounding::Infinite) => assert!(want.is_infinite(), "{text}"),
                Err(LiteralRounding::TooLarge(e)) => panic!("{text}: {e:?}"),
                Err(LiteralRounding::Zero) => assert_eq!(want, 0.0, "{text}"),
            }
            let want: f32 = text.parse().unwrap();
            match literal_f32(text).expect("a decimal") {
                Ok(x) => assert_eq!(x, want, "{text}"),
                Err(LiteralRounding::Infinite) => assert!(want.is_infinite(), "{text}"),
                Err(LiteralRounding::Zero) => assert_eq!(want, 0.0, "{text}"),
                Err(LiteralRounding::TooLarge(e)) => panic!("{text}: {e:?}"),
            }
        }
    }

    /// LIT-f64-pub-expect: text that is not a decimal is refused with `None`, at both formats,
    /// with no panic: letters, an exponent with no digits, a point with no digits, a
    /// hexadecimal float, `_`, spaces, a suffix, two signs, and the empty text.
    #[test]
    fn text_that_is_not_a_decimal_is_refused() {
        for text in [
            "", "abc", "1e", "1e+", ".", "-", "0x1p3", "1_000.0", " 1.0", "1.0 ", "inf", "NaN",
            "1.0f64", "--1.0",
        ] {
            assert_eq!(literal_f64(text), None, "{text:?}");
            assert_eq!(literal_f32(text), None, "{text:?}");
        }
    }

    /// NUM-expect-audit: `mul_mod` and `pow_mod` stay below `2^61 - 1` at the largest inputs,
    /// where the conversions they `expect` are tightest.
    #[test]
    fn the_residues_stay_below_the_modulus_at_their_largest_inputs() {
        let m = MERSENNE_61;
        for (a, b) in [(m - 1, m - 1), (m - 1, 1), (m - 2, m - 3), (0, m - 1)] {
            let want = u128::from(a) * u128::from(b) % u128::from(m);
            assert_eq!(u128::from(m61::mul(a, b)), want, "{a} * {b}");
        }
        // `(M - 1)^2 = 1`, and an exponent of `M - 1` or a multiple of it reduces to 0.
        assert_eq!(m61::pow(m - 1, &BigUint::from(2u8)), 1);
        assert_eq!(m61::pow(3, &BigUint::from(m - 1)), 1);
        assert_eq!(m61::pow(3, &(BigUint::from(m - 1) << 70u32)), 1);
        assert_eq!(m61::pow(m, &BigUint::from(5u8)), 0);
    }
}

/// A decimal exponent kept in its digits (`Ten`, plan rows KEPT-power-form and
/// PERF-rat-literal-text-length): each operation that reads the digits gives what the binary
/// form gives, and the ones a literal's checking uses convert nothing.
#[cfg(test)]
mod ten {
    use super::*;

    fn dec(text: &str) -> Rat {
        Rat::decimal(text)
            .expect("a short literal is given its memory")
            .expect("a decimal literal")
    }

    /// The same value in binary, made from the digits.
    fn binary(x: &Rat) -> Rat {
        x.bin().clone()
    }

    /// 22 digits, beyond an `i64`, so each literal below holds a `Ten`.
    const W: &str = "1000000000000000000000";
    const W1: &str = "1000000000000000000001";

    fn values() -> Vec<Rat> {
        let texts = [
            format!("1e{W}"),
            format!("10e{W}"),
            format!("1.0e{W}"),
            format!("1e{W1}"),
            format!("1e-{W}"),
            format!("-25e{W}"),
            format!("3.5e{W}"),
            format!("-7e-{W1}"),
            format!("0.008e{W}"),
            format!("12e-{W}"),
        ];
        texts.iter().map(|t| dec(t)).collect()
    }

    #[test]
    fn a_long_written_exponent_is_kept_in_its_digits() {
        let before = dec::conversions();
        for x in values() {
            assert!(x.ten.is_some(), "{x:?}");
        }
        // 19 digits that fit an `i64` and 18 digits are binary as before.
        assert!(dec("1e9223372036854775807").ten.is_none());
        assert!(dec("1e100000000000000000").ten.is_none());
        assert!(dec("0e1000000000000000000000").is_zero());
        assert_eq!(dec::conversions(), before);
    }

    /// A value with no `Ten` writes the `Debug` text it had before `ten` was added, which the
    /// R10 tests' recorded hashes hold; one with a `Ten` writes it.
    #[test]
    fn debug_writes_ten_only_when_held() {
        assert_eq!(
            format!("{:?}", dec("1")),
            "Rat { num: 1, den: 1, pows: [] }"
        );
        let near = format!("{:?}", dec("-1.5e300"));
        assert!(!near.contains("ten"), "{near}");
        let far = format!("{:?}", dec(&format!("1e{W}")));
        assert!(
            far.contains("ten: Ten { t: Dec(1000000000000000000000)"),
            "{far}"
        );
    }

    #[test]
    fn equality_order_and_residues_agree_with_the_binary_form() {
        let xs = values();
        let bs: Vec<Rat> = xs.iter().map(binary).collect();
        for (x, bx) in xs.iter().zip(&bs) {
            assert!(bx.ten.is_none());
            assert_eq!(x.residues(), bx.residues(), "{x:?}");
            assert_eq!(x.literal_text(), bx.literal_text(), "{x:?}");
            assert_eq!(x.is_integer(), bx.is_integer(), "{x:?}");
            if x.is_integer() {
                assert_eq!(x.integer_residues(), bx.integer_residues(), "{x:?}");
                assert_eq!(x.is_even(), bx.is_even(), "{x:?}");
            }
            assert!(x == bx && bx == x, "{x:?}");
            for (y, by) in xs.iter().zip(&bs) {
                assert_eq!(x == y, bx == by, "{x:?} == {y:?}");
                assert_eq!(x.cmp(y), bx.cmp(by), "{x:?} cmp {y:?}");
                assert_eq!(x.cmp(by), bx.cmp(by), "{x:?} cmp binary {y:?}");
                let p = x.mul(y).expect("small coefficients");
                let bp = bx.mul(by).expect("small coefficients");
                assert!(p == bp, "{x:?} * {y:?}");
                assert_eq!(p.residues(), bp.residues(), "{x:?} * {y:?}");
                let q = x.div(y).expect("small").expect("nonzero");
                let bq = bx.div(by).expect("small").expect("nonzero");
                assert!(q == bq, "{x:?} / {y:?}");
                assert_eq!(q.literal_text(), bq.literal_text(), "{x:?} / {y:?}");
            }
            for k in [1u32, 2, 3, 10] {
                let p = x.pow(&BigUint::from(k)).expect("small coefficients");
                let bp = bx.pow(&BigUint::from(k)).expect("small coefficients");
                assert!(p == bp, "{x:?} ^ {k}");
                assert_eq!(p.literal_text(), bp.literal_text(), "{x:?} ^ {k}");
            }
            let r = x
                .pow_int(&Rat::int(BigInt::from(-1)))
                .expect("small")
                .expect("nonzero");
            assert!(
                r.mul(x).expect("small") == Rat::int(BigInt::one()),
                "1 / {x:?}"
            );
            assert!(x.neg() == bx.neg() && x.abs() == bx.abs(), "{x:?}");
            // Each is past either end of `f64` and `f32`.
            assert_eq!(x.to_f64(), bx.to_f64(), "{x:?}");
            assert_eq!(x.to_f32(), bx.to_f32(), "{x:?}");
            let far = if x.t().is_some_and(Dec::is_negative) {
                LiteralRounding::Zero
            } else {
                LiteralRounding::Infinite
            };
            assert_eq!(x.to_f64(), Err(far), "{x:?}");
        }
    }

    #[test]
    fn the_operations_of_a_literal_convert_nothing() {
        let (one, ten, one0, small) = (
            dec(&format!("1e{W}")),
            dec(&format!("10e{W}")),
            dec(&format!("1.0e{W}")),
            dec(&format!("1e-{W}")),
        );
        let before = dec::conversions();
        assert!(one < ten && one == one0 && small < one && one != small);
        assert_eq!(one.literal_text(), format!("1e{W}r"));
        assert_eq!(ten.literal_text(), format!("1e{W1}r"));
        assert_eq!(small.literal_text(), format!("1e-{W}r"));
        assert_eq!(one.residues(), one0.residues());
        let cube = one.pow(&BigUint::from(3u8)).expect("nothing built");
        assert_eq!(cube.literal_text(), "1e3000000000000000000000r");
        assert!(one.mul(&small).expect("small") == Rat::int(BigInt::one()));
        assert_eq!(dec::conversions(), before);
        // A product of two wide exponents needs one in binary: `(1eWr)^(1eWr)` converts, and
        // its power of 2 is refused its memory.
        assert!(one.pow_int(&one).is_err());
        assert!(dec::conversions() > before);
    }
}
