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
//! and the exponent's, not the value's 3100 bits; `2 ** 2 ** 40` is `2^(2^40)`. Products,
//! quotients and powers add and multiply exponents. Order is decided by bounds on the two
//! values (`bound`), equality by the normal form, and a sum builds only the part of the
//! operands above their common powers. Printing builds the digits, at a cost proportional to
//! them. A value with no prime powers is a plain reduced rational, whose arithmetic is what it
//! was before the powers.

mod bound;
mod factor;
mod fast;
mod room;

use std::borrow::Cow;
use std::cell::Cell;
use std::cmp::Ordering;
use std::fmt;

use num_bigint::{BigInt, BigUint, Sign};
use num_integer::Integer;
use num_traits::{One, Pow, Signed, ToPrimitive, Zero};

use bound::{Format, Product};
use fast::built;
pub use fast::{mul as mul_uint, mul_int, pow as pow_uint};
pub use room::{LiteralRounding, TooLarge, bytes_of, room};

/// An exact number `num/den * prod p^e`: `num/den` reduced with `den` positive, the primes
/// `p` distinct and in increasing order, each `e` nonzero, and `num` and `den` divisible by
/// none of the `p`. Zero has no powers.
#[derive(Clone, Debug)]
pub struct Rat {
    num: BigInt,
    den: BigInt,
    pows: Box<[(u64, BigInt)]>,
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
        }
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
        }
    }

    /// The exact value of a decimal literal's text, such as `0.1`, `2.5e-3` or `1e400000`;
    /// `Ok(None)` when it is not decimal digits with an optional sign, fraction and exponent
    /// (the exponent with an optional sign). A written exponent is kept as powers of 2 and 5, so
    /// the text's length bounds the cost. [`TooLarge`] when the system refuses the memory for
    /// reading the digits, asked before anything is built.
    pub fn decimal(text: &str) -> Result<Option<Self>, TooLarge> {
        let (mantissa, exp): (&str, Option<(Sign, &str)>) = match text.find(['e', 'E']) {
            Some(i) => (&text[..i], Some(sign_of(&text[i + 1..]))),
            None => (text, None),
        };
        let (sign, mantissa) = sign_of(mantissa);
        let (whole, frac): (&str, &str) = mantissa.split_once('.').unwrap_or((mantissa, ""));
        let digits = |t: &str| t.bytes().all(|b| b.is_ascii_digit());
        let read = !(whole.is_empty() && frac.is_empty()) && digits(whole) && digits(frac);
        if !read || exp.is_some_and(|(_, e)| e.is_empty() || !digits(e)) {
            return Ok(None);
        }
        Rat::decimal_parts(sign, whole, frac, exp).map(Some)
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
        room(BigUint::from(len) << 6u32)?;
        let mantissa = match frac.is_empty() {
            true => BigInt::from_biguint(sign, read_digits(whole)),
            false => BigInt::from_biguint(sign, read_digits(&[whole, frac].concat())),
        };
        let shift = u64::try_from(frac.len()).expect("a text's length fits in 64 bits");
        Ok(match exp {
            None => Rat::over_ten_to(mantissa, shift),
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
        (&self.num, &self.pows)
    }

    /// Whether it is an integer.
    pub fn is_integer(&self) -> bool {
        self.den.is_one() && self.pows.iter().all(|(_, e)| !e.is_negative())
    }

    /// Whether it holds no prime powers: a plain reduced rational.
    fn is_plain(&self) -> bool {
        self.pows.is_empty()
    }

    /// The integer it is, built, or [`TooLarge`] when the system refuses the memory for it.
    /// It must be an integer.
    pub fn to_integer(&self) -> Result<BigInt, TooLarge> {
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
        room(
            width(
                &self.num,
                self.pows.iter().map(|(p, e)| (*p, e.magnitude())),
            ) << 3u32,
        )?;
        Ok(self.integer_built())
    }

    /// The integer it is, built, with no check of its size. It must be an integer.
    fn integer_built(&self) -> BigInt {
        let pows: Vec<(u64, BigUint)> = self
            .pows
            .iter()
            .map(|(p, e)| (*p, e.magnitude().clone()))
            .collect();
        fast::mul_int(&self.num, &built(&pows))
    }

    /// Whether the integer it is is even: a positive power of 2, or an even coefficient. It
    /// must be an integer.
    pub fn is_even(&self) -> bool {
        self.num.is_even()
            || self
                .pows
                .first()
                .is_some_and(|(p, e)| *p == 2 && e.is_positive())
    }

    /// The integer it is, built, unless it is surely beyond 64 bits. It must be an integer.
    pub(crate) fn small_integer(&self) -> Option<BigInt> {
        // `|n| >= 2^(bits(n) - 1)` and `p^e >= 2^((bits(p) - 1) e)`, so past this bound the
        // value is beyond `2^63`; within it, it has at most about 128 bits.
        let mut low = BigInt::from(self.num.bits()) - 1;
        for (p, e) in self.pows.iter() {
            low += e * (63 - p.leading_zeros());
        }
        (low <= BigInt::from(63)).then(|| self.integer_built())
    }

    /// The numerator's digits, with its sign.
    pub fn numer_text(&self) -> String {
        let sign = if self.is_negative() { "-" } else { "" };
        let pows = self
            .pows
            .iter()
            .filter(|(_, e)| e.is_positive())
            .map(|(p, e)| (*p, e.magnitude().clone()));
        format!("{sign}{}", digits(self.num.magnitude(), pows.collect()))
    }

    /// `Ok` when the system gives the memory to write its digits (`Rat::text_ask`); else
    /// [`TooLarge`] naming that memory, before anything is built.
    pub fn text_room(&self) -> Result<(), TooLarge> {
        room(self.text_ask())
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
        // fixed at 128 KiB). So a text needing less is refused when the free
        // memory lies between the two, and none aborts. Tested by
        // `printing_a_wide_number_is_refused_when_memory_is_short` (COMPLEXITY.md K30). A
        // complete solution would write the digits by halves into memory reserved once.
        (bits + (text << 3u32)) << 3u32
    }

    /// What writing its digits builds: the number, of at most the first many bits, and its
    /// digits, numerator's and denominator's, at most the second many bytes.
    pub(crate) fn text_size(&self) -> (BigUint, BigUint) {
        let side = |coef: &BigInt, sign: Sign| {
            let pows = self.pows.iter().filter(move |(_, e)| e.sign() == sign);
            width(coef, pows.map(|(p, e)| (*p, e.magnitude())))
        };
        let bits = side(&self.num, Sign::Plus) + side(&self.den, Sign::Minus);
        // `log10(2) < 1234 / 4096`; a digit is one byte.
        let text = ((&bits * 1234u32) >> 12u32) + 2u32;
        (bits, text)
    }

    /// The denominator's digits.
    pub fn denom_text(&self) -> String {
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
        if !self.is_plain() {
            // Complexity tradeoff: the memory asked for is eight times the width of the two
            // sides together, the factor `to_integer` asks for the same build (powers by
            // squaring, the product by `num::fast::mul`), whose peak it measured at
            // 5.49 times the width; this build was not measured on its own, and a power of 2
            // here is a shift, which needs less. So a number needing less is refused when the
            // free memory lies between the two, and none aborts. Tested by
            // `l01_17_value_representation::asks::addressing_a_wide_constant_is_refused_when_memory_is_short`
            // (COMPLEXITY.md K30). A complete solution would ask each allocation of the build
            // for its own memory.
            let (bits, _) = self.text_size();
            room(bits << 3u32)?;
        }
        fn side<'s>(coef: &'s BigInt, pows: &[(u64, BigInt)], sign: Sign) -> Cow<'s, BigUint> {
            let pows: Vec<(u64, BigUint)> = pows
                .iter()
                .filter(|(_, e)| e.sign() == sign)
                .map(|(p, e)| (*p, e.magnitude().clone()))
                .collect();
            match pows.is_empty() {
                true => Cow::Borrowed(coef.magnitude()),
                false => Cow::Owned(fast::mul(coef.magnitude(), built(&pows).magnitude())),
            }
        }
        Ok((
            side(&self.num, &self.pows, Sign::Plus),
            side(&self.den, &self.pows, Sign::Minus),
        ))
    }

    /// The value's residues, the same for every form of it: whether it is negative, and
    /// `|N| mod M` and `D mod M` for the value `N/D` in lowest terms, `M = 2^61 - 1`. The
    /// form `num/den * prod p^e` is in lowest terms as it stands, since `num/den` is reduced,
    /// no listed prime divides either, and each prime lies on one side, so `N` and `D` are the
    /// same whatever powers a form lists; each `p^e` is reduced by Fermat's little theorem,
    /// so the cost is the size of the coefficients and exponents, never of the value.
    pub fn residues(&self) -> (bool, u64, u64) {
        let side = |coef: &BigInt, sign: Sign| {
            let mut r = (coef.magnitude() % MERSENNE_61)
                .to_u64()
                .expect("a residue below 2^61");
            for (p, e) in self.pows.iter().filter(|(_, e)| e.sign() == sign) {
                r = mul_mod(r, pow_mod(*p, e.magnitude()));
            }
            r
        };
        (
            self.is_negative(),
            side(&self.num, Sign::Plus),
            side(&self.den, Sign::Minus),
        )
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
        // The signed exponents of 2 and 5 in the value, and the coefficients without them.
        let (mut num, mut den) = (self.num.abs(), self.den.clone());
        let [two, five] = [2, 5].map(|p| match self.pows.binary_search_by_key(&p, |(q, _)| *q) {
            Ok(i) => self.pows[i].1.clone(),
            Err(_) => {
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
        // literal's digits; only a computed constant such as `2r ** 400000`, `1r / 2r ** 400000`
        // or `1r / 3r` has an `m` beyond its source, and printing its type then costs the
        // digits of `m`, the size of the output. A number that is not a decimal has no literal
        // and prints as the quotient `nr/dr`, which the type syntax cannot write. Nothing is
        // refused. Tested by `a_computed_power_prints_its_digits` (COMPLEXITY.md K30). A
        // complete solution would give types a written power and quotient, such as
        // `2r ** 400000` and `1r / 3r`, and print the kept powers as they are.
        if !den.is_one() || !below.is_empty() {
            return self.to_string();
        }
        let tens = (&two).min(&five).clone();
        let mut pows = others(Sign::Plus);
        pows.extend([(2, &two - &tens), (5, &five - &tens)].map(|(p, e)| {
            (
                p,
                e.to_biguint()
                    .expect("an exponent less its least is not negative"),
            )
        }));
        let m = fast::to_decimal(&fast::mul(num.magnitude(), built(&pows).magnitude()));
        match tens.is_zero() {
            true => format!("{sign}{m}r"),
            false => format!("{sign}{m}e{tens}r"),
        }
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

    /// `a + b`, or `a - b` when `minus`.
    fn sum(&self, b: &Rat, minus: bool) -> Result<Rat, TooLarge> {
        let signed = |x: BigInt, y: BigInt| match minus {
            true => x - y,
            false => x + y,
        };
        if self.is_plain() && b.is_plain() {
            if self.den.is_one() && b.den.is_one() {
                // num-bigint builds the result once, at most one bit wider than the wider
                // operand.
                room(BigUint::from(self.num.bits().max(b.num.bits()) + 1))?;
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
            room(BigUint::from(n + d) << 4u32)?;
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
        // sum's coefficient; `10 ** 10 ** 9 + 1` builds the billion digits, while
        // `10 ** 10 ** 9 + 10 ** 10 ** 9` builds nothing. This is the cost of the output in this
        // form, and no input is refused for its size; a part that does not fit in memory is
        // `TooLarge`, found before building it. Tested by
        // `kept_powers_agree_with_the_built_value`, `close_products_compare_exactly` and
        // `a_sum_too_large_to_build_is_an_error_naming_its_size` (COMPLEXITY.md K30).
        // So the cost grows with the value and not with its text: `3 ** 2 ** k + 1` builds
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
        room((x.max(y) + 1u32) << 3u32)?;
        let ra = fast::mul_int(&a.num, &built(&rest_a));
        let rb = fast::mul_int(&b.num, &built(&rest_b));
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
            room(BigUint::from(self.num.bits() + b.num.bits()) << 3u32)?;
            return Ok(Rat::int(fast::mul_int(&self.num, &b.num)));
        }
        self.scaled(&b.num, &b.den, &b.pows, |x, y| x + y)
    }

    /// `a / b`, by the rule of [`Rat::mul`]; `Ok(None)` when `b` is zero.
    pub fn div(&self, b: &Rat) -> Result<Option<Rat>, TooLarge> {
        if b.is_zero() {
            return Ok(None);
        }
        self.scaled(&b.den, &b.num, &b.pows, |x, y| x - y).map(Some)
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
        // Complexity tradeoff: the memory asked for is sixteen times the sum of the four
        // coefficients' widths, a measured bound, not a proved one, on the two products, their
        // reduction by the gcd (a Burnikel-Ziegler remainder of the wider by the narrower,
        // Stein's gcd and two divisions by it) and the primes moved out into exponents
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
        room(BigUint::from(bits) << 4u32)?;
        Ok(Rat::build(
            fast::mul_int(&self.num, up),
            fast::mul_int(&self.den, down),
            merge(&self.pows, pows, f),
        ))
    }

    /// `-a`.
    pub fn neg(&self) -> Rat {
        Rat {
            num: -&self.num,
            den: self.den.clone(),
            pows: self.pows.clone(),
        }
    }

    /// `-a`, or [`TooLarge`] when the system refuses the memory for its coefficients: negating
    /// copies them.
    pub fn try_neg(&self) -> Result<Rat, TooLarge> {
        room(BigUint::from(self.num.bits() + self.den.bits()))?;
        Ok(self.neg())
    }

    /// A copy, or [`TooLarge`] when the system refuses the memory for its coefficients.
    fn try_copy(&self) -> Result<Rat, TooLarge> {
        room(BigUint::from(self.num.bits() + self.den.bits()))?;
        Ok(self.clone())
    }

    /// `|a|`.
    pub fn abs(&self) -> Rat {
        match self.is_negative() {
            true => self.neg(),
            false => self.clone(),
        }
    }

    /// `a^e`. Powers of primes multiply their exponents, and a numerator or denominator that
    /// fits in 64 bits is factored into primes, so `10 ** 10 ** 9` is `2^(10^9) * 5^(10^9)`.
    /// [`TooLarge`] when a wider part's power is built and the system refuses the memory.
    pub fn pow(&self, e: &BigUint) -> Result<Rat, TooLarge> {
        if e.is_zero() {
            return Ok(Rat::int(BigInt::one()));
        }
        if self.is_zero() {
            return Ok(self.clone());
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
        let wide: u64 = parts
            .iter()
            .filter(|part| part.to_u64().is_none())
            .map(|part| part.bits())
            .sum();
        if wide > 0 {
            room((BigUint::from(wide) * e) << 3u32)?;
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
                    for (p, k) in factor::factor(w) {
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
                // the bases made pairwise coprime by Bernstein's coprime-base algorithm.
                None => {
                    let e = e.to_u64().expect("an exponent whose power fits in memory");
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
        })
    }

    /// The Euclidean remainder of two integers, in `0 ..< |m|`; `m` is not zero. An exact
    /// division gives `0` and a dividend in `0 ..< |m|` gives itself, without building either;
    /// otherwise a power of a prime is reduced by modular exponentiation, so `10 ** 10 ** 9 mod
    /// 7` builds no large number. [`TooLarge`] when the divisor is built, or the two are
    /// compared to more bits than the system gives memory for.
    pub fn rem_euclid(&self, m: &Rat) -> Result<Rat, TooLarge> {
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
        // Complexity tradeoff: a remainder that is neither `0` nor the dividend itself is
        // found by building the divisor `m`, at a cost proportional to `m`'s size, which bounds
        // the remainder's; `3 ** 10 ** 9 mod 2 ** 10 ** 9` builds `2^(10^9)`, while
        // `10 ** 10 ** 12 mod 2 ** 10 ** 12` and `5 mod 2 ** 10 ** 12` build nothing. An input
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
            // `p^e mod m` (num-bigint's Montgomery power for an odd `m`, square and multiply
            // for an even one), their product and its division by `m`, and the peak heap was
            // at most 25.2 times `m`'s width over divisors of 2^8 to 2^13 words, odd and even.
            // So a kept-power dividend modulo a wide divisor whose steps need less is
            // `TooLarge` when the free memory lies between the two, and none aborts. Tested by
            // `a_kept_power_modulo_a_wide_number_is_refused_below_its_ask` (COMPLEXITY.md K30).
            // A complete solution would ask each allocation of the power and the division for
            // its own memory, which needs a modular power written here rather than
            // num-bigint's.
            room(BigUint::from(m.bits()) << 5u32)?;
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
        if self.is_plain() && m.is_plain() {
            // Complexity tradeoff: the memory asked for is the quotient's width for a divisor
            // of one word, which num-bigint divides into a single copy of the dividend, and
            // sixteen times the dividend's width for a wider divisor. Sixteen is measured, not
            // proved: the peak heap of `num::fast::div_euclid` by a divisor of two or more
            // words (Newton's reciprocal and two products, or long division over a sparse
            // divisor's nonzero words) was at most 7.94 times the dividend's width over
            // dividends of 2^8 to 2^20 words, divisors of 2 words to the dividend's length and
            // all four signs (2026-11-06, glibc's mmap threshold fixed at 128 KiB); sixteen
            // keeps the earlier ask, which tests depend on. So a quotient by a wide divisor that
            // needs less is refused when the free memory lies between the two, and none aborts.
            // Tested by `dividing_a_wide_number_is_refused_when_memory_is_short` and
            // `dividing_by_a_wide_divisor_answers_when_its_peak_is_given` (COMPLEXITY.md K30).
            // A complete solution would be a division whose peak is known by construction:
            // blocks of the divisor's length divided in place into a quotient allocated once.
            let a = BigUint::from(self.num.bits());
            room(match m.num.magnitude().to_u64() {
                Some(_) => a,
                None => a << 4u32,
            })?;
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
        // size, near the quotient's; `3 ** 10 ** 9 div 2 ** 10 ** 9` builds both, while
        // `10 ** 10 ** 12 div 2 ** 10 ** 12` builds nothing. An input is refused only when the
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
        Ok(self.div(m)?.expect("the divisor is not zero"))
    }

    /// The same number, with each prime of `others` moved out of `num` and `den` too. When one
    /// of them divides a coefficient, the coefficients are copied and divided; when `check`,
    /// [`TooLarge`] first if the system refuses the memory for that.
    fn aligned(&self, others: &[(u64, BigInt)], check: bool) -> Result<Cow<'_, Rat>, TooLarge> {
        let listed = |p: u64| self.pows.binary_search_by_key(&p, |(q, _)| *q).is_ok();
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
            room(BigUint::from(self.num.bits() + self.den.bits()) << 4u32)?;
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

/// The Mersenne prime `2^61 - 1`, the modulus of [`Rat::residues`].
const MERSENNE_61: u64 = (1 << 61) - 1;

/// `a * b mod 2^61 - 1`, for `a` and `b` below it.
fn mul_mod(a: u64, b: u64) -> u64 {
    let x = u128::from(a) * u128::from(b);
    let m = u128::from(MERSENNE_61);
    // `2^61 = 1 (mod M)`, so the high part adds to the low part; one subtraction ends it.
    let r = (x & m) + (x >> 61);
    let r = if r >= m { r - m } else { r };
    u64::try_from(r).expect("a residue below 2^61")
}

/// `p^e mod 2^61 - 1`, by squaring after reducing `e` modulo `M - 1` (Fermat), so the cost
/// is the length of `e` and 61 squarings. `p` is prime, so `p mod M` is zero only for
/// `p = M`, whose powers are 0 for `e > 0`.
fn pow_mod(p: u64, e: &BigUint) -> u64 {
    let base = p % MERSENNE_61;
    if base == 0 {
        return u64::from(e.is_zero());
    }
    let mut k = (e % (MERSENNE_61 - 1))
        .to_u64()
        .expect("an exponent below 2^61");
    let (mut b, mut r) = (base, 1);
    while k > 0 {
        if k & 1 == 1 {
            r = mul_mod(r, b);
        }
        b = mul_mod(b, b);
        k >>= 1;
    }
    r
}

/// `num / den` reduced, with `den` positive.
fn reduce(num: BigInt, den: BigInt) -> (BigInt, BigInt) {
    let g = gcd(&num, &den);
    let sign = if den.is_negative() { -1 } else { 1 };
    (
        sign * fast::exact_quotient(&num, &g),
        sign * fast::exact_quotient(&den, &g),
    )
}

/// The greatest common divisor of `a` and `b`, not negative.
fn gcd(a: &BigInt, b: &BigInt) -> BigInt {
    // The half gcd (`fast::gcd`) costs O(M(n) log n) in the wider width even when the other is
    // a word, so the wider is first reduced modulo the narrower by one division, O(M(n)) and
    // linear when the narrower is a word, and the gcd then runs at the narrower width.
    let (a, b) = (a.magnitude(), b.magnitude());
    let g = match a.bits().cmp(&b.bits()) {
        Ordering::Greater => fast::gcd(b, &fast::div_rem(a, b).1),
        Ordering::Less if !a.is_zero() => fast::gcd(a, &fast::div_rem(b, a).1),
        _ => fast::gcd(a, b),
    };
    BigInt::from(g)
}

/// The digits `read_decimal` hands to num-bigint whole. The value read does not depend on it.
//
// Complexity tradeoff: a timed crossover of two algorithms with identical results, nothing
// given up. A text of at most `LEAF_DIGITS` digits is read by num-bigint's `parse`, O(n^2), one
// word of digits at a time; a longer one is split by halves (`read_parts`), O(n log^2 n). Both
// give the same number for every text (test `num::tests::the_leaf_does_not_change_the_value`,
// leaf 1 against `LEAF_DIGITS` and against num-bigint; COMPLEXITY.md K41). Measured on
// 2026-11-07 (item KERNEL-leaf-digits, not committed): `read_digits` with each leaf on random
// texts, the test build (opt-level 2), the fewest instructions of 2 to 20 runs, load5 28 to 36:
//
//   digits      leaf 32     64     128     256     512    1024    2048
//   700          64,526  50,065  43,054  38,847  36,664  30,667  30,667
//   1,000        94,516  73,183  62,109  56,689  52,879  47,480  47,480
//   1,500       150,409 120,772 103,724  95,565  91,004  90,112  81,143
//   3,000       351,391 291,238 258,980 242,832 233,841 232,414 236,825
//   6,000       879,929 759,963 694,248 663,420 645,131 642,638 657,250
//   10^4 (M)      1.906   1.705   1.597   1.544   1.514   1.511   1.536
//   10^5 (M)     66.877  64.892  63.801  63.276  62.979  62.959  63.215
//   10^6 (M)     1,314.2 1,294.4 1,283.4 1,278.2 1,275.3 1,275.1 1,277.6
//
// 1024 has the fewest at every size but 700 and 1,000 (tied with 2048, which reads them
// whole) and 1,500 (2048, 10% fewer); from 3,000 digits 2048 costs 0.2% to 2.3% more, as the
// O(n^2) leaves grow. Processor time agreed within its noise at this load (10^6: 153 to 157
// ms for leaves 128 to 2048). The peak heap is the same at 512 and 1024, 23.6 bits per digit
// on 2^16 to 2^22 nines, within the 48 that `read_decimal` asks for. To be measured again at
// the Zed port, where both sides of the crossover change.
const LEAF_DIGITS: usize = 1024;

/// The sign of a text and the rest of it after an optional `-` or `+`.
pub(crate) fn sign_of(text: &str) -> (Sign, &str) {
    match (text.strip_prefix('-'), text.strip_prefix('+')) {
        (Some(rest), _) => (Sign::Minus, rest),
        (None, Some(rest)) => (Sign::Plus, rest),
        (None, None) => (Sign::Plus, text),
    }
}

/// The value of a text of ASCII decimal digits; `Ok(None)` when it is empty or holds anything
/// else, and [`TooLarge`] when the system refuses the memory for reading it, asked before
/// anything is built.
pub fn read_decimal(digits: &str) -> Result<Option<BigUint>, TooLarge> {
    if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
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
    room(BigUint::from(digits.len()) * 48u32)?;
    Ok(Some(read_digits(digits)))
}

/// The value of a nonempty text of ASCII decimal digits, with no check of its size.
///
/// num-bigint reads a text one machine word of digits at a time into the whole number read so
/// far, O(n^2) for `n` digits. This reads the text in two parts, the low part `LEAF_DIGITS *
/// 2^i` digits long and the high part no longer, and joins them as `high * 10^(LEAF_DIGITS *
/// 2^i) + low`, with the powers `10^(LEAF_DIGITS * 2^i)` built once by squaring. Each level
/// of the recursion costs about one widest product, O(M(n)) = O(n log n) with `fast::mul`,
/// and the recursion is `log2(n / LEAF_DIGITS)` deep, so the whole is O(n log^2 n). A text of
/// at most `LEAF_DIGITS` digits is read whole, with no power of ten built.
///
/// # Panics
///
/// When `digits` is empty or holds anything but ASCII decimal digits.
pub fn read_digits(digits: &str) -> BigUint {
    read_digits_by(digits, LEAF_DIGITS)
}

/// [`read_digits`] with texts of at most `leaf` digits read whole; `leaf` is at least 1.
fn read_digits_by(digits: &str, leaf: usize) -> BigUint {
    let Some(top) = split_depth(digits.len(), leaf) else {
        return digits.parse().expect("ASCII decimal digits");
    };
    let mut tens = vec![BigUint::from(10u32).pow(leaf as u32)];
    while tens.len() <= top {
        let last = tens.last().expect("the first power is built");
        let next = fast::mul(last, last);
        tens.push(next);
    }
    read_parts(digits, &tens, leaf)
}

/// The `i` for which a text of `len` digits splits into a low part of `leaf * 2^i` digits and
/// a high part of at least one and at most as many; `None` when it is read whole.
fn split_depth(len: usize, leaf: usize) -> Option<usize> {
    (len > leaf).then(|| ((len - 1) / leaf).ilog2() as usize)
}

/// [`read_decimal`] of checked digits, `tens[i]` being `10^(leaf * 2^i)`.
fn read_parts(digits: &str, tens: &[BigUint], leaf: usize) -> BigUint {
    let Some(i) = split_depth(digits.len(), leaf) else {
        return digits.parse().expect("ASCII decimal digits");
    };
    let (high, low) = digits.split_at(digits.len() - (leaf << i));
    fast::mul(&read_parts(high, tens, leaf), &tens[i]) + read_parts(low, tens, leaf)
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
fn valuation_upto(n: BigInt, p: u64, cap: u64) -> (u64, BigInt) {
    if n.is_zero() || cap == 0 {
        return (0, n);
    }
    if p == 2 {
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
        let x = match next.bits() > n.bits() {
            true => n.magnitude().clone(),
            false => fast::div_rem(n.magnitude(), &next).1,
        };
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
    (v, fast::exact_quotient(&n, &BigInt::from(pv)))
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
        bits += e * (p.ilog2() + u32::from(!p.is_power_of_two()));
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

/// The memory of one block step of [`rem`] by a divisor wider than a word, in multiples of the
/// divisor's width: the remainder so far, the block, their shifted sum, and its division by
/// the divisor through `fast::Divisor` (the divisor's reciprocal, built once, and two
/// transform products a step). The peak heap measured on 2026-11-06 over divisors of 2^8 to
/// 2^20 words, dividends of one to two blocks, lengths just above and below powers of two and
/// all-ones dividends, is at most 19.0 times the divisor's width (18.3 building the
/// reciprocal, 14.9 a step) with glibc's mmap threshold fixed at 128 KiB, so that freed
/// blocks go back to the system. With glibc's default threshold, which keeps freed blocks of
/// up to 32 MiB on the heap, the measured peak reaches 26.9 at 380,000 words, a constant
/// number of bytes retained rather than a share of the width; 24 leaves a fifth to spare over
/// the algorithm's own peak.
const REM_STEP: u32 = 24;

/// `a mod m` for an `m` that is not zero, read from the top of `a` with no copy of it, so its
/// memory is that of `m` whatever the size of `a`. A one-word `m` folds the words of `a` into
/// a two-word remainder; a wider `m` folds blocks of as many words as `m` has, each step
/// dividing a number of twice `m`'s length by `m`. [`TooLarge`] when the system refuses the
/// memory for a step, asked as [`REM_STEP`] times `m`'s width.
fn rem(a: &BigUint, m: &BigUint) -> Result<BigUint, TooLarge> {
    if let Some(w) = m.to_u64() {
        let w = u128::from(w);
        let r = a
            .iter_u64_digits()
            .rev()
            .fold(0u128, |r, d| ((r << 64) | u128::from(d)) % w);
        return Ok(BigUint::from(r));
    }
    // Complexity tradeoff: a step's memory is asked as `REM_STEP` times `m`'s width, a measured
    // bound on its peak (see `REM_STEP`), not a proved one, so a remainder whose step needs
    // less is refused when the free memory lies between the two. Tested by `a_wide_number_
    // modulo_a_wide_one_answers_when_its_peak_is_given` (COMPLEXITY.md K30). A complete
    // solution would divide each block in place into a quotient allocated once, whose peak is
    // known by construction.
    room(BigUint::from(m.bits()) * REM_STEP)?;
    let len = m.iter_u64_digits().len();
    // Each step divides a number below `m 2^(64 len)` by `m`, as `fast::Divisor` allows.
    let divisor = fast::Divisor::new(Cow::Borrowed(m));
    let mut words = a.iter_u64_digits().rev();
    let mut left = words.len();
    let mut take = match left % len {
        0 => len,
        k => k,
    };
    let mut block: Vec<u32> = Vec::with_capacity(2 * len);
    let mut r = BigUint::zero();
    while left > 0 {
        block.clear();
        for d in words.by_ref().take(take) {
            // Highest word first, so reversing the block gives the low half-word first.
            block.extend([(d >> 32) as u32, d as u32]);
        }
        block.reverse();
        r = divisor
            .div_rem(&((r << (64 * take)) + BigUint::from_slice(&block)))
            .1;
        left -= take;
        take = len;
    }
    Ok(r)
}

/// The Euclidean remainder from `r = |a| mod |m|`: `r` itself, or `|m| - r` for a negative
/// `a` and a nonzero `r`, built after asking for `m`'s width.
fn euclid(r: BigUint, negative: bool, m: &BigUint) -> Result<Rat, TooLarge> {
    if !negative || r.is_zero() {
        return Ok(Rat::int(BigInt::from(r)));
    }
    room(BigUint::from(m.bits()))?;
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
        room(BigUint::from(x.bits() + y.bits()))?;
    }
    Ok(Cow::Owned(fast::mul(x, y)))
}

/// The digits of `coef * prod pows`. The power of 10 they share is written as zeros, so a
/// decimal literal's digits cost their number.
fn digits(coef: &BigUint, pows: Vec<(u64, BigUint)>) -> String {
    let exp = |q: u64| {
        pows.iter()
            .find(|(p, _)| *p == q)
            .map_or(BigUint::zero(), |(_, e)| e.clone())
    };
    let tens = exp(2).min(exp(5));
    let rest: Vec<(u64, BigUint)> = pows
        .iter()
        .map(|(p, e)| match p {
            2 | 5 => (*p, e - &tens),
            _ => (*p, e.clone()),
        })
        .collect();
    let mut out = fast::to_decimal(&fast::mul(coef, built(&rest).magnitude()));
    if !coef.is_zero() {
        let zeros = tens
            .to_usize()
            .expect("a number whose digits fit in memory");
        out.push_str(&"0".repeat(zeros));
    }
    out
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
            outer: REFUSED.take(),
        }
    }
}

impl Drop for Watch {
    fn drop(&mut self) {
        WATCHED.set(self.was);
        REFUSED.set(self.outer.take());
    }
}

/// The first comparison refused since the last call, under a [`Watch`], and its test.
pub(crate) fn refused() -> Option<(Test, TooLarge)> {
    REFUSED.take()
}

/// Records the refusal `e` of the test `t` for [`refused`], after any recorded before it.
fn record(t: Test, e: TooLarge) {
    let first = REFUSED.take().unwrap_or((t, e));
    REFUSED.set(Some(first));
}

impl Rat {
    /// The order of the two by value, or [`TooLarge`] when they agree in so many leading bits
    /// that the system refuses the memory to tell them apart: each doubling of the precision
    /// of the bounds (`bound`) asks for it first, as does building the two in full.
    pub fn try_cmp(&self, other: &Rat) -> Result<Ordering, TooLarge> {
        self.order(other, true)
    }

    /// The order by value; when `check`, [`TooLarge`] as for [`Rat::try_cmp`], and otherwise
    /// the build is not checked.
    fn order(&self, other: &Rat, check: bool) -> Result<Ordering, TooLarge> {
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
                bound::cmp(&up, &down, check)?
            }
        })
    }

    /// An order on the normal forms, for a pair whose order by value was refused: total, and
    /// building nothing, but not the order by value.
    fn form_cmp(&self, other: &Rat) -> Ordering {
        (&self.num, &self.den, &self.pows).cmp(&(&other.num, &other.den, &other.pows))
    }
}

/// Equal exactly when the values are. Both sides are aligned to every prime either lists, and
/// then the two are equal exactly when their coefficients and exponents are, by unique
/// factorization. Aligning copies the coefficients when a prime the other lists divides one;
/// under a `Watch`, that copy asks the system for its memory first, and a refusal is
/// recorded for `refused` and the two are compared by their normal forms, as [`Ord`] does.
impl PartialEq for Rat {
    fn eq(&self, other: &Self) -> bool {
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

/// The order by value. Under a `Watch`, a pair the system refuses the memory to order is
/// recorded for `refused` and given the order of their normal forms, and the run stops at
/// its next step; with no watch, the build is not checked.
impl Ord for Rat {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.order(other, WATCHED.get()) {
            Ok(o) => o,
            Err(e) => {
                record(Test::Order, e);
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

/// Written as its literal: `3r`, `-1r/3r`.
impl fmt::Display for Rat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let den = self.denom_text();
        if den == "1" {
            write!(f, "{}r", self.numer_text())
        } else {
            write!(f, "{}r/{den}r", self.numer_text())
        }
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
            Rat::new(m, two.pow((-exp) as u32)).expect("den > 0")
        };
        Exact::Finite(Cow::Owned(r))
    }
}

/// How `String` writes a float (DESIGN.md sec:reduction): the shortest digits that read back
/// to it, in fixed notation when the decimal exponent is in -6..<21 and with an exponent
/// otherwise, so `f64(String(x))` is `x`, bit for bit.
pub fn show_f64(x: f64) -> String {
    if x.is_nan() {
        return "nan".into();
    }
    if x.is_infinite() {
        return if x > 0.0 { "inf" } else { "-inf" }.into();
    }
    // `{:e}` gives the shortest digits: `-1.25e-7`, `5e0`.
    let sci = format!("{x:e}");
    let (mantissa, exp) = sci.split_once('e').expect("an exponent");
    let exp: i32 = exp.parse().expect("an integer exponent");
    let (sign, mantissa) = match mantissa.strip_prefix('-') {
        Some(m) => ("-", m),
        None => ("", mantissa),
    };
    let digits: String = mantissa.chars().filter(|c| *c != '.').collect();
    let n = digits.len() as i32;
    let body = if (-6..21).contains(&exp) {
        if exp < 0 {
            format!("0.{}{digits}", "0".repeat((-exp - 1) as usize))
        } else if n <= exp + 1 {
            format!("{digits}{}.0", "0".repeat((exp + 1 - n) as usize))
        } else {
            let (whole, frac) = digits.split_at(exp as usize + 1);
            format!("{whole}.{frac}")
        }
    } else {
        let (first, rest): (&str, &str) = digits.split_at(1);
        let rest = if rest.is_empty() { "0" } else { rest };
        format!("{first}.{rest}e{exp}")
    };
    format!("{sign}{body}")
}

/// The float literal `text` at `f64`: decimal digits with an optional fraction and exponent,
/// no sign and no `_`, as the lexer keeps it (`0.1`, `1e9`, `2.5E-3`). It is the exact
/// decimal [`Rat::decimal`] projected by [`Rat::to_f64`], correctly rounded, to nearest with
/// ties to even; it is an error when that rounds to infinity, or to zero while the literal is
/// not zero, so `0e999` is zero and `1e-400` is an error.
pub fn literal_f64(text: &str) -> Result<f64, LiteralRounding> {
    literal(text)?.to_f64()
}

/// The float literal `text` at `f32`, by the rule of [`literal_f64`]: `1e39` rounds to
/// infinity and `1e-46` to zero.
pub fn literal_f32(text: &str) -> Result<f32, LiteralRounding> {
    literal(text)?.to_f32()
}

/// The exact value of the float literal `text`.
fn literal(text: &str) -> Result<Rat, LiteralRounding> {
    Ok(Rat::decimal(text)
        .map_err(LiteralRounding::Unread)?
        .expect("the lexer's float text is a decimal"))
}

/// The float equal to `r`, when there is one; [`TooLarge`] when rounding `r` was refused the
/// memory it needs.
pub(crate) fn exact_f64(r: &Rat) -> Result<Option<f64>, TooLarge> {
    // A double is m * 2^k, so its denominator is a power of two.
    let den = r.den.magnitude();
    let dyadic = den.trailing_zeros().unwrap_or(0) + 1 == den.bits()
        && r.pows.iter().all(|(p, e)| *p == 2 || e.is_positive());
    if !dyadic {
        return Ok(None);
    }
    let x = match r.to_f64() {
        Ok(x) => x,
        Err(LiteralRounding::TooLarge(e) | LiteralRounding::Unread(e)) => return Err(e),
        Err(LiteralRounding::Infinite | LiteralRounding::Zero) => return Ok(None),
    };
    Ok(match Exact::float(x) {
        Exact::Finite(f) => (*f == *r).then_some(x),
        Exact::NegInf | Exact::PosInf | Exact::NaN => None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `len` digits from splitmix64 started at `seed`.
    fn digits(seed: u64, len: usize) -> String {
        let mut x = seed;
        (0..len)
            .map(|_| {
                x = x.wrapping_add(0x9e37_79b9_7f4a_7c15);
                let mut z = x;
                z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
                z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
                char::from(b'0' + ((z ^ (z >> 31)) % 10) as u8)
            })
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
        for (seed, len) in (1..=1200).chain(edges).chain([5000]).enumerate() {
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
}
