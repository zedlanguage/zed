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

use std::borrow::Cow;
use std::cell::Cell;
use std::cmp::Ordering;
use std::fmt;

use num_bigint::{BigInt, BigUint, Sign};
use num_integer::Integer;
use num_traits::{Euclid, One, Pow, Signed, ToPrimitive, Zero};

use bound::{Format, Product};

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
        let (mantissa, exp) = match text.find(['e', 'E']) {
            Some(i) => (&text[..i], Some(sign_of(&text[i + 1..]))),
            None => (text, None),
        };
        let (sign, mantissa) = sign_of(mantissa);
        let (whole, frac) = mantissa.split_once('.').unwrap_or((mantissa, ""));
        let digits = |t: &str| t.bytes().all(|b| b.is_ascii_digit());
        let read = !(whole.is_empty() && frac.is_empty()) && digits(whole) && digits(frac);
        if !read || exp.is_some_and(|(_, e)| e.is_empty() || !digits(e)) {
            return Ok(None);
        }
        // Complexity tradeoff: the memory asked for is 64 bits for each digit of the text, a
        // measured bound, not a proved one, on the copy of the mantissa's digits, their reading
        // by halves, and the division by a power of ten in lowest terms or the powers of 2 and
        // 5 moved out into exponents: the peak heap was at most 31.3 bits per digit (9.41 times
        // the `3.32 n` bits of the number) over texts of 2^12 to 2^24 digits, all nines, a long
        // fraction, a run of zeros and an exponent. So a literal needing less is refused when
        // the free memory lies between the two, and none aborts. Tested by
        // `a_long_decimal_literal_is_refused_when_memory_is_short` (COMPLEXITY.md K30). A
        // complete solution would ask each allocation of the reading for its own memory.
        let len = whole.len() + frac.len() + exp.map_or(0, |(_, e)| e.len());
        room(BigUint::from(len) << 6u32)?;
        let mantissa = match frac.is_empty() {
            true => BigInt::from_biguint(sign, read_digits(whole)),
            false => BigInt::from_biguint(sign, read_digits(&[whole, frac].concat())),
        };
        let shift = u64::try_from(frac.len()).expect("a text's length fits in 64 bits");
        Ok(Some(match exp {
            None => Rat::over_ten_to(mantissa, shift),
            Some((s, e)) => {
                let e = BigInt::from_biguint(s, read_digits(e)) - shift;
                Rat::extract(mantissa, BigInt::one(), vec![(2, e.clone()), (5, e)])
            }
        }))
    }

    /// `digits / 10^k` as a plain reduced rational. `10^k` is `2^k 5^k`, so the common factor
    /// is `2^min(v2, k) 5^min(v5, k)` for the valuations `v2` and `v5` of `digits`: a shift and
    /// divisions by powers of 5 while they divide, which is one division by 5 for most digits,
    /// where num-bigint's gcd of the two wide numbers is O(n^2).
    fn over_ten_to(digits: BigInt, k: u64) -> Rat {
        if digits.is_zero() {
            return Rat::int(digits);
        }
        let (twos, rest) = valuation(digits, 2);
        let (fives, rest) = valuation(rest, 5);
        let (t, f) = (twos.min(k), fives.min(k));
        let five = |e: u64| Pow::pow(BigUint::from(5u32), e);
        let num = (rest * BigInt::from(five(fives - f))) << (twos - t);
        let den = BigInt::from(five(k - f) << (k - t));
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
        // num-bigint's squaring and the running product by its Toom-3 multiplication): the
        // peak heap was at most 5.49 times the width over integers of 2^14 to 2^24 bits, one
        // prime, several primes, and a wide coefficient times a power. So an integer needing
        // less is refused when the free memory lies between the two, and none aborts. Tested by
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
        let mut out = self.num.clone();
        for (p, e) in self.pows.iter() {
            out *= Pow::pow(BigInt::from(*p), e.magnitude());
        }
        out
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

    /// `Ok` when the system gives the memory to write its digits ([`Rat::text_ask`]); else
    /// [`TooLarge`] naming that memory, before anything is built.
    pub fn text_room(&self) -> Result<(), TooLarge> {
        room(self.text_ask())
    }

    /// The memory writing its digits asks for, in bits.
    pub(crate) fn text_ask(&self) -> BigUint {
        let (bits, text) = self.text_size();
        // Complexity tradeoff: the memory asked for is eight times the number's width and its
        // text together, a measured bound, not a proved one, on building the number, num-
        // bigint's conversion to decimal (by divide and conquer, its powers of ten and parts
        // held at once), the zeros of a kept power of ten, and the copy of the text into the
        // value: the peak heap was at most 4.52 times that over numbers of 2^12 to 2^20 bits,
        // plain, kept powers and rationals. So a text needing less is refused when the free
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
    /// shift, and a power of another prime is built by squaring.
    pub fn built_parts(&self) -> (Cow<'_, BigUint>, Cow<'_, BigUint>) {
        fn side<'s>(coef: &'s BigInt, pows: &[(u64, BigInt)], sign: Sign) -> Cow<'s, BigUint> {
            let pows: Vec<(u64, BigUint)> = pows
                .iter()
                .filter(|(_, e)| e.sign() == sign)
                .map(|(p, e)| (*p, e.magnitude().clone()))
                .collect();
            match pows.is_empty() {
                true => Cow::Borrowed(coef.magnitude()),
                false => Cow::Owned(coef.magnitude() * built(&pows).magnitude()),
            }
        }
        (
            side(&self.num, &self.pows, Sign::Plus),
            side(&self.den, &self.pows, Sign::Minus),
        )
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
        let below = others(Sign::Minus);
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
        let m = (num * built(&pows)).to_string();
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
            // on the two cross products, their sum and the reduction by the gcd (a
            // Burnikel-Ziegler remainder of the wider by the narrower, Stein's gcd and two
            // divisions by it): the peak heap was at most 8.8 times that width over numerators
            // and denominators of 3 to 2^16 words, and the reduction alone of an exact
            // quotient at most 10.9 times (`exact_div`). So a sum needing less is refused when
            // the free memory lies between the two, and none aborts. Tested by `a_wide_
            // rational_difference_is_refused_when_memory_is_short` (COMPLEXITY.md K30). A
            // complete solution would ask each allocation of the reduction for its own memory,
            // which needs a reduction written here rather than num-bigint's.
            let n = (self.num.bits() + b.den.bits()).max(b.num.bits() + self.den.bits()) + 1;
            let d = self.den.bits() + b.den.bits();
            room(BigUint::from(n + d) << 4u32)?;
            return Ok(Rat::new(
                signed(&self.num * &b.den, &b.num * &self.den),
                &self.den * &b.den,
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
        let ra = &a.num * built(&rest_a);
        let rb = &b.num * built(&rest_b);
        Ok(Rat::build(
            signed(ra * &b.den, rb * &a.den),
            &a.den * &b.den,
            common,
        ))
    }

    /// `a * b`, or [`TooLarge`] when the system refuses the memory for the products of the
    /// coefficients and their reduction, asked before anything is built. The kept powers add
    /// their exponents and are not built.
    pub fn mul(&self, b: &Rat) -> Result<Rat, TooLarge> {
        if self.is_plain() && b.is_plain() && self.den.is_one() && b.den.is_one() {
            // Complexity tradeoff: the memory asked for a product of two integers is eight
            // times the product's width, a measured bound, not a proved one, on num-bigint's
            // multiplication (Toom-3, whose parts and their products are held at once): the
            // peak heap was at most 5.0 times the product's width over operands of 2^8 to 2^18
            // words, balanced, unbalanced and all ones. So a product needing less is refused
            // when the free memory lies between the two, and none aborts. Tested by
            // `a_product_or_quotient_of_wide_numbers_is_refused_when_memory_is_short`
            // (COMPLEXITY.md K30).
            // A complete solution would be a multiplication whose scratch is allocated once,
            // its size known by construction.
            room(BigUint::from(self.num.bits() + b.num.bits()) << 3u32)?;
            return Ok(Rat::int(&self.num * &b.num));
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
        // reduction alone of an exact quotient at most 10.9 times (`exact_div`). So a product
        // or quotient needing less is refused when the free memory lies between the two, and
        // none aborts. Tested by
        // `a_product_or_quotient_of_wide_numbers_is_refused_when_memory_is_short`
        // and `an_exact_quotient_of_a_wide_number_is_refused_when_memory_is_short`
        // (COMPLEXITY.md K30). A complete solution would ask each allocation of the reduction
        // for its own memory, which needs a reduction written here rather than num-bigint's.
        let bits = self.num.bits() + self.den.bits() + up.bits() + down.bits();
        room(BigUint::from(bits) << 4u32)?;
        Ok(Rat::build(
            &self.num * up,
            &self.den * down,
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
        // powers together, a measured bound, not a proved one, on num-bigint's power by
        // squaring (each square by Toom-3, the base and the running result held at once), the
        // numerator's power held while the denominator's is built: the peak heap was at most
        // 6.09 times the width over bases of 2^10 to 2^22 bits and exponents 2 to 31, and 3.55
        // times it for a rational with both parts wide. So a power needing less is refused when
        // the free memory lies between the two, and none aborts. Tested by
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
        let mut pows: Vec<(u64, BigInt)> =
            self.pows.iter().map(|(p, x)| (*p, x * &times)).collect();
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
                None => raised[i] = BigInt::from(Pow::pow(part, e)),
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
            // proved: the peak heap of num-bigint's `div_euclid` by a divisor of two or more
            // words (Burnikel-Ziegler division, which pads both operands to a power of two of
            // words and copies them at each level) is at most 15.0 times the dividend's width
            // over dividends of 2^8 to 2^20 words, divisors of 2 words to the dividend's
            // length and all four signs, the worst a dividend of all ones just above a power of
            // two of words. So a quotient by a wide divisor that needs less, often under eight
            // times, is refused when the free memory lies between the two, and none aborts.
            // Tested by `dividing_a_wide_number_is_refused_when_memory_is_short` and
            // `dividing_by_a_wide_divisor_answers_when_its_peak_is_given` (COMPLEXITY.md K30).
            // A complete solution would be a division whose peak is known by construction:
            // blocks of the divisor's length divided in place into a quotient allocated once.
            let a = BigUint::from(self.num.bits());
            room(match m.num.magnitude().to_u64() {
                Some(_) => a,
                None => a << 4u32,
            })?;
            return Ok(Rat::int(Euclid::div_euclid(&self.num, &m.num)));
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
    (sign * (num / &g), sign * (den / g))
}

/// The greatest common divisor of `a` and `b`, not negative.
fn gcd(a: &BigInt, b: &BigInt) -> BigInt {
    // num-bigint's gcd, Stein's algorithm, costs the product of the two widths even when one is
    // a word, so the wider is first reduced modulo the narrower by one division, linear in the
    // wider when the narrower is a word, and the gcd then runs at the narrower width.
    match a.magnitude().bits().cmp(&b.magnitude().bits()) {
        Ordering::Greater => b.gcd(&(a % b)),
        Ordering::Less if !a.is_zero() => a.gcd(&(b % a)),
        _ => a.gcd(b),
    }
}

/// The digits `read_decimal` hands to num-bigint whole. The value read does not depend on it.
const LEAF_DIGITS: usize = 512;

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
    // Complexity tradeoff: the memory asked for is 32 bits for each digit, a measured bound,
    // not a proved one, on the reading by halves (the powers of ten, the parts and their
    // products held at once): the peak heap was at most 20.0 bits per digit (6.00 times the
    // `3.32 n` bits of the number) over texts of 2^12 to 2^24 nines. So a text needing less is
    // refused when the free memory lies between the two, and none aborts. Tested by
    // `a_long_decimal_literal_is_refused_when_memory_is_short` (COMPLEXITY.md K30). A complete
    // solution would ask each allocation of the reading for its own memory.
    room(BigUint::from(digits.len()) << 5u32)?;
    Ok(Some(read_digits(digits)))
}

/// The value of a nonempty text of ASCII decimal digits, with no check of its size.
///
/// num-bigint reads a text one machine word of digits at a time into the whole number read so
/// far, O(n^2) for `n` digits. This reads the text in two parts, the low part `LEAF_DIGITS *
/// 2^i` digits long and the high part no longer, and joins them as `high * 10^(LEAF_DIGITS *
/// 2^i) + low`, with the powers `10^(LEAF_DIGITS * 2^i)` built once by squaring. The cost is
/// that of the widest product, O(n^1.47) with num-bigint's Toom-3 multiplication, and the
/// recursion is `log2(n / LEAF_DIGITS)` deep.
fn read_digits(digits: &str) -> BigUint {
    let mut tens = vec![BigUint::from(10u32).pow(LEAF_DIGITS as u32)];
    if let Some(top) = split_depth(digits.len()) {
        while tens.len() <= top {
            let next = tens.last().expect("the first power is built").pow(2u32);
            tens.push(next);
        }
    }
    read_parts(digits, &tens)
}

/// The `i` for which a text of `len` digits splits into a low part of `LEAF_DIGITS * 2^i`
/// digits and a high part of at least one and at most as many; `None` when it is read whole.
fn split_depth(len: usize) -> Option<usize> {
    (len > LEAF_DIGITS).then(|| ((len - 1) / LEAF_DIGITS).ilog2() as usize)
}

/// [`read_decimal`] of checked digits, `tens[i]` being `10^(LEAF_DIGITS * 2^i)`.
fn read_parts(digits: &str, tens: &[BigUint]) -> BigUint {
    let Some(i) = split_depth(digits.len()) else {
        return digits.parse().expect("ASCII decimal digits");
    };
    let (high, low) = digits.split_at(digits.len() - (LEAF_DIGITS << i));
    read_parts(high, tens) * &tens[i] + read_parts(low, tens)
}

/// The power of the prime `p` in `n`, and `n` without it. Powers `p, p^2, p^4, ...` divide
/// out while they can, then the same powers in decreasing order, so the cost is `log v`
/// divisions for a power `v`, not `v`.
fn valuation(n: BigInt, p: u64) -> (u64, BigInt) {
    if n.is_zero() || n.magnitude().is_one() {
        return (0, n);
    }
    if p == 2 {
        let z = n.trailing_zeros().expect("n is not zero");
        return (z, n >> z);
    }
    let mut n = n;
    let mut powers = vec![BigInt::from(p)];
    let mut v = 0u64;
    loop {
        let last = powers.last().expect("powers starts with p");
        let (q, r) = n.div_rem(last);
        if !r.is_zero() {
            break;
        }
        n = q;
        v += 1 << (powers.len() - 1);
        let next = last * last;
        powers.push(next);
    }
    for (i, pw) in powers.iter().enumerate().rev() {
        let (q, r) = n.div_rem(pw);
        if r.is_zero() {
            n = q;
            v += 1 << i;
        }
    }
    (v, n)
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

/// `prod p^e`, built. A power of 2 is a shift, done last, so `2^e` costs its `e` bits and
/// not the squarings of a multiplication.
fn built(pows: &[(u64, BigUint)]) -> BigInt {
    let mut out = BigUint::one();
    let mut twos = None;
    for (p, e) in pows {
        match (p, e.is_zero()) {
            (_, true) => {}
            (2, false) => twos = Some(e),
            _ => out *= Pow::pow(BigUint::from(*p), e),
        }
    }
    if let Some(e) = twos {
        out <<= e.to_u64().expect("a power of 2 whose bits fit in memory");
    }
    BigInt::from(out)
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

/// A number the evaluator must build, or read, for which the system refused the memory
/// (DESIGN.md sec:domains): the number is a value of the language, and building it is the
/// machine's failure, not the program's.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TooLarge {
    /// The memory asked for, in bits: a measured multiple of the size of what is built, not
    /// the size of the number.
    pub bits: BigUint,
}

impl TooLarge {
    /// The memory asked for, in bytes, rounded up.
    pub fn bytes(&self) -> BigUint {
        bytes_of(&self.bits)
    }
}

/// `bits` bits of memory in bytes, rounded up.
pub fn bytes_of(bits: &BigUint) -> BigUint {
    (bits + 7u32) >> 3u32
}

/// `Ok` when the system gives `bits` bits of memory, asked of the allocator itself and freed
/// at once, so the answer is the machine's and the evaluator sets no limit. A build that would
/// ask for more than the system gives is reported before it starts, where num-bigint would
/// abort the process.
pub(crate) fn room(bits: BigUint) -> Result<(), TooLarge> {
    match given(&bits) {
        true => Ok(()),
        false => Err(TooLarge { bits }),
    }
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
/// divisor's width: the remainder so far, the block, their shifted sum, and num-bigint's
/// Burnikel-Ziegler division of it by the divisor, which pads to a power of two of words and
/// copies at each level. The peak heap measured over divisors of 2^8 to 2^20 words, dividends
/// of one to two blocks, lengths just above and below powers of two and all-ones dividends, is
/// at most 21.3 times the divisor's width, the worst a divisor just above a power of two of
/// words; 24 leaves an eighth to spare.
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
        r = &((r << (64 * take)) + BigUint::from_slice(&block)) % m;
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
    Ok(Cow::Owned(x * y))
}

/// Whether the allocator gives `bits` bits at once, asked and freed at once.
fn given(bits: &BigUint) -> bool {
    let words = (bits + 63u32) >> 6u32;
    words
        .to_usize()
        .is_some_and(|w| Vec::<u64>::new().try_reserve_exact(w).is_ok())
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
    let mut out = (BigInt::from(coef.clone()) * built(&rest)).to_string();
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
        let (first, rest) = digits.split_at(1);
        let rest = if rest.is_empty() { "0" } else { rest };
        format!("{first}.{rest}e{exp}")
    };
    format!("{sign}{body}")
}

/// Why a float literal has no value at a binary float carrier (DESIGN.md sec:domains), or why
/// a number could not be rounded to one.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LiteralRounding {
    /// It rounds to infinity: it is beyond the largest finite float.
    Infinite,
    /// It is not zero, but it rounds to zero: it is below half the least subnormal.
    Zero,
    /// It lies so near a rounding boundary that telling which side it is on needs more
    /// memory than the system gives.
    TooLarge(TooLarge),
    /// The literal has so many digits that reading them needs more memory than the system
    /// gives.
    Unread(TooLarge),
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
