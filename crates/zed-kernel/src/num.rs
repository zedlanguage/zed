//! Exact numbers (step L1.17): unbounded integers, rationals, and the order of numbers by
//! value across `int`, `rat` and floats (DESIGN.md sec:keys, the natural order).
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
//! values ([`bound`]), equality by the normal form, and a sum builds only the part of the
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

    /// `2^s`.
    fn two_pow(s: BigInt) -> Rat {
        if s.is_zero() {
            return Rat::int(BigInt::one());
        }
        Rat {
            num: BigInt::one(),
            den: BigInt::one(),
            pows: Box::new([(2, s)]),
        }
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
    /// `None` when it is not decimal digits with an optional `-`, fraction and exponent. A
    /// written exponent is kept as powers of 2 and 5, so the text's length bounds the cost.
    pub fn decimal(text: &str) -> Option<Self> {
        let (mantissa, exp) = match text.find(['e', 'E']) {
            Some(i) => (&text[..i], Some(text[i + 1..].parse::<BigInt>().ok()?)),
            None => (text, None),
        };
        let (whole, frac) = mantissa.split_once('.').unwrap_or((mantissa, ""));
        let digits: BigInt = format!("{whole}{frac}").parse().ok()?;
        match exp {
            None => {
                let scale = BigInt::from(10).pow(u32::try_from(frac.len()).ok()?);
                Rat::new(digits, scale)
            }
            Some(e) => {
                let e = e - frac.len();
                Some(Rat::extract(
                    digits,
                    BigInt::one(),
                    vec![(2, e.clone()), (5, e)],
                ))
            }
        }
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
        room(width(
            &self.num,
            self.pows.iter().map(|(p, e)| (*p, e.magnitude())),
        ))?;
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

    /// `Ok` when the system gives the memory to write its digits: the number built, of at
    /// most `bits` bits, and its text, at most `bits * log10(2) + 2` bytes; else [`TooLarge`]
    /// naming `bits`, before anything is built.
    pub fn text_room(&self) -> Result<(), TooLarge> {
        let side = |coef: &BigInt, sign: Sign| {
            let pows = self.pows.iter().filter(move |(_, e)| e.sign() == sign);
            width(coef, pows.map(|(p, e)| (*p, e.magnitude())))
        };
        let bits = side(&self.num, Sign::Plus) + side(&self.den, Sign::Minus);
        // `log10(2) < 1234 / 4096`; a digit is one byte.
        let text = ((&bits * 1234u32) >> 12u32) + 2u32;
        match given(&(&bits + (text << 3u32))) {
            true => Ok(()),
            false => Err(TooLarge { bits }),
        }
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
        if self.is_plain() && b.is_plain() {
            if self.den.is_one() && b.den.is_one() {
                return Ok(Rat::int(&self.num + &b.num));
            }
            return Ok(
                Rat::new(&self.num * &b.den + &b.num * &self.den, &self.den * &b.den)
                    .expect("den > 0"),
            );
        }
        if self.is_zero() {
            return Ok(b.clone());
        }
        if b.is_zero() {
            return Ok(self.clone());
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
        let a = self.aligned(&b.pows);
        let b = b.aligned(&self.pows);
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
        room(sizes[0].clone().max(sizes[1].clone()) + 1u32)?;
        let ra = &a.num * built(&rest_a);
        let rb = &b.num * built(&rest_b);
        Ok(Rat::build(
            ra * &b.den + rb * &a.den,
            &a.den * &b.den,
            common,
        ))
    }

    /// `a - b`, by the rule of [`Rat::add`].
    pub fn sub(&self, b: &Rat) -> Result<Rat, TooLarge> {
        self.add(&b.neg())
    }

    /// `a * b`.
    pub fn mul(&self, b: &Rat) -> Rat {
        if self.is_plain() && b.is_plain() {
            if self.den.is_one() && b.den.is_one() {
                return Rat::int(&self.num * &b.num);
            }
            return Rat::new(&self.num * &b.num, &self.den * &b.den).expect("den > 0");
        }
        Rat::build(
            &self.num * &b.num,
            &self.den * &b.den,
            merge(&self.pows, &b.pows, |x, y| x + y),
        )
    }

    /// `a / b`; `None` when `b` is zero.
    pub fn div(&self, b: &Rat) -> Option<Rat> {
        if b.is_zero() {
            return None;
        }
        if self.is_plain() && b.is_plain() {
            return Rat::new(&self.num * &b.den, &self.den * &b.num);
        }
        Some(Rat::build(
            &self.num * &b.den,
            &self.den * &b.num,
            merge(&self.pows, &b.pows, |x, y| x - y),
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
        let times = BigInt::from(e.clone());
        let mut pows: Vec<(u64, BigInt)> =
            self.pows.iter().map(|(p, x)| (*p, x * &times)).collect();
        let mut parts = [BigInt::one(), BigInt::one()];
        for (i, part) in [self.num.magnitude(), self.den.magnitude()]
            .into_iter()
            .enumerate()
        {
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
                // times `e`; one that does not fit in memory is `TooLarge`. Tested by
                // `a_power_of_a_wide_base_is_built` (COMPLEXITY.md K30).
                // A complete solution would keep an opaque base `b^e` beside the primes, with
                // the bases made pairwise coprime by Bernstein's coprime-base algorithm.
                None => {
                    room(BigUint::from(part.bits()) * e)?;
                    parts[i] = BigInt::from(Pow::pow(part, e));
                }
            }
        }
        pows.sort_unstable_by_key(|(p, _)| *p);
        let [mut num, den] = parts;
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
            return Ok(Rat::int(Euclid::rem_euclid(&self.num, &m.num)));
        }
        if self.divides_by(m) {
            return Ok(Rat::int(BigInt::zero()));
        }
        if !self.is_negative() && self.try_cmp(&m.abs())? == Ordering::Less {
            return Ok(self.clone());
        }
        self.rem_built(m)
    }

    /// The Euclidean remainder by an `m` that does not divide this integer, found by building
    /// `m`.
    fn rem_built(&self, m: &Rat) -> Result<Rat, TooLarge> {
        // Complexity tradeoff: a remainder that is neither `0` nor the dividend itself is
        // found by building the divisor `m`, at a cost proportional to `m`'s size, which bounds
        // the remainder's; `3 ** 10 ** 9 mod 2 ** 10 ** 9` builds `2^(10^9)`, while
        // `10 ** 10 ** 12 mod 2 ** 10 ** 12` and `5 mod 2 ** 10 ** 12` build nothing. No input
        // is refused for its size; one whose divisor does not fit in memory is `TooLarge`.
        // Tested by `an_exact_division_by_a_huge_power_builds_nothing` and
        // `kept_powers_agree_with_the_built_value` (COMPLEXITY.md K30). A complete solution
        // would keep a residue modulo a kept power unbuilt, as `p^a mod p^b` is, which needs
        // modular arithmetic on the kept forms.
        let m = m.to_integer()?.magnitude().clone();
        let mut r = self.num.magnitude() % &m;
        for (p, e) in self.pows.iter() {
            r = r * BigUint::from(*p).modpow(e.magnitude(), &m) % &m;
        }
        let r = BigInt::from(r);
        Ok(if self.is_negative() && !r.is_zero() {
            Rat::int(BigInt::from(m) - r)
        } else {
            Rat::int(r)
        })
    }

    /// The Euclidean quotient of two integers; `m` is not zero. An exact division keeps the
    /// powers, and a dividend smaller than `|m|` gives `0` or `±1`, building nothing; any
    /// other builds the remainder, by the rule of [`Rat::rem_euclid`], and the dividend's part
    /// above the powers it shares with the remainder, by the rule of [`Rat::add`].
    pub fn div_euclid(&self, m: &Rat) -> Result<Rat, TooLarge> {
        if self.is_plain() && m.is_plain() {
            return Ok(Rat::int(Euclid::div_euclid(&self.num, &m.num)));
        }
        let q = self.div(m).expect("the divisor is not zero");
        if q.is_integer() {
            return Ok(q);
        }
        if self.abs().try_cmp(&m.abs())? == Ordering::Less {
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
        // `10 ** 10 ** 12 div 2 ** 10 ** 12` builds nothing. No input is refused for its size;
        // one whose parts do not fit in memory is `TooLarge`. Tested by
        // `an_exact_division_by_a_huge_power_builds_nothing` and
        // `kept_powers_agree_with_the_built_value` (COMPLEXITY.md K30). A complete solution
        // would keep the floor of a quotient of kept powers unbuilt, which needs the same
        // modular arithmetic on kept forms as `rem_built`.
        let r = self.rem_built(m)?;
        Ok(self.sub(&r)?.div(m).expect("the divisor is not zero"))
    }

    /// Whether the integer `m` divides this integer: their quotient is an integer, found by
    /// subtracting exponents.
    fn divides_by(&self, m: &Rat) -> bool {
        self.div(m).expect("the divisor is not zero").is_integer()
    }

    /// The same number, with each prime of `others` moved out of `num` and `den` too.
    fn aligned(&self, others: &[(u64, BigInt)]) -> std::borrow::Cow<'_, Rat> {
        let listed = |p: u64| self.pows.binary_search_by_key(&p, |(q, _)| *q).is_ok();
        let divides = |p: u64| divides(self.num.magnitude(), p) || divides(self.den.magnitude(), p);
        let new: Vec<u64> = others
            .iter()
            .map(|(p, _)| *p)
            .filter(|&p| !listed(p) && divides(p))
            .collect();
        if new.is_empty() {
            return std::borrow::Cow::Borrowed(self);
        }
        let mut pows = self.pows.to_vec();
        pows.extend(new.into_iter().map(|p| (p, BigInt::zero())));
        pows.sort_unstable_by_key(|(p, _)| *p);
        Cow::Owned(Rat::extract(self.num.clone(), self.den.clone(), pows))
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
        // `|self| * 2^s == w` is read as `self == ±w * 2^-s`: the side built is the small one.
        let is = |s: &BigInt, w: &BigUint| {
            let w = Rat::int(BigInt::from(w.clone())).mul(&Rat::two_pow(-s));
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
    let g = num.gcd(&den);
    let sign = if den.is_negative() { -1 } else { 1 };
    (sign * (num / &g), sign * (den / g))
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

/// `prod p^e`, built.
fn built(pows: &[(u64, BigUint)]) -> BigInt {
    let mut out = BigUint::one();
    for (p, e) in pows {
        if !e.is_zero() {
            out *= Pow::pow(BigUint::from(*p), e);
        }
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

/// A number the evaluator must build, of at most `bits` bits, for which the system refused
/// the memory (DESIGN.md sec:domains): the number is a value of the language, and building
/// it is the machine's failure, not the program's.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TooLarge {
    /// At most this many bits: the size the build needs.
    pub bits: BigUint,
}

/// `Ok` when the system gives the memory for a number of `bits` bits, asked of the allocator
/// itself and freed at once, so the answer is the machine's and the evaluator sets no limit.
/// A build that would ask for more than the system gives is reported before it starts, where
/// num-bigint would abort the process.
fn room(bits: BigUint) -> Result<(), TooLarge> {
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
    /// The first comparison in the watched run whose build the system refused.
    static REFUSED: Cell<Option<TooLarge>> = const { Cell::new(None) };
}

/// While it lives, an [`Ord`] comparison of two numbers on this thread asks the system for the
/// memory of its bounds, as [`Rat::try_cmp`] does, and records the first refusal for
/// [`refused`] instead of building. A run makes one and reads the record after each step;
/// dropping it restores the watch it replaced, so a run nested in another keeps its own.
pub(crate) struct Watch {
    was: bool,
    outer: Option<TooLarge>,
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

/// The first comparison refused since the last call, under a [`Watch`].
pub(crate) fn refused() -> Option<TooLarge> {
    REFUSED.take()
}

impl Rat {
    /// The order of the two by value, or [`TooLarge`] when they agree in so many leading bits
    /// that the system refuses the memory to tell them apart: each doubling of the precision
    /// of the bounds ([`bound`]) asks for it first, as does building the two in full.
    pub fn try_cmp(&self, other: &Rat) -> Result<Ordering, TooLarge> {
        self.order(other, true)
    }

    /// The order by value; when `check`, [`TooLarge`] as for [`Rat::try_cmp`], and otherwise
    /// the build is not checked.
    fn order(&self, other: &Rat, check: bool) -> Result<Ordering, TooLarge> {
        if self.is_plain() && other.is_plain() {
            if self.den.is_one() && other.den.is_one() {
                return Ok(self.num.cmp(&other.num));
            }
            return Ok((&self.num * &other.den).cmp(&(&other.num * &self.den)));
        }
        let sign = self.num.sign().cmp(&other.num.sign());
        if sign != Ordering::Equal || self.is_zero() {
            return Ok(sign);
        }
        // With both coprime to every listed prime, the two are equal exactly when their
        // coefficients and exponents are, and otherwise one side holds a prime the other lacks.
        let a = self.aligned(&other.pows);
        let b = other.aligned(&self.pows);
        let n = times(a.num.magnitude(), b.den.magnitude(), check)?;
        let d = times(b.num.magnitude(), a.den.magnitude(), check)?;
        let f = merge(&a.pows, &b.pows, |x, y| x - y);
        let pows = |sign: Sign| {
            f.iter()
                .filter(|(_, e)| e.sign() == sign)
                .map(|(p, e)| (*p, e.magnitude().clone()))
                .collect()
        };
        let o = match f.is_empty() {
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
        };
        Ok(match self.is_negative() {
            true => o.reverse(),
            false => o,
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
/// factorization, so equality builds nothing.
impl PartialEq for Rat {
    fn eq(&self, other: &Self) -> bool {
        if self.is_plain() && other.is_plain() {
            return self.num == other.num && self.den == other.den;
        }
        if self.num.sign() != other.num.sign() {
            return false;
        }
        let a = self.aligned(&other.pows);
        let b = other.aligned(&self.pows);
        a.num == b.num && a.den == b.den && a.pows == b.pows
    }
}

impl Eq for Rat {}

/// The order by value. Under a [`Watch`], a pair the system refuses the memory to order is
/// recorded for [`refused`] and given the order of their normal forms, and the run stops at
/// its next step; with no watch, the build is not checked.
impl Ord for Rat {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.order(other, WATCHED.get()) {
            Ok(o) => o,
            Err(e) => {
                let first = REFUSED.take().unwrap_or(e);
                REFUSED.set(Some(first));
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
pub(crate) enum Exact {
    NegInf,
    Finite(Rat),
    PosInf,
    /// After every number, as the canonical NaN is after `+inf` in a float's total order.
    NaN,
}

impl Exact {
    /// The exact value of a float: every finite double is a dyadic rational.
    pub(crate) fn float(x: f64) -> Exact {
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
        Exact::Finite(r)
    }
}

/// How `String` writes a float (DESIGN.md sec:numeric): the shortest digits that read back
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
}

/// The float literal `text` at `f64`: decimal digits with an optional fraction and exponent,
/// no sign and no `_`, as the lexer keeps it (`0.1`, `1e9`, `2.5E-3`). It is the exact
/// decimal [`Rat::decimal`] projected by [`Rat::to_f64`], correctly rounded, to nearest with
/// ties to even; it is an error when that rounds to infinity, or to zero while the literal is
/// not zero, so `0e999` is zero and `1e-400` is an error.
pub fn literal_f64(text: &str) -> Result<f64, LiteralRounding> {
    Rat::decimal(text)
        .expect("the lexer's float text is a decimal")
        .to_f64()
}

/// The float literal `text` at `f32`, by the rule of [`literal_f64`]: `1e39` rounds to
/// infinity and `1e-46` to zero.
pub fn literal_f32(text: &str) -> Result<f32, LiteralRounding> {
    Rat::decimal(text)
        .expect("the lexer's float text is a decimal")
        .to_f32()
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
        Err(LiteralRounding::TooLarge(e)) => return Err(e),
        Err(LiteralRounding::Infinite | LiteralRounding::Zero) => return Ok(None),
    };
    Ok(match Exact::float(x) {
        Exact::Finite(f) => (f == *r).then_some(x),
        Exact::NegInf | Exact::PosInf | Exact::NaN => None,
    })
}
