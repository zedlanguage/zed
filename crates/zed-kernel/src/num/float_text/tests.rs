use super::*;
use crate::num::{Format, Rat};
use num_bigint::BigInt;
use num_traits::{One, Zero};

/// A splitmix64 stream.
struct Mix(u64);

impl Mix {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    /// A number in `0..n`.
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }

    fn digits(&mut self, len: usize) -> String {
        (0..len)
            .map(|_| char::from(b'0' + self.below(10) as u8))
            .collect()
    }
}

const FORMATS: [FloatFormat; 4] = [
    FloatFormat::F64,
    FloatFormat::F32,
    FloatFormat::F16,
    FloatFormat::BF16,
];

/// The exact reading of the unsigned literal `text`: its exact rational rounded by
/// [`Rat::project`], the reader this module replaces.
fn oracle(text: &str, format: FloatFormat) -> Result<u64, LiteralRounding> {
    let r = Rat::decimal(text).expect("memory").expect("a decimal");
    let f = Format {
        prec: format.precision() as u64,
        emin: 1 - format.emax(),
        emax: format.emax(),
    };
    Ok(match r.project(&f)? {
        None => 0,
        Some((_, m, t)) => {
            let fraction_bits = format.precision() - 1;
            if m >> fraction_bits == 0 {
                m
            } else {
                ((t + format.emax()) as u64) << fraction_bits | (m & ((1 << fraction_bits) - 1))
            }
        }
    })
}

/// Whether the mantissa of `text` holds a nonzero digit.
fn nonzero(text: &str) -> bool {
    let mantissa = text.split(['e', 'E']).next().expect("a mantissa");
    mantissa.bytes().any(|b| (b'1'..=b'9').contains(&b))
}

/// What std reads `text` as, `x` with encoding `bits`, under the literal rule.
fn by_std(text: &str, infinite: bool, zero: bool, bits: u64) -> Result<u64, LiteralRounding> {
    if infinite {
        Err(LiteralRounding::Infinite)
    } else if zero && nonzero(text) {
        Err(LiteralRounding::Zero)
    } else {
        Ok(bits)
    }
}

/// `text` read in every format agrees with the exact reading, and at `f64` and `f32` with std.
fn check(text: &str) {
    for format in FORMATS {
        let ours = read_float(text, format).expect("a decimal");
        assert_eq!(ours, oracle(text, format), "{format:?} `{text}`");
    }
    let x: f64 = text.parse().expect("std reads it");
    let expected = by_std(text, x.is_infinite(), x == 0.0, x.to_bits());
    assert_eq!(
        read_float(text, FloatFormat::F64),
        Some(expected),
        "std `{text}`"
    );
    let x: f32 = text.parse().expect("std reads it");
    let expected = by_std(text, x.is_infinite(), x == 0.0, u64::from(x.to_bits()));
    assert_eq!(
        read_float(text, FloatFormat::F32),
        Some(expected),
        "std f32 `{text}`"
    );
}

/// The float after the finite encoding `bits` in `format`.
fn next_up(bits: u64, format: FloatFormat) -> Result<u64, LiteralRounding> {
    let infinity = ((2 * format.emax() + 1) as u64) << (format.precision() - 1);
    if bits + 1 == infinity {
        Err(LiteralRounding::Infinite)
    } else {
        Ok(bits + 1)
    }
}

fn pow(b: u32, e: u32) -> BigUint {
    BigUint::from(b).pow(e)
}

#[test]
fn the_power_table_is_the_truncated_powers_of_five() {
    for q in -342i64..=324 {
        let p = pow(5, q.unsigned_abs() as u32);
        let b = p.bits() as usize;
        let t = if q >= 0 {
            if b <= 128 {
                p << (128 - b)
            } else {
                p >> (b - 128)
            }
        } else {
            (BigUint::one() << (127 + b)) / p
        };
        assert_eq!(BigUint::from(POW5[(q + 342) as usize]), t, "5^{q}");
    }
}

#[test]
fn exponent_of_a_power_of_ten() {
    for q in -342i64..=324 {
        let b = pow(5, q.unsigned_abs() as u32).bits() as i64;
        // floor(log2 10^q) = q + floor(log2 5^q): b - 1 for q >= 0, -b for q < 0 (5^q is
        // never a power of two).
        let expected = q + if q >= 0 { b - 1 } else { -b };
        assert_eq!((q * 217_706) >> 16, expected, "q = {q}");
    }
}

/// Mushtak and Lemire's check, on this table: a significand `w < 2^64` whose product with
/// `POW5[q]` has the 137 low bits at least `2^137 - 2^64`, the only case where the truncation
/// can change bit 73 of the high 128 bits, exists only if a convergent of `POW5[q] / 2^137`
/// with denominator below `2^64` is such a significand. There is none for `q` outside
/// `-27..=55`, and for `q` in `-27..0` every one is a multiple of `5^-q`, read exactly instead.
#[test]
fn the_truncated_powers_never_carry() {
    let modulus: BigInt = BigInt::one() << 137;
    let limit: BigInt = BigInt::one() << 64;
    let low = &modulus - &limit;
    let mut found = Vec::new();
    for q in -342i64..=324 {
        if (0..=55).contains(&q) {
            continue;
        }
        let t = BigInt::from(POW5[(q + 342) as usize]);
        let (mut a, mut b) = (t.clone(), modulus.clone());
        let (mut q1, mut q2) = (BigInt::zero(), BigInt::one());
        while !b.is_zero() {
            let digit = &a / &b;
            (a, b) = (b.clone(), &a % &b);
            let den = &digit * &q1 + &q2;
            (q2, q1) = (q1, den.clone());
            if den >= limit {
                break;
            }
            if den.is_zero() {
                continue;
            }
            if (&t * &den) % &modulus >= low {
                found.push((q, den));
            }
        }
    }
    for (q, den) in &found {
        let five = BigInt::from(pow(5, q.unsigned_abs() as u32));
        assert!(
            (-27..0).contains(q) && (den % five).is_zero(),
            "q = {q}: the significand {den} can carry"
        );
    }
}

#[test]
fn schubfach_logarithms_are_exact() {
    // Whether `n1/d1 <= n2/d2`.
    let le = |a: &(BigUint, BigUint), b: &(BigUint, BigUint)| &a.0 * &b.1 <= &b.0 * &a.1;
    let power = |base: u32, e: i32| {
        let p = pow(base, e.unsigned_abs());
        if e >= 0 {
            (p, BigUint::one())
        } else {
            (BigUint::one(), p)
        }
    };
    let scaled = |x: (BigUint, BigUint), n: u32, d: u32| (x.0 * n, x.1 * d);
    for e in -1700..=1700 {
        let x = power(2, e);
        let k = floor_log10_pow2(e);
        assert!(
            le(&power(10, k), &x) && !le(&power(10, k + 1), &x),
            "log10 2^{e}"
        );
        let x = scaled(power(2, e), 3, 4);
        let k = floor_log10_three_quarters_pow2(e);
        assert!(
            le(&power(10, k), &x) && !le(&power(10, k + 1), &x),
            "log10 3/4 2^{e}"
        );
    }
    for e in -400..=400 {
        let x = power(10, e);
        let k = floor_log2_pow10(e);
        assert!(
            le(&power(2, k), &x) && !le(&power(2, k + 1), &x),
            "log2 10^{e}"
        );
    }
}

#[test]
fn shortest_texts_of_doubles_read_back() {
    let mut mix = Mix(1);
    for _ in 0..200_000 {
        let x = f64::from_bits(mix.next() >> 1);
        if !x.is_finite() {
            continue;
        }
        for text in [format!("{x:e}"), format!("{x:?}")] {
            assert_eq!(
                read_float(&text, FloatFormat::F64),
                Some(Ok(x.to_bits())),
                "`{text}`"
            );
        }
    }
    let mut mix = Mix(2);
    for i in 0..2_000 {
        let x = f64::from_bits(mix.next() >> 1);
        if x.is_finite() && i % 2 == 0 {
            check(&format!("{x:e}"));
        }
    }
}

/// Every `f32` of `bits`, its shortest text read back at `f32`.
fn f32_bits_read_back(bits: impl Iterator<Item = u32>) {
    for b in bits {
        let x = f32::from_bits(b);
        if !x.is_finite() {
            continue;
        }
        let text = format!("{x:e}");
        let expected = Some(Ok(u64::from(b)));
        assert_eq!(read_float(&text, FloatFormat::F32), expected, "`{text}`");
    }
}

#[test]
fn shortest_texts_of_sampled_floats_read_back() {
    let mut mix = Mix(3);
    f32_bits_read_back((0..1_000_000).map(|_| mix.next() as u32));
    // The subnormals and the first normals, and the top of the range.
    f32_bits_read_back(0..(1 << 24));
    f32_bits_read_back(0x7f00_0000..0x7f80_0000);
}

/// The `f32` patterns from `part * 2^29` to the next part, split across every core. The eight
/// parts cover all 2^32 (half are negative), each in under a minute on 32 cores.
fn every_float_of_part(part: u64) {
    let (start, end) = (part << 29, (part + 1) << 29);
    let threads = std::thread::available_parallelism().map_or(1, |n| n.get()) as u64;
    let step = (end - start).div_ceil(threads);
    std::thread::scope(|s| {
        for i in 0..threads {
            let (from, to) = (start + i * step, (start + (i + 1) * step).min(end));
            s.spawn(move || f32_bits_read_back((from..to).map(|b| b as u32)));
        }
    });
}

macro_rules! every_float {
    ($($name:ident = $part:expr;)*) => {$(
        #[test]
        #[ignore = "long: an eighth of every f32"]
        fn $name() {
            every_float_of_part($part);
        }
    )*};
}

every_float! {
    every_float_read_back_0 = 0;
    every_float_read_back_1 = 1;
    every_float_read_back_2 = 2;
    every_float_read_back_3 = 3;
    every_float_read_back_4 = 4;
    every_float_read_back_5 = 5;
    every_float_read_back_6 = 6;
    every_float_read_back_7 = 7;
}

#[test]
fn random_texts_of_up_to_800_digits() {
    let mut mix = Mix(4);
    for i in 0..1_500 {
        let len = 1 + mix.below(if i % 4 == 0 { 800 } else { 40 }) as usize;
        let digits = mix.digits(len);
        let point = mix.below(len as u64 + 2) as usize;
        let mantissa = if point > len {
            digits.clone()
        } else {
            format!("{}.{}", &digits[..point], &digits[point..])
        };
        // A magnitude across and beyond every format's range.
        let magnitude = mix.below(720) as i64 - 360;
        let exp = magnitude - point.min(len) as i64;
        check(&format!("{mantissa}e{exp}"));
    }
}

/// The exact decimal text of `h * 2^e`.
fn exact_text(h: &BigUint, e: i64) -> String {
    if e >= 0 {
        format!("{}e0", h << e as usize)
    } else {
        format!("{}e{e}", h * pow(5, e.unsigned_abs() as u32))
    }
}

/// The halfway point `(2m + 1) * 2^(e - 1)` and the texts just above and below it.
fn halfway_texts(m: u64, e: i64) -> [String; 3] {
    let h = BigUint::from(2 * m + 1);
    let (digits, exp) = if e >= 1 {
        (h << (e - 1) as usize, 0)
    } else {
        (h * pow(5, (1 - e) as u32), e - 1)
    };
    [
        format!("{digits}e{exp}"),
        format!("{digits}000000000000000000000001e{}", exp - 24),
        format!("{}e{}", digits * 10u32 - 1u32, exp - 1),
    ]
}

#[test]
fn halfway_points_and_subnormals() {
    let mut mix = Mix(5);
    for format in FORMATS {
        let p = format.precision();
        for i in 0..300 {
            // Normal and subnormal significands, over the whole range of exponents.
            let m = if i % 3 == 0 {
                1 + mix.below((1 << (p - 1)) - 1)
            } else {
                (1 << (p - 1)) | mix.below(1 << (p - 1))
            };
            let e = if i % 3 == 0 {
                format.tiny()
            } else {
                format.tiny() + mix.below((2 * format.emax() - 1) as u64) as i64
            };
            let [tie, above, below] = halfway_texts(m, e);
            let lower = read_float(&exact_text(&BigUint::from(m), e), format);
            assert!(matches!(lower, Some(Ok(_))), "{format:?} {m} * 2^{e}");
            let lower = lower.expect("read").expect("finite");
            let up = next_up(lower, format);
            let even = if m % 2 == 0 { Ok(lower) } else { up.clone() };
            assert_eq!(
                read_float(&tie, format),
                Some(even),
                "{format:?} `{tie}` goes to even"
            );
            assert_eq!(
                read_float(&below, format),
                Some(Ok(lower)),
                "{format:?} `{below}`"
            );
            assert_eq!(read_float(&above, format), Some(up), "{format:?} `{above}`");
            for text in [&tie, &above, &below] {
                check(text);
            }
        }
    }
}

#[test]
fn the_edges_to_infinity_and_zero() {
    for format in FORMATS {
        let p = format.precision();
        let max = (1u64 << p) - 1;
        let top = format.emax() - p + 1;
        let [tie, above, below] = halfway_texts(max, top);
        let largest = read_float(&exact_text(&BigUint::from(max), top), format)
            .expect("read")
            .expect("finite");
        assert_eq!(
            read_float(&tie, format),
            Some(Err(LiteralRounding::Infinite))
        );
        assert_eq!(
            read_float(&above, format),
            Some(Err(LiteralRounding::Infinite))
        );
        assert_eq!(read_float(&below, format), Some(Ok(largest)));
        let [tie, above, below] = halfway_texts(0, format.tiny());
        assert_eq!(read_float(&tie, format), Some(Err(LiteralRounding::Zero)));
        assert_eq!(read_float(&above, format), Some(Ok(1)));
        assert_eq!(read_float(&below, format), Some(Err(LiteralRounding::Zero)));
        for text in [tie, above, below] {
            check(&text);
        }
    }
    for text in ["0e999999999999999999999", "0.000e-99999", "0", "0."] {
        for format in FORMATS {
            assert_eq!(read_float(text, format), Some(Ok(0)), "`{text}`");
        }
    }
    for text in [
        "1e99999999999999999999999",
        "1e309",
        "17976931348623159e292",
    ] {
        assert_eq!(
            read_float(text, FloatFormat::F64),
            Some(Err(LiteralRounding::Infinite))
        );
    }
    for text in [
        "1e-99999999999999999999999",
        "1e-400",
        "2.4703282292062327e-324",
    ] {
        assert_eq!(
            read_float(text, FloatFormat::F64),
            Some(Err(LiteralRounding::Zero))
        );
    }
    // 2^-25 is halfway between 0 and the least subnormal of f16.
    assert_eq!(
        read_float("298023223876953125e-25", FloatFormat::F16),
        Some(Err(LiteralRounding::Zero))
    );
}

#[test]
fn significands_of_19_and_20_digits() {
    for text in [
        "9999999999999999999",
        "99999999999999999999",
        "10000000000000000000",
        "1000000000000000000",
        "18446744073709551615",
        "18446744073709551616",
        "9007199254740993",
        "9007199254740993000000",
        "90071992547409930000000000000000000000001e-24",
        "900719925474099299999999999999999999999e-23",
        "1.7976931348623157e308",
        "179769313486231580793728971405303415079934132710037826936173778980444968292764750946649017977587207096330286416692887910946555547851940402630657488671505820681908902000708383676273854845817711531764475730270069855571366959622842914819860834936475292719074168444365510704342711559699508093042880177904174551110e-1",
        "4.9406564584124654e-324",
        "2.4703282292062328e-324",
        "0.000000000000000000000000000000000000000000001e-279",
    ] {
        check(text);
    }
    let mut mix = Mix(6);
    for i in 0..600 {
        let x = f64::from_bits(mix.next() >> 1);
        if !x.is_finite() || x == 0.0 {
            continue;
        }
        // The exact expansion of `x` or of a halfway point near it, cut to 18 to 21 digits.
        let bits = x.to_bits();
        let (m, e) = decode(bits, FloatFormat::F64);
        let full = if i % 2 == 0 {
            exact_text(&BigUint::from(m), e)
        } else {
            halfway_texts(m, e)[0].clone()
        };
        let (digits, exp) = full.split_once('e').expect("an exponent");
        let exp: i64 = exp.parse().expect("an exponent");
        for keep in 18..=21 {
            if digits.len() > keep {
                let cut = digits.len() - keep;
                check(&format!("{}e{}", &digits[..keep], exp + cut as i64));
                let up = format!(
                    "{}e{}",
                    digits[..keep].parse::<u128>().expect("digits") + 1,
                    exp + cut as i64
                );
                check(&up);
            }
        }
    }
}

/// Texts of every shape the scanner tells apart: leading zeros before and after the point, a
/// point before, inside or after the digits, trailing zeros, and 17 to 22 significant digits
/// around the 19 kept.
#[test]
fn texts_of_every_shape() {
    let mut mix = Mix(5);
    for _ in 0..20_000 {
        let zeros = |mix: &mut Mix, n: u64| "0".repeat(mix.below(n) as usize);
        let lead = zeros(&mut mix, 3);
        let len = 1 + mix.below(23) as usize;
        let mut digits = format!("{}{}", 1 + mix.below(9), mix.digits(len - 1));
        digits.push_str(&zeros(&mut mix, 4));
        let text = match mix.below(4) {
            0 => format!("{lead}{digits}"),
            1 => format!("{lead}.{}{digits}", zeros(&mut mix, 4)),
            2 => format!("{lead}{digits}."),
            _ => {
                let at = mix.below(digits.len() as u64 + 1) as usize;
                format!("{lead}{}.{}", &digits[..at], &digits[at..])
            }
        };
        let text = match mix.below(3) {
            0 => text,
            1 => format!("{text}e{}", mix.below(40) as i64 - 20),
            _ => format!("{text}E+{}", mix.below(20)),
        };
        check(&text);
    }
}

#[test]
fn syntax_and_sign() {
    for text in [
        "", ".", "e5", "1e", "1e+", "--1", "1..2", "1.2.3", "0x10", "1_000", " 1", "1 ", "inf",
        "nan", "1e5.0",
    ] {
        assert_eq!(read_float(text, FloatFormat::F64), None, "`{text}`");
        assert_eq!(Rat::decimal(text).expect("memory"), None, "`{text}`");
    }
    for text in ["1.", ".5", "+2.5e+3", "-2.5E-3", "007", "0.0"] {
        let x: f64 = text.parse().expect("std reads it");
        assert_eq!(
            read_float(text, FloatFormat::F64),
            Some(Ok(x.to_bits())),
            "`{text}`"
        );
        assert_eq!(read_f64_ieee(text).map(f64::to_bits), Some(x.to_bits()));
    }
    assert_eq!(read_f64_ieee("-1e999"), Some(f64::NEG_INFINITY));
    assert_eq!(
        read_f64_ieee("-1e-999").map(f64::to_bits),
        Some((-0.0f64).to_bits())
    );
    assert_eq!(read_float("-0", FloatFormat::F16), Some(Ok(0x8000)));
    assert_eq!(read_float("-1.5", FloatFormat::BF16), Some(Ok(0xbfc0)));
    assert_eq!(read_float("65504", FloatFormat::F16), Some(Ok(0x7bff)));
    assert_eq!(
        read_float("65520", FloatFormat::F16),
        Some(Err(LiteralRounding::Infinite))
    );
}

/// `show_f64` as it was: std's `{:e}` rebuilt into the layout.
fn std_show(x: f64) -> String {
    if x.is_nan() {
        return "nan".into();
    }
    if x.is_infinite() {
        return if x > 0.0 { "inf" } else { "-inf" }.into();
    }
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

fn shows_as_before(bits: u64) {
    let x = f64::from_bits(bits);
    let shown = show_f64(x);
    assert_eq!(shown, std_show(x), "{bits:#x}");
    if x.is_finite() {
        assert_eq!(
            read_f64_ieee(&shown).map(f64::to_bits),
            Some(bits),
            "`{shown}`"
        );
    }
}

#[test]
fn shown_as_before_on_random_doubles() {
    let mut mix = Mix(7);
    for _ in 0..1_000_000 {
        shows_as_before(mix.next());
    }
}

#[test]
fn shown_as_before_on_edge_doubles() {
    let specials = [
        0.0,
        -0.0,
        f64::INFINITY,
        f64::NEG_INFINITY,
        f64::NAN,
        f64::MAX,
        f64::MIN_POSITIVE,
    ];
    for x in specials {
        shows_as_before(x.to_bits());
    }
    // The least subnormals, the largest, and the first normals.
    for c in (1..200_000).chain((1 << 52) - 100_000..(1 << 52) + 100_000) {
        shows_as_before(c);
    }
    // Every power of two (the narrower lower half of the rounding interval) and its neighbors,
    // the largest values, and the integers around 2^53.
    for field in 1..2047u64 {
        for d in [-2i64, -1, 0, 1, 2] {
            shows_as_before((field << 52).wrapping_add_signed(d));
        }
    }
    for b in 0x7fef_ffff_ffff_0000..0x7ff0_0000_0000_0000 {
        shows_as_before(b);
    }
    for i in (1u64 << 53) - 1_000..(1 << 53) + 1_000 {
        shows_as_before((i as f64).to_bits());
    }
    // The powers of ten and their neighbors, the ties of `every_sampled_tie_prints_the_larger_magnitude`.
    for k in -325..=308 {
        let x: f64 = format!("1e{k}").parse().expect("std reads it");
        for b in [x.to_bits().wrapping_sub(1), x.to_bits(), x.to_bits() + 1] {
            shows_as_before(b);
            shows_as_before(b | 1 << 63);
        }
    }
    assert_eq!(show_f64(1666666666666669.0 + 0.25), "1666666666666669.3");
    assert_eq!(show_f64(5e-324), "5.0e-324");
    assert_eq!(show_f64(1e21), "1.0e21");
    assert_eq!(show_f64(1e-7), "1.0e-7");
    assert_eq!(show_f64(0.000001), "0.000001");
}
