//! `rat(s)` reads what `String` writes for a `rat`, the same without the `r`s, or a decimal with
//! digits on both sides of the point; any other text is `#invalid` (DESIGN.md L1.18).

use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Pow};
use zed_kernel::term::build::{lit, prim};
use zed_kernel::{Prim, Rat, Value, eval};

use super::x;

/// `rat(s)` by the kernel's own primitive.
fn read_value(s: &str) -> Value {
    eval(&prim(Prim::CastRat, vec![lit(Value::str(s))])).unwrap()
}

/// `rat(s)`, printed.
fn read(s: &str) -> String {
    read_value(s).to_string()
}

#[test]
fn a_price_read_from_a_form_field() {
    assert_eq!(x("rat(\"-1r/3r\")"), "-1r/3r");
    assert_eq!(x("rat(\"19.99\") * 3r"), "5997r/100r");
    assert_eq!(
        x("rat(text(\"2/4\")) else 0r"),
        "0r",
        "String writes 1r/2r, never 2r/4r"
    );
    assert_eq!(
        x("rat(text(\"1/-3\"))"),
        "#invalid",
        "the sign is on the numerator"
    );
}

#[test]
fn every_printed_rat_reads_back_to_itself() {
    let mut values: Vec<Rat> = Vec::new();
    for num in -30..=30 {
        for den in 1..=30 {
            values.push(Rat::new(BigInt::from(num), BigInt::from(den)).unwrap());
        }
    }
    let two = BigInt::from(2);
    let three = BigInt::from(3);
    let wide = [
        (Pow::pow(&two, 300u32) + 1, Pow::pow(&three, 200u32)),
        (-Pow::pow(BigInt::from(10), 500u32), BigInt::from(7)),
        (BigInt::from(7), Pow::pow(BigInt::from(10), 500u32) + 1),
        (Pow::pow(&three, 1000u32), Pow::pow(&two, 999u32)),
    ];
    values.extend(wide.into_iter().map(|(n, d)| Rat::new(n, d).unwrap()));
    // Powers kept as exponents print their digits in full and read back as the same value.
    for text in ["1e300", "-2.5e-200", "123456789e45"] {
        values.push(Rat::decimal(text).unwrap().unwrap());
    }
    for r in values {
        let v = Value::rat(r);
        let Value::Str(shown) = eval(&prim(Prim::Show, vec![lit(v.clone())])).unwrap() else {
            panic!("String writes a string");
        };
        assert_eq!(read_value(&shown.flat()), v, "rat(String({v}))");
        // The same without the `r`s reads the same value.
        let plain = shown.flat().replace('r', "");
        assert_eq!(read_value(&plain), v, "rat({plain:?})");
    }
}

#[test]
fn text_that_string_never_writes_is_invalid() {
    let rejected = [
        // The eight forms the BUGCLASS hunt found read as values.
        ("1/-3", "a negative denominator"),
        ("1r/-3r", "a negative denominator"),
        ("-1/-3", "two signs"),
        ("1/3r", "an `r` on one part only"),
        ("1r/3", "an `r` on one part only"),
        ("2r/4r", "not in lowest terms"),
        ("-0", "a negative zero"),
        ("1/03", "a leading zero"),
        // More of the same kinds.
        ("2/4", "not in lowest terms"),
        ("0r/5r", "zero is written 0r"),
        ("3r/1r", "a denominator of 1 is not written"),
        ("3/1", "a denominator of 1 is not written"),
        ("-0r", "a negative zero"),
        ("03", "a leading zero"),
        ("-03r", "a leading zero"),
        ("1r/03r", "a leading zero"),
        ("1r/0r", "a zero denominator"),
        ("1/0", "a zero denominator"),
        ("0/0", "a zero denominator"),
        ("+1/3", "a sign is only `-`"),
        ("1/+3", "a sign is only `-`"),
        ("+5", "a sign is only `-`"),
        ("\u{2212}1", "a sign is only `-`, not U+2212"),
        ("", "no digits"),
        ("-", "no digits"),
        ("r", "no digits"),
        ("-r", "no digits"),
        ("/3", "no numerator"),
        ("1r/", "no denominator"),
        ("1//3", "two slashes"),
        ("1/3/5", "two slashes"),
        ("3rr", "two `r`s"),
        ("1 /3", "white space"),
        (" 1", "white space"),
        ("1/3 ", "white space"),
        ("1/2.5", "a decimal denominator"),
        // Decimals need digits on both sides of the point, and no exponent or `r`.
        (".5", "no digits before the point"),
        ("5.", "no digits after the point"),
        ("-.5", "no digits before the point"),
        ("1.5r", "a decimal with an `r`"),
        ("1.5e3", "an exponent"),
        ("1e3", "an exponent"),
        ("1.2.3", "two points"),
        ("0x10", "not decimal digits"),
        ("\u{0661}", "an Arabic-Indic digit"),
        ("inf", "not a number a rat holds"),
        ("nan", "not a number a rat holds"),
    ];
    for (s, why) in rejected {
        assert_eq!(read(s), "#invalid", "rat({s:?}): {why}");
    }
}

#[test]
fn text_that_string_writes_or_a_decimal_is_read() {
    let read_as = [
        ("3r", "3r"),
        ("3", "3r"),
        ("-3", "-3r"),
        ("0r", "0r"),
        ("0", "0r"),
        ("-1r/3r", "-1r/3r"),
        ("-1/3", "-1r/3r"),
        (
            "123456789012345678901234567890r",
            "123456789012345678901234567890r",
        ),
        ("0.25", "1r/4r"),
        ("-0.5", "-1r/2r"),
        ("10.0", "10r"),
        // DESIGN.md asks only for digits on both sides of the point.
        ("00.50", "1r/2r"),
        ("-0.0", "0r"),
        ("0.0390625", "5r/128r"),
        ("31.25", "125r/4r"),
    ];
    for (s, want) in read_as {
        assert_eq!(read(s), want, "rat({s:?})");
    }
}

#[test]
fn a_decimal_keeps_the_powers_of_2_and_5_it_does_not_cancel() {
    // `m / 10^k` has the common factor `2^min(v2, k) 5^min(v5, k)`; the cases with each
    // valuation below, at and above `k`.
    let cases = [
        ("0.1", "1r/10r"),
        ("0.2", "1r/5r"),
        ("0.5", "1r/2r"),
        ("0.8", "4r/5r"),
        ("6.4", "32r/5r"),
        ("0.625", "5r/8r"),
        ("1.024", "128r/125r"),
        ("1250.0", "1250r"),
        ("0.15625", "5r/32r"),
    ];
    for (s, want) in cases {
        assert_eq!(read(s), want, "rat({s:?})");
        let digits: BigInt = s.replace('.', "").parse().unwrap();
        let k = s.len() - s.find('.').unwrap() - 1;
        let by_gcd = Rat::new(digits, Pow::pow(BigInt::from(10), k)).unwrap();
        assert_eq!(Value::rat(by_gcd).to_string(), want, "{s} by the gcd");
    }
    let wide = format!("{}.{}", "7".repeat(2000), "5".repeat(2000));
    let digits: BigInt = wide.replace('.', "").parse().unwrap();
    let ten_k = Pow::pow(BigInt::from(10), 2000u32);
    let g = digits.gcd(&ten_k);
    assert!(!g.is_one(), "the wide case has a common factor");
    let by_gcd = Rat::new(digits / &g, ten_k / g).unwrap();
    assert_eq!(read(&wide), Value::rat(by_gcd).to_string());
}

/// `2^a 5^b m` as a decimal with `k` digits after the point, zeros put in front as needed.
fn with_point(digits: &str, k: usize) -> String {
    let padded = format!(
        "{}{digits}",
        "0".repeat((k + 1).saturating_sub(digits.len()))
    );
    let (whole, frac) = padded.split_at(padded.len() - k);
    format!("{whole}.{}", if frac.is_empty() { "0" } else { frac })
}

#[test]
fn a_decimal_is_reduced_as_by_the_gcd_whatever_its_powers_of_2_and_5() {
    // The powers of 2 and 5 below, at and above the number of fraction digits `k`, near powers
    // of 2 (where the reading of the power by its binary digits changes length), with a cofactor
    // `m`, and through an exponent, which keeps them as powers.
    let twos = [0u32, 1, 2, 3, 7, 8, 9, 63, 64, 65, 200];
    let fives = [
        0u32, 1, 2, 3, 4, 5, 6, 7, 8, 9, 15, 16, 17, 31, 33, 100, 255, 256, 257,
    ];
    for a in twos {
        for b in fives {
            for m in [1u32, 3, 7, 21] {
                let d = (BigInt::one() << a) * Pow::pow(BigInt::from(5), b) * m;
                let text = d.to_string();
                let (a, b) = (a as usize, b as usize);
                let ks = [
                    0,
                    1,
                    2,
                    3,
                    5,
                    6,
                    a,
                    a + 1,
                    b,
                    b + 1,
                    b.saturating_sub(1),
                    a + b + 3,
                ];
                for k in ks {
                    let ten_k = Pow::pow(BigInt::from(10), k);
                    let want = Rat::new(d.clone(), ten_k.clone()).unwrap();
                    let s = with_point(&text, k);
                    assert_eq!(read_value(&s), Value::rat(want.clone()), "rat({s:?})");
                    let lit = Rat::decimal(&format!("{text}e-{k}")).unwrap().unwrap();
                    assert_eq!(lit, want, "{text}e-{k}");
                    let up = Rat::decimal(&format!("{s}e{k}")).unwrap().unwrap();
                    let want_up = Rat::new(d.clone(), BigInt::one());
                    assert_eq!(up, want_up.unwrap(), "{s}e{k}");
                }
            }
        }
    }
    let half = Rat::new(BigInt::one(), BigInt::from(2)).unwrap();
    assert_eq!(Rat::decimal("5e-1").unwrap().unwrap(), half);
    assert_eq!(read("-0.5000"), "-1r/2r");
}
