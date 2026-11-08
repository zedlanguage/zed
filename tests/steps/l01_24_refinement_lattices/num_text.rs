//! An interval end read from decimal text (`Num`'s `FromStr`, which the ZIR text reader uses for
//! a class's modulus). The text is read by halves (`zed_kernel::num::read_digits`), in
//! O(n log^2 n) for n digits; num-bigint's own reading, which it replaced, is O(n^2). Each value
//! and each error is num-bigint's (item P14-bigint-parse).

use num_bigint::BigInt;
use zed_tests::instances::Rng;
use zed_tests::scaling;
use zedc::store::interval::Num;

/// num-bigint's reading of `text`, the reading `Num` had before.
fn by_num_bigint(text: &str) -> Result<Num, num_bigint::ParseBigIntError> {
    text.parse::<BigInt>().map(Num::from)
}

/// `len` random digits.
fn digits(rng: &mut Rng, len: usize) -> String {
    (0..len)
        .map(|_| char::from(b'0' + rng.int(0, 9) as u8))
        .collect()
}

/// Every length from 1 to 1500 digits and some up to 20,000, either side of where the text is
/// split (1024 digits and its doublings), each plain, with leading zeros, with a sign and with
/// `_` between some digits.
#[test]
fn a_decimal_end_reads_as_num_bigint_reads_it_at_every_length() {
    let mut rng = Rng::new(14);
    let lengths = (1..=1500).chain([2047, 2048, 2049, 4095, 4096, 4097, 8193, 20_000]);
    for len in lengths {
        let plain = digits(&mut rng, len);
        let padded = format!("{}{plain}", "0".repeat(rng.int(1, 600) as usize));
        let sign = ["", "+", "-"][rng.int(0, 2) as usize];
        let marked: String = padded
            .chars()
            .enumerate()
            .flat_map(|(i, c)| {
                let mark = i > 0 && rng.int(0, 6) == 0;
                mark.then_some('_').into_iter().chain([c])
            })
            .collect();
        for text in [plain, padded, format!("{sign}{marked}")] {
            assert_eq!(
                text.parse::<Num>(),
                by_num_bigint(&text),
                "{len} digits: {text}"
            );
        }
    }
}

/// Nines and powers of ten either side of the split lengths: the carries cross every part.
#[test]
fn nines_and_powers_of_ten_read_exactly() {
    for len in [18, 19, 20, 511, 512, 513, 1023, 1024, 1025, 2049] {
        let nines = "9".repeat(len);
        let ten = format!("1{}", "0".repeat(len - 1));
        for text in [nines, ten] {
            for text in [text.clone(), format!("-{text}"), format!("+{text}")] {
                assert_eq!(text.parse::<Num>(), by_num_bigint(&text), "{text}");
            }
        }
    }
    let zeros = "0".repeat(3000);
    assert_eq!(zeros.parse::<Num>(), Ok(Num::from(0i64)));
    assert_eq!(format!("-{zeros}").parse::<Num>(), Ok(Num::from(0i64)));
}

/// Texts that are not integers get num-bigint's error, long ones too.
#[test]
fn a_text_that_is_not_an_integer_gets_num_bigints_error() {
    let long = "7".repeat(3000);
    let texts = [
        "".to_string(),
        "+".into(),
        "-".into(),
        "_1".into(),
        "-_1".into(),
        "+-1".into(),
        "-+1".into(),
        "--1".into(),
        "++1".into(),
        " 1".into(),
        "1 ".into(),
        "1a".into(),
        "1.0".into(),
        "0x10".into(),
        "\u{661}".into(),
        format!("{long}x"),
        format!("-+{long}"),
        format!("_{long}"),
    ];
    for text in texts {
        let ours = text.parse::<Num>();
        assert!(ours.is_err(), "{text:?}");
        assert_eq!(ours, by_num_bigint(&text), "{text:?}");
    }
    // `_` after the first digit is dropped, as num-bigint drops it, doubled or last.
    for text in ["1_", "1__2", "-1_2_", "+0_0_7"] {
        assert_eq!(text.parse::<Num>(), by_num_bigint(text), "{text}");
    }
}

/// 160,000 and 1,280,000 digits, built before timing: read by halves, within n log n. These are
/// the sizes of the kernel's own reading test (`l01_18_scalar_interpreter`), above the width
/// where the kernel's product leaves num-bigint's Toom-3 for its transform; from 20,000 to
/// 160,000 digits the products are Toom-3's, about n^1.46, and the reading measured 30.5 times.
#[test]
fn reading_a_long_decimal_end_scales() {
    let texts = scaling::inputs(160_000, |n| digits(&mut Rng::new(n as u64), n));
    scaling::check("reading a decimal end of n digits", 160_000, |n| {
        let num: Num = texts[&n].parse().expect("digits");
        assert!(num > Num::from(0i64));
    });
}

/// An end of 20,000 and of 160,000 digits written in decimal, the value built before timing.
/// num-bigint writes a number of 32 words or more by halves, dividing by the square powers of
/// its base, and divides by Burnikel and Ziegler's recursion above 64 words: O(M(n) log n),
/// with num-bigint's product M (Toom-3 at these sizes, about n^1.46). Measured, it grows about
/// 2.85 times per doubling at every size from 10,000 to 1,280,000 digits, 23.6 times here, close
/// to the limit; built without num-bigint as one codegen unit it took 24.8 times. Both sizes are
/// below the 60,000 words where `Num` turns to the kernel's printer, which is slower there; the
/// printer is held to n log^2 n by `writing_a_wide_end_scales` (COMPLEXITY.md K81).
#[test]
fn writing_a_long_decimal_end_scales() {
    let ends = scaling::inputs(20_000, |n| {
        let text = digits(&mut Rng::new(n as u64), n);
        text.parse::<Num>().expect("digits")
    });
    scaling::check("writing a decimal end of n digits", 20_000, |n| {
        assert!(!ends[&n].to_string().is_empty());
    });
}

/// A random number of `words` 64-bit words, the top one not zero.
fn wide(rng: &mut Rng, words: usize) -> BigInt {
    let mut digits: Vec<u32> = (0..2 * words).map(|_| rng.next_u64() as u32).collect();
    if let Some(top) = digits.last_mut() {
        *top |= 1 << 31;
    }
    BigInt::from(num_bigint::BigUint::new(digits))
}

/// Item NUM-print-fast: an end's text, written by `zed_kernel::num::to_decimal`, is num-bigint's
/// for both signs: zero and the edges of `i64` and `i128`, where the form changes; the powers
/// of ten `10^(597 2^i)` that the printer divides by and their neighbors, where a half is zero
/// or all nines; random numbers of every power's width in words `31 2^i` and one either side;
/// and numbers past 60,000 words, where the kernel's printer takes over from num-bigint's,
/// among them powers made by `pow`, which are kept unexpanded until written.
#[test]
fn a_written_end_is_num_bigints_text() {
    let mut rng = Rng::new(81);
    let one = BigInt::from(1);
    let mut values: Vec<BigInt> = vec![
        BigInt::from(0),
        one.clone(),
        BigInt::from(i64::MAX),
        BigInt::from(i64::MAX) + 1,
        BigInt::from(i128::MAX),
        BigInt::from(i128::MAX) + 1,
        BigInt::from(u128::MAX) + 1,
    ];
    let ten = BigInt::from(10);
    for i in 0..12 {
        let words = 31usize << i;
        for w in [words - 1, words, words + 1] {
            values.push(wide(&mut rng, w));
        }
        let p = ten.pow(597 << i);
        values.extend([&p - 1, &p + 1, p.clone()]);
        if i < 8 {
            values.extend([&p * &p - 1, &p * &p + &p]);
        }
    }
    values.extend([wide(&mut rng, 60_000), wide(&mut rng, 70_000)]);
    for x in &values {
        for x in [x.clone(), -x] {
            let text = x.to_string();
            assert_eq!(Num::from(&x).to_string(), text, "{} digits", text.len());
        }
    }
    for (base, k) in [
        (3i64, 300_000u32),
        (-3, 300_001),
        (10, 1_300_000),
        (7, 1000),
    ] {
        let text = BigInt::from(base).pow(k).to_string();
        assert_eq!(Num::from(base).pow(k).to_string(), text, "{base} ** {k}");
    }
}

/// An end of 65,536 and 524,288 words (about 1.26 and 10.1 million digits) written in decimal,
/// by the kernel's printer: O(M(n) log n) = O(n log^2 n), about 2.3 times the work per
/// doubling, 12 times here (COMPLEXITY.md K81).
#[test]
fn writing_a_wide_end_scales() {
    let n = 1 << 16;
    let ends = scaling::inputs(n, |m| Num::from(wide(&mut Rng::new(m as u64), m)));
    scaling::check("writing a decimal end of n words", n, |m| {
        assert!(!ends[&m].to_string().is_empty());
    });
}

/// Item NUM-print-fast: writing an end takes at most 1.1 times num-bigint's processor time at
/// each size of COMPLEXITY.md K81, 10,000 to 1,280,000 digits (519 to 66,439 words), the
/// fastest of five runs each, in up to three tries. Below 60,000 words the end is written by
/// num-bigint itself; at 66,439 the kernel's printer took 0.93 to 0.96 times its time
/// (2026-11-08). Processor time, not instructions: there the printer runs 1.06 times
/// num-bigint's instructions in less time.
#[test]
fn writing_an_end_is_never_slower_than_num_bigint() {
    let mut meter = scaling::Meter::of_cpu_time();
    for digits in [
        10_000u32, 20_000, 40_000, 80_000, 160_000, 320_000, 640_000, 1_280_000,
    ] {
        let mut rng = Rng::new(u64::from(digits));
        let x: BigInt = (BigInt::from(10).pow(digits - 1) * rng.int(1, 9))
            + digits_of(&mut rng, digits as usize - 1);
        let num = Num::from(&x);
        let mut seen = Vec::new();
        let fastest = |meter: &mut scaling::Meter, f: &dyn Fn()| {
            (0..5)
                .map(|_| meter.work(f).units)
                .min()
                .expect("five runs")
        };
        let held = (0..3).any(|_| {
            let ours = fastest(&mut meter, &|| assert!(!num.to_string().is_empty()));
            let theirs = fastest(&mut meter, &|| assert!(!x.to_string().is_empty()));
            let ratio = ours as f64 / theirs as f64;
            seen.push(format!("{ours} against {theirs} ns, {ratio:.3}"));
            ratio <= 1.1
        });
        assert!(held, "{digits} digits: {}", seen.join("; "));
        eprintln!("{digits} digits: {}", seen.join("; "));
    }
}

/// `len` random digits as a number.
fn digits_of(rng: &mut Rng, len: usize) -> BigInt {
    digits(rng, len).parse().expect("digits")
}
