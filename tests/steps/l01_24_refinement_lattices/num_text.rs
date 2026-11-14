//! An interval end read from decimal text (`Num`'s `FromStr`, which the ZIR text reader uses for
//! a class's modulus). The text is read by halves (`zed_kernel::num::read_digits`), in
//! O(n log^2 n) for n digits; num-bigint's own reading, which it replaced, is O(n^2). Each value
//! and each error is num-bigint's (item P14-bigint-parse).

use num_bigint::{BigInt, BigUint};
use zed_kernel::num::{PRINT_HANDOFF, PRINT_WHOLE, to_decimal_split};
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
/// or all nines, and random numbers of every such power's width in words `31 2^i` and one
/// either side, up to the first power past `PRINT_WHOLE` words, where the kernel's split takes
/// over from num-bigint's; that power, its neighbors and its sum with the power below it,
/// whose low half is that power padded with zeros, all split; and powers made by `pow`, which
/// are kept unexpanded until written, below and past `PRINT_WHOLE` words. Random numbers of
/// `PRINT_WHOLE - 1` to `PRINT_WHOLE + 1` words are in
/// `a_written_end_is_num_bigints_text_at_the_edges`.
///
/// TEST-bench-move-l0123, author P169: this ran the widths and powers for `i` up to 11
/// (63,489 words, `10^1,222,656`), random numbers of `PRINT_WHOLE` and `2 PRINT_WHOLE` words,
/// and the kept powers `3^300000`, `-3^300001`, `10^1300000` and `7^1000`, with `Rng::new(81)`:
/// 10.9 s alone at load 38, nearly all of it in the sizes past `i` = 8, which take the same
/// branches of the split as the first size past `PRINT_WHOLE`. It now stops at that first
/// power (`i` = 8 with `PRINT_WHOLE` at 7845), and the kept powers are `3^30000`, `-3^30001`,
/// `10^k` for the least `k` of more than `PRINT_WHOLE` words plus 1000, and `7^1000`, with a
/// fresh seed.
#[test]
fn a_written_end_is_num_bigints_text() {
    let (mut rng, seed) = Rng::fresh("written ends");
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
    let whole_bits = 64 * PRINT_WHOLE as u64;
    for i in 0.. {
        let p = ten.pow(597 << i);
        if p.bits() > whole_bits {
            let below = ten.pow(597 << (i - 1));
            values.extend([&p - 1, &p + 1, &p + &below, p]);
            break;
        }
        let words = 31usize << i;
        for w in [words - 1, words, words + 1] {
            values.push(wide(&mut rng, w));
        }
        values.extend([&p - 1, &p + 1, p.clone()]);
    }
    for x in &values {
        for x in [x.clone(), -x] {
            let text = x.to_string();
            assert_eq!(
                Num::from(&x).to_string(),
                text,
                "{} digits, ZED_TEST_SEED={seed}",
                text.len()
            );
        }
    }
    let past = (whole_bits as f64 * std::f64::consts::LOG10_2) as u32 + 1000;
    for (base, k) in [(3i64, 30_000u32), (-3, 30_001), (10, past), (7, 1000)] {
        let text = BigInt::from(base).pow(k).to_string();
        assert_eq!(Num::from(base).pow(k).to_string(), text, "{base}^{k}");
    }
}

/// Item PRINT-below-whole: an end's text is num-bigint's, both signs, at the edges where the
/// kernel's printer changes how it works: zero and every one-digit number; `10^k`, `10^k - 1`
/// and `10^k + 1` for `k` up to 40; and random numbers and all-ones numbers of `PRINT_WHOLE - 1`,
/// `PRINT_WHOLE` and `PRINT_WHOLE + 1` words, the first printed by num-bigint whole, the others
/// by the split. The split's own edges are in `both_printing_methods_write_the_same_text`.
#[test]
fn a_written_end_is_num_bigints_text_at_the_edges() {
    let mut rng = Rng::new(2026);
    let ten = BigInt::from(10);
    let mut values: Vec<BigInt> = (0..10).map(BigInt::from).collect();
    for k in 1..=40u32 {
        let p = ten.pow(k);
        values.extend([&p - 1, &p + 1, p]);
    }
    for w in [PRINT_WHOLE - 1, PRINT_WHOLE, PRINT_WHOLE + 1] {
        values.push(wide(&mut rng, w));
        values.push((BigInt::from(1) << (64 * w)) - 1);
    }
    for x in &values {
        for x in [x.clone(), -x] {
            let text = x.to_string();
            assert_eq!(Num::from(&x).to_string(), text, "{} digits", text.len());
        }
    }
}

/// Item PRINT-below-whole: an end's text against a reference that shares no code with either
/// way of printing: the text it was read from by num-bigint's parser (`BigInt::from_str`, by
/// products of powers of the base), both signs. Random texts of the digits in the middle of
/// 1, 2, 31, 500, `PRINT_WHOLE - 1` and `PRINT_WHOLE` words, so that the smaller are printed by
/// num-bigint whole and the last by the split; and at the same lengths but `PRINT_WHOLE - 1`
/// the texts `99...9`, `10...0` and `10...01`, whose halves at every split are all nines or
/// zeros.
///
/// TEST-bench-move-l0123, author P169: this ran the four texts at 1, 2, 31, 500,
/// `PRINT_WHOLE - 1`, `PRINT_WHOLE` and `2 PRINT_WHOLE` words with `Rng::new(4096)`: 1.5 s alone
/// at load 38, half of it at `2 PRINT_WHOLE` words, whose split takes the branches the split at
/// `PRINT_WHOLE` words takes. It now stops at `PRINT_WHOLE` words, and at `PRINT_WHOLE - 1`
/// words, printed whole as the smaller sizes are, runs only the random text; with a fresh seed.
#[test]
fn a_written_end_is_the_text_it_was_read_from_on_both_sides_of_print_whole() {
    let (mut rng, seed) = Rng::fresh("texts either side of PRINT_WHOLE");
    for w in [1, 2, 31, 500, PRINT_WHOLE - 1, PRINT_WHOLE] {
        // In the middle of the numbers of `w` words: 32 bits, more than 9 digits, from each end.
        let len = ((64 * w - 32) as f64 * std::f64::consts::LOG10_2) as usize;
        let random = format!("{}{}", rng.int(1, 9), digits(&mut rng, len - 1));
        let mut texts = vec![random];
        if w != PRINT_WHOLE - 1 {
            texts.extend([
                "9".repeat(len),
                format!("1{}", "0".repeat(len - 1)),
                format!("1{}1", "0".repeat(len - 2)),
            ]);
        }
        for text in texts {
            let x: BigInt = text.parse().expect("digits");
            assert_eq!(x.magnitude().bits().div_ceil(64), w as u64, "{len} digits");
            assert_eq!(
                Num::from(&x).to_string(),
                text,
                "{w} words, ZED_TEST_SEED={seed}"
            );
            assert_eq!(
                Num::from(-&x).to_string(),
                format!("-{text}"),
                "{w} words, ZED_TEST_SEED={seed}"
            );
        }
    }
}

/// Small instance of `bench::writing_a_long_decimal_end_scales`: a random text of digits of
/// `PRINT_WHOLE + 1` words, its first digit not 0, read as a `Num` by its own reader (not
/// num-bigint's) and written by the split, is the same text, with a sign too. The reader is
/// checked against num-bigint's only up to 20,000 digits in
/// `a_decimal_end_reads_as_num_bigint_reads_it_at_every_length`.
#[test]
fn a_long_decimal_end_read_as_num_is_written_as_its_text() {
    let (mut rng, seed) = Rng::fresh("a long decimal end");
    let len = ((64 * (PRINT_WHOLE + 1) - 32) as f64 * std::f64::consts::LOG10_2) as usize;
    let text = format!("{}{}", rng.int(1, 9), digits(&mut rng, len - 1));
    let end = text.parse::<Num>().expect("digits");
    assert_eq!(end.to_string(), text, "ZED_TEST_SEED={seed}");
    let negative = format!("-{text}");
    let end = negative.parse::<Num>().expect("digits");
    assert_eq!(end.to_string(), negative, "ZED_TEST_SEED={seed}");
}

/// Item PRINT-below-whole: the two ways of printing, forced, write the same text: num-bigint's
/// printing of the whole number and the kernel's split (`zed_kernel::num::to_decimal_split`),
/// below `PRINT_WHOLE`, where `to_decimal` uses only the first. Random and all-ones numbers of
/// 1 to 40 words and of every power's width `31 2^i` and one either side up to 3968 words; the
/// powers `10^(597 2^i)` the split divides by and their neighbors; either side of the most bits
/// the split prints as one leaf without building powers, `floor(3.32 * 597) 2^i` for the least
/// `i` with `31 2^i > PRINT_HANDOFF` (31,712 with `PRINT_HANDOFF` at 248), and of the first
/// power it divides by, `10^(597 2^i)` (`10^9552`, 496 words); both computed from
/// `PRINT_HANDOFF`, so that they follow it when the benchmark `crossover print-handoff` resets
/// it.
#[test]
fn both_printing_methods_write_the_same_text() {
    let mut rng = Rng::new(597);
    let ones = |w: usize| (BigUint::from(1u32) << (64 * w)) - 1u32;
    let mut values: Vec<BigUint> = (1..=40)
        .flat_map(|w| [wide(&mut rng, w).into_parts().1, ones(w)])
        .collect();
    let ten = BigUint::from(10u32);
    for i in 0..8 {
        let words = 31usize << i;
        for w in [words - 1, words, words + 1] {
            values.extend([wide(&mut rng, w).into_parts().1, ones(w)]);
        }
        let p = ten.pow(597 << i);
        values.extend([&p - 1u32, &p + 1u32, p]);
    }
    let i = (0..)
        .find(|&i| 31usize << i > PRINT_HANDOFF)
        .expect("a power wider than the handoff");
    let leaf_bits = (597 * 332 / 100) << i;
    let two = BigUint::from(2u32);
    for bits in [leaf_bits - 1, leaf_bits, leaf_bits + 1] {
        let p = two.pow(bits);
        values.extend([&p - 1u32, p]);
    }
    let first = ten.pow(597 << i);
    values.extend([&first - 1u32, &first + 1u32, first]);
    for x in &values {
        assert_eq!(to_decimal_split(x), x.to_string(), "{} bits", x.bits());
    }
}

mod bench;
