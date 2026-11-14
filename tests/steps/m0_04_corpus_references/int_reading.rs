//! The references' reading of an integer (`zedrt::try_parse_int`) at any number of digits
//! (item CORPUS-int-cap). It refused more than 4300 digits, a limit DESIGN does not have; it now
//! reads the digits by halves, the method of `zed_kernel::num::read_digits`, joining the halves
//! with powers of five and a number-theoretic transform product (`zedrt::product`; the references
//! do not use the kernel). Each value is checked against num-bigint's own reading and against the
//! kernel's reader, and the product against num-bigint's. The text read is what DESIGN L1.18 says
//! `int(s)` reads, an optional `-` and ASCII digits; the texts it makes `#invalid` (a `+`, white
//! space, `_`, other scripts) are checked at the same lengths (FAIL-ref-text-reading).

use num_bigint::{BigInt, BigUint, Sign};
use zed_corpus_ref::zedrt::product::{
    Factor, KEPT_WORDS, TRANSFORM_WORDS, mul, transform_len, transform_mul, twiddles,
};
use zed_corpus_ref::zedrt::{LEAF_DIGITS, parse_int, try_parse_int};
use zed_kernel::num::read_digits;
use zed_tests::instances::Rng;

/// `len` random digits, the first not 0.
fn digits(rng: &mut Rng, len: usize) -> String {
    (0..len)
        .map(|i| char::from(b'0' + rng.int(i64::from(i == 0), 9) as u8))
        .collect()
}

/// `text` with `_` between some of its digits.
fn marked(rng: &mut Rng, text: &str) -> String {
    text.chars()
        .enumerate()
        .flat_map(|(i, c)| {
            let mark = i > 0 && rng.int(0, 6) == 0;
            mark.then_some('_').into_iter().chain([c])
        })
        .collect()
}

/// `text` in Arabic-Indic digits (U+0660 to U+0669).
fn arabic_indic(text: &str) -> String {
    text.chars()
        .map(|c| match c.to_digit(10) {
            Some(d) => char::from_u32(0x660 + d).expect("an Arabic-Indic digit"),
            None => c,
        })
        .collect()
}

/// A number of `len` random digits reads as num-bigint and the kernel's reader read its digits,
/// plain, after `-` and with leading zeros; the texts DESIGN L1.18 makes `#invalid` at the same
/// length are read as nothing: a `+`, white space around it, `_` between digits, and the digits
/// in another script, alone or mixed with ASCII digits.
pub(super) fn reads_a_number_of_length(rng: &mut Rng, len: usize) {
    let plain = digits(rng, len);
    let expected: BigInt = plain.parse().expect("digits");
    let kernel = BigInt::from_biguint(Sign::Plus, read_digits(&plain));
    assert_eq!(kernel, expected, "{len} digits: the kernel's reader");
    let negative = -expected.clone();
    let texts = [
        (plain.clone(), &expected),
        (format!("-{plain}"), &negative),
        (format!("000{plain}"), &expected),
        (format!("-000{plain}"), &negative),
    ];
    for (text, value) in texts {
        assert_eq!(try_parse_int(&text).as_ref(), Some(value), "{len} digits");
    }
    let mut mixed = arabic_indic(&plain);
    mixed.insert(0, '7');
    let invalid = [
        format!("+{plain}"),
        format!(" \t{plain}\n"),
        format!("-{plain} "),
        format!("1_{}", marked(rng, &plain)),
        arabic_indic(&plain),
        format!("-{}", arabic_indic(&plain)),
        mixed,
    ];
    for text in invalid {
        assert_eq!(try_parse_int(&text), None, "{len} digits: {text:?}");
    }
}

/// A number of 4300 digits (the old limit) and of 4301 (refused before) reads as num-bigint
/// read it; 100,000 digits are in `bench/digits.rs`.
#[test]
fn a_number_of_any_length_reads_as_num_bigint_and_the_kernel_read_it() {
    let mut rng = Rng::new(4301);
    for len in [1, 9, 4300, 4301] {
        reads_a_number_of_length(&mut rng, len);
    }
}

/// Zeros of length `len`, alone or after `-`, read as 0 (after `+` as nothing, DESIGN L1.18),
/// and the power of ten and the nines of that length read exactly.
pub(super) fn zeros_nines_and_a_power_of_ten(len: usize) {
    let zeros = "0".repeat(len);
    for text in [zeros.clone(), format!("-{zeros}")] {
        assert_eq!(try_parse_int(&text), Some(BigInt::from(0)), "{len} zeros");
    }
    assert_eq!(try_parse_int(&format!("+{zeros}")), None, "+{len} zeros");
    let nines = "9".repeat(len);
    let ten = format!("1{zeros}");
    for text in [nines, ten] {
        let expected: BigInt = text.parse().expect("digits");
        assert_eq!(try_parse_int(&text), Some(expected), "{text}");
    }
}

/// Either side of 4300 digits; 20,000 digits are in `bench/digits.rs`.
#[test]
fn zeros_nines_and_powers_of_ten_read_exactly() {
    for len in [1, 4300, 4301] {
        zeros_nines_and_a_power_of_ten(len);
    }
}

/// A long text that is not an integer is still refused, with the same message.
#[test]
fn a_long_text_that_is_not_an_integer_is_refused() {
    let long = "7".repeat(5000);
    let texts = [
        format!("_{long}"),
        format!("{long}_"),
        format!("{long}__1"),
        format!("+-{long}"),
        format!("{long}a"),
        format!("{long} 1"),
        format!("{long}.0"),
        "-".to_string(),
        String::new(),
    ];
    for text in texts {
        assert_eq!(try_parse_int(&text), None, "{text}");
        assert_eq!(parse_int(&text), Err(format!("invalid int: {text}")));
    }
}

/// A natural of `words` random 32-bit words, the top one not 0.
fn natural(rng: &mut Rng, words: usize) -> BigUint {
    let mut digits: Vec<u32> = (0..words)
        .map(|_| rng.int(0, i64::from(u32::MAX)) as u32)
        .collect();
    if let Some(top) = digits.last_mut() {
        *top = (*top).max(1);
    }
    BigUint::new(digits)
}

/// The transform's product equals num-bigint's: zero, one word, factors whose coefficients are
/// all ones (the largest sums the transform holds), lengths that fill a power of two exactly
/// and one past it, squares (two transforms in place of three), unbalanced factors, and `mul`
/// on both sides of its crossover. The squares of all ones at 754, 2,900 and 11,136 words have
/// the largest sums of coefficients of 26, 25 and 24 bits, and one word more takes a bit less.
#[test]
fn the_transform_product_equals_num_bigint() {
    let mut rng = Rng::new(2048);
    let ones = |words: usize| BigUint::new(vec![u32::MAX; words]);
    let zero = BigUint::default();
    let mut pairs = vec![
        (zero.clone(), zero.clone()),
        (zero.clone(), natural(&mut rng, 300)),
        (BigUint::from(1u32), BigUint::from(1u32)),
        (BigUint::from(u32::MAX), BigUint::from(u32::MAX)),
        (BigUint::from(1u32), natural(&mut rng, 777)),
        (ones(4096), ones(4096)),
        (ones(1), ones(5000)),
        (natural(&mut rng, 3), natural(&mut rng, 9001)),
    ];
    for words in [754, 755, 2900, 2901, 11_136, 11_137] {
        pairs.push((ones(words), ones(words)));
    }
    for words in [1, 2, 3, 7, 8, 9, 255, 256, 257, 1000, 1024, 1025] {
        pairs.push((natural(&mut rng, words), natural(&mut rng, words)));
        let square = natural(&mut rng, words);
        pairs.push((square.clone(), square));
        pairs.push((natural(&mut rng, words), natural(&mut rng, 2 * words + 1)));
    }
    let crossover = TRANSFORM_WORDS as usize;
    for words in [crossover - 1, crossover, crossover + 1] {
        pairs.push((natural(&mut rng, words), natural(&mut rng, words)));
        pairs.push((natural(&mut rng, words), natural(&mut rng, 3 * words)));
    }
    for (a, b) in pairs {
        let expected = &a * &b;
        let what = format!("{} and {} bits", a.bits(), b.bits());
        assert_eq!(transform_mul(&a, &b), expected, "transform_mul, {what}");
        assert_eq!(
            transform_mul(&b, &a),
            expected,
            "transform_mul swapped, {what}"
        );
        assert_eq!(mul(&a, &b), expected, "mul, {what}");
    }
}

/// A factor's square and its products equal num-bigint's, kept and plain, for factors below and
/// at each crossover and above them, random and with every coefficient all ones; the other
/// factor zero, one, as long as the kept one (the kept transform's length), half as long or
/// much shorter (a new length).
#[test]
fn a_kept_factor_multiplies_as_num_bigint_does() {
    let mut rng = Rng::new(4096);
    let ones = |words: usize| BigUint::new(vec![u32::MAX; words]);
    let (kept, crossover) = (KEPT_WORDS as usize, TRANSFORM_WORDS as usize);
    for words in [
        1,
        kept - 1,
        kept,
        kept + 1,
        crossover - 1,
        crossover,
        crossover + 1,
        3 * crossover,
    ] {
        for value in [natural(&mut rng, words), ones(words)] {
            let roots = twiddles(transform_len(value.bits(), value.bits()));
            let factors = [
                Factor::new(value.clone(), value.bits(), &roots),
                Factor::plain(value.clone()),
            ];
            for factor in factors {
                assert_eq!(factor.value(), &value);
                let what = format!("a factor of {} bits", value.bits());
                assert_eq!(factor.square(&roots), &value * &value, "square of {what}");
                let others = [
                    BigUint::default(),
                    BigUint::from(1u32),
                    natural(&mut rng, kept.min(words)),
                    natural(&mut rng, words.div_ceil(2)),
                    natural(&mut rng, words),
                    ones(words),
                ];
                for a in others {
                    let expected = &a * &value;
                    assert_eq!(
                        factor.times(&a, &roots),
                        expected,
                        "{} bits times {what}",
                        a.bits()
                    );
                }
            }
        }
    }
}

/// Texts long enough that the reading's products go through the transform read as num-bigint
/// reads them: random digits, nines (every coefficient of the parts at its largest), and a
/// length of a power of two times `LEAF_DIGITS` and one past it.
#[test]
fn a_number_read_by_the_transform_reads_as_num_bigint_read_it() {
    let mut rng = Rng::new(40);
    // A power `5^d` has about 0.073 d words and a part of d digits about 0.104 d. At 40 digits a
    // word of `TRANSFORM_WORDS`, the powers below the last from about 1.2 times `KEPT_WORDS` up
    // keep their transforms; at the power of two the last product, of two factors of more than
    // `TRANSFORM_WORDS` words, is by the transform too; one past it, the last power is squared
    // by its kept transform and multiplies a part of one digit.
    let long = 40 * TRANSFORM_WORDS as usize;
    let power = LEAF_DIGITS * (long / LEAF_DIGITS).next_power_of_two();
    for len in [long, power, power + 1] {
        for text in [digits(&mut rng, len), "9".repeat(len)] {
            let expected: BigInt = text.parse().expect("digits");
            assert_eq!(try_parse_int(&text), Some(expected), "{len} digits");
        }
    }
}
