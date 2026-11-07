//! The references' reading of an integer (`zedrt::try_parse_int`) at any number of digits
//! (item CORPUS-int-cap). It refused more than 4300 digits, a limit DESIGN does not have; it now
//! reads the digits by halves, the method of `zed_kernel::num::read_digits`, with num-bigint's
//! product (the references do not use the kernel). Each value is checked against num-bigint's
//! own reading and against the kernel's reader.

use num_bigint::{BigInt, Sign};
use zed_corpus_ref::zedrt::{parse_int, try_parse_int};
use zed_kernel::num::read_digits;
use zed_tests::instances::Rng;
use zed_tests::scaling;

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

/// A number of 4300 digits (the old limit), of 4301 (refused before) and of 100,000 reads as
/// num-bigint and the kernel's reader read its digits: plain, signed, with `_` between digits,
/// with spaces around it, and in another script.
#[test]
fn a_number_of_any_length_reads_as_num_bigint_and_the_kernel_read_it() {
    let mut rng = Rng::new(4301);
    for len in [4300, 4301, 100_000] {
        let plain = digits(&mut rng, len);
        let expected: BigInt = plain.parse().expect("digits");
        let kernel = BigInt::from_biguint(Sign::Plus, read_digits(&plain));
        assert_eq!(kernel, expected, "{len} digits: the kernel's reader");
        let negative = -expected.clone();
        let padded = format!("000{plain}");
        let texts = [
            (plain.clone(), &expected),
            (format!("+{plain}"), &expected),
            (format!("-{plain}"), &negative),
            (format!("-{}", marked(&mut rng, &padded)), &negative),
            (format!(" \t{plain}\n"), &expected),
            (
                arabic_indic(&format!("-{}", marked(&mut rng, &plain))),
                &negative,
            ),
        ];
        for (text, value) in texts {
            assert_eq!(try_parse_int(&text).as_ref(), Some(value), "{len} digits");
        }
    }
}

/// Zeros of any length and any sign read as 0, and the powers of ten and the nines either side
/// of 4300 digits read exactly.
#[test]
fn zeros_nines_and_powers_of_ten_read_exactly() {
    for len in [1, 4300, 4301, 20_000] {
        let zeros = "0".repeat(len);
        for text in [zeros.clone(), format!("-{zeros}"), format!("+{zeros}")] {
            assert_eq!(try_parse_int(&text), Some(BigInt::from(0)), "{len} zeros");
        }
        let nines = "9".repeat(len);
        let ten = format!("1{zeros}");
        for text in [nines, ten] {
            let expected: BigInt = text.parse().expect("digits");
            assert_eq!(try_parse_int(&text), Some(expected), "{text}");
        }
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

/// Reading a number of 100,000 and of 800,000 digits, each text built before timing. The reading
/// by halves is O(M(n) log n), and O(M(n)) with num-bigint's Toom-3 product, about n^1.46, whose
/// levels' costs fall geometrically: 8^1.46 is 20.9, within the limit of 24 for power 1. num-bigint
/// reading the text whole, O(n^2), fails it (COMPLEXITY.md F38).
#[test]
fn reading_a_long_number_scales() {
    let texts = scaling::inputs(100_000, |n| {
        let mut rng = Rng::new(n as u64);
        format!("-{}", digits(&mut rng, n))
    });
    scaling::check("reading an integer of n digits", 100_000, |n| {
        let value = try_parse_int(&texts[&n]).expect("digits");
        assert!(value < BigInt::from(0));
    });
}
