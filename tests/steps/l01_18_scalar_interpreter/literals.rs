//! A float literal is correctly rounded to the nearest f64, ties to even (DESIGN.md
//! sec:domains). It is an error when it rounds to infinity, or to zero while its digits are
//! not all zero; a literal of zero digits is zero whatever its exponent. Each literal read as
//! an f64 is written with `f64`: a decimal literal that nothing gives a carrier is rejected
//! (L1.26b).

use zed_kernel::num::LiteralRounding;

use super::x;
use zed_tests::step_helpers::l01_16_elaboration::{elab, errors};

/// `zed_kernel::num::literal_f64` of a decimal; every text of these tests is one.
fn literal_f64(text: &str) -> Result<f64, LiteralRounding> {
    zed_kernel::num::literal_f64(text).expect("a decimal")
}

/// `zed_kernel::num::literal_f32` of a decimal.
fn literal_f32(text: &str) -> Result<f32, LiteralRounding> {
    zed_kernel::num::literal_f32(text).expect("a decimal")
}

#[test]
fn a_price_reads_as_the_nearest_f64() {
    assert_eq!(x("0.1f64"), "0.1");
    assert_eq!(x("0.1f64 == 0.1000000000000000055511151231257827"), "true");
    assert_eq!(literal_f64("0.1"), Ok(0.1));
    assert_eq!(literal_f64("19.99"), Ok(19.99));
    // Halfway between 2^53 and 2^53 + 2: the tie goes to the even significand.
    assert_eq!(literal_f64("9007199254740993.0"), Ok(9007199254740992.0));
    assert_eq!(literal_f64("9007199254740995.0"), Ok(9007199254740996.0));
}

#[test]
fn a_literal_beyond_the_largest_f64_is_an_error() {
    assert_eq!(
        errors("distance = 1e400f64;\n"),
        [
            "`1e400` is larger than the largest f64, 1.7976931348623157e308, so as an f64 it rounds to infinity. Write `1e400r` for the exact rational, or a number within the range of f64. [1e400f64]"
        ]
    );
    // The sign is not part of the literal: `-1e400` fails on `1e400`.
    assert_eq!(
        errors("debt = -1e400f64;\n"),
        [
            "`1e400` is larger than the largest f64, 1.7976931348623157e308, so as an f64 it rounds to infinity. Write `1e400r` for the exact rational, or a number within the range of f64. [1e400f64]"
        ]
    );
    // Just above the largest f64, but nearer it than to the next power of two: it rounds down.
    assert_eq!(x("1.7976931348623158e308f64"), "1.7976931348623157e308");
    assert_eq!(
        literal_f64("1.7976931348623159e308"),
        Err(LiteralRounding::Infinite)
    );
}

#[test]
fn a_nonzero_literal_below_the_least_subnormal_is_an_error() {
    assert_eq!(
        errors("tolerance = 1e-400f64;\n"),
        [
            "`1e-400` is not zero, and it lies nearer to zero than to the least positive f64, \
             5.0e-324, so as an f64 it rounds to zero. Write `1e-400r` for the exact rational, \
             or `0.0` if zero is meant. [1e-400f64]"
        ]
    );
    // Below half the least subnormal it rounds to zero; above half, up to it.
    assert_eq!(literal_f64("2e-324"), Err(LiteralRounding::Zero));
    assert_eq!(x("3e-324f64"), "5.0e-324");
}

#[test]
fn a_subnormal_literal_is_accepted() {
    assert_eq!(x("5e-324f64"), "5.0e-324");
    assert_eq!(x("2.2250738585072009e-308f64"), "2.225073858507201e-308");
    assert_eq!(x("1e-310f64"), "1.0e-310");
}

#[test]
fn zero_digits_are_zero_at_any_exponent() {
    assert_eq!(x("0.0f64"), "0.0");
    assert_eq!(x("0e999f64"), "0.0");
    assert_eq!(x("0.000e-99999f64"), "0.0");
    assert_eq!(x("-0.0f64"), "-0.0");
    assert_eq!(x("String(-0e400f64)"), "\"-0.0\"");
}

#[test]
fn a_long_digit_string_with_a_huge_exponent_rounds_by_its_value() {
    let ones = "1".repeat(500);
    let zeros = "0".repeat(500);
    // 1.11…e-200 with 500 digits before the point is about 1.1e299: finite.
    assert_eq!(x(&format!("{ones}.0e-200f64")), "1.1111111111111112e299");
    // The same digits at e-100 are about 1.1e399: infinite.
    assert_eq!(
        literal_f64(&format!("{ones}.0e-100")),
        Err(LiteralRounding::Infinite)
    );
    // 500 zeros after the point put the 1 at 1e-501, then e200 brings it to 1e-301.
    assert_eq!(x(&format!("0.{zeros}1e200f64")), "1.0e-301");
    assert_eq!(
        literal_f64(&format!("0.{zeros}1e-10")),
        Err(LiteralRounding::Zero)
    );
    // An exponent past any machine integer still rounds by value.
    assert_eq!(
        literal_f64("1e99999999999999999999999"),
        Err(LiteralRounding::Infinite)
    );
    assert_eq!(
        literal_f64("1e-99999999999999999999999"),
        Err(LiteralRounding::Zero)
    );
    assert_eq!(literal_f64("0e99999999999999999999999"), Ok(0.0));
}

#[test]
fn an_f32_literal_rounds_by_the_same_rule() {
    assert_eq!(literal_f32("0.1"), Ok(0.1f32));
    assert_eq!(literal_f32("1e39"), Err(LiteralRounding::Infinite));
    assert_eq!(literal_f32("1e-46"), Err(LiteralRounding::Zero));
    assert_eq!(literal_f32("1e-45"), Ok(f32::from_bits(1)));
    assert_eq!(literal_f32("3.4028235e38"), Ok(f32::MAX));
    assert_eq!(literal_f32("0e99"), Ok(0.0));
}

#[test]
fn every_out_of_range_literal_of_a_unit_is_reported() {
    let e = elab("a = 1e400f64;\nb = 1e-400f64;\nc = 2.5f64;\n").unwrap_err();
    assert_eq!(e.len(), 2, "{e:?}");
}

/// A literal of `n` threes, a one and an exponent that brings it near 1, so every digit counts.
pub(crate) fn digits_near_one(n: usize) -> String {
    format!("{}1.0e-{n}", "3".repeat(n))
}

/// Just above the point halfway between 1 and the next `f64`, with `n` zeros before the last
/// digit, so the digits are compared with the halfway point's to the last one.
pub(crate) fn digits_above_a_tie(n: usize) -> String {
    format!(
        "1.00000000000000011102230246251565404236316680908203125{}1",
        "0".repeat(n)
    )
}

/// The sample of Nigel Tao's corpus in `tests/data/parse-number-fxx`, whose source, license
/// and choice of lines are in that directory: lines of the `f16`, `f32` and `f64` encodings in
/// hex and a float literal. zed-kernel's `float_text::tests` checks every line in all three
/// formats.
const CORPUS: &str = include_str!("../../data/parse-number-fxx/sample.txt");

/// `m` texts of the corpus with their `f64` encodings, the `i`th the corpus's `i mod 8000`th:
/// the inputs of `bench::literals`'s reading and printing of many literals
/// (TESTS-float-text-corpus).
pub(super) fn corpus_lines(m: usize) -> Vec<(&'static str, u64)> {
    let lines: Vec<(&str, u64)> = CORPUS
        .lines()
        .filter(|line| !line.starts_with('#'))
        .map(|line| {
            let fields: Vec<&str> = line.split(' ').collect();
            let [_, _, f64, text] = fields[..] else {
                panic!("a corpus line of four fields: `{line}`");
            };
            (text, u64::from_str_radix(f64, 16).expect("hex"))
        })
        .collect();
    lines.iter().cycle().take(m).copied().collect()
}

#[test]
fn corpus_literals_read_to_their_encodings_and_print_back() {
    // The inputs of `bench::literals`'s reading and printing at a small size, past the end of
    // the corpus: each text reads to its encoding, and each encoding prints as a text that
    // reads back to it.
    let lines = corpus_lines(9_000);
    assert_eq!(lines[8_000], lines[0]);
    for (text, bits) in lines {
        let x = f64::from_bits(bits);
        let read = zed_kernel::num::read_f64_ieee(text).expect("a decimal");
        assert_eq!(read.to_bits(), bits, "`{text}`");
        let shown = zed_kernel::num::show_f64(x);
        let back = zed_kernel::num::read_f64_ieee(&shown);
        assert!(
            back == Some(x) || x.is_infinite(),
            "`{text}` shown as `{shown}`"
        );
    }
}

#[test]
fn a_long_literal_rounds_by_every_digit() {
    // The inputs of `bench::literals` at a small size: 3331.0e-3 and the digits above a tie.
    assert_eq!(x(&format!("{}f64", digits_near_one(3))), "3.331");
    assert_eq!(literal_f64(&digits_near_one(3)), Ok(3.331));
    assert_eq!(literal_f64(&digits_above_a_tie(3)), Ok(1.0 + f64::EPSILON));
    // Exactly at the tie, the even significand, 1.
    assert_eq!(
        literal_f64("1.00000000000000011102230246251565404236316680908203125"),
        Ok(1.0)
    );
    assert_eq!(x(&format!("0.{}1e3f64", "3".repeat(3))), "333.1");
}
