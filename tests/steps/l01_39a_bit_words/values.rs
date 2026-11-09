//! The cases DESIGN.md step L1.39a names, through the surface: each word at 0, 1, `2 ^ 63` and
//! `2 ^ 64 + 1` where its domain allows.

use super::x;

#[test]
fn the_named_cases() {
    assert_eq!(x("bitNot(5, width: 3)"), "2");
    assert_eq!(x("rotl(8, 1, width: 4)"), "1");
    assert_eq!(x("trailingZeros(0, width: 8)"), "8");
}

#[test]
fn masking_a_byte_and_packing_two() {
    let src = "word = 51966;\nlow = bitAnd(word, 255);\nhigh = shr(word, 8);\n\
               packed = bitOr(shl(high, 8), low);\nflipped = bitXor(word, 65535);\n";
    let v = |n| zed_tests::step_helpers::l01_16_elaboration::value(src, n);
    assert_eq!(v("low"), "254");
    assert_eq!(v("high"), "202");
    assert_eq!(v("packed"), "51966");
    assert_eq!(v("flipped"), "13569");
}

#[test]
fn a_receiver_is_the_first_operand() {
    assert_eq!(x("12.bitAnd(10)"), "8");
    assert_eq!(x("255.popCount"), "8");
    assert_eq!(x("1.leadingZeros(width: 32)"), "31");
    assert_eq!(x("1.rotr(1, width: 8)"), "128");
}

#[test]
fn each_word_at_zero_and_one() {
    for (e, v) in [
        ("bitAnd(0, 1)", "0"),
        ("bitOr(0, 1)", "1"),
        ("bitXor(1, 1)", "0"),
        ("bitNot(0, width: 1)", "1"),
        ("bitNot(1, width: 1)", "0"),
        ("shl(1, 0)", "1"),
        ("shl(0, 1)", "0"),
        ("shr(1, 1)", "0"),
        ("shr(0, 0)", "0"),
        ("popCount(0)", "0"),
        ("popCount(1)", "1"),
        ("leadingZeros(0, width: 1)", "1"),
        ("leadingZeros(1, width: 1)", "0"),
        ("trailingZeros(1, width: 1)", "0"),
        ("rotl(1, 1, width: 1)", "1"),
        ("rotr(0, 1, width: 1)", "0"),
        ("f64Bits(0.0)", "0"),
        ("f64Bits(1.0)", "4607182418800017408"),
    ] {
        assert_eq!(x(e), v, "{e}");
    }
}

#[test]
fn each_word_at_two_to_the_63() {
    let p63 = "9223372036854775808";
    for (e, v) in [
        ("bitAnd(2^63, 2^63 + 1)", p63),
        ("bitOr(2^63, 1)", "9223372036854775809"),
        ("bitXor(2^63, 2^63)", "0"),
        ("bitNot(2^63, width: 64)", "9223372036854775807"),
        ("shl(1, 63)", p63),
        ("shl(-1, 63)", "-9223372036854775808"),
        ("shr(2^63, 63)", "1"),
        ("shr(-(2^63) - 1, 63)", "-2"),
        ("popCount(2^63)", "1"),
        ("leadingZeros(2^63, width: 64)", "0"),
        ("trailingZeros(2^63, width: 64)", "63"),
        ("rotl(2^63, 1, width: 64)", "1"),
        ("rotr(1, 1, width: 64)", p63),
        ("f64Bits(-0.0)", p63),
    ] {
        assert_eq!(x(e), v, "{e}");
    }
}

#[test]
fn each_word_at_two_to_the_64_plus_one() {
    for (e, v) in [
        ("bitAnd(2^64 + 1, 3)", "1"),
        ("bitOr(2^64 + 1, 2)", "18446744073709551619"),
        ("bitXor(2^64 + 1, 2^64)", "1"),
        ("bitNot(2^64 + 1, width: 65)", "18446744073709551614"),
        ("shl(2^64 + 1, 1)", "36893488147419103234"),
        ("shr(2^64 + 1, 64)", "1"),
        ("shr(-(2^64) - 1, 1)", "-9223372036854775809"),
        ("popCount(2^64 + 1)", "2"),
        ("leadingZeros(2^64 + 1, width: 70)", "5"),
        ("trailingZeros(2^64 + 1, width: 65)", "0"),
        ("rotl(2^64 + 1, 1, width: 65)", "3"),
        ("rotr(2^64 + 1, 1, width: 65)", "27670116110564327424"),
    ] {
        assert_eq!(x(e), v, "{e}");
    }
}

#[test]
fn a_shift_count_is_never_masked() {
    assert_eq!(x("shl(1, 64)"), "18446744073709551616");
    assert_eq!(x("shl(1, 200) == 2^200"), "true");
    assert_eq!(x("shr(2^200, 199)"), "2");
    assert_eq!(x("shr(5, 1000)"), "0");
    assert_eq!(x("shr(-5, 1000)"), "-1");
    assert_eq!(
        x("rotl(5, 1000003, width: 3)"),
        x("rotl(5, 1000003 mod 3, width: 3)")
    );
}

#[test]
fn a_failure_passes_through() {
    assert_eq!(x("bitAnd(#oops, 1)"), "#oops");
    assert_eq!(x("shl(1, #late)"), "#late");
    // Two failures combine as they do under every strict word.
    assert_eq!(x("rotl(#a, #b, width: 8)"), x("#a + #b"));
}
