//! Unbounded integers and exact rationals, from literals through arithmetic.

use crate::l01_16_elaboration::{errors, term, value};

#[test]
fn integers_widen_past_64_bits_and_narrow_back() {
    let src = "max = 9223372036854775807;\nnext = max + 1;\nback = next - 1;\n\
               same = back == max;\ngoogol = 10 ** 100;\n";
    assert_eq!(value(src, "next"), "9223372036854775808");
    assert_eq!(value(src, "same"), "true");
    assert_eq!(
        value(src, "googol"),
        format!("1{}", "0".repeat(100)),
        "`**` past 64 bits"
    );
    // The most negative machine integer is a literal past 64 bits, negated.
    let src = "lo = -9223372036854775808;\nn = lo - 1;\n";
    assert_eq!(value(src, "lo"), "-9223372036854775808");
    assert_eq!(value(src, "n"), "-9223372036854775809");
}

#[test]
fn big_literals_in_any_base_and_euclidean_division() {
    let src = "mask = 0xffff_ffff_ffff_ffff_ffff;\nbits = 0b1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000;\n\
               q = -100000000000000000000 div 7;\nr = -100000000000000000000 mod 7;\n\
               check = q * 7 + r;\nz = 100000000000000000000 div 0;\n";
    assert_eq!(value(src, "mask"), "1208925819614629174706175");
    assert_eq!(value(src, "bits"), "18446744073709551616");
    assert_eq!(value(src, "q"), "-14285714285714285715");
    assert_eq!(
        value(src, "r"),
        "5",
        "a Euclidean remainder is never negative"
    );
    assert_eq!(value(src, "check"), "-100000000000000000000");
    assert_eq!(value(src, "z"), "#divByZero");
}

#[test]
fn powers_of_zero_one_and_minus_one_stay_small() {
    let src = "a = 1 ** 100000000000000000000;\nb = (-1) ** 100000000000000000001;\n\
               c = 0 ** 100000000000000000000;\nd = 7 ** 0;\n";
    assert_eq!(value(src, "a"), "1");
    assert_eq!(value(src, "b"), "-1");
    assert_eq!(value(src, "c"), "0");
    assert_eq!(value(src, "d"), "1");
}

#[test]
fn a_number_past_the_size_limit_is_an_evaluator_error() {
    let src = "huge = 3 ** 10000000;\n";
    assert_eq!(
        value(src, "huge"),
        "error: a number beyond the evaluator's size limit"
    );
    let e = errors("x = 1e999999r;\n");
    assert_eq!(
        e,
        ["this rational is beyond the evaluator's size limit [1e999999r]"]
    );
}

#[test]
fn rationals_are_exact() {
    let src = "tenth = 0.1r;\nexact = tenth + 0.2r == 0.3r;\nfloaty = 0.1 + 0.2 == 0.3;\n\
               third = 1r / 3r;\nwhole = third + third + third;\nneg = -third * 2r;\n\
               fee = 2.5e-3r;\nbig = 1e30r / 7r;\n";
    assert_eq!(value(src, "exact"), "true");
    assert_eq!(value(src, "floaty"), "false");
    assert_eq!(value(src, "third"), "1r/3r");
    assert_eq!(value(src, "whole"), "1r");
    assert_eq!(value(src, "neg"), "-2r/3r");
    assert_eq!(value(src, "fee"), "1r/400r");
    assert_eq!(value(src, "big"), "1000000000000000000000000000000r/7r");
    assert_eq!(term(src, "third"), "(1r / 3r)");
}

#[test]
fn rational_division_by_zero_is_an_atom() {
    let src = "share(positional total, positional n) = total / n;\n\
               a = share(10r, 4r);\nb = share(10r, 0r);\nc = share(10r, 0r) else 0r;\n";
    assert_eq!(value(src, "a"), "5r/2r");
    assert_eq!(value(src, "b"), "#divByZero");
    assert_eq!(value(src, "c"), "0r");
}

#[test]
fn numbers_of_different_kinds_do_not_mix() {
    assert_eq!(
        value("a = 1r + 1;\n", "a"),
        "error: type error: Add applied to 1r, 1"
    );
    assert_eq!(
        value("b = 1r < 2.0;\n", "b"),
        "error: type error: Lt applied to 1r, 2.0"
    );
    // `==` across kinds is false: the values differ, though their order ties them by value.
    assert_eq!(value("c = 1 == 1.0;\n", "c"), "false");
}
