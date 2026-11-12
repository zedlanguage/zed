//! Unbounded integers and exact rationals, from literals through arithmetic.

use zed_tests::step_helpers::l01_16_elaboration::{errors, term, value};

#[test]
fn integers_widen_past_64_bits_and_narrow_back() {
    let src = "max = 9223372036854775807;\nnext = max + 1;\nback = next - 1;\n\
               same = back == max;\ngoogol = 10^100;\n";
    assert_eq!(value(src, "next"), "9223372036854775808");
    assert_eq!(value(src, "same"), "true");
    assert_eq!(
        value(src, "googol"),
        format!("1{}", "0".repeat(100)),
        "`^` past 64 bits"
    );
    // The most negative machine integer is a literal past 64 bits, negated.
    let src = "lo = -9223372036854775808;\nn = lo - 1;\n";
    assert_eq!(value(src, "lo"), "-9223372036854775808");
    assert_eq!(value(src, "n"), "-9223372036854775809");
}

#[test]
fn big_literals_in_any_base_and_euclidean_division() {
    let src = "whole(positional v: int) = v;\nmask = 0xffff_ffff_ffff_ffff_ffff;\nbits = 0b1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000;\n\
               q = -100000000000000000000 div 7;\nr = -100000000000000000000 mod 7;\n\
               check = q * 7 + r;\nz = 100000000000000000000 div whole(0);\n";
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
    let src = "a = 1^100000000000000000000;\nb = (-1)^100000000000000000001;\n\
               c = 0^100000000000000000000;\nd = 7^0;\n";
    assert_eq!(value(src, "a"), "1");
    assert_eq!(value(src, "b"), "-1");
    assert_eq!(value(src, "c"), "0");
    assert_eq!(value(src, "d"), "1");
}

#[test]
fn a_number_far_past_a_machine_word_is_exact() {
    // `3 ^ 10000000` has 4.7 million digits and `1e999999r` a million: both are kept as
    // powers of primes, so their remainders, order and quotients come without the digits.
    let src = "huge = 3^10000000;\nlast = huge mod 1000;\nbelow = huge < 3^10000001;\n\
               x = 1e999999r;\nten = x / 1e999998r;\ntiny = 1r / x * 1e1000000r;\n";
    assert_eq!(value(src, "last"), "1");
    assert_eq!(value(src, "below"), "true");
    assert_eq!(value(src, "ten"), "10r");
    assert_eq!(value(src, "tiny"), "10r");
}

#[test]
fn rationals_are_exact() {
    let src = "tenth = 0.1r;\nexact = tenth + 0.2r == 0.3r;\nfloaty = 0.1f64 + 0.2f64 == 0.3f64;\n\
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
    // Values of two kinds do not mix; the checker finds it before anything runs.
    assert_eq!(
        errors("x = 1r;\na = x + f64(1);\n"),
        ["`+` does not take (1r, f64): no arrow of `+` takes these types. [x + f64(1)]"]
    );
    // A name bound to an integer literal is an `int`, and does not mix with a `rat`.
    assert_eq!(
        errors("i = 1;\na = 1r + i;\n"),
        ["`+` does not take (1r, 1): no arrow of `+` takes these types. [1r + i]"]
    );
    // A literal with a suffix keeps its carrier, and is rejected with the forms to write; a
    // literal without one takes the carrier the other side expects, exactly (steps L1.26,
    // L1.26a, L1.26b).
    assert_eq!(
        errors("b = 1r < 2.0f64;\n"),
        [
            "The suffix makes the literal `2.0f64` an `f64`, never `rat`. Try `b = 1r < 2.0` instead.\n  fixes, each checked \
             here:\n    b = 1r < 2.0;     the literal is then exactly 2.0, a rat\n    b = 1r < 2.0r;    \
             the literal is then exactly 2.0, a rat [2.0f64]"
        ]
    );
    // Two literals without a suffix, one a decimal, have nothing to give them a carrier.
    assert_eq!(
        errors("c = 1 == 1.0;\n"),
        [
            "Nothing gives the literal `1.0` a carrier. Try `c = 1 == 1.0f64` instead.\n  fixes, \
             each checked here:\n    c = 1 == 1.0f64;    c is true\n    c = 1 == 1.0r;      c is \
             true [1.0]"
        ]
    );
    assert_eq!(value("a = 1r + 1;\n", "a"), "2r");
    assert_eq!(value("b = 1r < 2;\n", "b"), "true");
    assert_eq!(value("c = 1 == 1.0f64;\n", "c"), "true");
}
