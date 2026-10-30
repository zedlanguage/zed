//! The checked casts: `T(x)` is `x` as a `T` when it is the same number, `#inexact` when a
//! number has no equal `T`, and `#invalid` when the source is not a `T` at all.

use super::x;

#[test]
fn reading_a_quantity_from_a_form_field() {
    assert_eq!(x("int(\"42\")"), "42");
    assert_eq!(x("int(\"-7\")"), "-7");
    assert_eq!(x("int(\"4 2\")"), "#invalid");
    assert_eq!(x("int(\"\")"), "#invalid");
    assert_eq!(
        x("int(\"+5\")"),
        "#invalid",
        "a sign is only `-`, as `String` writes it"
    );
    assert_eq!(x("int(\"twelve\") else 1"), "1");
    assert_eq!(
        x("int(\"123456789012345678901234567890\")"),
        "123456789012345678901234567890"
    );
}

#[test]
fn a_float_to_int_must_be_whole() {
    assert_eq!(x("int(3.0)"), "3");
    assert_eq!(x("int(-2.5)"), "#inexact");
    assert_eq!(x("int(1.0e20)"), "100000000000000000000");
    assert_eq!(x("int(1.0 / 0.0)"), "#invalid");
    assert_eq!(x("int(0.0 / 0.0)"), "#invalid");
    assert_eq!(x("int(7r/2r)"), "#inexact");
    assert_eq!(x("int(rat(6) / rat(2))"), "3");
}

#[test]
fn a_float_is_an_exact_rational() {
    assert_eq!(x("rat(0.5)"), "1r/2r");
    assert_eq!(x("rat(0.1)"), "3602879701896397r/36028797018963968r");
    assert_eq!(x("rat(-3)"), "-3r");
    assert_eq!(x("rat(1.0 / 0.0)"), "#invalid");
}

#[test]
fn a_rational_reads_as_string_writes_it_or_as_a_decimal() {
    assert_eq!(x("rat(\"1r/3r\")"), "1r/3r");
    assert_eq!(x("rat(\"2/4\")"), "1r/2r");
    assert_eq!(x("rat(\"3r\")"), "3r");
    assert_eq!(x("rat(\"0.25\")"), "1r/4r");
    assert_eq!(x("rat(\"1/0\")"), "#invalid");
    assert_eq!(x("rat(\".5\")"), "#invalid");
    assert_eq!(x("rat(String(5r/7r)) == 5r/7r"), "true");
}

#[test]
fn a_number_to_f64_must_be_exactly_representable() {
    assert_eq!(x("f64(3)"), "3.0");
    assert_eq!(
        x("f64(2 ** 60)"),
        "1152921504606847000.0",
        "the shortest digits that read back"
    );
    assert_eq!(x("f64(2 ** 60 + 1)"), "#inexact", "2^60 + 1 needs 61 bits");
    assert_eq!(x("f64(3r/8r)"), "0.375");
    assert_eq!(x("f64(1r/3r)"), "#inexact");
    assert_eq!(x("f64(rat(1) / rat(2 ** 1074))"), "5.0e-324");
    assert_eq!(x("f64(rat(1) / rat(2 ** 1075))"), "#inexact");
}

#[test]
fn a_float_reads_correctly_rounded_and_overflow_is_inexact() {
    assert_eq!(x("f64(\"0.1\") == 0.1"), "true");
    assert_eq!(x("f64(\"2.5e-3\")"), "0.0025");
    assert_eq!(x("f64(\"7\")"), "7.0");
    assert_eq!(x("f64(\"1e400\")"), "#inexact");
    assert_eq!(x("f64(\"-1e400\")"), "#inexact");
    assert_eq!(x("f64(\"1,5\")"), "#invalid");
    assert_eq!(x("f64(\"infinity\")"), "#invalid");
    assert_eq!(x("f64(\"1e\")"), "#invalid");
}

#[test]
fn a_cast_of_a_kind_it_does_not_take_is_a_type_error() {
    assert!(
        x("int(true)").starts_with("error: type error"),
        "{}",
        x("int(true)")
    );
    assert!(x("len(3)").starts_with("error: type error"));
}
