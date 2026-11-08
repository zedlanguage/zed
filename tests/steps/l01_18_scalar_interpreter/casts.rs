//! The checked casts: `T(x)` is `x` as a `T` when it is the same number, `#inexact` when a
//! number has no equal `T`, and `#invalid` when the source is not a `T` at all.

use super::x;
use zed_kernel::{Prim, Term, Value};
use zed_tests::step_helpers::l01_16_elaboration::errors;

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
    assert_eq!(x("rat(\"1/2\")"), "1r/2r");
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
        x("f64(2 ^ 60)"),
        "1152921504606847000.0",
        "the shortest digits that read back"
    );
    assert_eq!(x("f64(2 ^ 60 + 1)"), "#inexact", "2^60 + 1 needs 61 bits");
    assert_eq!(x("f64(3r/8r)"), "0.375");
    assert_eq!(x("f64(1r/3r)"), "#inexact");
    assert_eq!(x("f64(rat(1) / rat(2 ^ 1074))"), "5.0e-324");
    assert_eq!(x("f64(rat(1) / rat(2 ^ 1075))"), "#inexact");
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
    assert_eq!(
        errors("x = int(true);\n"),
        ["`int` does not take (true) [int(true)]"]
    );
    assert_eq!(
        errors("x = len(3);\n"),
        ["`len` does not take (3) [len(3)]"]
    );
}

/// `"p0" ++ "p1" ++ …`: each piece is longer than a block of a string holds, so the string is
/// held as a join of the pieces and a cast writes it out to read it.
fn joined(pieces: &[String]) -> String {
    let quoted: Vec<String> = pieces.iter().map(|p| format!("\"{p}\"")).collect();
    quoted.join(" ++ ")
}

#[test]
fn a_number_received_in_pieces_reads_as_one() {
    // An account balance sent in three packets: a sign and digits, digits, digits.
    let pieces = [
        format!("-{}", "1234567890".repeat(13)),
        "9876543210".repeat(13),
        "5".repeat(130),
    ];
    assert_eq!(x(&format!("int({})", joined(&pieces))), pieces.concat());
    // A character that is not a digit in the middle piece makes the whole text no int.
    let bad = [
        "1".repeat(130),
        format!("x{}", "1".repeat(130)),
        "1".repeat(130),
    ];
    assert_eq!(x(&format!("int({})", joined(&bad))), "#invalid");
    // A fraction whose `/` falls in the last piece, (2·10^387 + 1) / 4, in lowest terms as
    // `String` writes it.
    let fraction = [
        format!("2{}", "0".repeat(129)),
        "0".repeat(130),
        format!("{}1r/4r", "0".repeat(127)),
    ];
    assert_eq!(x(&format!("rat({})", joined(&fraction))), fraction.concat());
    // A decimal whose point falls in the first piece reads as the same text unjoined.
    let decimal = [
        format!("0.{}", "3".repeat(130)),
        "7".repeat(130),
        "1".repeat(130),
    ];
    assert_eq!(
        x(&format!(
            "rat({}) == rat(\"{}\")",
            joined(&decimal),
            decimal.concat()
        )),
        "true"
    );
    // A float of 393 digits after the point rounds to the nearest f64, and one past the
    // largest f64 is inexact, written in pieces as in one.
    let half = [
        format!("0.5{}", "0".repeat(130)),
        "0".repeat(130),
        format!("{}1", "0".repeat(130)),
    ];
    assert_eq!(x(&format!("f64({})", joined(&half))), "0.5");
    let huge = [
        format!("1{}", "0".repeat(130)),
        "0".repeat(130),
        "0".repeat(140),
    ];
    assert_eq!(x(&format!("f64({})", joined(&huge))), "#inexact");
}

#[test]
fn a_number_joined_from_a_thousand_pieces_reads_as_one() {
    // A `foldl` of `++` over a thousand pieces of 130 digits: the string is a tree whose middle
    // holds nodes of nodes, and each cast reads it in order. The chain is a kernel term, so
    // the text is joined by the evaluator as the program's `++` joins it.
    let pieces: Vec<String> = (0..1000)
        .map(|i| char::from(b'1' + (i % 9) as u8).to_string().repeat(130))
        .collect();
    let cast = |p: Prim, before: &str, after: &str| {
        let join = |a: Term, s: &str| Term::Prim(Prim::Concat, vec![a, Term::Lit(Value::str(s))]);
        let text = pieces
            .iter()
            .fold(Term::Lit(Value::str(before)), |t, s| join(t, s));
        let text = join(text, after);
        zed_kernel::eval(&Term::Prim(p, vec![text]))
            .unwrap()
            .to_string()
    };
    let digits = pieces.concat();
    assert_eq!(cast(Prim::CastInt, "-", ""), format!("-{digits}"));
    assert_eq!(cast(Prim::CastRat, "", "r"), format!("{digits}r"));
    let read = |s: &str| {
        zed_kernel::eval(&Term::Prim(Prim::CastF64, vec![Term::Lit(Value::str(s))]))
            .unwrap()
            .to_string()
    };
    assert_eq!(cast(Prim::CastF64, "0.", ""), read(&format!("0.{digits}")));
    // It differs from 1/9 in its 131st digit, far below half a unit in the last place of an
    // f64, so it rounds to the f64 nearest 1/9, as 21 ones do.
    assert_eq!(
        cast(Prim::CastF64, "0.", ""),
        read(&format!("0.{}", "1".repeat(21)))
    );
}
