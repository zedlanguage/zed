//! Completeness cases for step M0.4 (TEST-complete-m0, author P189): the shared helpers of the
//! references at each kind of value, and each reference's branches for input it does not read
//! as data. Expected values follow DESIGN.md (sec:reduction for the float sum and printing, step
//! L1.18 for `lower`) and the header comment of each reference. The case list is
//! `COMPLETENESS.md`.

use super::on_text;
use zed_corpus_ref::zedrt::{fsum, lower, parse_float};

#[test]
fn a_float_sum_is_the_exact_sum_rounded_once_at_every_kind_of_value() {
    let bits = |xs: &[f64]| fsum(xs.iter().copied()).map(f64::to_bits);
    // No value and an exact zero are 0.0.
    assert_eq!(bits(&[]), Ok(0));
    assert_eq!(bits(&[1.0, -1.0]), Ok(0));
    // Rounded once: 0.1 + 0.2 + 0.3 left to right is 0.6000000000000001.
    assert_eq!(fsum([0.1, 0.2, 0.3]), Ok(0.6));
    // No intermediate overflow where the exact sum is finite.
    assert_eq!(fsum([f64::MAX, f64::MAX, -f64::MAX]), Ok(f64::MAX));
    // Subnormal terms and results: 2 * 2^-1074, and the largest subnormal.
    assert_eq!(bits(&[5e-324, 5e-324]), Ok(2));
    assert_eq!(
        bits(&[f64::MIN_POSITIVE, -5e-324]),
        Ok(0x000F_FFFF_FFFF_FFFF)
    );
    // Ties to even: 2^53 - 1 + 0.5 rounds up into the next binade, 2^53 - 2 + 0.5 down.
    let two53 = 2f64.powi(53);
    assert_eq!(fsum([two53 - 1.0, 0.5]), Ok(two53));
    assert_eq!(fsum([two53 - 2.0, 0.5]), Ok(two53 - 2.0));
    // The special values.
    assert!(fsum([f64::NAN, 1.0]).is_ok_and(f64::is_nan));
    assert!(fsum([1.0, f64::NAN, f64::INFINITY]).is_ok_and(f64::is_nan));
    assert_eq!(fsum([f64::INFINITY, 1.0]), Ok(f64::INFINITY));
    assert_eq!(fsum([f64::NEG_INFINITY, 1.0]), Ok(f64::NEG_INFINITY));
    assert_eq!(
        fsum([f64::INFINITY, f64::NEG_INFINITY]),
        Err("-inf + inf in fsum".to_string())
    );
    // A finite sum beyond the largest double, at either sign.
    for x in [f64::MAX, -f64::MAX] {
        assert_eq!(
            fsum([x, x]),
            Err("intermediate overflow in fsum".to_string()),
            "{x}"
        );
    }
}

#[test]
fn a_float_text_reads_as_design_says_where_the_reference_agrees() {
    // DESIGN step L1.18: an optional `-`, then `inf`, `nan`, or digits with an optional fraction
    // and exponent, correctly rounded; a zero after `-` is -0.0, and a value at most half the
    // smallest subnormal is a zero of its sign.
    let read = |s: &str| parse_float(s).map(f64::to_bits);
    assert_eq!(parse_float("1.5"), Ok(1.5));
    assert_eq!(parse_float("2.5e-3"), Ok(0.0025));
    assert_eq!(parse_float("1e3"), Ok(1000.0));
    // The exponent is written as `String` writes it, `e` and a sign only as `-`; the compiler
    // reads it so (l01_18 `completeness.rs`, `1E5` and `1e+5` are `#invalid`).
    for s in ["1E3", "1e+3"] {
        assert_eq!(parse_float(s), Err(format!("invalid float: {s}")), "{s:?}");
    }
    assert_eq!(read("-0"), Ok((-0.0f64).to_bits()));
    assert_eq!(read("1e-400"), Ok(0));
    assert_eq!(read("-1e-400"), Ok((-0.0f64).to_bits()));
    assert_eq!(parse_float("inf"), Ok(f64::INFINITY));
    assert_eq!(parse_float("-inf"), Ok(f64::NEG_INFINITY));
    assert!(parse_float("nan").is_ok_and(f64::is_nan));
    for s in [
        "", ".", "-", "e5", ".e5", "1e", "1e+", "1e5.", "1.2.3", "abc", "0x10", "_1", "1_", "1__0",
        "1_.5", "1._5",
    ] {
        assert_eq!(parse_float(s), Err(format!("invalid float: {s}")), "{s:?}");
    }
}

#[test]
fn lower_takes_the_full_mapping_with_the_final_sigma() {
    // DESIGN step L1.18: `lower` is Unicode's full case mapping, which maps U+0130 to two code
    // points and capital sigma to the final form only after a cased letter and before none,
    // case-ignorable characters (here the apostrophe) skipped.
    for (s, want) in [
        ("İ", "i\u{307}"),
        ("ΟΔΟΣ", "οδος"),
        ("Σ", "σ"),
        ("ΣΑ", "σα"),
        ("ΑΣ'", "ας'"),
        ("Α'Σ", "α'ς"),
        ("ΑΣ'Β", "ασ'β"),
        ("ΑΣ Β", "ας β"),
    ] {
        assert_eq!(lower(s), want, "{s}");
    }
}

/// The output and result of reference `number` on `input`, compared with the expected ones.
fn check(number: &str, name: &str, input: &str, out: &str, result: Result<(), &str>) {
    assert_eq!(
        on_text(number, name, input),
        (out.to_string(), result.map_err(str::to_string)),
        "{number} on {input:?}"
    );
}

#[test]
fn a_line_with_the_wrong_number_of_fields_is_an_error() {
    check(
        "06",
        "case_head",
        "1 1\n",
        "",
        Err("the header is not n m p"),
    );
    check(
        "16",
        "case_tick",
        "1 a\n",
        "",
        Err("not \"tick player dx\": 1 a"),
    );
    check(
        "23",
        "case_join",
        "o 1\n",
        "",
        Err("not \"side id amount\": o 1"),
    );
    check(
        "27",
        "case_chain",
        "a\n",
        "",
        Err("not \"child parent\": a"),
    );
    check(
        "29",
        "case_dedup",
        "a 1\n",
        "",
        Err("not \"id time value\": a 1"),
    );
}

#[test]
fn a_matrix_row_range_before_the_first_row_is_empty() {
    // n = -5: the rows 1..-4 of three, -4 counting from the end to -1, which is moved to 0.
    check("06", "case_rows", "-5 1 1\n2\n3\n", "", Ok(()));
}

#[test]
fn percent_decoding_of_a_surrogate_or_a_value_past_u10ffff_fails_the_line() {
    // %ED%A0%80 is U+D800 and %F7%BF%BF%BF is 0x1FFFFF: neither is a character.
    check(
        "08",
        "case_surrogate",
        "%ED%A0%80\n",
        "",
        Err("not a printable character: U+d800"),
    );
    check(
        "08",
        "case_past",
        "ok\n%F7%BF%BF%BF\n",
        "ok\n",
        Err("not a printable character: U+1fffff"),
    );
}

#[test]
fn a_spreadsheet_cycle_is_named_after_a_walk_past_closed_and_shared_cells() {
    // The walk in name order: a closes, b reads c before c's own turn and a closed, c is passed
    // over as visited, and d reaches itself through e.
    let input = "a = 1\nb = c+a\nc = 2\nd = e\ne = d\n";
    let out = "a=1\na=1 b=1\na=1 b=3 c=2\na=1 b=3 c=2 d=0\n";
    check(
        "15",
        "case_walk",
        input,
        out,
        Err("the cell d depends on itself"),
    );
}

#[test]
fn a_word_frequency_line_whose_first_piece_is_not_an_int_is_skipped() {
    let plain = on_text("18", "case_plain", "1 a b\n7 a\n");
    assert_eq!(plain.1, Ok(()));
    let skipped = on_text("18", "case_skip", "x a\n1 a b\n\nnine a\n7 a\n");
    assert_eq!(skipped, plain);
}

#[test]
fn a_failed_balance_stays_failed_and_an_unknown_kind_is_ignored() {
    let input = "open a\nwd a 5\nwd a 1\ndep a 9\nnote a\nopen b\ndep b 3\nnote zz 1\n";
    let out = "a: insufficient at tx 1, short 5\nb: 3\ntotal 3 over 1 accounts, 1 failed\n";
    check("19", "case_ledger", input, out, Ok(()));
}

#[test]
fn stats_of_no_line_divide_by_zero() {
    check("21", "case_stats", "", "", Err("float division by zero"));
}

#[test]
fn a_buy_request_with_no_quantity_fails_at_the_farthest_position() {
    // "buy apple": the get alternative fails at 0 and the buy alternative at 9, where a quantity
    // was expected; with "x" there it fails at 10, past the space.
    check(
        "30",
        "case_buy",
        "buy apple\nbuy apple x\nbuy apple 2\n",
        "bad request at 9\nbad request at 10\napple=6\n",
        Ok(()),
    );
}

#[test]
fn a_missing_account_operand_or_heat_step_is_an_error() {
    check("19", "case_account", "dep a 5\n", "", Err("no account a"));
    check("28", "case_operands", "1 +\n", "", Err("too few operands"));
    // One step: the rows of steps 0 and 1 print, and there is no step 2.
    check(
        "26",
        "case_steps",
        "1\n0 8 0\n",
        "t=0: 0 8 0\nt=1: 0 4 0\n",
        Err("no step 2"),
    );
}
