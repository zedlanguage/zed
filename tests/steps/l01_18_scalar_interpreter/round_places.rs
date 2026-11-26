//! `places: k` on the six rounding words and `allocate` (plan row SPEC-round-places-wire;
//! DESIGN.md sec:corner_cases, "Rounding to a number of decimal places" and "Splitting an
//! amount without losing a part"). Every expected value is DESIGN's or written out by hand,
//! not computed by the code under test.

use zed_tests::step_helpers::l01_16_elaboration::term;
use zed_tests::step_helpers::l01_26_type_resolution::{sig, type_errors};

use super::x;

/// The six calls of the DESIGN table's columns at `places: 1`, in its order, on `a`.
fn columns(a: &str) -> [String; 6] {
    [
        format!("round({a}, places: 1)"),
        format!("round({a}, places: 1, ties: #away)"),
        format!("floor({a}, places: 1)"),
        format!("ceil({a}, places: 1)"),
        format!("trunc({a}, places: 1)"),
        format!("awayFromZero({a}, places: 1)"),
    ]
}

/// DESIGN's table at `places: 1`.
const TABLE: [(&str, [&str; 6]); 3] = [
    ("0.25r", ["0.2r", "0.3r", "0.2r", "0.3r", "0.2r", "0.3r"]),
    ("-0.25r", ["-0.2r", "-0.3r", "-0.3r", "-0.2r", "-0.2r", "-0.3r"]),
    ("0.35r", ["0.4r", "0.4r", "0.3r", "0.4r", "0.3r", "0.4r"]),
];

#[test]
fn every_value_of_the_design_table_at_one_place() {
    for (a, want) in TABLE {
        for (call, w) in columns(a).iter().zip(want) {
            assert_eq!(x(call), w, "{call}");
        }
    }
}

#[test]
fn ties_away_may_come_before_places() {
    assert_eq!(x("round(0.25r, ties: #away, places: 1)"), "0.3r");
    assert_eq!(x("round(0.25r, places: 1, ties: #even)"), "0.2r");
}

#[test]
fn two_places_round_to_hundredths() {
    assert_eq!(x("round(2.675r, places: 2)"), "2.68r");
    assert_eq!(x("round(2.665r, places: 2)"), "2.66r");
    assert_eq!(x("floor(-2.671r, places: 2)"), "-2.68r");
    assert_eq!(x("round(1r/3r, places: 2)"), "0.33r");
}

#[test]
fn a_negative_place_count_rounds_a_rat_to_a_multiple_of_a_power_of_ten() {
    assert_eq!(x("round(1250r, places: -2)"), "1200r");
    assert_eq!(x("round(1350r, places: -2)"), "1400r");
    assert_eq!(x("ceil(1201r, places: -2)"), "1300r");
}

#[test]
fn zero_places_on_a_rat_is_the_whole_number_as_a_rat() {
    assert_eq!(x("round(2.5r, places: 0)"), "2r");
    assert_eq!(x("round(3.5r, places: 0)"), "4r");
}

#[test]
fn an_int_with_places_at_least_zero_is_itself() {
    assert_eq!(x("round(1234, places: 2)"), "1234");
    assert_eq!(x("floor(-7, places: 0)"), "-7");
}

#[test]
fn an_int_with_negative_places_rounds_to_a_multiple_of_a_power_of_ten() {
    assert_eq!(x("round(1250, places: -2)"), "1200");
    assert_eq!(x("round(1350, places: -2)"), "1400");
    assert_eq!(x("floor(-1201, places: -2)"), "-1300");
    assert_eq!(x("trunc(-1299, places: -2)"), "-1200");
    assert_eq!(x("round(1250, places: -2, ties: #away)"), "1300");
}

#[test]
fn places_keeps_the_kind_of_its_operand() {
    assert_eq!(
        sig("f(positional x: int, k: int) = round(x, places: k);", "f"),
        "(int, k: int) -> int"
    );
    assert_eq!(
        sig("f(positional x: rat) = floor(x, places: 2);", "f"),
        "rat -> rat"
    );
}

/// The message is DESIGN's, word for word.
#[test]
fn a_float_with_places_is_rejected_with_the_rat_repair() {
    assert_eq!(
        type_errors("f(positional x: f64) = round(x, places: 2);"),
        vec![
            "`round(x, places: 2)` rounds a float to decimal places, which a float cannot \
             hold exactly: write `round(rat(x), places: 2)`. [round(x, places: 2)]"
                .to_string()
        ]
    );
}

#[test]
fn an_f32_with_places_is_rejected_with_the_rat_repair() {
    assert_eq!(
        type_errors("f(positional y: f32) = floor(y, places: 1);"),
        vec![
            "`floor(y, places: 1)` rounds a float to decimal places, which a float cannot \
             hold exactly: write `floor(rat(y), places: 1)`. [floor(y, places: 1)]"
                .to_string()
        ]
    );
}

#[test]
fn ties_with_places_still_takes_only_even_or_away() {
    let errs = type_errors("f(positional x: rat) = round(x, places: 1, ties: #up);");
    let want = "`ties:` takes the constant `#even` or `#away`, and `#up` is not one of them.";
    assert!(
        errs.len() == 1 && errs[0].starts_with(want) && errs[0].ends_with("[#up]"),
        "{errs:?}"
    );
}

#[test]
fn allocate_splits_an_int_by_largest_remainder() {
    assert_eq!(x("allocate(2, [2, 1, 1])"), "[1, 1, 0]");
    assert_eq!(x("allocate(10, [1, 1, 1])"), "[4, 3, 3]");
}

#[test]
fn allocate_splits_a_rat_into_hundredths() {
    assert_eq!(
        x("allocate(10r, [1, 1, 1], places: 2)"),
        "[3.34r, 3.33r, 3.33r]"
    );
}

#[test]
fn allocate_of_a_negative_total_negates_the_split() {
    assert_eq!(x("allocate(-10, [1, 1, 1])"), "[-4, -3, -3]");
}

#[test]
fn allocate_with_all_weights_zero_is_invalid() {
    assert_eq!(x("allocate(10, [0, 0])"), "#invalid");
}

#[test]
fn allocate_with_a_negative_weight_is_invalid() {
    assert_eq!(x("allocate(10, [3, -1])"), "#invalid");
}

#[test]
fn allocate_of_a_rat_off_the_grid_is_invalid() {
    assert_eq!(x("allocate(0.005r, [1, 1], places: 2)"), "#invalid");
}

#[test]
fn allocate_gives_a_list_or_invalid_as_a_whole() {
    assert_eq!(
        sig("f(positional t: rat) = allocate(t, [1, 2], places: 2);", "f"),
        "rat -> (int ->? rat) | #invalid"
    );
}

#[test]
fn allocate_elaborates_to_its_primitive_with_zero_places_by_default() {
    assert_eq!(
        term("x = allocate(2, [2, 1, 1]);\n", "x"),
        "allocate(2, [2, 1, 1], 0)"
    );
}

#[test]
fn allocate_is_refused_as_a_function_value_with_the_lambda_as_repair() {
    let errs = type_errors("g = allocate;\n");
    assert!(
        errs.len() == 1
            && errs[0].starts_with("`allocate` is given here as a function value")
            && errs[0].contains("repair: write `(total, weights) -> allocate(total, weights)`"),
        "{errs:?}"
    );
}
