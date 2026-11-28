//! `places: k` on the six rounding words and `allocate` (plan row SPEC-round-places-wire;
//! DESIGN.md sec:corner_cases, "Rounding to a number of decimal places" and "Splitting an
//! amount without losing a part"). Every expected value is DESIGN's or written out by hand,
//! not computed by the code under test.

use num_bigint::BigInt;
use zed_kernel::{Family, Prim, Rat, Term, Value};
use zed_tests::step_helpers::l01_16_elaboration::term;
use zed_tests::step_helpers::l01_26_type_resolution::{sig, type_errors};
use zed_tests::step_helpers::l01_29_diagnostics::rejected_with_main;

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

/// DESIGN's table at `places: 1`, each value as the printer writes a rat, in lowest terms:
/// DESIGN's `0.2` is `1r/5r`, `0.3` is `3r/10r` and `0.4` is `2r/5r`.
const TABLE: [(&str, [&str; 6]); 3] = [
    (
        "0.25r",
        ["1r/5r", "3r/10r", "1r/5r", "3r/10r", "1r/5r", "3r/10r"],
    ),
    (
        "-0.25r",
        [
            "-1r/5r", "-3r/10r", "-3r/10r", "-1r/5r", "-1r/5r", "-3r/10r",
        ],
    ),
    (
        "0.35r",
        ["2r/5r", "2r/5r", "3r/10r", "2r/5r", "3r/10r", "2r/5r"],
    ),
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
    // 0.3 and 0.2.
    assert_eq!(x("round(0.25r, ties: #away, places: 1)"), "3r/10r");
    assert_eq!(x("round(0.25r, places: 1, ties: #even)"), "1r/5r");
}

#[test]
fn two_places_round_to_hundredths() {
    // 2.68 = 268/100 = 67/25; 2.66 = 266/100 = 133/50; 0.33 = 33/100.
    assert_eq!(x("round(2.675r, places: 2)"), "67r/25r");
    assert_eq!(x("round(2.665r, places: 2)"), "133r/50r");
    assert_eq!(x("floor(-2.671r, places: 2)"), "-67r/25r");
    assert_eq!(x("round(1r/3r, places: 2)"), "33r/100r");
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
    // The value printer writes a list with its keys, as `{0 -> 1, ...}`.
    assert_eq!(x("allocate(2, [2, 1, 1])"), "{0 -> 1, 1 -> 1, 2 -> 0}");
    assert_eq!(x("allocate(10, [1, 1, 1])"), "{0 -> 4, 1 -> 3, 2 -> 3}");
}

#[test]
fn allocate_splits_a_rat_into_hundredths() {
    assert_eq!(
        x("allocate(10r, [1, 1, 1], places: 2)"),
        // 3.34 = 334/100 = 167/50 and 3.33 = 333/100.
        "{0 -> 167r/50r, 1 -> 333r/100r, 2 -> 333r/100r}"
    );
    // PRINT-list-and-decimal-rat-form: DESIGN's `[3.34r, 3.33r, 3.33r]` is the value, written
    // as a literal, and the printed form reads back as that value.
    assert_eq!(
        x("allocate(10r, [1, 1, 1], places: 2) == [3.34r, 3.33r, 3.33r]"),
        "true"
    );
    let printed = "{0 -> 167r/50r, 1 -> 333r/100r, 2 -> 333r/100r}";
    assert_eq!(x(printed), printed);
    assert_eq!(x(&format!("{printed} == [3.34r, 3.33r, 3.33r]")), "true");
}

#[test]
fn allocate_of_a_negative_total_negates_the_split() {
    assert_eq!(x("allocate(-10, [1, 1, 1])"), "{0 -> -4, 1 -> -3, 2 -> -3}");
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
        sig(
            "f(positional t: rat) = allocate(t, [1, 2], places: 2);",
            "f"
        ),
        // `[rat]` is the rank `int ->? rat` of rats, as the checker prints it.
        "rat -> [rat] | #invalid"
    );
}

#[test]
fn allocate_elaborates_to_its_primitive_with_zero_places_by_default() {
    assert_eq!(
        term("x = allocate(2, [2, 1, 1]);\n", "x"),
        // The term printer writes a family literal as its keys and values in turn.
        "allocate(2, entries(0, 2, 1, 1, 2, 1), 0)"
    );
}

/// The total `1000000.01r` of the benchmark, as an exact rational.
pub(super) fn bench_total() -> Rat {
    Rat::new(BigInt::from(100_000_001), BigInt::from(100)).expect("a nonzero denominator")
}

/// `allocate(1000000.01r, ws, places: 2)` for the `n` weights `ws[i] = i % 7 + 1`, built as a
/// kernel term with its operands as literals.
pub(super) fn allocate_input(n: usize) -> Term {
    let leaves = (0..n).map(|i| (vec![Value::Int(i as i64)], Value::Int((i % 7 + 1) as i64)));
    let weights = Family::from_leaves(leaves).expect("distinct keys");
    let args = vec![
        Term::Lit(Value::rat(bench_total())),
        Term::Lit(Value::Family(weights)),
        Term::Lit(Value::Int(2)),
    ];
    Term::Prim(Prim::Allocate, args)
}

/// The benchmark's input at a small size: one part per weight, each a rat, summing to the
/// total exactly.
#[test]
fn allocate_of_the_benchmark_input_keeps_the_total() {
    let Value::Family(parts) = zed_kernel::eval(&allocate_input(50)).expect("a value") else {
        panic!("not a list");
    };
    assert_eq!(parts.len(), 50);
    let mut sum = Rat::int(BigInt::from(0));
    for (_, p) in parts.iter() {
        let Value::Rat(p) = p else {
            panic!("not a rat: {p:?}");
        };
        sum = sum.add(p).expect("a small sum");
    }
    assert_eq!(sum, bench_total());
}

#[test]
fn allocate_is_refused_as_a_function_value_with_the_lambda_as_repair() {
    assert_eq!(
        type_errors("g = allocate;\n"),
        vec![
            "`allocate` is given here as a function value; this version of zedc checks \
             `allocate` only where it is called. [allocate]"
                .to_string()
        ]
    );
    let out = rejected_with_main("g = allocate;\n");
    assert!(
        out.contains(
            "`allocate` is given here as a function value; this version of zedc checks \
             `allocate` only where it is called"
        ) && out.contains("repair: write `(total, weights) -> allocate(total, weights)`"),
        "{out}"
    );
}

#[test]
fn allocate_with_one_argument_is_refused_with_both_forms_as_repairs() {
    let src = "f(positional t: int) = allocate(t);\n";
    assert_eq!(
        type_errors(src),
        vec![
            "`allocate` takes a total and a list of weights, passed by position, and an \
             optional `places:` by name. [allocate(t)]"
                .to_string()
        ]
    );
    let out = rejected_with_main(src);
    assert!(
        out.contains("repair: write `allocate(total, weights)`")
            && out.contains("repair: write `allocate(total, weights, places: 2)`"),
        "{out}"
    );
}

#[test]
fn allocate_with_its_total_before_the_dot_is_refused_with_the_call_as_repair() {
    let src = "f(positional t: int) = t.allocate([1, 2]);\n";
    assert_eq!(
        type_errors(src),
        vec![
            "`allocate` is called here with its total before the dot; this version of zedc \
             builds `allocate` only with every argument in the parentheses. \
             [t.allocate([1, 2])]"
                .to_string()
        ]
    );
    let out = rejected_with_main(src);
    assert!(out.contains("repair: write `allocate(t, [1, 2])`"), "{out}");
}
