//! An `is` test narrows the name it tests: to the tested type where it holds, and to the
//! rest where it does not, through `not`, `&&` and `||`.

use super::{sig, type_errors};
use crate::l01_16_elaboration::value;

const N: &str = "n(x: int | String) = if x is String { len(x) } else { x * 2 };\n";

#[test]
fn each_branch_sees_its_part_of_the_union() {
    assert_eq!(sig(N, "n"), "(x: int | String) -> int");
    assert_eq!(value(&format!("{N}y = n(x: \"ab\");\n"), "y"), "2");
    assert_eq!(value(&format!("{N}y = n(x: 5);\n"), "y"), "10");
}

#[test]
fn not_swaps_the_branches() {
    assert!(
        type_errors("n(x: int | String) = if x is not String { x * 2 } else { len(x) };\n")
            .is_empty()
    );
}

#[test]
fn and_narrows_where_both_hold_and_or_where_both_fail() {
    assert!(
        type_errors(
            "n(x: int | String, y: int | String) = if x is int && y is int { x + y } else { 0 };\n"
        )
        .is_empty()
    );
    assert!(
        type_errors(
            "n(x: int | String, y: int | String) = \
             if x is String || y is String { 0 } else { x + y };\n"
        )
        .is_empty()
    );
}

#[test]
fn the_right_operand_sees_the_left_ones_narrowing() {
    assert!(type_errors("long(x: int | String) = x is String && len(x) > 2;\n").is_empty());
    assert!(type_errors("short(x: int | String) = x is int || len(x) < 2;\n").is_empty());
    assert_eq!(
        type_errors("long(x: int | String) = x is int && len(x) > 2;\n"),
        ["`len` does not take (int) [len(x)]"]
    );
}

#[test]
fn without_a_test_the_whole_union_must_fit() {
    assert_eq!(
        type_errors("n(x: int | String) = x * 2;\n"),
        ["`*` does not take (String, 2) [x * 2]"]
    );
    // The narrowed branch is checked as the narrowed type.
    assert_eq!(
        type_errors("n(x) = if x is String { x + 1 } else { 0 };\n"),
        ["`+` does not take (String, 1) [x + 1]"]
    );
}

#[test]
fn a_condition_must_be_bool() {
    assert_eq!(
        type_errors("c = if 1 { 2 } else { 3 };\n"),
        ["the condition of `if` is 1, not bool [1]"]
    );
}
