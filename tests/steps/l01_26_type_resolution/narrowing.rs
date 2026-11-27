//! An `is` test narrows the name it tests: to the tested type where it holds, and to the
//! rest where it does not, through `not`, `&&` and `||`.

use super::{sig, type_errors};
use zed_tests::instances::permutations;
use zed_tests::step_helpers::l01_16_elaboration::value;

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
        [
            "`len` does not take (int): no arrow of `len` takes these types. Try `len(String(x))` instead. [len(x)]"
        ]
    );
}

#[test]
fn without_a_test_the_whole_union_must_fit() {
    assert_eq!(
        type_errors("n(x: int | String) = x * 2;\n"),
        ["`*` does not take (String, 2): no arrow of `*` takes these types. [x * 2]"]
    );
    // The narrowed branch is checked as the narrowed type.
    assert_eq!(
        type_errors("n(x) = if x is String { x + 1 } else { 0 };\n"),
        ["`+` does not take (String, 1): no arrow of `+` takes these types. [x + 1]"]
    );
}

#[test]
fn the_tested_classes_end_alike_whatever_the_order_of_their_tests_and_uses() {
    // Plan row PROOF-join-narrowed-rescan-rounds (b): each test `if a is int { a } else { b }`
    // links the class of `a` to the class it gives, which holds `b`'s, and the uses (`* 2`,
    // `len`, `+`) are checked when their classes are joined, so the joins run with use checks
    // inside them (`Ck::join_narrowed`). The statements are independent, and each of their 24
    // orders makes the classes, and so their roots and links, in another order; the
    // signature and the errors are the same in every order.
    let parts = [
        "  x1 = if a is int { a } else { b };\n",
        "  x2 = if b is int { b } else { c };\n",
        "  x3 = if c is int { c + 1 } else { d };\n",
        "  y = d * 2;\n",
    ];
    for last in ["", "  z = len(d);\n"] {
        let mut seen: Option<(String, Vec<String>)> = None;
        for order in permutations(4) {
            let body: String = order.iter().map(|&i| parts[i]).collect();
            let text = format!(
                "f(positional a, positional b, positional c, positional d) {{\n{body}{last}  \
                 return (x1, x2, x3, y);\n}}\n"
            );
            let mut errors = type_errors(&text);
            errors.sort();
            let got = (
                if errors.is_empty() {
                    sig(&text, "f")
                } else {
                    String::new()
                },
                errors,
            );
            match &seen {
                None => seen = Some(got),
                Some(first) => assert_eq!(&got, first, "{text}"),
            }
        }
        // The program with `len(d)` beside `d * 2` is rejected, and the one without accepted.
        let (sig, errors) = seen.expect("24 orders");
        assert_eq!(last.is_empty(), errors.is_empty(), "{sig} {errors:?}");
    }
}

#[test]
fn a_condition_must_be_bool() {
    assert_eq!(
        type_errors("c = if 1 { 2 } else { 3 };\n"),
        [
            "the condition of `if` is 1, not bool: `if` chooses its branch by a `bool`, and this condition may be another value. [1]"
        ]
    );
}
