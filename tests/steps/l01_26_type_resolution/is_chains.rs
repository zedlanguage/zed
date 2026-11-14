//! Chains of `is` tests joined by `&&` and `||` (IS-chain-quad). Each side of `&&` is checked
//! with the names its left sides tested narrowed, and the whole chain's tests narrow the branch
//! it guards. A chain of k tests narrowed every fact of its left side again at each of its k
//! levels and copied the facts into a new list at each level, O(k²): 2.68 s at k = 4000
//! against 0.18 s at k = 1000. The chain now keeps its left side narrowed while the right side
//! is checked, narrows only the right side's facts on top, and joins the lists by moving the
//! shorter onto the longer (COMPLEXITY.md IS-chain-quad).

use super::{sig, type_errors};
use zed_tests::step_helpers::l01_16_elaboration::value;

#[test]
fn every_side_of_a_long_chain_sees_the_tests_left_of_it() {
    let text = "order(x: int | String, y: int | String) = \
                if x is int && y is int && x > 0 && y > x { y - x } else { 0 };\n";
    assert_eq!(type_errors(text), Vec::<String>::new());
    assert_eq!(
        sig(text, "order"),
        "type T1 = int | String;\n(x: T1, y: T1) -> int"
    );
    assert_eq!(value(&format!("{text}d = order(x: 2, y: 7);\n"), "d"), "5");
    assert_eq!(
        value(&format!("{text}d = order(x: \"a\", y: 7);\n"), "d"),
        "0"
    );
}

#[test]
fn a_chain_nested_to_the_right_narrows_as_one_nested_to_the_left() {
    let left = "f(x: int | String, y: int | String) = \
                if x is int && y is int && x < y { y - x } else { 0 };\n";
    let right = "f(x: int | String, y: int | String) = \
                 if x is int && (y is int && x < y) { y - x } else { 0 };\n";
    assert_eq!(type_errors(left), Vec::<String>::new());
    assert_eq!(type_errors(right), Vec::<String>::new());
    assert_eq!(sig(left, "f"), sig(right, "f"));
}

#[test]
fn where_a_chain_of_or_fails_every_side_failed() {
    let text = "total(x: int | String, y: int | String, z: int | String) = \
                if x is int || y is int || z is int { 0 } else { len(x) + len(y) + len(z) };\n";
    assert_eq!(type_errors(text), Vec::<String>::new());
    let right = "total(x: int | String, y: int | String, z: int | String) = \
                 if x is int || (y is int || z is int) { 0 } else { len(x) + len(y) + len(z) };\n";
    assert_eq!(type_errors(right), Vec::<String>::new());
}

#[test]
fn not_of_a_chain_of_or_narrows_the_side_of_and_after_it() {
    // `!(a || b)` holds where both fail, so `x > y` sees both names as int.
    let text = "gap(x: int | String, y: int | String) = \
                if !(x is String || y is String) && x > y { x - y } else { 0 };\n";
    assert_eq!(type_errors(text), Vec::<String>::new());
    assert_eq!(value(&format!("{text}d = gap(x: 9, y: 4);\n"), "d"), "5");
}

#[test]
fn a_chain_of_or_narrows_nothing_where_it_holds() {
    // Where `x is int || y is int` holds, either may be a String.
    assert_eq!(
        type_errors(
            "f(x: int | String, y: int | String) = \
             if (x is int || y is int) && x > 0 { 1 } else { 0 };\n"
        ),
        ["`>` does not take (String, 0): no arrow of `>` takes these types. [x > 0]"]
    );
}

#[test]
fn a_side_far_along_a_chain_is_checked_with_the_tests_that_hold_there() {
    assert_eq!(
        type_errors(
            "f(x: int | String, y: int | String) = \
             if y is String && x is int && len(y) > 0 && len(x) > 2 { 1 } else { 0 };\n"
        ),
        [
            "`len` does not take (int): no arrow of `len` takes these types. Try `len(String(x))` instead. [len(x)]"
        ]
    );
}

#[test]
fn a_chain_outside_a_condition_narrows_its_right_sides() {
    let text = "both(x: int | String, y: int | String) = x is int && y is int && x < y;\n";
    assert_eq!(type_errors(text), Vec::<String>::new());
    assert_eq!(
        value(&format!("{text}b = both(x: 1, y: 2);\n"), "b"),
        "true"
    );
}

#[test]
fn the_narrowing_of_a_chain_ends_with_its_branch() {
    // After the `if`, `x` is its whole type again.
    assert_eq!(
        type_errors(
            "f(x: int | String) = {\n\
             a = if x is int && x > 0 && x is int { x } else { 0 };\n\
             x * 2\n\
             };\n"
        ),
        ["`*` does not take (String, 2): no arrow of `*` takes these types. [x * 2]"]
    );
}

/// A function of `x: int | String` returning `x` where the chain of `k` sides `side(j)` holds.
pub(super) fn chain(k: usize, op: &str, side: impl Fn(usize) -> String) -> String {
    let sides: Vec<String> = (0..k).map(side).collect();
    format!(
        "f(x: int | String) = if {} {{ x }} else {{ 0 }};\n",
        sides.join(&format!(" {op} "))
    )
}

/// The chain of `k` sides `side(j)`, each `&&` with the rest of the chain on its right.
pub(super) fn right_chain(k: usize, side: impl Fn(usize) -> String) -> String {
    let mut c = side(k - 1);
    for j in (0..k - 1).rev() {
        c = format!("{} && ({c})", side(j));
    }
    format!("f(x: int | String) = if {c} {{ x }} else {{ 0 }};\n")
}

/// A chain of `k` tests of `k` names, each bound to `x`.
pub(super) fn names_chain(k: usize) -> String {
    let binds: String = (0..k).map(|j| format!("y{j} = x;\n")).collect();
    let tests: Vec<String> = (0..k).map(|j| format!("y{j} is int")).collect();
    format!(
        "f(x: int | String) = {{\n{binds}if {} {{ x }} else {{ 0 }}\n}};\n",
        tests.join(" && ")
    )
}

/// `k` sides `x is int` joined by `&&` as a balanced tree, each half in parentheses.
pub(super) fn balanced(k: usize) -> String {
    // The text is built bottom up, level by level, so its depth is log2 k.
    let mut level: Vec<String> = vec!["x is int".into(); k];
    while level.len() > 1 {
        level = level
            .chunks(2)
            .map(|p| match p {
                [a, b] => format!("({a}) && ({b})"),
                [a] => a.clone(),
                _ => unreachable!("chunks of two"),
            })
            .collect();
    }
    format!(
        "f(x: int | String) = if {} {{ x }} else {{ 0 }};\n",
        level[0]
    )
}

/// The side `j` of a chain of `is` tests and comparisons.
pub(super) fn test_or_comparison(j: usize) -> String {
    match j % 2 {
        0 => "x is int".to_string(),
        _ => format!("x > {j}"),
    }
}

#[test]
fn chains_and_trees_of_is_tests_are_accepted() {
    // A small instance of each benchmark of `bench::is_chains`.
    let is_int = |_: usize| "x is int".to_string();
    for text in [
        chain(3, "&&", is_int),
        right_chain(3, is_int),
        chain(4, "&&", test_or_comparison),
        right_chain(4, test_or_comparison),
        names_chain(3),
        chain(3, "||", is_int),
        balanced(5),
    ] {
        assert_eq!(type_errors(&text), Vec::<String>::new(), "{text}");
    }
}
