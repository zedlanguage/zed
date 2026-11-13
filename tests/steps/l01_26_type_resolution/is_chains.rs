//! Chains of `is` tests joined by `&&` and `||` (IS-chain-quad). Each side of `&&` is checked
//! with the names its left sides tested narrowed, and the whole chain's tests narrow the branch
//! it guards. A chain of k tests narrowed every fact of its left side again at each of its k
//! levels and copied the facts into a new list at each level, O(k²): 2.68 s at k = 4000
//! against 0.18 s at k = 1000. The chain now keeps its left side narrowed while the right side
//! is checked, narrows only the right side's facts on top, and joins the lists by moving the
//! shorter onto the longer (COMPLEXITY.md IS-chain-quad).

use super::{sig, type_errors};
use zed_tests::scaling;
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
fn chain(k: usize, op: &str, side: impl Fn(usize) -> String) -> String {
    let sides: Vec<String> = (0..k).map(side).collect();
    format!(
        "f(x: int | String) = if {} {{ x }} else {{ 0 }};\n",
        sides.join(&format!(" {op} "))
    )
}

/// The chain of `k` sides `side(j)`, each `&&` with the rest of the chain on its right.
fn right_chain(k: usize, side: impl Fn(usize) -> String) -> String {
    let mut c = side(k - 1);
    for j in (0..k - 1).rev() {
        c = format!("{} && ({c})", side(j));
    }
    format!("f(x: int | String) = if {c} {{ x }} else {{ 0 }};\n")
}

/// A chain of `k` tests of `k` names, each bound to `x`.
fn names_chain(k: usize) -> String {
    let binds: String = (0..k).map(|j| format!("y{j} = x;\n")).collect();
    let tests: Vec<String> = (0..k).map(|j| format!("y{j} is int")).collect();
    format!(
        "f(x: int | String) = {{\n{binds}if {} {{ x }} else {{ 0 }}\n}};\n",
        tests.join(" && ")
    )
}

/// Checks the units `text(m)` at `n` and `8n`, read and resolved before the timing, for work
/// of order n log n at most: each fact of the chain is narrowed once and moved at most log2 n
/// times.
fn scales(what: &str, text: impl Fn(usize) -> String + Sync) {
    let n = 500;
    let built = scaling::inputs(n, |m| zed_tests::deep::resolved(&text(m)));
    scaling::check_order(what, n, 1, |m| {
        let (stmts, res) = &built[&m];
        let info = zedc::check::walk::check(stmts, res);
        assert!(info.errors.is_empty(), "{what}: {:?}", info.errors);
    });
}

#[test]
fn a_chain_of_is_tests_nested_to_the_left_scales() {
    scales("a chain of n `x is int` joined by `&&`", |k| {
        chain(k, "&&", |_| "x is int".into())
    });
}

#[test]
fn a_chain_of_is_tests_nested_to_the_right_scales() {
    scales("a chain of n `x is int`, each `&&` with the rest", |k| {
        right_chain(k, |_| "x is int".into())
    });
}

#[test]
fn a_chain_of_is_tests_and_comparisons_scales() {
    let side = |j: usize| match j % 2 {
        0 => "x is int".to_string(),
        _ => format!("x > {j}"),
    };
    scales("a chain of n `is` tests and comparisons", |k| {
        chain(k, "&&", side)
    });
    scales(
        "a chain of n `is` tests and comparisons nested right",
        |k| right_chain(k, side),
    );
}

#[test]
fn a_chain_of_is_tests_of_many_names_scales() {
    scales("a chain of `is` tests of n names", names_chain);
}

#[test]
fn a_chain_of_is_tests_joined_by_or_scales() {
    scales("a chain of n `x is int` joined by `||`", |k| {
        chain(k, "||", |_| "x is int".into())
    });
}

/// `k` sides `x is int` joined by `&&` as a balanced tree, each half in parentheses.
fn balanced(k: usize) -> String {
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

#[test]
fn a_balanced_tree_of_is_tests_scales() {
    // Each join moves the shorter list of facts onto the longer, so a fact moves once per
    // level of the tree: n log n.
    scales("a balanced tree of n `x is int` joined by `&&`", balanced);
}
