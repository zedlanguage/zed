//! The array display `[a, b, c]` and the family type `[T]` (item SEQ-desugar). They are arrays
//! keyed by rank, `{0 -> a, 1 -> b, 2 -> c}` of type `int[0..<3] -> T` and `int[0..<_] -> T`
//! (sec:grammar, rules `ArrayExpr` and `RankArrayType`), not the `Seq` of sec:order, whose keys are
//! origins. The tree keeps the elements in written order, which is their rank order; the
//! desugaring rules copied from the spec say so.

use super::{check, fmt, refused};
use zed_tests::step_helpers::m0_03_grammar_tools::{Part, grammar};

/// The desugaring rule of `rule` in the spec's desugaring rules.
fn rule(rule: &str) -> String {
    let text = grammar(Part::Desugar);
    let line = text
        .lines()
        .find(|l| l.split(':').next().map(str::trim) == Some(rule))
        .unwrap_or_else(|| panic!("no desugaring rule for {rule}"));
    line.split_once(':')
        .expect("a rule and its text")
        .1
        .trim()
        .into()
}

#[test]
fn the_desugaring_rules_read_rank_keyed_arrays() {
    let display = rule("ArrayExpr");
    assert!(
        display.contains("{0 -> ⟦e0⟧, …, n−1 -> ⟦en−1⟧}")
            && display.contains("int[0..<n] -> T")
            && display.contains("keyed by rank"),
        "{display}"
    );
    let ty = rule("RankArrayType");
    assert!(ty.contains("int[0..<_] -> T"), "{ty}");
    for text in [display, ty] {
        assert!(!text.contains("Seq"), "an array is no Seq: {text}");
    }
}

#[test]
fn a_display_lists_its_elements_in_rank_order() {
    check(&[
        // A week of readings: rank 0 is Monday's.
        (
            "week(m, t, w) = [m, t, w, 0, 0, 0, 0];",
            "(def week (m t w) = (array m t w 0 0 0 0))",
        ),
        ("pair(a, b) = [b, a];", "(def pair (a b) = (array b a))"),
        (
            "rows(x) = [(x, 1), (x, 2)];",
            "(def rows (x) = (array (tuple x 1) (tuple x 2)))",
        ),
    ]);
}

#[test]
fn the_empty_display_and_one_element() {
    check(&[
        ("none(x) = [];", "(def none (x) = (array))"),
        ("one(x) = [x];", "(def one (x) = (array x))"),
        ("one(x) = [x,];", "(def one (x) = (array x))"),
        ("f(x: [int]) = [];", "(def f ((x: (array int))) = (array))"),
    ]);
}

#[test]
fn arrays_nest() {
    check(&[
        (
            "grid(x) = [[x, 0], [], [0]];",
            "(def grid (x) = (array (array x 0) (array) (array 0)))",
        ),
        (
            "deep(x) = [[[x]]];",
            "(def deep (x) = (array (array (array x))))",
        ),
        (
            "rows(m: [[f64]]) = m;",
            "(def rows ((m: (array (array f64)))) = m)",
        ),
        (
            "cube(m: [[[int]]]) = m;",
            "(def cube ((m: (array (array (array int))))) = m)",
        ),
    ]);
}

#[test]
fn arrays_format_to_themselves() {
    for text in [
        "grid(x) = [[x, 0], [], [0]];\n",
        "rows(m: [[f64]]) = m;\n",
        "none(x) = [];\n",
    ] {
        assert_eq!(fmt(text), text);
    }
}

#[test]
fn resolution_names_the_array_forms() {
    assert_eq!(
        refused("grid(m: [[int]]) = [m];"),
        [
            concat!(zed_tests::not_yet!("a family type `[T]`"), " [[[int]]]"),
            concat!(zed_tests::not_yet!("an array display"), " [[m]]"),
        ]
    );
    assert_eq!(
        refused("none(x) = [];"),
        [concat!(zed_tests::not_yet!("an array display"), " [[]]")]
    );
}
