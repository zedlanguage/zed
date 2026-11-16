//! Ranges written as step L1.12 parses them, read as the intervals of the lattice (DESIGN.md
//! step L1.24, RANGE-L1): the checker reads `x: int[lo..=hi]` into the interval the
//! parameter's cell starts from, and the order, meet and join are the interval lattice's.

use zed_tests::step_helpers::l01_26_type_resolution::sig_of;
use zedc::check::written_ints;
use zedc::store::interval::IntervalSet;

/// The interval of the range `r`, as the checker reads it from the parameter `x: r`.
fn ints(r: &str) -> IntervalSet {
    let sig = sig_of(&format!("f(x: {r}) = x;\n"), "f");
    let written = sig.params[0]
        .range
        .as_ref()
        .unwrap_or_else(|| panic!("`x: {r}` has no range"));
    written_ints(written)
}

#[test]
fn a_narrower_range_lies_inside_a_wider_one_and_not_the_reverse() {
    let (narrow, wide) = (ints("int[0..=5]"), ints("int[0..=10]"));
    assert!(narrow.is_subset(&wide));
    assert!(!wide.is_subset(&narrow));
}

#[test]
fn a_range_below_an_end_and_one_through_the_end_before_it_are_one_type() {
    assert_eq!(ints("int[0..<10]"), ints("int[0..=9]"));
    // The signature prints the two alike, each end inclusive.
    let printed = |r: &str| {
        sig_of(&format!("f(x: {r}) = x;\n"), "f").params[0]
            .range
            .as_ref()
            .map(|w| w.text.to_string())
    };
    assert_eq!(printed("int[0..<10]"), Some("int[0..=9]".into()));
    assert_eq!(printed("int[0..<10]"), printed("int[0..=9]"));
    // Bounds below 0, past 2^64, and a name bound to an int.
    assert_eq!(ints("int[-5..<6]"), ints("int[-5..=5]"));
    assert_eq!(
        ints("int[0..<18446744073709551617]"),
        ints("int[0..=18446744073709551616]")
    );
    // The result's type prints as `int`, though DESIGN.md L1.25 gives the body's hull,
    // `int[0..=9]` here: a signature has no place for a result interval yet (row
    // RANGE-result-hull). The interval of the body is the cell's, read by the tests of step
    // L1.39.
    assert_eq!(
        sig_of("n = 10;\nf(x: int[0..<n]) = x;\n", "f").to_string(),
        "(x: int[0..=9]) -> int"
    );
}

#[test]
fn the_meet_of_two_half_open_ranges_is_their_overlap_and_the_join_is_int() {
    let (from, to) = (ints("int[0..]"), ints("int[_..=10]"));
    assert_eq!(from.meet(&to), ints("int[0..=10]"));
    assert_eq!(from.join(&to), IntervalSet::top());
    assert_eq!(ints("int[_..]"), IntervalSet::top());
}
