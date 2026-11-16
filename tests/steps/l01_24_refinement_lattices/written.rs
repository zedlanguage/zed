//! Ranges written as step L1.12 parses them, read as the intervals of the lattice (DESIGN.md
//! step L1.24, RANGE-L1): the checker reads `x: int[lo..=hi]` into the interval the
//! parameter's cell starts from, and the order, meet and join are the interval lattice's.

use zed_tests::step_helpers::l01_26_type_resolution::sig_of;
use zedc::check::written_ints;
use zedc::store::interval::IntervalSet;

/// The interval of the range `r`, as the checker reads it from the parameter `x: r`.
fn ints(r: &str) -> IntervalSet {
    let sig = sig_of(&format!("f(x: {r}) = x;\n"), "f");
    let written = (sig.params[0].range.as_ref())
        .and_then(|w| w.int())
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
            .and_then(|w| w.int())
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
    // The result prints as the body's hull, each end inclusive (DESIGN.md L1.25, row
    // RANGE-result-hull): here the parameter's own range.
    assert_eq!(
        sig_of("n = 10;\nf(x: int[0..<n]) = x;\n", "f").to_string(),
        "(x: int[0..=9]) -> int[0..=9]"
    );
}

#[test]
fn the_meet_of_two_half_open_ranges_is_their_overlap_and_the_join_is_int() {
    let (from, to) = (ints("int[0..]"), ints("int[_..=10]"));
    assert_eq!(from.meet(&to), ints("int[0..=10]"));
    assert_eq!(from.join(&to), IntervalSet::top());
    assert_eq!(ints("int[_..]"), IntervalSet::top());
}

/// Row RANGE-result-hull: printed signatures carry the ranges DESIGN gives them. DESIGN.md
/// L1.25: "with ranges written on parameters (step L1.12), `f(x: int[0..=9]) = x + 1` gives
/// `int[1..=10]`, `g(x: int[-3..=4]) = x * x` gives `int[0..=16]`"; and the L1.39 test row:
/// "`g0(y) = f(y)`, with no written type on `y`, is accepted with the inferred signature
/// `g0(y: int[0..=10]) -> int[0..=10]`".
#[test]
fn a_function_of_a_ranged_parameter_prints_the_hull_of_its_result() {
    assert_eq!(
        sig_of("f(x: int[0..=9]) = x + 1;\n", "f").to_string(),
        "(x: int[0..=9]) -> int[1..=10]"
    );
    assert_eq!(
        sig_of("g(x: int[-3..=4]) = x * x;\n", "g").to_string(),
        "(x: int[-3..=4]) -> int[0..=16]"
    );
    assert_eq!(
        sig_of("f(x: int[0..=10]) = x;\ng0(y) = f(x: y);\n", "g0").to_string(),
        "(y: int[0..=10]) -> int[0..=10]"
    );
}

/// `n` functions of `x: int[0..=9]`, each but the first calling the one before it and adding 1:
/// the call reads the hull of the one it calls, so `h<i>` gives `int[i..=i + 9]`. The names
/// are `h<i>`, since `f32` and `f64` name prelude types.
pub(super) fn hull_chain(n: usize) -> String {
    let mut text = String::from("h0(x: int[0..=9]) = x;\n");
    for i in 1..n {
        text.push_str(&format!("h{i}(x: int[0..=9]) = h{}(x: x) + 1;\n", i - 1));
    }
    text
}

/// The signature `h<i>` of [`hull_chain`] has.
pub(super) fn hull_chain_sig(i: usize) -> String {
    format!("(x: int[0..=9]) -> int[{i}..={}]", i + 9)
}

/// Small instance of `bench::a_chain_of_ranged_functions_prints_each_hull_in_linear_time`.
#[test]
fn each_function_of_a_chain_prints_the_hull_of_the_one_it_calls_plus_one() {
    let text = hull_chain(4);
    for i in 0..4 {
        assert_eq!(
            sig_of(&text, &format!("h{i}")).to_string(),
            hull_chain_sig(i)
        );
    }
}

/// The same on a partial map's key (RANGE-keys accepts `m: int[5..<10] ->? int` and checks each
/// call against the range): printed types are syntax, so the range prints as written, each end
/// inclusive.
#[test]
fn a_partial_map_parameter_prints_the_range_on_its_key() {
    assert_eq!(
        sig_of("f(positional m: int[5..<10] ->? int) = m(6);\n", "f").to_string(),
        "(int[5..=9] ->? int) -> int | #notFound"
    );
}

/// Row RANGE-key-component-print: the ranges on a tuple key's components print as written,
/// each end inclusive, a component with none as its type, and the printed parameter, written
/// back as the declaration, prints the same.
#[test]
fn a_partial_map_parameter_prints_the_ranges_on_its_tuple_key() {
    let cases = [
        (
            "((int[0..<2], int[0..<3]))",
            "(1, 2)",
            "((int[0..=1], int[0..=2]))",
        ),
        ("((int[0..<2], int))", "(1, 7)", "((int[0..=1], int))"),
        (
            "((bool, int[-3..=-1], int[4..]))",
            "(true, -2, 9)",
            "((bool, int[-3..=-1], int[4..]))",
        ),
        ("(int[0..<2],)", "(1,)", "(int[0..=1],)"),
    ];
    for (key, arg, printed) in cases {
        let expected = format!("({printed} ->? int) -> int | #notFound");
        let src = |k: &str| format!("f(positional m: {k} ->? int) = m({arg});\n");
        assert_eq!(sig_of(&src(key), "f").to_string(), expected, "{key}");
        assert_eq!(
            sig_of(&src(printed), "f").to_string(),
            expected,
            "{printed}"
        );
    }
}
