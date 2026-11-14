//! Item EQ-no-common-carrier: `==` and `!=` between two values that no value is both of
//! always give the same answer, so they are rejected (DESIGN.md L1.26: "Two forced literals of
//! different carriers under `==` are rejected like any two values with no common carrier";
//! sec:diagnostics rows "Two numeric values with no common carrier" and "Two values compared
//! by `==` or `!=` whose types share no value"). Two values meet when their carriers do, so
//! `a == b` with `a = 1` and `b = 2` stays legal. A literal with a suffix is a value of its
//! carrier like any other: `x == 1r` with `x: bool` is rejected as `x == r` with `r: rat` is.
//! A comparison with an atom, or with a side that holds only atoms, stays legal, and so does
//! one with a side that holds a type variable or the unknown.

use zed_kernel::Value;
use zed_kernel::types::Type;
use zedc::check::ty::{Carrier, Ty};
use zedc::rejection::Row;

use super::type_errors;

/// The rejection of `a op b`, of the types `ta` and `tb` at their carriers, that no repair
/// fits.
fn answer(a: &str, ta: &str, op: &str, b: &str, tb: &str) -> String {
    let ans = op != "==";
    format!(
        "No value is both `{ta}` and `{tb}`: `{a} : {ta} {op} {b} : {tb}` is always `{ans}`. \
         Try `{ans}` instead. [{a} {op} {b}]"
    )
}

/// The rejection of `a op b`, of the types `ta` and `tb`, with the repairs `repairs`.
fn repaired(a: &str, ta: &str, op: &str, b: &str, tb: &str, repairs: &str) -> String {
    format!(
        "No value is both `{ta}` and `{tb}`: `{a} : {ta} {op} {b} : {tb}` always gives the same \
         answer. Try {repairs} instead. [{a} {op} {b}]"
    )
}

#[test]
fn a_literal_with_a_suffix_compared_with_a_value_that_holds_no_number_is_rejected() {
    assert_eq!(
        type_errors("f(positional x: bool) = x == 1r;\n"),
        [answer("x", "bool", "==", "1r", "rat")]
    );
    // The other order, a literal forced to `f64`, `!=`, and an atom on the other side.
    assert_eq!(
        type_errors("f(positional x: bool | #none) = 1.5f64 != x;\n"),
        [answer("1.5f64", "f64", "!=", "x", "bool | #none")]
    );
    assert_eq!(
        type_errors("f(positional x: bool) = -2r == x;\n"),
        [answer("-2r", "rat", "==", "x", "bool")]
    );
    // A cast of the text is no repair: `#invalid` makes it narrowing (DESIGN.md
    // sec:diagnostics).
    assert_eq!(
        type_errors("f(positional x: String) = x == 1r;\n"),
        [answer("x", "String", "==", "1r", "rat")]
    );
    assert_eq!(
        type_errors("f(positional x: String) = 2.5f64 == x;\n"),
        [answer("2.5f64", "f64", "==", "x", "String")]
    );
    // A tuple: only the components that may equal the literal are offered.
    assert_eq!(
        type_errors("f(positional x: (int, rat)) = x == 1r;\n"),
        [repaired(
            "x",
            "(int, rat)",
            "==",
            "1r",
            "rat",
            "`x[1] == 1r` to compare a component"
        )]
    );
    assert_eq!(
        type_errors("f(positional x: (int, int)) = x == 1r;\n"),
        [answer("x", "(int, int)", "==", "1r", "rat")]
    );
}

#[test]
fn a_component_of_a_written_tuple_is_named_by_its_place() {
    assert_eq!(
        type_errors("f(positional p: (bool, int)) = p == (1r, 2);\n"),
        [
            "No value is both `bool` and `rat`: `p[0] : bool` compared by `==` with component `[0]` \
             of the right operand is always `false`. Try `false` instead. [p == (1r, 2)]"
        ]
    );
    // Of two components that share no value, the first written is named.
    assert_eq!(
        type_errors("f(positional p: (bool, int, String)) = (1r, 2, true) != p;\n"),
        [
            "No value is both `rat` and `bool`: component `[0]` of the left operand compared by `!=` \
             with `p[0] : bool` is always `true`. Try `true` instead. [(1r, 2, true) != p]"
        ]
    );
    // Nested: the place goes down each level.
    assert_eq!(
        type_errors("f(positional p: (int, (int, bool))) = p == (1, (2, 1r));\n"),
        [
            "No value is both `bool` and `rat`: `p[1][1] : bool` compared by `==` with component \
             `[1][1]` of the right operand is always `false`. Try `false` instead. \
             [p == (1, (2, 1r))]"
        ]
    );
}

#[test]
fn two_values_that_no_value_is_both_of_are_rejected() {
    let bs = "f(positional b: bool, positional s: String) = ";
    assert_eq!(
        type_errors(&format!("{bs}b == s;\n")),
        [answer("b", "bool", "==", "s", "String")]
    );
    assert_eq!(
        type_errors(&format!("{bs}s != b;\n")),
        [answer("s", "String", "!=", "b", "bool")]
    );
    // A union none of whose members the other side holds.
    assert_eq!(
        type_errors("f(positional x: bool | (int, int), positional s: String) = x == s;\n"),
        [answer("x", "bool | (int, int)", "==", "s", "String")]
    );
    // An atom on one side only does not make them meet.
    assert_eq!(
        type_errors("f(positional x: bool | #none, positional s: String) = x == s;\n"),
        [answer("x", "bool | #none", "==", "s", "String")]
    );
    // Two tuples of different lengths, and two that differ in a nested component.
    assert_eq!(
        type_errors("f(positional p: (int, int), positional q: (int, int, int)) = p == q;\n"),
        [answer("p", "(int, int)", "==", "q", "(int, int, int)")]
    );
    assert_eq!(
        type_errors(
            "f(positional p: (bool, (int, String)), positional q: (bool, (int, int))) = \
             p == q;\n"
        ),
        [answer(
            "p",
            "(bool, (int, String))",
            "==",
            "q",
            "(bool, (int, int))"
        )]
    );
    // A name bound to a literal is a value of the literal's carrier.
    assert_eq!(
        type_errors("f(positional s: String) = { a = 1r; a == s };\n"),
        [answer("a", "rat", "==", "s", "String")]
    );
}

#[test]
fn two_numbers_of_no_common_carrier_get_no_narrowing_cast() {
    // No value is converted implicitly, and an `int` is never equal to an `f64`. Each cast that
    // would make them meet narrows (`f64(n)` of an unbounded `int`, `int(y)`, `f64(r)`,
    // `rat(y)`), so none is offered.
    let text = "f(positional n: int, positional y: f64) = n == y;\n";
    assert_eq!(type_errors(text), [answer("n", "int", "==", "y", "f64")]);
    let (info, _) = zed_tests::step_helpers::l01_26_type_resolution::info(text);
    assert_eq!(info.errors[0].row, Some(Row::NoCommonCarrier));
    assert_eq!(
        type_errors("f(positional r: rat, positional y: f64) = r != y;\n"),
        [answer("r", "rat", "!=", "y", "f64")]
    );
    // A string and a number: no cast of the text, which `#invalid` makes narrowing.
    let text = "f(positional s: String, positional n: int) = s == n;\n";
    assert_eq!(type_errors(text), [answer("s", "String", "==", "n", "int")]);
    let (info, _) = zed_tests::step_helpers::l01_26_type_resolution::info(text);
    assert_eq!(info.errors[0].row, Some(Row::EqNoCommonCarrier));
}

#[test]
fn components_that_may_be_equal_are_offered() {
    assert_eq!(
        type_errors("f(positional x: (int, int), positional y: int) = x == y;\n"),
        [repaired(
            "x",
            "(int, int)",
            "==",
            "y",
            "int",
            "`x[0] == y` or `x[1] == y` to compare a component"
        )]
    );
    assert_eq!(
        type_errors("f(positional y: String, positional x: (int, String)) = y != x;\n"),
        [repaired(
            "y",
            "String",
            "!=",
            "x",
            "(int, String)",
            "`y != x[1]` to compare a component"
        )]
    );
}

/// The repair steps of the rejection of `text`, in order.
fn repairs(text: &str) -> Vec<String> {
    let (info, _) = zed_tests::step_helpers::l01_26_type_resolution::info(text);
    assert_eq!(info.errors.len(), 1, "{:?}", info.errors);
    (info.errors[0].notes.iter())
        .filter_map(|n| n.text.strip_prefix("repair: ").map(str::to_owned))
        .collect()
}

#[test]
fn the_menu_is_given_again_as_repair_steps_in_its_order() {
    let casts = repairs("f(positional n: int, positional y: f64) = n == y;\n");
    assert_eq!(casts, ["write `false` in place of `n == y`"]);
    let parts = repairs("f(positional x: (int, int), positional y: int) = x == y;\n");
    assert_eq!(parts, ["write `x[0] == y`", "write `x[1] == y`"]);
    let none = repairs("f(positional b: bool, positional s: String) = b != s;\n");
    assert_eq!(none, ["write `true` in place of `b != s`"]);
    let inside = repairs("f(positional p: (bool, int)) = p == (1r, 2);\n");
    assert_eq!(inside, ["write `false` in place of the comparison"]);
}

#[test]
fn comparisons_whose_sides_may_share_a_value_stay_legal() {
    for ok in [
        // Two literals bound to names meet at their carrier.
        "f() = { a = 1; b = 2; a == b };\n",
        "f(positional x: bool | #none) = x == #none;\n",
        "f(positional a: int, positional b: int) = (a div b) == #divByZero;\n",
        "f(positional x: #a | #b) = x == #a;\n",
        "f(positional x: bool) = x == true;\n",
        "f(positional x: String) = rat(x) == 1r;\n",
        "f(positional x: (int, rat)) = x[1] == 1r;\n",
        "f(positional x: rat | String) = x == 1r;\n",
        "f(positional x: f64) = x == 1;\n",
        "f(positional x: f64) = x == 1.5f64;\n",
        "f(positional p: (int, bool)) = p == (1, true);\n",
        "f(positional x: int | String, positional y: bool | String) = x == y;\n",
        "f(positional x: (int, int) | (bool, String), positional y: (bool, String)) = x == y;\n",
        // A type variable may be anything.
        "f(positional x, positional y: bool) = x == y;\n",
        "f(positional x, positional y: (bool, int)) = (x, 1) == y;\n",
    ] {
        assert!(type_errors(ok).is_empty(), "{ok}: {:?}", type_errors(ok));
    }
}

#[test]
fn a_literal_rejected_by_its_carrier_is_not_rejected_twice() {
    // The literal's own rejection names the comparison; this one adds nothing.
    let errors = type_errors("f(positional x: int) = x == 1.5f64;\n");
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(
        errors[0].starts_with("The suffix makes the literal `1.5f64`"),
        "{errors:?}"
    );
}

fn int(n: i64) -> Ty {
    Ty::lit(&Value::Int(n))
}

#[test]
fn carriers_widen_each_value_to_its_carrier_and_keep_the_rest() {
    let none = Ty::set(Type::atom("none"));
    let t = int(1).union(&int(2)).union(&none);
    assert_eq!(t.carriers(), Ty::carrier(Carrier::Int).union(&none));
    let pair = Ty::tuple(vec![int(1), Ty::lit(&Value::Bool(true))]);
    assert_eq!(
        pair.carriers(),
        Ty::tuple(vec![Ty::carrier(Carrier::Int), Ty::carrier(Carrier::Bool)])
    );
    // A carrier, an atom, a variable and the empty type are as they were.
    for t in [
        Ty::carrier(Carrier::Str),
        none,
        Ty::var("a".into()),
        Ty::empty(),
    ] {
        assert_eq!(t.carriers(), t);
    }
    assert!(int(1).carriers().meets(&int(2).carriers()));
    assert!(!int(1).carriers().meets(&Ty::carrier(Carrier::Rat)));
}

/// Tuples nested `d` deep, `((…(b, int)…, int), int)`.
fn nested(d: usize, b: Ty) -> Ty {
    (0..d).fold(b, |t, _| Ty::tuple(vec![t, int(0)]))
}

/// The carriers of tuples nested `d` deep meet when their bottoms share a carrier and not
/// otherwise.
pub(super) fn carriers_of_nested_tuples(d: usize) {
    let (a, b) = (
        nested(d, int(1)).carriers(),
        nested(d, Ty::carrier(Carrier::Str)).carriers(),
    );
    assert!(a.meets(&nested(d, int(7)).carriers()), "{d} deep");
    assert!(!a.meets(&b), "{d} deep");
}

#[test]
fn carriers_of_a_nested_tuple_meet_by_the_carrier_at_the_bottom() {
    // Small instances of the benchmark
    // `bench::no_common_value::carriers_of_a_deep_tuple_run_on_a_shallow_stack`.
    for d in 0..5 {
        carriers_of_nested_tuples(d);
    }
}

/// `x == y` with `x` a union of `n` tuples `(#ak, String)` and `y` one of `n` tuples
/// `(#ak, int)`: a scan of each arm against each would compare `n^2` pairs.
pub(super) fn wide_union(n: usize) -> String {
    let arms = |last: &str| {
        (0..n)
            .map(|k| format!("(#a{k}, {last})"))
            .collect::<Vec<_>>()
    };
    format!(
        "f(positional x: {}, positional y: {}) = x == y;\n",
        arms("String").join(" | "),
        arms("int").join(" | ")
    )
}

/// `x == y` with `x` and `y` tuples of `n` components, the last `String` in one and `int` in
/// the other.
pub(super) fn wide_tuples(n: usize) -> String {
    let ints = vec!["int"; n - 1].join(", ");
    format!("f(positional x: ({ints}, String), positional y: ({ints}, int)) = x == y;\n")
}

/// `p == (0, …, 0, 1r)` with `p` a tuple of `n` components, the last `bool`.
pub(super) fn wide_written(n: usize) -> String {
    let ints = vec!["int"; n - 1].join(", ");
    let zeros = vec!["0"; n - 1].join(", ");
    format!("f(positional p: ({ints}, bool)) = p == ({zeros}, 1r);\n")
}

/// `t(k+1) = (t(k), t(k))` from `t(0) = 1`: `2^n` paths through `n` nodes.
pub(super) fn shared(n: usize) -> Ty {
    (0..n).fold(int(1), |t, _| Ty::tuple(vec![t.clone(), t]))
}

#[test]
fn carriers_of_shared_tuples_widen_each_component() {
    // A small instance of the benchmark `bench::no_common_value::carriers_of_shared_tuples_scale`.
    let int_ = Ty::carrier(Carrier::Int);
    let pair = Ty::tuple(vec![int_.clone(), int_]);
    assert_eq!(shared(2).carriers(), Ty::tuple(vec![pair.clone(), pair]));
}

#[test]
fn two_wide_types_that_share_no_value_are_rejected() {
    // A small instance of each benchmark
    // `bench::no_common_value::rejecting_two_wide_types_that_share_no_value_scales_for_…`.
    let errors = type_errors(&wide_union(2));
    assert_eq!(
        errors,
        [answer(
            "x",
            "(#a0, String) | (#a1, String)",
            "==",
            "y",
            "(#a0, int) | (#a1, int)"
        )]
    );
    assert_eq!(
        type_errors(&wide_written(3)),
        [
            "No value is both `bool` and `rat`: `p[2] : bool` compared by `==` with component `[2]` \
             of the right operand is always `false`. Try `false` instead. [p == (0, 0, 1r)]"
        ]
    );
    for text in [wide_union(3), wide_tuples(3), wide_written(3)] {
        let (info, _) = super::info(&text);
        let rows: Vec<_> = info.errors.iter().map(|e| e.row).collect();
        assert_eq!(rows, [Some(Row::EqNoCommonCarrier)], "{text}");
    }
}
