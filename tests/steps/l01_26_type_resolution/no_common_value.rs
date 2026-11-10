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
use zed_tests::deep::{on_small_stack, statements};
use zed_tests::scaling;
use zedc::check::ty::{Carrier, Ty};
use zedc::rejection::Row;

use super::type_errors;

/// The rejection of `a op b`, of the types `ta` and `tb` at their carriers, that no repair
/// fits.
fn answer(a: &str, ta: &str, op: &str, b: &str, tb: &str) -> String {
    let ans = op != "==";
    format!(
        "`{a}` is {} `{ta}` and `{b}` is {} `{tb}` here, and no value is both, so the \
         comparison always gives `{ans}`; write `{ans}` in place of `{a} {op} {b}` \
         [{a} {op} {b}]",
        article(ta),
        article(tb)
    )
}

/// The rejection of `a op b`, of the types `ta` and `tb`, with the repairs `repairs`.
fn repaired(a: &str, ta: &str, op: &str, b: &str, tb: &str, repairs: &str) -> String {
    format!(
        "`{a}` is {} `{ta}` and `{b}` is {} `{tb}` here, and no value is both, so the \
         comparison always gives the same answer; write {repairs} [{a} {op} {b}]",
        article(ta),
        article(tb)
    )
}

fn article(t: &str) -> &'static str {
    match t.as_bytes() {
        [b'a' | b'e' | b'i' | b'o', ..] | [b'f', b'0'..=b'9', ..] => "an",
        _ => "a",
    }
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
    // Text holds a number its cast reads.
    assert_eq!(
        type_errors("f(positional x: String) = x == 1r;\n"),
        [repaired(
            "x",
            "String",
            "==",
            "1r",
            "rat",
            "`rat(x) == 1r` to compare the numbers"
        )]
    );
    assert_eq!(
        type_errors("f(positional x: String) = 2.5f64 == x;\n"),
        [repaired(
            "2.5f64",
            "f64",
            "==",
            "x",
            "String",
            "`2.5f64 == f64(x)` to compare the numbers"
        )]
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
            "`p[0]` is a `bool` and component `[0]` of the right operand is a `rat` here, and \
             no value is both, so the comparison always gives `false`; write `false` in place \
             of the comparison [p == (1r, 2)]"
        ]
    );
    // Of two components that share no value, the first written is named.
    assert_eq!(
        type_errors("f(positional p: (bool, int, String)) = (1r, 2, true) != p;\n"),
        [
            "component `[0]` of the left operand is a `rat` and `p[0]` is a `bool` here, and \
             no value is both, so the comparison always gives `true`; write `true` in place of \
             the comparison [(1r, 2, true) != p]"
        ]
    );
    // Nested: the place goes down each level.
    assert_eq!(
        type_errors("f(positional p: (int, (int, bool))) = p == (1, (2, 1r));\n"),
        [
            "`p[1][1]` is a `bool` and component `[1][1]` of the right operand is a `rat` here, \
             and no value is both, so the comparison always gives `false`; write `false` in \
             place of the comparison [p == (1, (2, 1r))]"
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
        [repaired(
            "a",
            "rat",
            "==",
            "s",
            "String",
            "`a == rat(s)` to compare the numbers"
        )]
    );
}

#[test]
fn two_numbers_of_no_common_carrier_get_the_casts_that_make_them_meet() {
    // No value is converted implicitly, and an `int` is never equal to an `f64`.
    let text = "f(positional n: int, positional y: f64) = n == y;\n";
    assert_eq!(
        type_errors(text),
        [repaired(
            "n",
            "int",
            "==",
            "y",
            "f64",
            "`f64(n) == y` or `n == int(y)` to compare the numbers"
        )]
    );
    let (info, _) = zed_tests::step_helpers::l01_26_type_resolution::info(text);
    assert_eq!(info.errors[0].row, Some(Row::NoCommonCarrier));
    assert_eq!(
        type_errors("f(positional r: rat, positional y: f64) = r != y;\n"),
        [repaired(
            "r",
            "rat",
            "!=",
            "y",
            "f64",
            "`f64(r) != y` or `r != rat(y)` to compare the numbers"
        )]
    );
    // A string and a number: the cast of the text.
    let text = "f(positional s: String, positional n: int) = s == n;\n";
    assert_eq!(
        type_errors(text),
        [repaired(
            "s",
            "String",
            "==",
            "n",
            "int",
            "`int(s) == n` to compare the numbers"
        )]
    );
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
    assert_eq!(casts, ["write `f64(n) == y`", "write `n == int(y)`"]);
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
    assert!(errors[0].starts_with("the literal `1.5f64`"), "{errors:?}");
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

#[test]
fn carriers_of_a_deep_tuple_run_on_a_2_mib_stack() {
    on_small_stack(|| {
        let (a, b) = (
            nested(100_000, int(1)).carriers(),
            nested(100_000, Ty::carrier(Carrier::Str)).carriers(),
        );
        assert!(a.meets(&nested(100_000, int(7)).carriers()));
        assert!(!a.meets(&b));
    });
}

#[test]
fn carriers_of_shared_tuples_scale() {
    // `t(k+1) = (t(k), t(k))` has `2^n` paths through `n` nodes; each is widened once.
    let shared = |n: usize| (0..n).fold(int(1), |t, _| Ty::tuple(vec![t.clone(), t]));
    let ts: Vec<_> = [512, scaling::FACTOR * 512]
        .into_iter()
        .map(|n| (n, shared(n)))
        .collect();
    scaling::check_order("carriers of n shared tuples", 512, 1, |n| {
        let (_, t) = ts.iter().find(|(k, _)| *k == n).unwrap();
        assert!(!t.carriers().is_empty());
    });
}

/// Checks the programs `text(n)` and `text(8n)`, lexed, parsed and resolved before timing,
/// and checks each is rejected once, in the row `row`, in time linear in n.
fn rejects_linearly(what: &str, n: usize, text: fn(usize) -> String, row: Row) {
    let units: Vec<_> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| {
            let stmts = statements(&text(m));
            let res = zedc::resolve::resolve(&stmts).unwrap();
            (m, stmts, res)
        })
        .collect();
    scaling::check_order(what, n, 1, |m| {
        let (_, stmts, res) = units.iter().find(|(k, _, _)| *k == m).unwrap();
        let info = zedc::check::walk::check(stmts, res);
        let rows: Vec<_> = info.errors.iter().map(|e| e.row).collect();
        assert_eq!(rows, [Some(row)], "{:?}", info.errors);
    });
}

/// `x == y` with `x` a union of `n` tuples `(#ak, String)` and `y` one of `n` tuples
/// `(#ak, int)`: a scan of each arm against each would compare `n^2` pairs.
fn wide_union(n: usize) -> String {
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
fn wide_tuples(n: usize) -> String {
    let ints = vec!["int"; n - 1].join(", ");
    format!("f(positional x: ({ints}, String), positional y: ({ints}, int)) = x == y;\n")
}

/// `p == (0, …, 0, 1r)` with `p` a tuple of `n` components, the last `bool`.
fn wide_written(n: usize) -> String {
    let ints = vec!["int"; n - 1].join(", ");
    let zeros = vec!["0"; n - 1].join(", ");
    format!("f(positional p: ({ints}, bool)) = p == ({zeros}, 1r);\n")
}

#[test]
fn rejecting_two_wide_types_that_share_no_value_scales() {
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
    rejects_linearly(
        "== of a union of n tuples",
        256,
        wide_union,
        Row::EqNoCommonCarrier,
    );
    rejects_linearly(
        "== of two tuples of n components",
        256,
        wide_tuples,
        Row::EqNoCommonCarrier,
    );
    assert_eq!(
        type_errors(&wide_written(3)),
        [
            "`p[2]` is a `bool` and component `[2]` of the right operand is a `rat` here, and \
             no value is both, so the comparison always gives `false`; write `false` in place \
             of the comparison [p == (0, 0, 1r)]"
        ]
    );
    rejects_linearly(
        "== of a tuple of n components and a written one",
        256,
        wide_written,
        Row::EqNoCommonCarrier,
    );
}
