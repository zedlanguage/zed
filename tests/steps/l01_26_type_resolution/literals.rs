//! A bare literal adopts the carrier its context expects wherever the context gives one: an
//! operand of `==` against a parameter whose carrier is inferred, a parameter declared as a
//! union with one numeric member, and a component of a tuple, at any depth (DESIGN.md
//! L1.26, sec:domains). The repairs of LIT-adopt.

use std::path::PathBuf;

use zed_kernel::{F64, Value};
use zed_tests::scaling;
use zedc::testing::test;

use super::{info, type_errors};
use crate::l01_16_elaboration::value;

/// The values the literals of `text` adopt, sorted by position.
fn adopted(text: &str) -> Vec<Value> {
    let (i, _) = info(text);
    let mut v: Vec<_> = i.adopt.into_iter().collect();
    v.sort_by_key(|(s, _)| s.start);
    v.into_iter().map(|(_, x)| x).collect()
}

fn f64(x: f64) -> Value {
    Value::Float(F64::new(x))
}

#[test]
fn the_readings_unit_passes_every_row() {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("steps/l01_26_type_resolution/zed/readings.zed");
    let outcomes = test(&std::fs::read_to_string(path).unwrap());
    assert_eq!(outcomes.len(), 18);
    let failed: Vec<_> = outcomes.iter().filter(|o| o.failure.is_some()).collect();
    assert!(failed.is_empty(), "{failed:?}");
}

#[test]
fn a_literal_compared_with_an_inferred_parameter_follows_its_carrier() {
    let one = "isOne(positional x) = x == 1;\n";
    assert_eq!(value(&format!("{one}y = isOne(1.0);\n"), "y"), "true");
    assert_eq!(value(&format!("{one}y = isOne(1r);\n"), "y"), "true");
    assert_eq!(value(&format!("{one}y = isOne(1);\n"), "y"), "true");
    assert_eq!(value(&format!("{one}y = isOne(2.0);\n"), "y"), "false");
    // On either side, and under `-` and `!=`.
    let left = "isOne(positional x) = 1 == x;\ny = isOne(1.0);\n";
    assert_eq!(value(left, "y"), "true");
    let neg = "isMinus(positional x) = x == -1;\ny = isMinus(-1r);\n";
    assert_eq!(value(neg, "y"), "true");
    let ne = "notOne(positional x) = x != 1;\ny = notOne(1.0);\n";
    assert_eq!(value(ne, "y"), "false");
    // A decimal literal follows a rat; it never follows an int.
    let half = "isHalf(positional x) = x == 0.5;\n";
    assert_eq!(value(&format!("{half}y = isHalf(1r / 2r);\n"), "y"), "true");
    assert_eq!(value(&format!("{half}y = isHalf(1);\n"), "y"), "false");
}

#[test]
fn a_literal_that_is_no_value_of_the_carrier_it_follows_is_unequal() {
    // 9007199254740993 is no f64: compared with one it keeps its own carrier, and no f64
    // equals it.
    let big = "isBig(positional x) = x == 9007199254740993;\n";
    assert_eq!(
        value(&format!("{big}y = isBig(9007199254740993);\n"), "y"),
        "true"
    );
    assert_eq!(
        value(&format!("{big}y = isBig(9007199254740992.0);\n"), "y"),
        "false"
    );
}

#[test]
fn a_literal_argument_at_an_open_type_variable_keeps_its_own_carrier() {
    // `g`'s parameter is a variable that the call fixes from its one argument, the literal,
    // so `1` is an int there, and an int is not an f64: no value is converted.
    let text = "outer(positional x) = {\n  g(positional y) = y == x;\n  g(1)\n};\n\
                a = outer(1);\nb = outer(1.0);\n";
    assert_eq!(value(text, "a"), "true");
    assert_eq!(value(text, "b"), "false");
}

#[test]
fn a_literal_adopts_the_one_numeric_member_of_a_union() {
    let text = "f(positional x: f64 | String) = x is f64;\ny = f(1);\n";
    assert_eq!(adopted(text), [f64(1.0)]);
    assert_eq!(value(text, "y"), "true");
    let text = "f(positional x: f64 | bool) = x == 1.0;\ny = f(1);\n";
    assert_eq!(value(text, "y"), "true");
    let text = "f(positional x: rat | #none) = x is rat;\ny = f(-2);\n";
    assert_eq!(value(text, "y"), "true");
    // A decimal literal at a union whose one carrier it can adopt is rat.
    let text = "f(positional x: int | rat) = x is rat;\ny = f(0.5);\n";
    assert_eq!(value(text, "y"), "true");
}

#[test]
fn a_literal_keeps_its_carrier_at_a_union_of_two_it_can_adopt() {
    // Its own carrier among them: kept, nothing adopted.
    let text = "f(positional x: int | f64) = x is int;\ny = f(1);\n";
    assert!(adopted(text).is_empty());
    assert_eq!(value(text, "y"), "true");
    let text = "f(positional x: int | f64) = x is f64;\ny = f(0.5);\n";
    assert_eq!(value(text, "y"), "true");
    // Not among them: the type names no one carrier, which is its own error.
    assert_eq!(
        type_errors("f(positional x: f64 | rat) = x;\ny = f(1);\n"),
        [
            "`1` at `rat | f64` adopts no one carrier: the type holds numbers of rat and f64; \
             write the one meant, as `1r` or `1.0` [1]"
        ]
    );
    assert_eq!(
        type_errors("f(positional x: f64 | rat) = x;\ny = f(-1);\n"),
        [
            "`-1` at `rat | f64` adopts no one carrier: the type holds numbers of rat and f64; \
             write the one meant, as `-1r` or `-1.0` [1]"
        ]
    );
}

#[test]
fn literals_in_a_tuple_adopt_its_components_carriers() {
    let text = "f(positional p: (f64, f64)) = p == (1.0, 2.0);\ny = f((1, 2));\n";
    assert_eq!(adopted(text), [f64(1.0), f64(2.0)]);
    assert_eq!(value(text, "y"), "true");
    // At any depth, beside components that are not literals.
    let text = "f(positional p: ((f64, String), rat)) = p == ((3.0, \"a\"), 1r / 2r);\n\
                y = f(((3, \"a\"), 0.5));\n";
    assert_eq!(value(text, "y"), "true");
    // An inexact component is an error at that literal.
    assert_eq!(
        type_errors("f(positional p: (f64, f64)) = p;\ny = f((9007199254740993, 1));\n"),
        ["`9007199254740993` is not an f64 [9007199254740993]"]
    );
}

#[test]
fn literals_in_a_tuple_adopt_the_carrier_every_shape_of_its_length_holds_there() {
    // A position is a point or a named place with a distance from it: at the second
    // component both shapes hold f64, at the first only one holds a number.
    let ty = "(f64, f64) | (String, f64)";
    let text = format!("tu(positional p: {ty}) = p == (1.0, 2.0);\ny = tu((1, 2));\n");
    assert_eq!(adopted(&text), [f64(1.0), f64(2.0)]);
    assert_eq!(value(&text, "y"), "true");
    let text = format!("tu(positional p: {ty}) = p == (\"a\", 2.0);\ny = tu((\"a\", 2));\n");
    assert_eq!(adopted(&text), [f64(2.0)]);
    assert_eq!(value(&text, "y"), "true");
    // A shape of another length does not count.
    let text = "tu(positional p: (f64, f64) | (rat, rat, rat)) = p == (1.0, 2.0);\n\
                y = tu((1, 2));\n";
    assert_eq!(value(text, "y"), "true");
    // Nested: the inner shapes are those of every outer shape at that component.
    let text = "tu(positional p: ((f64, String), int) | ((String, f64), int)) = \
                p == ((1.0, \"a\"), 3);\ny = tu(((1, \"a\"), 3));\n";
    assert_eq!(adopted(text), [f64(1.0)]);
    assert_eq!(value(text, "y"), "true");
    // Numbers of two carriers at a component across the shapes: no one carrier, so the
    // literal keeps int, which no shape takes there.
    let errors =
        type_errors("tu(positional p: (f64, String) | (rat, String)) = p;\ny = tu((1, \"a\"));\n");
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(errors[0].contains("does not take"), "{errors:?}");
}

/// `tu` at a union of `w` tuple shapes of length 2, all but the last with a string first,
/// called on `(1, 2)`, and on a tuple of `(1, 2)` nested 2 deep at the same shapes inside.
fn shapes(w: usize) -> String {
    let mut ty: Vec<String> = (0..w - 1)
        .map(|i| format!("(String, f64) | (#a{i}, f64)"))
        .collect();
    ty.push("(f64, f64)".into());
    let one = ty.join(" | ");
    format!(
        "tu(positional p: {one}) = 0;\ny = tu((1, 2));\n\
         tv(positional p: ({one}, {one})) = 0;\nz = tv(((1, 2), (3, 4)));\n"
    )
}

#[test]
fn adopting_at_a_union_of_many_tuple_shapes_scales() {
    assert_eq!(adopted(&shapes(3)), [1.0, 2.0, 1.0, 2.0, 3.0, 4.0].map(f64));
    checks_linearly(
        "adopting the literals of tuples at n tuple shapes",
        64,
        shapes,
        |_| 6,
    );
}

#[test]
fn literals_in_a_tuple_compared_with_a_tuple_adopt_its_components() {
    let text = "isOrigin(positional p: (f64, f64)) = p == (0, 0);\n\
                a = isOrigin((0.0, 0.0));\nb = isOrigin((0.0, 0.5));\n";
    assert_eq!(value(text, "a"), "true");
    assert_eq!(value(text, "b"), "false");
    // Two literal tuples: the integers adopt the other side's carriers.
    assert_eq!(value("y = (1, (2, 3)) == (1.0, (2r, 3));\n", "y"), "true");
}

#[test]
fn sum_reads_literals_at_the_other_components_carrier() {
    let text = "f(positional x: f64) = sum((x, 2));\ny = f(1.0);\n";
    assert_eq!(value(text, "y"), "3.0");
    let text = "f(positional x: f64) = sum((2, x, 3));\ny = f(1.0);\n";
    assert_eq!(value(text, "y"), "6.0");
    assert_eq!(value("y = sum((1, 2.5));\n", "y"), "3.5");
    assert_eq!(value("y = sum((1, 2));\n", "y"), "3");
}

/// `isAt((0, 0, …))` of `w` components, compared with a tuple of `w` literals, and `sum` of
/// `w` literals beside a parameter.
fn wide(w: usize) -> String {
    let fs = vec!["f64"; w].join(", ");
    let zs: Vec<String> = (0..w).map(|i| i.to_string()).collect();
    let zs = zs.join(", ");
    format!(
        "isAt(positional p: ({fs})) = p == ({zs});\ny = isAt(({zs}));\n\
         s(positional x: f64) = sum((x, {zs}));\n"
    )
}

/// `isAt` of a tuple nested `d` deep, `((…(0, 0)…, 0), 0)`, at f64 components, called on the
/// same tuple of literals and compared with it.
fn deep(d: usize) -> String {
    let (mut ty, mut lit) = ("f64".to_string(), "0".to_string());
    for _ in 0..d {
        ty = format!("({ty}, f64)");
        lit = format!("({lit}, 0)");
    }
    format!("isAt(positional p: {ty}) = p == {lit};\ny = isAt({lit});\n")
}

/// Checks the programs `text(n)` and `text(8n)`, lexed, parsed and resolved before timing,
/// and checks the checker's work is linear; each check adopts `adopts(n)` literals.
fn checks_linearly(what: &str, n: usize, text: fn(usize) -> String, adopts: fn(usize) -> usize) {
    use zed_tests::deep::statements;
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
        let info = zedc::check::check(stmts, res);
        assert!(info.errors.is_empty(), "{:?}", info.errors);
        assert_eq!(info.adopt.len(), adopts(m));
    });
}

#[test]
fn adopting_the_literals_of_a_wide_tuple_scales() {
    assert_eq!(adopted(&wide(3)).len(), 9);
    checks_linearly(
        "adopting the literals of tuples of width n",
        64,
        wide,
        |m| 3 * m,
    );
}

#[test]
fn adopting_the_literals_of_a_deep_tuple_scales() {
    // The parser, the checker and the type printer recurse on the nesting.
    std::thread::Builder::new()
        .stack_size(1 << 29)
        .spawn(|| {
            assert_eq!(value(&deep(3), "y"), "true");
            checks_linearly(
                "adopting the literals of tuples nested n deep",
                128,
                deep,
                |m| 2 * (m + 1),
            );
        })
        .unwrap()
        .join()
        .unwrap();
}
