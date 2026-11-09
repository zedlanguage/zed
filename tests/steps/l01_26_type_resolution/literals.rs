//! A generic literal `kn` takes the carrier its context expects wherever the context gives
//! one: an operand of `==` against a parameter whose carrier is inferred, a parameter declared
//! as a union with one numeric member, and a component of a tuple, at any depth (DESIGN.md
//! L1.26, L1.26a, sec:domains). A plain literal keeps its own carrier in each of these places,
//! and where that carrier is not expected it is rejected with the forms to write.

use std::path::PathBuf;

use zed_kernel::{F64, Value};
use zed_tests::scaling;
use zedc::testing::test;

use super::{info, type_errors};
use zed_tests::step_helpers::l01_16_elaboration::value;

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

/// The menu for the plain literal `lit` where `want` is expected, at the expression `at`.
fn menu(lit: &str, carrier: &str, want: &str, forms: &str, at: &str) -> String {
    let forms = match forms {
        "" => String::new(),
        f => format!("; write {f}"),
    };
    format!(
        "`{lit}` is {carrier} where `{want}` is expected; a literal takes no other carrier\
         {forms} [{at}]"
    )
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
fn a_generic_literal_compared_with_an_inferred_parameter_follows_its_carrier() {
    let one = "isOne(positional x) = x == 1n;\n";
    assert_eq!(value(&format!("{one}y = isOne(1.0);\n"), "y"), "true");
    assert_eq!(value(&format!("{one}y = isOne(1r);\n"), "y"), "true");
    assert_eq!(value(&format!("{one}y = isOne(1);\n"), "y"), "true");
    assert_eq!(value(&format!("{one}y = isOne(2.0);\n"), "y"), "false");
    // On either side, and under `-` and `!=`.
    let left = "isOne(positional x) = 1n == x;\ny = isOne(1.0);\n";
    assert_eq!(value(left, "y"), "true");
    let neg = "isMinus(positional x) = x == -1n;\ny = isMinus(-1r);\n";
    assert_eq!(value(neg, "y"), "true");
    let ne = "notOne(positional x) = x != 1n;\ny = notOne(1.0);\n";
    assert_eq!(value(ne, "y"), "false");
}

#[test]
fn a_plain_literal_compared_with_an_inferred_parameter_fixes_its_carrier() {
    // `x == 1` makes `isOne` take an int, so a call at an f64 is rejected at its argument.
    let one = "isOne(positional x) = x == 1;\n";
    assert_eq!(value(&format!("{one}y = isOne(1);\n"), "y"), "true");
    assert_eq!(
        type_errors(&format!("{one}y = isOne(1.0);\n")),
        [menu("1.0", "an f64", "int", "", "1.0")]
    );
    // A decimal fixes f64, and no rat is one; a decimal takes no `n`.
    let half = "isHalf(positional x) = x == 0.5;\n";
    assert_eq!(value(&format!("{half}y = isHalf(0.5);\n"), "y"), "true");
    assert_eq!(
        type_errors(&format!("{half}y = isHalf(0.5r);\n")),
        [
            "`isHalf` does not take (5e-1r): these are the types of its arguments here, and `isHalf` has no arrow that takes them all [isHalf(0.5r)]"
        ]
    );
    assert_eq!(
        type_errors(&format!("{half}y = isHalf(1);\n")),
        [menu("1", "an int", "f64", "`1.0` or `1n`", "1")]
    );
}

#[test]
fn a_generic_literal_that_is_no_value_of_the_carrier_it_follows_is_unequal() {
    // 9007199254740993 is no f64: compared with one at run time, no f64 equals it.
    let big = "isBig(positional x) = x == 9007199254740993n;\n";
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
fn a_literal_at_a_union_with_one_numeric_member() {
    // The generic literal takes it; the plain one of another carrier is rejected.
    let text = "f(positional x: f64 | String) = x is f64;\ny = f(1n);\n";
    assert_eq!(adopted(text), [f64(1.0)]);
    assert_eq!(value(text, "y"), "true");
    assert_eq!(
        type_errors("f(positional x: f64 | String) = x is f64;\ny = f(1);\n"),
        [menu("1", "an int", "f64", "`1.0` or `1n`", "1")]
    );
    let text = "f(positional x: f64 | bool) = x == 1.0;\ny = f(1n);\n";
    assert_eq!(value(text, "y"), "true");
    let text = "f(positional x: rat | #none) = x is rat;\ny = f(-2n);\n";
    assert_eq!(value(text, "y"), "true");
    // A decimal at a union holding int and rat: its `r` form is the one offered.
    assert_eq!(
        type_errors("f(positional x: int | rat) = x is rat;\ny = f(0.5);\n"),
        [menu("0.5", "an f64", "int | rat", "`0.5r`", "0.5")]
    );
    let text = "f(positional x: int | rat) = x is rat;\ny = f(0.5r);\n";
    assert_eq!(value(text, "y"), "true");
}

#[test]
fn a_literal_at_a_union_of_two_carriers() {
    // Its own carrier among them: kept, nothing adopted.
    let text = "f(positional x: int | f64) = x is int;\ny = f(1);\n";
    assert!(adopted(text).is_empty());
    assert_eq!(value(text, "y"), "true");
    let text = "f(positional x: int | f64) = x is f64;\ny = f(0.5);\n";
    assert_eq!(value(text, "y"), "true");
    // Not among them: a plain literal is rejected with both forms.
    assert_eq!(
        type_errors("f(positional x: f64 | rat) = x;\ny = f(1);\n"),
        [menu("1", "an int", "rat | f64", "`1.0` or `1r`", "1")]
    );
    // A generic literal there names no one carrier, which is its own error.
    assert_eq!(
        type_errors("f(positional x: f64 | rat) = x;\ny = f(1n);\n"),
        [
            "`1n` at `rat | f64` adopts no one carrier: the type holds numbers of rat and f64; \
             write the one meant, as `1r` or `1.0` [1n]"
        ]
    );
    assert_eq!(
        type_errors("f(positional x: f64 | rat) = x;\ny = f(-1n);\n"),
        [
            "`-1n` at `rat | f64` adopts no one carrier: the type holds numbers of rat and f64; \
             write the one meant, as `-1r` or `-1.0` [-1n]"
        ]
    );
}

#[test]
fn generic_literals_in_a_tuple_take_its_components_carriers() {
    let text = "f(positional p: (f64, f64)) = p == (1.0, 2.0);\ny = f((1n, 2n));\n";
    assert_eq!(adopted(text), [f64(1.0), f64(2.0)]);
    assert_eq!(value(text, "y"), "true");
    // At any depth, beside components that are not literals.
    let text = "f(positional p: ((f64, String), rat)) = p == ((3.0, \"a\"), 1r / 2r);\n\
                y = f(((3n, \"a\"), 0.5r));\n";
    assert_eq!(value(text, "y"), "true");
    // An inexact component is an error at that literal.
    assert_eq!(
        type_errors("f(positional p: (f64, f64)) = p;\ny = f((9007199254740993n, 1n));\n"),
        [
            "`9007199254740993n` is not an f64: a literal written with `n` takes the carrier expected only when it is exactly a number of that carrier, and no f64 is exactly this number; write a literal that is exactly an f64, or write the number followed by `r` if the exact rational is meant [9007199254740993n]"
        ]
    );
}

#[test]
fn plain_literals_in_a_tuple_keep_their_carriers() {
    // `(1, 2)` at `(f64, f64)` is rejected, at its first integer.
    assert_eq!(
        type_errors("f(positional p: (f64, f64)) = p;\ny = f((1, 2));\n"),
        [menu("1", "an int", "f64", "`1.0` or `1n`", "1")]
    );
    assert_eq!(
        type_errors("f(positional p: (f64, f64)) = p;\ny = f((1.0, 2));\n"),
        [menu("2", "an int", "f64", "`2.0` or `2n`", "2")]
    );
    assert_eq!(
        value(
            "f(positional p: (f64, f64)) = p == (1.0, 2.0);\ny = f((1.0, 2.0));\n",
            "y"
        ),
        "true"
    );
}

#[test]
fn generic_literals_in_a_tuple_take_the_carrier_every_shape_of_its_length_holds_there() {
    // A position is a point or a named place with a distance from it: at the second
    // component both shapes hold f64, at the first only one holds a number.
    let ty = "(f64, f64) | (String, f64)";
    let text = format!("tu(positional p: {ty}) = p == (1.0, 2.0);\ny = tu((1n, 2n));\n");
    assert_eq!(adopted(&text), [f64(1.0), f64(2.0)]);
    assert_eq!(value(&text, "y"), "true");
    let text = format!("tu(positional p: {ty}) = p == (\"a\", 2.0);\ny = tu((\"a\", 2n));\n");
    assert_eq!(adopted(&text), [f64(2.0)]);
    assert_eq!(value(&text, "y"), "true");
    // A shape of another length does not count.
    let text = "tu(positional p: (f64, f64) | (rat, rat, rat)) = p == (1.0, 2.0);\n\
                y = tu((1n, 2n));\n";
    assert_eq!(value(text, "y"), "true");
    // Nested: the inner shapes are those of every outer shape at that component.
    let text = "tu(positional p: ((f64, String), int) | ((String, f64), int)) = \
                p == ((1.0, \"a\"), 3);\ny = tu(((1n, \"a\"), 3));\n";
    assert_eq!(adopted(text), [f64(1.0)]);
    assert_eq!(value(text, "y"), "true");
    // Numbers of two carriers at a component across the shapes: no one carrier, the same
    // error as for a lone literal.
    assert_eq!(
        type_errors("tu(positional p: (f64, String) | (rat, String)) = p;\ny = tu((1n, \"a\"));\n"),
        [
            "`1n` at `rat | f64` adopts no one carrier: the type holds numbers of rat and f64; \
             write the one meant, as `1r` or `1.0` [1n]"
        ]
    );
    // Two carriers, int among them: the generic literal is int, as the plain one is.
    let text = "tu(positional p: (int, String) | (f64, String)) = p == (1, \"a\");\n\
                y = tu((1n, \"a\"));\n";
    assert_eq!(value(text, "y"), "true");
    let text = "tu(positional p: (int, String) | (f64, String)) = p == (1, \"a\");\n\
                y = tu((1, \"a\"));\n";
    assert!(adopted(text).is_empty());
    assert_eq!(value(text, "y"), "true");
}

/// `tu` at a union of `w` tuple shapes of length 2, all but the last with a string first,
/// called on `(1n, 2n)`, on a tuple of `(1n, 2n)` nested 2 deep at the same shapes inside, and
/// compared by `==` with `(1n, 2n)`.
fn shapes(w: usize) -> String {
    let mut ty: Vec<String> = (0..w - 1)
        .map(|i| format!("(String, f64) | (#a{i}, f64)"))
        .collect();
    ty.push("(f64, f64)".into());
    let one = ty.join(" | ");
    format!(
        "tu(positional p: {one}) = 0;\ny = tu((1n, 2n));\n\
         tv(positional p: ({one}, {one})) = 0;\nz = tv(((1n, 2n), (3n, 4n)));\n\
         tw(positional p: {one}) = p == (1n, 2n);\n"
    )
}

#[test]
fn adopting_at_a_union_of_many_tuple_shapes_scales() {
    assert_eq!(
        adopted(&shapes(3)),
        [1.0, 2.0, 1.0, 2.0, 3.0, 4.0, 1.0, 2.0].map(f64)
    );
    checks_linearly(
        "adopting the literals of tuples at n tuple shapes",
        64,
        shapes,
        |_| 8,
    );
}

#[test]
fn literals_in_a_tuple_compared_with_a_tuple() {
    let text = "isOrigin(positional p: (f64, f64)) = p == (0n, 0n);\n\
                a = isOrigin((0.0, 0.0));\nb = isOrigin((0.0, 0.5));\n";
    assert_eq!(value(text, "a"), "true");
    assert_eq!(value(text, "b"), "false");
    // Two literal tuples: the generic integers take the other side's carriers.
    assert_eq!(
        value("y = (1n, (2n, 3n)) == (1.0, (2r, 3));\n", "y"),
        "true"
    );
    // Plain ones are rejected where the other side's carrier is not theirs.
    assert_eq!(
        type_errors("y = (1, (2, 3)) == (1.0, (2r, 3));\n"),
        [
            menu("1", "an int", "f64", "`1.0` or `1n`", "1"),
            menu("2", "an int", "rat", "`2r` or `2n`", "2"),
        ]
    );
    // A plain literal beside a value in a tuple: `(x, 1) == (y, z)` with `z: f64`.
    assert_eq!(
        type_errors(
            "f(positional x: f64, positional y: f64, positional z: f64) = (x, 1) == (y, z);\n"
        ),
        [menu("1", "an int", "f64", "`1.0` or `1n`", "1")]
    );
}

#[test]
fn sum_reads_generic_literals_at_the_other_components_carrier() {
    let text = "f(positional x: f64) = sum((x, 2n));\ny = f(1.0);\n";
    assert_eq!(value(text, "y"), "3.0");
    let text = "f(positional x: f64) = sum((2n, x, 3n));\ny = f(1.0);\n";
    assert_eq!(value(text, "y"), "6.0");
    assert_eq!(value("y = sum((1, 2));\n", "y"), "3");
    // A plain literal of another carrier is rejected, and only once: `sum` adds no error of
    // its own after the `+` it applies.
    assert_eq!(
        type_errors("f(positional x: f64) = sum((x, 2));\n"),
        [menu("2", "an int", "f64", "`2.0` or `2n`", "2")]
    );
    assert_eq!(
        type_errors("y = sum((1, 2.5));\n"),
        [menu("1", "an int", "f64", "`1.0` or `1n`", "1")]
    );
}

/// `isAt((0n, 1n, …))` of `w` components, compared with a tuple of `w` generic literals, and
/// `sum` of `w` generic literals beside a parameter.
fn wide(w: usize) -> String {
    let fs = vec!["f64"; w].join(", ");
    let zs: Vec<String> = (0..w).map(|i| format!("{i}n")).collect();
    let zs = zs.join(", ");
    format!(
        "isAt(positional p: ({fs})) = p == ({zs});\ny = isAt(({zs}));\n\
         s(positional x: f64) = sum((x, {zs}));\n"
    )
}

/// `isAt` of a tuple nested `d` deep, `((…(0n, 0n)…, 0n), 0n)`, at f64 components, called on
/// the same tuple of generic literals and compared with it.
fn deep(d: usize) -> String {
    let (mut ty, mut lit) = ("f64".to_string(), "0n".to_string());
    for _ in 0..d {
        ty = format!("({ty}, f64)");
        lit = format!("({lit}, 0n)");
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
        let info = zedc::check::walk::check(stmts, res);
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
    // The parser, the checker and the type printer recurse on the nesting, within a 2 MiB
    // stack at 1,024 deep (it ran on 512 MiB, TY-sub-stack).
    zed_tests::deep::on_small_stack(|| {
        assert_eq!(value(&deep(3), "y"), "true");
        checks_linearly(
            "adopting the literals of tuples nested n deep",
            128,
            deep,
            |m| 2 * (m + 1),
        );
    });
}

/// The operands of `p == ((…(0n, 0n)…, 0n), 0n)`, the tuple nested `d` deep, with `p` at f64
/// components, as in [`deep`].
fn deep_operands(d: usize) -> zedc::check::Operands {
    use zedc::check::ty::{Carrier, Ty};
    let nested = |c| {
        let mut t = Ty::carrier(c);
        for _ in 0..d {
            t = Ty::tuple(vec![t, Ty::carrier(c)]);
        }
        t
    };
    let mut lit = "0n".to_string();
    for _ in 0..d {
        lit = format!("({lit}, 0n)");
    }
    let stmts = zed_tests::deep::statements(&format!("y = {lit};\n"));
    let Some(zedc::ast::StmtKind::Bind { value, .. }) = stmts.into_iter().next().map(|s| s.kind)
    else {
        unreachable!("a binding")
    };
    zedc::check::Operands::new(nested(Carrier::F64), value, nested(Carrier::Int))
}

#[test]
fn pairing_the_sides_of_a_deep_comparison_scales() {
    // The check of the whole program in `adopting_the_literals_of_a_deep_tuple_scales` spends
    // about 357,000 instructions a level, most of them outside `==`, and that hides a `sides`
    // that walks each level's whole type for variables, O(d^2) with no allocation: the test
    // passed such a `sides` at 9.1 times the instructions from depth 128 to 1,024. Here the
    // operands are built before the timing, and only their pairing by `==` is timed. The
    // pairing itself spends about 106,000 instructions a level, most in `class_of_ty` of each
    // literal's carrier, so the O(d^2) walk reaches the limit only from depth 2,048: that
    // `sides` takes 37.3 times the instructions from 2,048 to 16,384 here, and this one 8.0.
    assert_eq!(deep_operands(3).adoptions(), 4);
    let ops: Vec<_> = [2048, scaling::FACTOR * 2048]
        .into_iter()
        .map(|d| (d, deep_operands(d)))
        .collect();
    scaling::check_order(
        "pairing the sides of == of tuples nested n deep",
        2048,
        1,
        |d| {
            let (_, o) = ops.iter().find(|(k, _)| *k == d).unwrap();
            assert_eq!(o.adoptions(), d + 1);
        },
    );
}

#[test]
fn a_literal_compared_with_a_union() {
    // One numeric member: the generic literal takes it, the plain one of another carrier is
    // rejected.
    let text = "f(positional x: f64 | String) = x == 1n;\ny = f(1.0);\n";
    assert_eq!(adopted(text), [f64(1.0)]);
    assert_eq!(value(text, "y"), "true");
    assert_eq!(
        type_errors("f(positional x: f64 | String) = x == 1;\n"),
        [menu("1", "an int", "f64", "`1.0` or `1n`", "1")]
    );
    // Two, its own among them: it keeps its own, and an f64 is not an int.
    let text = "f(positional x: int | f64) = x == 1;\na = f(1);\nb = f(1.0);\n";
    assert!(adopted(text).is_empty());
    assert_eq!(value(text, "a"), "true");
    assert_eq!(value(text, "b"), "false");
    // Two, its own not among them: the plain literal is rejected, on either side, and the
    // generic one names no one carrier.
    let want = menu("1", "an int", "rat | f64", "`1.0` or `1r`", "1");
    assert_eq!(
        type_errors("f(positional x: f64 | rat) = x == 1;\n"),
        [want.as_str()]
    );
    assert_eq!(
        type_errors("f(positional x: f64 | rat) = 1 != x;\n"),
        [want.as_str()]
    );
    assert_eq!(
        type_errors("f(positional x: f64 | rat) = x == 1n;\n"),
        [
            "`1n` at `rat | f64` adopts no one carrier: the type holds numbers of rat and f64; \
             write the one meant, as `1r` or `1.0` [1n]"
        ]
    );
    // A class that `++` has narrowed to String holds no number.
    assert_eq!(
        type_errors("f(positional x) = (x ++ \"a\" == \"a\") && x == 1;\n"),
        ["`1` is an int, compared with a value of `String`, which holds no number [1]"]
    );
}

#[test]
fn generic_literals_in_a_tuple_compared_with_a_union_of_tuple_shapes_take_across_the_shapes() {
    let ty = "(f64, f64) | (String, f64)";
    let text = format!(
        "isAt(positional p: {ty}) = p == (1n, 2n);\na = isAt((1.0, 2.0));\n\
         b = isAt((\"a\", 2.0));\n"
    );
    assert_eq!(adopted(&text), [f64(1.0), f64(2.0)]);
    assert_eq!(value(&text, "a"), "true");
    assert_eq!(value(&text, "b"), "false");
    let text = format!("isAt(positional p: {ty}) = (\"a\", 2n) == p;\ny = isAt((\"a\", 2.0));\n");
    assert_eq!(value(&text, "y"), "true");
    // Nested, and beside a shape of another length.
    let text = "isAt(positional p: ((f64, String), int) | ((String, f64), int) | (rat, rat, rat)) = \
                p == ((1n, \"a\"), 3);\ny = isAt(((1.0, \"a\"), 3));\n";
    assert_eq!(value(text, "y"), "true");
    // Numbers of two carriers at a component across the shapes, neither the literal's own.
    assert_eq!(
        type_errors("isAt(positional p: (f64, f64) | (rat, rat)) = p == (1, 2.0);\n"),
        [menu("1", "an int", "rat | f64", "`1.0` or `1r`", "1")]
    );
}

#[test]
fn a_plain_literal_is_rejected_at_each_kind_of_declared_type() {
    // A typed parameter's default is checked against its type, as an argument is.
    assert_eq!(
        type_errors("scaled(x: f64, scale: f64 = 2) = x * scale;\n"),
        [menu("2", "an int", "f64", "`2.0` or `2n`", "2")]
    );
    assert_eq!(
        type_errors("scaled(x: f64, scale: f64 = \"x\") = x * scale;\n"),
        [
            "the default of `scale` is \"x\", not f64: a default is a value of its parameter's type [\"x\"]"
        ]
    );
    assert!(type_errors("scaled(x: f64, scale: f64 = 2n) = x * scale;\n").is_empty());
    // A literal in another base has no decimal form: only its generic form is offered.
    let f = "f(positional x: f64) = x;\n";
    assert_eq!(
        type_errors(&format!("{f}y = f(0xFF);\n")),
        [menu("0xFF", "an int", "f64", "`0xFFn`", "0xFF")]
    );
    assert_eq!(value(&format!("{f}y = f(0xFFn);\n"), "y"), "255.0");
    // A negative literal: the menu names the negation, and the span is the literal with its
    // `-`.
    assert_eq!(
        type_errors(&format!("{f}y = f(-3);\n")),
        [menu("-3", "an int", "f64", "`-3.0` or `-3n`", "-3")]
    );
    assert_eq!(value(&format!("{f}y = f(-3n);\n"), "y"), "-3.0");
}

/// `n` plain integers at an `f64` parameter, and `n` compared by `==` with a parameter whose
/// class `0.5` fixed at f64: each is rejected with its menu, `2 n` errors in all.
fn menus(n: usize) -> String {
    let calls: String = (0..n).map(|i| format!("y{i} = f({i});\n")).collect();
    let tests: Vec<String> = (0..n).map(|i| format!("x == {i}")).collect();
    format!(
        "f(positional x: f64) = x;\n{calls}g(positional x) = x == 0.5 || {};\n",
        tests.join(" || ")
    )
}

#[test]
fn rejecting_plain_literals_with_their_menus_scales() {
    assert_eq!(
        type_errors(&menus(2)),
        [
            menu("0", "an int", "f64", "`0.0` or `0n`", "0"),
            menu("1", "an int", "f64", "`1.0` or `1n`", "1"),
            menu("0", "an int", "f64", "`0.0` or `0n`", "0"),
            menu("1", "an int", "f64", "`1.0` or `1n`", "1"),
        ]
    );
    // A copy of every earlier error at each menu takes 45.2 times the bytes from 256 to 2,048
    // here, and fails; a scan of every earlier error's text at each menu does not, since the
    // checker's own work at each rejected literal is far larger than the scan up to n = 8,192.
    use zed_tests::deep::statements;
    let n = 256;
    let units: Vec<_> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| {
            let stmts = statements(&menus(m));
            let res = zedc::resolve::resolve(&stmts).unwrap();
            (m, stmts, res)
        })
        .collect();
    scaling::check_order(
        "rejecting n plain literals at a parameter and n compared with a class",
        n,
        1,
        |m| {
            let (_, stmts, res) = units.iter().find(|(k, _, _)| *k == m).unwrap();
            let info = zedc::check::walk::check(stmts, res);
            assert_eq!(info.errors.len(), 2 * m);
        },
    );
}
