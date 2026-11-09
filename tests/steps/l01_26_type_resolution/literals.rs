//! A bare literal takes the carrier its context gives wherever the context gives one: an
//! operand of `==` against a parameter whose carrier is inferred, a parameter declared as a
//! union with one numeric member, and a component of a tuple, at any depth (DESIGN.md L1.26,
//! L1.26a, L1.26b, sec:domains). Where the context gives two carriers and neither is `int`, or
//! none the literal can take, it is rejected with the forms to write.

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

/// The rejection of the literal `lit` at `rat | f64`, which can be either.
fn two_carriers(lit: &str) -> String {
    let digits = lit.trim_start_matches('-');
    let float = match digits.contains('.') {
        true => format!("{lit}f64"),
        false => format!("{lit}.0f64"),
    };
    format!(
        "the literal `{lit}` can be a `rat` or an `f64` at `rat | f64`, and nothing here chooses \
         one; write `{lit}r` or `{float}` [{lit}]"
    )
}

/// The rejection of the decimal literal `lit` where `int` is expected.
fn decimal_at_int(lit: &str) -> String {
    format!(
        "the literal `{lit}` is a decimal, and `int` is expected here; a decimal literal is never \
         an `int` [{lit}]"
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
fn a_literal_compared_with_an_inferred_parameter_follows_its_carrier() {
    let one = "isOne(positional x) = x == 1;\n";
    assert_eq!(value(&format!("{one}y = isOne(1.0f64);\n"), "y"), "true");
    assert_eq!(value(&format!("{one}y = isOne(1r);\n"), "y"), "true");
    assert_eq!(value(&format!("{one}y = isOne(1);\n"), "y"), "true");
    assert_eq!(value(&format!("{one}y = isOne(2.0f64);\n"), "y"), "false");
    // On either side, and under `-` and `!=`.
    let left = "isOne(positional x) = 1 == x;\ny = isOne(1.0f64);\n";
    assert_eq!(value(left, "y"), "true");
    let neg = "isMinus(positional x) = x == -1;\ny = isMinus(-1r);\n";
    assert_eq!(value(neg, "y"), "true");
    let ne = "notOne(positional x) = x != 1;\ny = notOne(1.0f64);\n";
    assert_eq!(value(ne, "y"), "false");
    // A decimal follows `rat` as well, exactly, and is unequal to every `int`.
    let half = "isHalf(positional x) = x == 0.5;\n";
    assert_eq!(value(&format!("{half}y = isHalf(0.5f64);\n"), "y"), "true");
    assert_eq!(value(&format!("{half}y = isHalf(1r / 2r);\n"), "y"), "true");
    assert_eq!(value(&format!("{half}y = isHalf(1);\n"), "y"), "false");
}

#[test]
fn a_literal_that_is_no_value_of_the_carrier_it_follows_is_unequal() {
    // 9007199254740993 is no f64: compared with one at run time, no f64 equals it.
    let big = "isBig(positional x) = x == 9007199254740993;\n";
    assert_eq!(
        value(&format!("{big}y = isBig(9007199254740993);\n"), "y"),
        "true"
    );
    assert_eq!(
        value(&format!("{big}y = isBig(9007199254740992.0f64);\n"), "y"),
        "false"
    );
}

#[test]
fn a_literal_argument_that_nothing_fixes_is_an_int() {
    // `g`'s parameter is a variable that the call fixes from its one argument, the literal,
    // which nothing else fixes, so `1` is an int there, and an int equals no f64.
    let text = "outer(positional x) = {\n  g(positional y) = y == x;\n  g(1)\n};\n\
                a = outer(1);\nb = outer(1.0f64);\n";
    assert_eq!(value(text, "a"), "true");
    assert_eq!(value(text, "b"), "false");
}

#[test]
fn a_literal_at_a_union_with_one_numeric_member_takes_it() {
    let text = "f(positional x: f64 | String) = x is f64;\ny = f(1);\n";
    assert_eq!(adopted(text), [f64(1.0)]);
    assert_eq!(value(text, "y"), "true");
    let text = "f(positional x: f64 | bool) = x == 1.0;\ny = f(1);\n";
    assert_eq!(value(text, "y"), "true");
    let text = "f(positional x: rat | #none) = x is rat;\ny = f(-2);\n";
    assert_eq!(value(text, "y"), "true");
    // A decimal at a union holding int and rat takes `rat`, the one it can take.
    let text = "f(positional x: int | rat) = x is rat;\ny = f(0.5);\n";
    assert_eq!(value(text, "y"), "true");
}

#[test]
fn a_literal_at_a_union_of_two_carriers() {
    // An integer literal is an `int` where the union holds `int`: nothing adopted.
    let text = "f(positional x: int | f64) = x is int;\ny = f(1);\n";
    assert!(adopted(text).is_empty());
    assert_eq!(value(text, "y"), "true");
    // A decimal is never an `int`, so it takes `f64`.
    let text = "f(positional x: int | f64) = x is f64;\ny = f(0.5);\n";
    assert_eq!(value(text, "y"), "true");
    // Two carriers, neither `int`: nothing chooses one. The note that writes `f`'s type names
    // the part it uses twice, `T1`.
    for lit in ["1", "-1", "0.5"] {
        let defined = two_carriers(lit).replace(
            &format!(" [{lit}]"),
            &format!("\n  T1 stands for a part written more than once:\n    type T1 = rat | f64; [{lit}]"),
        );
        assert_eq!(
            type_errors(&format!("f(positional x: f64 | rat) = x;\ny = f({lit});\n")),
            [defined]
        );
    }
    let text = "f(positional x: f64 | rat) = x is rat;\ny = f(1r);\n";
    assert_eq!(value(text, "y"), "true");
}

#[test]
fn literals_in_a_tuple_take_its_components_carriers() {
    let text = "f(positional p: (f64, f64)) = p == (1.0, 2.0);\ny = f((1, 2));\n";
    assert_eq!(value(text, "y"), "true");
    assert!(adopted(text).contains(&f64(1.0)));
    // At any depth, beside components that are not literals.
    let text = "f(positional p: ((f64, String), rat)) = p == ((3.0, \"a\"), 1r / 2r);\n\
                y = f(((3, \"a\"), 0.5));\n";
    assert_eq!(value(text, "y"), "true");
    let text = "f(positional p: (f64, f64)) = p;\ny = f((1.0, 2));\n";
    assert_eq!(value(text, "y"), "(1.0, 2.0)");
    // An inexact component is an error at that literal.
    assert_eq!(
        type_errors("f(positional p: (f64, f64)) = p;\ny = f((9007199254740993, 1));\n"),
        [
            "the literal `9007199254740993` has no exact `f64`, and `f64` is expected here; an \
             integer literal takes a carrier only where it is exact; write `9007199254740992` \
             [9007199254740993]"
        ]
    );
}

#[test]
fn literals_in_a_tuple_take_the_carrier_every_shape_of_its_length_holds_there() {
    // A position is a point or a named place with a distance from it: at the second
    // component both shapes hold f64, at the first only one holds a number.
    let ty = "(f64, f64) | (String, f64)";
    let text = format!("tu(positional p: {ty}) = p == (1.0, 2.0);\ny = tu((1, 2));\n");
    assert_eq!(value(&text, "y"), "true");
    let text = format!("tu(positional p: {ty}) = p == (\"a\", 2.0);\ny = tu((\"a\", 2));\n");
    assert_eq!(value(&text, "y"), "true");
    // A shape of another length does not count.
    let text = "tu(positional p: (f64, f64) | (rat, rat, rat)) = p == (1.0, 2.0);\n\
                y = tu((1, 2));\n";
    assert_eq!(value(text, "y"), "true");
    // Nested: the inner shapes are those of every outer shape at that component.
    let text = "tu(positional p: ((f64, String), int) | ((String, f64), int)) = \
                p == ((1.0, \"a\"), 3);\ny = tu(((1, \"a\"), 3));\n";
    assert_eq!(value(text, "y"), "true");
    // Numbers of two carriers at a component across the shapes, neither `int`: no one
    // carrier, the same error as for a lone literal.
    assert_eq!(
        type_errors("tu(positional p: (f64, String) | (rat, String)) = p;\ny = tu((1, \"a\"));\n"),
        [two_carriers("1")]
    );
    // Two carriers, int among them: the integer literal is an `int`, nothing adopted.
    let text = "tu(positional p: (int, String) | (f64, String)) = p;\ny = tu((1, \"a\"));\n";
    assert!(adopted(text).is_empty());
    let text = "tu(positional p: (int, String) | (f64, String)) = p == (1, \"a\");\n\
                y = tu((1, \"a\"));\n";
    assert_eq!(value(text, "y"), "true");
}

/// `tu` at a union of `w` tuple shapes of length 2, all but the last with a string first,
/// called on `(1, 2)`, on a tuple of `(1, 2)` nested 2 deep at the same shapes inside, and
/// compared by `==` with `(1, 2)`.
fn shapes(w: usize) -> String {
    let mut ty: Vec<String> = (0..w - 1)
        .map(|i| format!("(String, f64) | (#a{i}, f64)"))
        .collect();
    ty.push("(f64, f64)".into());
    let one = ty.join(" | ");
    format!(
        "tu(positional p: {one}) = 0;\ny = tu((1, 2));\n\
         tv(positional p: ({one}, {one})) = 0;\nz = tv(((1, 2), (3, 4)));\n\
         tw(positional p: {one}) = p == (1, 2);\n"
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
    let text = "isOrigin(positional p: (f64, f64)) = p == (0, 0);\n\
                a = isOrigin((0.0, 0.0));\nb = isOrigin((0.0, 0.5));\n";
    assert_eq!(value(text, "a"), "true");
    assert_eq!(value(text, "b"), "false");
    // Two literal tuples: the bare integers take the other side's carriers.
    assert_eq!(
        value("y = (1, (2, 3)) == (1.0f64, (2r, 3));\n", "y"),
        "true"
    );
    // A bare decimal meets only a bare integer, so nothing gives it a carrier.
    assert_eq!(
        type_errors("y = (1, (2, 3)) == (1.0, (2r, 3));\n"),
        [
            "the literal `1.0` is a decimal, and nothing here gives it a carrier; a decimal \
             literal takes the carrier of its use, never `int`, and Zed does not choose one for \
             it; write `1.0f64` or `1.0r` [1.0]"
        ]
    );
    // A literal beside a value in a tuple: `(x, 1) == (y, z)` with `z: f64`.
    assert!(
        type_errors(
            "f(positional x: f64, positional y: f64, positional z: f64) = (x, 1) == (y, z);\n"
        )
        .is_empty()
    );
}

#[test]
fn sum_reads_literals_at_the_other_components_carrier() {
    let text = "f(positional x: f64) = sum((x, 2));\ny = f(1.0);\n";
    assert_eq!(value(text, "y"), "3.0");
    let text = "f(positional x: f64) = sum((2, x, 3));\ny = f(1.0);\n";
    assert_eq!(value(text, "y"), "6.0");
    assert_eq!(value("y = sum((1, 2));\n", "y"), "3");
    assert_eq!(value("y = sum((1, 2.5f64));\n", "y"), "3.5");
    assert!(type_errors("f(positional x: f64) = sum((x, 2));\n").is_empty());
}

/// `isAt((0, 1, …))` of `w` components, compared with a tuple of `w` literals, and `sum` of
/// `w` literals beside a parameter.
fn wide(w: usize) -> String {
    let fs = vec!["f64"; w].join(", ");
    let zs: Vec<String> = (0..w).map(|i| format!("{i}")).collect();
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

/// The operands of `p == ((…(0, 0)…, 0), 0)`, the tuple nested `d` deep, with `p` at f64
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
    let mut lit = "0".to_string();
    for _ in 0..d {
        lit = format!("({lit}, 0)");
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
    // One numeric member: the literal takes it.
    let text = "f(positional x: f64 | String) = x == 1;\ny = f(1.0);\n";
    assert_eq!(adopted(text), [f64(1.0)]);
    assert_eq!(value(text, "y"), "true");
    // Two, `int` among them: an integer literal is an `int`, and an f64 is not an int.
    let text = "f(positional x: int | f64) = x == 1;\na = f(1);\nb = f(1.0f64);\n";
    assert!(adopted(text).is_empty());
    assert_eq!(value(text, "a"), "true");
    assert_eq!(value(text, "b"), "false");
    // Two, neither `int`: nothing chooses one, on either side.
    assert_eq!(
        type_errors("f(positional x: f64 | rat) = x == 1;\n"),
        [two_carriers("1")]
    );
    assert_eq!(
        type_errors("f(positional x: f64 | rat) = 1 != x;\n"),
        [two_carriers("1")]
    );
}

#[test]
fn a_number_literal_compared_with_a_string_is_rejected() {
    // Author decision A15 (2026-11-09): no carrier of `1` is a string, so `x == 1` is never
    // true; the repairs compare the text or read the number it holds.
    let want = "the literal `1` is a number, and `x` is a `String` here, which no number \
                equals, so the comparison always gives the same answer; write `x == \"1\"` to \
                compare the text or `int(x) == 1` to compare the number the text holds [1]";
    assert_eq!(type_errors("f(positional x: String) = x == 1;\n"), [want]);
    assert_eq!(
        type_errors("f(positional x: #none | String) = x == 1;\n"),
        [want]
    );
    // An inferred parameter that `++` makes a string, before the comparison or after it.
    assert_eq!(
        type_errors("f(positional x) = (x ++ \"a\" == \"a\") && x == 1;\n"),
        [want]
    );
    assert_eq!(
        type_errors("f(positional x) = x == 1 && (x ++ \"a\" == \"a\");\n"),
        [want]
    );
    // A decimal on the left of `!=`: the repairs keep the operator and the order.
    assert_eq!(
        type_errors("f(positional x: String) = 1.5 != x;\n"),
        [
            "the literal `1.5` is a number, and `x` is a `String` here, which no number equals, \
             so the comparison always gives the same answer; write `\"1.5\" != x` to compare \
             the text, `1.5 != f64(x)` or `1.5 != rat(x)` to compare the number the text holds \
             [1.5]"
        ]
    );
    // Each repair checks, and so does a comparison with an atom.
    for ok in [
        "f(positional x: String) = x == \"1\";\n",
        "f(positional x: String) = int(x) == 1;\n",
        "f(positional x: String) = 1.5 != f64(x);\n",
        "f(positional x: String) = 1.5 != rat(x);\n",
        "f(positional x: String | #none) = x == #none;\n",
        "f(positional x) = x == 1;\n",
    ] {
        assert!(type_errors(ok).is_empty(), "{ok}");
    }
    assert_eq!(
        value(
            "f(positional x: String) = int(x) == 1;\ny = f(\"1\");\n",
            "y"
        ),
        "true"
    );
}

#[test]
fn literals_in_a_tuple_compared_with_a_union_of_tuple_shapes_take_across_the_shapes() {
    let ty = "(f64, f64) | (String, f64)";
    let text = format!(
        "isAt(positional p: {ty}) = p == (1, 2);\na = isAt((1.0, 2.0));\n\
         b = isAt((\"a\", 2.0));\n"
    );
    assert_eq!(value(&text, "a"), "true");
    assert_eq!(value(&text, "b"), "false");
    let text = format!("isAt(positional p: {ty}) = (\"a\", 2) == p;\ny = isAt((\"a\", 2.0));\n");
    assert_eq!(value(&text, "y"), "true");
    // Nested, and beside a shape of another length.
    let text = "isAt(positional p: ((f64, String), int) | ((String, f64), int) | (rat, rat, rat)) = \
                p == ((1, \"a\"), 3);\ny = isAt(((1.0, \"a\"), 3));\n";
    assert_eq!(value(text, "y"), "true");
    // Numbers of two carriers at a component across the shapes, neither `int`.
    assert_eq!(
        type_errors("isAt(positional p: (f64, f64) | (rat, rat)) = p == (1, 2.0);\n"),
        [two_carriers("1"), two_carriers("2.0")]
    );
}

#[test]
fn a_literal_at_each_kind_of_declared_type() {
    // A typed parameter's default is checked against its type, as an argument is.
    assert!(type_errors("scaled(x: f64, scale: f64 = 2) = x * scale;\n").is_empty());
    assert_eq!(
        type_errors("scaled(x: f64, scale: f64 = \"x\") = x * scale;\n"),
        [
            "the default of `scale` is \"x\", not f64: a default is a value of its parameter's type [\"x\"]"
        ]
    );
    // A literal in another base, and a negative literal.
    let f = "f(positional x: f64) = x;\n";
    assert_eq!(value(&format!("{f}y = f(0xFF);\n"), "y"), "255.0");
    assert_eq!(value(&format!("{f}y = f(-3);\n"), "y"), "-3.0");
    // A decimal at `int`, with its `-`.
    let g = "g(positional x: int) = x;\n";
    for lit in ["0.5", "-2.5"] {
        assert_eq!(
            type_errors(&format!("{g}y = g({lit});\n")),
            [decimal_at_int(lit)]
        );
    }
}

/// `n` decimals at an `int` parameter, and `n` compared by `==` with a parameter whose class
/// `div` fixed at `int`: each is rejected, `2 n` errors in all.
fn menus(n: usize) -> String {
    let calls: String = (0..n).map(|i| format!("y{i} = f({i}.5);\n")).collect();
    let tests: Vec<String> = (0..n).map(|i| format!("x == {i}.5")).collect();
    format!(
        "f(positional x: int) = x;\n{calls}g(positional x) = (x div 2 == 0) || {};\n",
        tests.join(" || ")
    )
}

#[test]
fn rejecting_literals_with_their_menus_scales() {
    assert_eq!(
        type_errors(&menus(2)),
        [
            decimal_at_int("0.5"),
            decimal_at_int("1.5"),
            decimal_at_int("0.5"),
            decimal_at_int("1.5"),
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
        "rejecting n decimals at a parameter and n compared with a class",
        n,
        1,
        |m| {
            let (_, stmts, res) = units.iter().find(|(k, _, _)| *k == m).unwrap();
            let info = zedc::check::walk::check(stmts, res);
            assert_eq!(info.errors.len(), 2 * m);
        },
    );
}
