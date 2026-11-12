//! A bare literal takes the carrier its context gives wherever the context gives one: an
//! operand of `==` against a parameter whose carrier is inferred, a parameter declared as a
//! union with one numeric member, and a component of a tuple, at any depth (DESIGN.md L1.26,
//! L1.26a, L1.26b, sec:domains). Where the context gives two carriers and neither is `int`, or
//! none the literal can take, it is rejected with the forms to write.

use std::path::PathBuf;

use zed_kernel::{F64, Value};
use zed_tests::scaling;
use zedc::testing::test;

use super::{info, menu, tried, type_errors};
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

/// The rejection of the literal `lit` at `f64 | rat`, which can be either, with a fix for
/// each: the line `line` gives with the literal written with that carrier.
fn two_carriers(lit: &str, line: impl Fn(&str) -> String) -> String {
    let float = match lit.contains('.') {
        true => lit.to_string(),
        false => format!("{lit}.0"),
    };
    let (r, f) = (line(&format!("{lit}r")), line(&format!("{float}f64")));
    let (rh, fh) = (
        format!("the literal is then exactly {lit}, a rat"),
        format!("the literal is then the f64 {float}"),
    );
    let fixes = [(r.as_str(), rh.as_str()), (f.as_str(), fh.as_str())];
    format!(
        "Nothing chooses one carrier of `f64 | rat` for the literal `{lit}`{}{} [{lit}]",
        tried(&fixes),
        menu(&fixes)
    )
}

/// The rejection of the decimal literal `lit` where `int` is expected.
fn decimal_at_int(lit: &str) -> String {
    format!("A decimal literal is never an `int`: the literal `{lit}`. [{lit}]")
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
    // the part it uses twice, `T1`, defined before the menu of fixes.
    for lit in ["1", "-1", "0.5"] {
        let defined = two_carriers(lit, |w| format!("y = f({w});")).replacen(
            "\n  fixes, each checked here:",
            "\n  T1 stands for a part written more than once:\n    type T1 = f64 | rat;\n  \
             fixes, each checked here:",
            1,
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
        [format!(
            "No `f64` equals the literal `9007199254740993`. Try `y = f((9007199254740992, \
             1))` instead.{} [9007199254740993]",
            menu(&[(
                "y = f((9007199254740992, 1));",
                "the literal is then 9007199254740992.0, the nearer f64 by ties to even"
            )])
        )]
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
        [two_carriers("1", |w| format!("y = tu(({w}, \"a\"));"))]
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
        [format!(
            "Nothing gives the literal `1.0` a carrier. Try `y = (1, (2, 3)) == (1.0f64, (2r, 3))` \
             instead.{} [1.0]",
            menu(&[
                // The binder's value: DESIGN.md sec:diagnostics, "The value a fix names":
                // "`y is true` for `y = 1 == 1.0f64`".
                ("y = (1, (2, 3)) == (1.0f64, (2r, 3));", "y is true"),
                ("y = (1, (2, 3)) == (1.0r, (2r, 3));", "y is true"),
            ])
        )]
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
        [two_carriers("1", |w| format!(
            "f(positional x: f64 | rat) = x == {w};"
        ))]
    );
    assert_eq!(
        type_errors("f(positional x: f64 | rat) = 1 != x;\n"),
        [two_carriers("1", |w| format!(
            "f(positional x: f64 | rat) = {w} != x;"
        ))]
    );
}

#[test]
fn a_number_literal_compared_with_a_string_is_rejected() {
    // Author decision A15 (2026-11-09): no carrier of `1` is a string, so `x == 1` is never
    // true; the fix compares the text. A cast of the string is no fix: `#invalid` makes it
    // narrowing (DESIGN.md sec:diagnostics).
    let want = |head: &str, tail: &str| {
        never_equal(
            "String",
            "x == 1",
            &[(&format!("{head}x == \"1\"{tail}"), "compares the text")],
        )
    };
    assert_eq!(
        type_errors("f(positional x: String) = x == 1;\n"),
        [want("f(positional x: String) = ", ";")]
    );
    assert_eq!(
        type_errors("f(positional x: #none | String) = x == 1;\n"),
        [want("f(positional x: #none | String) = ", ";")]
    );
    // An inferred parameter that `++` makes a string, before the comparison or after it.
    assert_eq!(
        type_errors("f(positional x) = (x ++ \"a\" == \"a\") && x == 1;\n"),
        [want("f(positional x) = (x ++ \"a\" == \"a\") && ", ";")]
    );
    assert_eq!(
        type_errors("f(positional x) = x == 1 && (x ++ \"a\" == \"a\");\n"),
        [want("f(positional x) = ", " && (x ++ \"a\" == \"a\");")]
    );
    // A decimal on the left of `!=`: the fixes keep the operator and the order.
    assert_eq!(
        type_errors("f(positional x: String) = 1.5 != x;\n"),
        [format!(
            "No number equals a `String`: `1.5 != x : String` always gives the same answer. Try \
             `f(positional x: String) = \"1.5\" != x` instead.{} [1.5]",
            menu(&[(
                "f(positional x: String) = \"1.5\" != x;",
                "compares the text"
            )])
        )]
    );
    // Each fix checks, and so does a comparison with an atom.
    for ok in [
        "f(positional x: String) = x == \"1\";\n",
        "f(positional x: String) = int(x) == 1;\n",
        "f(positional x) = (x ++ \"a\" == \"a\") && int(x) == 1;\n",
        "f(positional x) = x == \"1\" && (x ++ \"a\" == \"a\");\n",
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

/// The rejection of `1` compared by `==` or `!=` with `x` of the type `ty`, which holds no
/// number, as `cmp` writes it, with the fixes `fixes`.
fn never_equal(ty: &str, cmp: &str, fixes: &[(&str, &str)]) -> String {
    let shown = cmp.replace('x', &format!("x : {ty}"));
    format!(
        "No number equals a `{ty}`: `{shown}` always gives the same answer{}{} [1]",
        tried(fixes),
        menu(fixes)
    )
}

/// The fixes of a comparison with a `bool`: `line` with `true`, then with `false`.
fn truth(line: impl Fn(&str) -> String) -> [(String, &'static str); 2] {
    ["true", "false"].map(|b| (line(b), "compares with a truth value"))
}

/// `fixes` as the pairs [`menu`] takes.
fn refs<'a>(fixes: &'a [(String, &'static str)]) -> Vec<(&'a str, &'static str)> {
    fixes.iter().map(|(l, h)| (l.as_str(), *h)).collect()
}

#[test]
fn a_number_literal_compared_with_a_bool_or_a_tuple_is_rejected() {
    // A `bool` is `true` or `false` and a tuple is its components, so neither equals a number,
    // as a string does not (A15): the comparison always gives the same answer. The literal on
    // either side.
    assert_eq!(
        type_errors("f(positional x: bool) = x == 1;\n"),
        [never_equal(
            "bool",
            "x == 1",
            &refs(&truth(|b| format!("f(positional x: bool) = x == {b};")))
        )]
    );
    assert_eq!(
        type_errors("f(positional x: bool | #none) = 1 != x;\n"),
        [never_equal(
            "bool",
            "1 != x",
            &refs(&truth(|b| format!(
                "f(positional x: bool | #none) = {b} != x;"
            )))
        )]
    );
    let pair = |head: &str| {
        [0, 1].map(|i| {
            (
                format!("{head}x[{i}] == 1;"),
                format!("compares component {i}"),
            )
        })
    };
    let menu_of = |ty: &str, p: [(String, String); 2]| {
        let p: Vec<(&str, &str)> = p.iter().map(|(l, h)| (l.as_str(), h.as_str())).collect();
        never_equal(ty, "x == 1", &p)
    };
    assert_eq!(
        type_errors("f(positional x: (int, int)) = x == 1;\n"),
        [menu_of(
            "(int, int)",
            pair("f(positional x: (int, int)) = ")
        )]
    );
    assert_eq!(
        type_errors("f(positional x: (int, String)) = 1 == x;\n"),
        [never_equal(
            "(int, String)",
            "1 == x",
            &[(
                "f(positional x: (int, String)) = 1 == x[0];",
                "compares component 0"
            )]
        )]
    );
    // Shapes of two lengths: an index both have.
    assert_eq!(
        type_errors("f(positional x: (int, int) | (int, int, int) | #none) = x == 1;\n"),
        [menu_of(
            "(int, int) | (int, int, int)",
            pair("f(positional x: (int, int) | (int, int, int) | #none) = ")
        )]
    );
    // A string on the other side too, and both orders for it.
    assert_eq!(
        type_errors("f(positional x: String) = 1 == x;\n"),
        [never_equal(
            "String",
            "1 == x",
            &[("f(positional x: String) = \"1\" == x;", "compares the text")]
        )]
    );
    let either = "f(positional x: bool | String) = x == ";
    assert_eq!(
        type_errors("f(positional x: bool | String) = x == 1;\n"),
        [never_equal(
            "bool | String",
            "x == 1",
            &[
                (&format!("{either}\"1\";"), "compares the text"),
                (&format!("{either}true;"), "compares with a truth value"),
                (&format!("{either}false;"), "compares with a truth value"),
            ]
        )]
    );
    // An inferred parameter that `&&` makes a `bool`, before the comparison or after it.
    assert_eq!(
        type_errors("f(positional x) = (x && true) || x == 1;\n"),
        [never_equal(
            "bool",
            "x == 1",
            &refs(&truth(|b| format!(
                "f(positional x) = (x && true) || x == {b};"
            )))
        )]
    );
    assert_eq!(
        type_errors("f(positional x) = 1 == x || (x && true);\n"),
        [never_equal(
            "bool",
            "1 == x",
            &refs(&truth(|b| format!(
                "f(positional x) = {b} == x || (x && true);"
            )))
        )]
    );
    // An operand that is no name: the fixes write in place of the literal.
    assert_eq!(
        type_errors("f(positional x: bool) = (x && x) == 1;\n"),
        [format!(
            "No number equals a `bool`: `1` compared by `==` with a `bool` always gives the same \
             answer. Try `f(positional x: bool) = (x && x) == true` instead.{} [1]",
            menu(&refs(&truth(|b| format!(
                "f(positional x: bool) = (x && x) == {b};"
            ))))
        )]
    );
    // No fix of those fits: the answer the comparison always gives.
    assert_eq!(
        type_errors("f(positional x: (String, bool)) = x != 1;\n"),
        [format!(
            "No number equals a `(String, bool)`: `x : (String, bool) != 1` is always `true`. Try `f(positional x: (String, bool)) = \
             true` instead.{} [1]",
            menu(&[(
                "f(positional x: (String, bool)) = true;",
                "the answer the comparison always gives"
            )])
        )]
    );
    assert_eq!(
        type_errors("f(positional x: (int, int)) = 1.5 == x;\n"),
        [format!(
            "No number equals a `(int, int)`: `1.5 == x : (int, int)` is always `false`. Try `f(positional x: (int, int)) = \
             false` instead.{} [1.5]",
            menu(&[(
                "f(positional x: (int, int)) = false;",
                "the answer the comparison always gives"
            )])
        )]
    );
}

#[test]
fn a_type_of_one_value_is_written_with_no_article() {
    // `t` holds one value, so the message names it as that value, "`t` is `true`", where a
    // type of many values takes an article, "`x` is a `String`" (MSG-literal-type-article).
    let fixes = truth(|b| format!("less = t == {b};"));
    let fixes = refs(&fixes);
    assert_eq!(
        type_errors("t = true;\nless = t == 1;\n"),
        [format!(
            "No number equals `true`: `t : true == 1` always gives the same answer{}{} [1]",
            tried(&fixes),
            menu(&fixes)
        )]
    );
    let fixes = [("less = t == \"1\";", "compares the text")];
    assert_eq!(
        type_errors("t = \"km\";\nless = t == 1;\n"),
        [format!(
            "No number equals `\"km\"`: `t : \"km\" == 1` always gives the same answer{}{} [1]",
            tried(&fixes),
            menu(&fixes)
        )]
    );
    // A component of one value, met by the literal inside a tuple.
    let fixes = truth(|b| format!("less = t == ({b}, 2);"));
    let fixes = refs(&fixes);
    assert_eq!(
        type_errors("t = (true, 2);\nless = t == (1, 2);\n"),
        [format!(
            "No number equals `true`: `1` compared by `==` with a component of `t` always gives \
             the same answer{}{} [1]",
            tried(&fixes),
            menu(&fixes)
        )]
    );
    // A type of many values keeps its article.
    let fixes = [("f(positional x: String) = x == \"1\";", "compares the text")];
    assert_eq!(
        type_errors("f(positional x: String) = x == 1;\n"),
        [never_equal("String", "x == 1", &fixes)]
    );
}

#[test]
fn a_number_literal_in_a_tuple_compared_with_a_component_that_holds_no_number_is_rejected() {
    // Component by component, as a literal in a tuple reads a declared tuple type.
    assert_eq!(
        type_errors("f(positional p: (String, int)) = p == (1, 2);\n"),
        [format!(
            "No number equals a `String`: `1` compared by `==` with a component of `p` always gives \
             the same answer. Try `f(positional p: (String, int)) = p == (\"1\", 2)` instead.{} [1]",
            menu(&[(
                "f(positional p: (String, int)) = p == (\"1\", 2);",
                "compares the text"
            )])
        )]
    );
    assert_eq!(
        type_errors("f(positional p: (bool, int)) = (1, 2) != p;\n"),
        [format!(
            "No number equals a `bool`: `1` compared by `!=` with a component of `p` always gives \
             the same answer. Try `f(positional p: (bool, int)) = (true, 2) != p` instead.{} [1]",
            menu(&refs(&truth(|b| format!(
                "f(positional p: (bool, int)) = ({b}, 2) != p;"
            ))))
        )]
    );
    // No value of a tuple type is offered: the message asks for one.
    assert_eq!(
        type_errors("f(positional p: ((int, int), int)) = p == (1, 2);\n"),
        [
            "No number equals a `(int, int)`: `1` compared by `==` with a component of `p` always \
             gives the same answer. Write a value of `(int, int)` in place of `1`. [1]"
        ]
    );
    // A component that holds a number in one shape of a union takes it there.
    assert!(type_errors("f(positional p: (String, int) | (int, int)) = p == (1, 2);\n").is_empty());
}

#[test]
fn each_repair_of_a_number_literal_compared_with_no_number_checks() {
    for ok in [
        "f(positional x: bool) = x == true;\n",
        "f(positional x: bool | #none) = false != x;\n",
        "f(positional x: (int, int)) = x[0] == 1;\n",
        "f(positional x: (int, String)) = 1 == x[0];\n",
        "f(positional x: (int, int) | (int, int, int) | #none) = x[1] == 1;\n",
        "f(positional x: String) = \"1\" == x;\n",
        "f(positional x: String) = 1 == int(x);\n",
        "f(positional x: bool | String) = x == \"1\";\n",
        "f(positional p: (String, int)) = p == (\"1\", 2);\n",
        "f(positional p: (bool, int)) = (true, 2) != p;\n",
        // A comparison with an atom or a failure stays legal.
        "f(positional x: bool | #none) = x == #none;\n",
        "f(positional x: (int, int) | #none) = #none != x;\n",
        "f(positional a: int, positional b: int) = (a div b) == #divByZero;\n",
        // A type of atoms alone holds no value a number could be taken for.
        "f(positional x: #a | #b) = x == #a;\n",
    ] {
        assert!(type_errors(ok).is_empty(), "{ok}: {:?}", type_errors(ok));
    }
    let f = "f(positional x: bool) = x == true;\ng(positional x: (int, int)) = x[1] == 2;\n";
    assert_eq!(value(&format!("{f}y = f(true);\n"), "y"), "true");
    assert_eq!(value(&format!("{f}y = g((1, 2));\n"), "y"), "true");
}

/// A function comparing a parameter whose tuple type has `n` components with `1`.
fn wide_tuple(n: usize) -> String {
    let comps = vec!["int"; n].join(", ");
    format!("f(positional x: ({comps})) = x == 1;\n")
}

#[test]
fn the_component_repairs_of_a_wide_tuple_scale() {
    // One repair per component, each read once in each shape.
    let n = 256;
    let units: Vec<_> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| {
            let stmts = zed_tests::deep::statements(&wide_tuple(m));
            let res = zedc::resolve::resolve(&stmts).unwrap();
            (m, stmts, res)
        })
        .collect();
    scaling::check_order(
        "the repairs of a tuple of n components compared with a literal",
        n,
        1,
        |m| {
            let (_, stmts, res) = units.iter().find(|(k, _, _)| *k == m).unwrap();
            let info = zedc::check::walk::check(stmts, res);
            assert_eq!(info.errors.len(), 1);
            assert!(
                info.errors[0]
                    .message
                    .contains(&format!("`x[{}] == 1`", m - 1))
            );
        },
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
        {
            let at = |w: &str| format!("isAt(positional p: (f64, f64) | (rat, rat)) = p == {w};");
            [
                two_carriers("1", |w| at(&format!("({w}, 2.0)"))),
                two_carriers("2.0", |w| at(&format!("(1, {w})"))),
            ]
        }
    );
}

#[test]
fn a_literal_at_each_kind_of_declared_type() {
    // A typed parameter's default is checked against its type, as an argument is.
    assert!(type_errors("scaled(x: f64, scale: f64 = 2) = x * scale;\n").is_empty());
    assert_eq!(
        type_errors("scaled(x: f64, scale: f64 = \"x\") = x * scale;\n"),
        [
            "the default of `scale` is \"x\", not f64: a default is a value of its parameter's type. [\"x\"]"
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
