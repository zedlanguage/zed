//! A decimal literal inside a compound value is rejected where nothing gives it a carrier,
//! as a decimal bound alone is (author decision 2026-11-09, item MSG-literal-tuple): in a
//! tuple, a nested tuple, an atom payload, a block, a string hole, a default, and an argument
//! whose parameter does not fix its type. Each fix names the binder and the position the
//! literal holds, `y[0]`, or the part of a payload. A decimal that its context gives a carrier
//! stays accepted.
//!
//! Records, arrays, sets and maps, ranges, `match` and struct construction are not compiled
//! at L1 ("part of the Zed language … does not compile it yet"), so they have no case here.

use super::fixes::{fixes, pairs};
use zed_tests::scaling;
use zed_tests::step_helpers::l01_16_elaboration::value;
use zed_tests::step_helpers::l01_26_type_resolution::{Resolved, type_errors};

/// Checks each fix of the one rejection of `src`, whose rejected line is its last: the
/// program with that line replaced is accepted, and where the fix names a position of a
/// binder the line binds, as in `y[0] is 0.5`, that position holds the value it names.
/// Returns the fixes, for the caller to pin.
fn checked(src: &str) -> Vec<(String, String)> {
    let fixes = fixes(src);
    assert!(!fixes.is_empty(), "{src}: an empty menu");
    let lines: Vec<&str> = src.lines().collect();
    let (last, before) = lines.split_last().unwrap();
    for (line, holds) in &fixes {
        let fixed: String = (before.iter().copied())
            .chain([line.as_str()])
            .map(|l| format!("{l}\n"))
            .collect();
        assert_eq!(
            type_errors(&fixed),
            Vec::<String>::new(),
            "the fix {line:?} of {last:?}"
        );
        let Some((path, v)) = holds.split_once(" is ") else {
            continue;
        };
        let root = path.split('[').next().unwrap();
        let binds = [format!("{root} ="), format!("{root},")];
        if !path.contains(' ') && binds.iter().any(|b| line.starts_with(b.as_str())) {
            let read = format!("{fixed}held = {path};\n");
            assert_eq!(value(&read, "held"), v, "the fix {line:?} of {last:?}");
        }
    }
    fixes
}

/// The text of each rejection of `src`, in order.
fn rejected_at(src: &str) -> Vec<String> {
    (type_errors(src).iter())
        .map(|e| e.rsplit_once(" [").unwrap().1.trim_end_matches(']').into())
        .collect()
}

#[test]
fn a_decimal_in_a_tuple_names_its_position() {
    assert_eq!(rejected_at("y = (0.5, \"a\");\n"), ["0.5"]);
    assert_eq!(
        checked("y = (0.5, \"a\");\n"),
        pairs(&[
            ("y = (0.5f64, \"a\");", "y[0] is 0.5"),
            ("y = (0.5r, \"a\");", "y[0] is 1r/2r"),
        ])
    );
    assert_eq!(
        checked("y = (1, -0.5);\n"),
        pairs(&[
            ("y = (1, -0.5f64);", "y[1] is -0.5"),
            ("y = (1, -0.5r);", "y[1] is -1r/2r"),
        ])
    );
    assert_eq!(
        checked("y = (true, 1e3);\n"),
        pairs(&[
            ("y = (true, 1e3f64);", "y[1] is 1000.0"),
            ("y = (true, 1e3r);", "y[1] is 1000r"),
        ])
    );
    assert_eq!(
        checked("y = (1, 0.5 * 2);\n"),
        pairs(&[
            ("y = (1, 0.5f64 * 2);", "y[1] is 1.0"),
            ("y = (1, 0.5r * 2);", "y[1] is 1r"),
        ])
    );
}

#[test]
fn a_decimal_in_a_nested_tuple_names_each_position() {
    assert_eq!(
        checked("y = (1, (2, (3, 0.5)));\n"),
        pairs(&[
            ("y = (1, (2, (3, 0.5f64)));", "y[1][1][1] is 0.5"),
            ("y = (1, (2, (3, 0.5r)));", "y[1][1][1] is 1r/2r"),
        ])
    );
}

#[test]
fn each_decimal_of_a_tuple_is_rejected_on_its_own() {
    let src = "y = (0.5, 0.25, 0.75);\n";
    assert_eq!(rejected_at(src), ["0.5", "0.25", "0.75"]);
    let errors = type_errors(src);
    for (e, (fix, holds)) in errors.iter().zip([
        ("y = (0.5f64, 0.25, 0.75);", "y[0] is 0.5"),
        ("y = (0.5, 0.25f64, 0.75);", "y[1] is 0.25"),
        ("y = (0.5, 0.25, 0.75f64);", "y[2] is 0.75"),
    ]) {
        assert!(e.contains(&format!("\n    {fix}    {holds}\n")), "{e}");
    }
}

#[test]
fn a_division_of_integer_literals_in_a_tuple_lists_its_menu() {
    assert_eq!(
        checked("y = ((1 + 2) / 3, 1);\n"),
        pairs(&[
            ("y = ((f64(1) + 2) / 3, 1);", "y[0] is 1.0"),
            ("y = ((1.0f64 + 2) / 3, 1);", "y[0] is 1.0"),
            ("y = ((1r + 2) / 3, 1);", "y[0] is 1r"),
        ])
    );
}

#[test]
fn a_decimal_bound_to_several_names_or_to_none_names_its_place() {
    assert_eq!(
        checked("a, b = (0.5, 1);\n"),
        pairs(&[
            ("a, b = (0.5f64, 1);", "a is 0.5"),
            ("a, b = (0.5r, 1);", "a is 1r/2r")
        ])
    );
    assert_eq!(
        checked("_ = 0.5;\n"),
        pairs(&[
            ("_ = 0.5f64;", "the value is 0.5"),
            ("_ = 0.5r;", "the value is 1r/2r")
        ])
    );
    assert_eq!(
        checked("_ = (1, 0.5);\n"),
        pairs(&[
            ("_ = (1, 0.5f64);", "component 1 of the value is 0.5"),
            ("_ = (1, 0.5r);", "component 1 of the value is 1r/2r"),
        ])
    );
}

#[test]
fn a_decimal_in_an_atom_payload_names_the_payload() {
    assert_eq!(
        checked("y = #bad(0.5);\n"),
        pairs(&[
            ("y = #bad(0.5f64);", "the payload of `#bad` is 0.5"),
            ("y = #bad(0.5r);", "the payload of `#bad` is 1r/2r"),
        ])
    );
    assert_eq!(
        checked("y = #bad(x: 0.5);\n"),
        pairs(&[
            ("y = #bad(x: 0.5f64);", "the field `x` of `#bad` is 0.5"),
            ("y = #bad(x: 0.5r);", "the field `x` of `#bad` is 1r/2r"),
        ])
    );
    assert_eq!(
        checked("y = #bad((1, 0.5));\n"),
        pairs(&[
            (
                "y = #bad((1, 0.5f64));",
                "component 1 of the payload of `#bad` is 0.5"
            ),
            (
                "y = #bad((1, 0.5r));",
                "component 1 of the payload of `#bad` is 1r/2r"
            ),
        ])
    );
    assert_eq!(rejected_at("y = (#bad(0.5), 1);\n"), ["0.5"]);
}

#[test]
fn a_decimal_in_a_block_a_hole_or_a_default_is_rejected() {
    assert_eq!(
        checked("y = { q = (0.5, 1); q };\n"),
        pairs(&[
            ("y = { q = (0.5f64, 1); q };", "q[0] is 0.5"),
            ("y = { q = (0.5r, 1); q };", "q[0] is 1r/2r"),
        ])
    );
    assert_eq!(
        checked("y = \"${(1, 0.5)}\";\n"),
        pairs(&[
            ("y = \"${(1, 0.5f64)}\";", "the literal is then the f64 0.5"),
            (
                "y = \"${(1, 0.5r)}\";",
                "the literal is then exactly 0.5, a rat"
            ),
        ])
    );
    assert_eq!(
        checked("f(x = (0.5, 1)) = x;\n"),
        pairs(&[
            ("f(x = (0.5f64, 1)) = x;", "x[0] is 0.5"),
            ("f(x = (0.5r, 1)) = x;", "x[0] is 1r/2r"),
        ])
    );
}

#[test]
fn a_decimal_argument_at_a_type_variable_is_rejected() {
    let menu = |line: &str, lit: &str| {
        let f = |s: &str| line.replace(lit, &format!("{lit}{s}"));
        pairs(&[
            (&f("f64"), &format!("the literal is then the f64 {lit}")),
            (
                &f("r"),
                &format!("the literal is then exactly {lit}, a rat"),
            ),
        ])
    };
    let cases = [
        ("id(x) = x;\n", "y = id(x: 0.5);"),
        ("id(x) = x;\n", "y = id(x: (1, 0.5));"),
        ("first(p) = p[0];\n", "y = first(p: (0.5, 1));"),
        ("second(p) = p[1];\n", "y = second(p: (0.5, 1));"),
        ("two(a, b) = a;\n", "y = two(a: 0.5, b: 1);"),
        ("plus(p) = p[0] + 1;\n", "y = plus(p: (0.5, 1));"),
    ];
    for (def, line) in cases {
        assert_eq!(
            checked(&format!("{def}{line}\n")),
            menu(line, "0.5"),
            "{line}"
        );
    }
    // Under an operation the literal is still the argument's.
    assert_eq!(
        rejected_at("id(x) = x;\ny = id(x: 0.5) * 2.0f64;\n"),
        ["0.5"]
    );
    assert_eq!(rejected_at("id(x) = x;\ny = id(x: 0.5) + 1;\n"), ["0.5"]);
}

#[test]
fn a_decimal_that_its_context_gives_a_carrier_stays_accepted() {
    let cases = [
        ("y = (0.5f64, \"a\");\n", "(0.5, \"a\")"),
        ("y = (2.5r, 1);\n", "(5r/2r, 1)"),
        ("y = (0x10, 1);\n", "(16, 1)"),
        ("y = (0.5 + 0.25f64, 1);\n", "(0.75, 1)"),
        ("y = (0.5, 1) == (0.5f64, 1);\n", "true"),
        ("y = (0.5f64, 1) == (0.5, 1);\n", "true"),
        ("f(x: f64) = x;\ny = (f(x: 0.5), 1);\n", "(0.5, 1)"),
        (
            "first(p: (f64, String)) = p[0];\ny = first(p: (0.5, \"a\"));\n",
            "0.5",
        ),
        (
            "first(p: (rat, bool)) = p[0];\ny = first(p: (0.5, true));\n",
            "1r/2r",
        ),
        (
            "f(x, p) = x + p[0];\ny = f(x: 1.0f64, p: (0.5, 1));\n",
            "1.5",
        ),
        ("add(a, b) = a + b;\ny = add(a: 0.5, b: 1.0f64);\n", "1.5"),
        ("id(x) = x;\ny = id(x: 1) + 2;\n", "3"),
        ("f(p) = p[0] + 1;\ny = f(p: (2, 1));\n", "3"),
        ("y = #ok((1, 2));\n", "#ok((1, 2))"),
    ];
    for (src, v) in cases {
        assert_eq!(type_errors(src), Vec::<String>::new(), "{src}");
        assert_eq!(value(src, "y"), v, "{src}");
    }
}

/// `y = (1, (1, … (1, 0.5) …))`, `n` tuples deep: one rejection, whose fixes each write the
/// line and name `y[1]…[1]`, `n` indexes. Negative control (run once, not committed): a
/// `value_parts` that wrote the path of each tuple from the root as it reached it, `O(n^2)`,
/// failed at n = 2,000 with 18.5 times the bytes; at n = 500 it passed, since the checker's
/// own work on each tuple hides it there.
fn deep(n: usize) -> String {
    format!("y = {}0.5{};\n", "(1, ".repeat(n), ")".repeat(n))
}

/// `y = (1, 1, …, 0.5)`, `n` components with the decimal last, or the same tuple passed to a
/// generic `id`.
fn wide(n: usize, call: bool) -> String {
    let t = format!("({}0.5)", "1, ".repeat(n));
    match call {
        false => format!("y = {t};\n"),
        true => format!("id(x) = x;\ny = id(x: {t});\n"),
    }
}

#[test]
fn a_deeply_nested_tuple_checks_in_linear_time() {
    scaling::on_a_thread(1 << 29, || {
        assert_eq!(
            checked(&deep(2)),
            pairs(&[
                ("y = (1, (1, 0.5f64));", "y[1][1] is 0.5"),
                ("y = (1, (1, 0.5r));", "y[1][1] is 1r/2r"),
            ])
        );
        let n = 2000;
        let units = scaling::inputs(n, |m| Resolved::new(&deep(m)));
        for (m, u) in &units {
            let [e] = &u.type_errors()[..] else {
                panic!("one rejection")
            };
            assert!(e.contains(&format!("{} is 0.5\n", "[1]".repeat(*m))), "{e}");
        }
        scaling::check_order("rejecting a decimal n tuples deep", n, 1, |m| {
            std::hint::black_box(units[&m].type_errors());
        });
    });
}

#[test]
fn a_wide_tuple_checks_in_linear_time() {
    scaling::on_a_thread(1 << 29, || {
        for call in [false, true] {
            assert_eq!(rejected_at(&wide(3, call)), ["0.5"]);
            let n = 1000;
            let units = scaling::inputs(n, |m| Resolved::new(&wide(m, call)));
            for (m, u) in &units {
                let [e] = &u.type_errors()[..] else {
                    panic!("one rejection")
                };
                assert!(call || e.contains(&format!("y[{m}] is 0.5\n")), "{e}");
            }
            let what = match call {
                false => "rejecting the decimal of a tuple of n components",
                true => "rejecting the decimal of a tuple of n components passed to `id`",
            };
            scaling::check_order(what, n, 1, |m| {
                std::hint::black_box(units[&m].type_errors());
            });
        }
    });
}
