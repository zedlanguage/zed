//! A literal inside a compound value that nothing gives a carrier is rejected where its
//! carrier matters, as one bound alone is (author decision 2026-11-09, item MSG-literal-tuple):
//! in a tuple, a nested tuple, an atom payload, a block, a string hole, a default, and an
//! argument whose parameter does not fix its type. Each fix names the binder and the position
//! the literal holds, `y[0]`, or the part of a payload. Since the author decision of
//! 2026-11-12 a decimal that nothing fixes takes `f64` (DESIGN.md step L1.26b), in all these
//! places, so the rejection these tests reach is that of a `/` of integer literals alone, which
//! has no carrier at `int`; the decimals themselves are accepted, at `f64`
//! (`an_unfixed_decimal_in_a_compound_value_takes_f64`).
//!
//! Records, arrays, sets and maps, ranges, `match` and struct construction are not supported
//! at L1 ("part of the Zed language but is not supported by this version of zedc"), so they
//! have no case here.

use super::fixes::{fixes, pairs};
use zed_tests::step_helpers::l01_16_elaboration::value;
use zed_tests::step_helpers::l01_26_type_resolution::type_errors;

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
fn a_division_in_a_tuple_names_its_position() {
    assert_eq!(rejected_at("y = (1 / 2, \"a\");\n"), ["1 / 2"]);
    assert_eq!(
        checked("y = (1 / 2, \"a\");\n"),
        pairs(&[
            ("y = (1r / 2, \"a\");", "y[0] is 1r/2r"),
            ("y = (1.0 / 2, \"a\");", "y[0] is 0.5"),
            ("y = (f64(1) / 2, \"a\");", "y[0] is 0.5"),
        ])
    );
    assert_eq!(
        checked("y = (1, -1 / 2);\n"),
        pairs(&[
            ("y = (1, -1r / 2);", "y[1] is -1r/2r"),
            ("y = (1, -1.0 / 2);", "y[1] is -0.5"),
            ("y = (1, -f64(1) / 2);", "y[1] is -0.5"),
        ])
    );
    assert_eq!(
        checked("y = (1, 1 / 2 * 2);\n"),
        pairs(&[
            ("y = (1, 1r / 2 * 2);", "y[1] is 1r"),
            ("y = (1, 1.0 / 2 * 2);", "y[1] is 1.0"),
            ("y = (1, f64(1) / 2 * 2);", "y[1] is 1.0"),
        ])
    );
    // A decimal past the range of `f64` is still rejected in a tuple, and named as written.
    assert_eq!(
        type_errors("y = (true, 1e400);\n"),
        [
            "`1e400` is larger than the largest f64, 1.7976931348623157e308, so as an f64 it \
             rounds to infinity. Write `1e400r` for the exact rational, or a number within the \
             range of f64. [1e400]"
        ]
    );
}

#[test]
fn a_division_in_a_nested_tuple_names_each_position() {
    assert_eq!(
        checked("y = (1, (2, (3, 1 / 2)));\n"),
        pairs(&[
            ("y = (1, (2, (3, 1r / 2)));", "y[1][1][1] is 1r/2r"),
            ("y = (1, (2, (3, 1.0 / 2)));", "y[1][1][1] is 0.5"),
            ("y = (1, (2, (3, f64(1) / 2)));", "y[1][1][1] is 0.5"),
        ])
    );
}

#[test]
fn the_divisions_of_a_tuple_are_rejected_in_one_message() {
    // Each division is named in a step of its own, and the fixes write them all.
    let src = "y = (1 / 2, 1 / 4, 3 / 4);\n";
    assert_eq!(
        type_errors(src),
        [
            "3 parts of the value of `y` are literals that nothing here gives a carrier, and Zed \
             does not choose one for them; the steps below give each one. Try `y = (1r / 2, 1r \
             / 4, 3r / 4)` instead.\n  fixes, each checked here:\n    y = (1r / 2, 1r / 4, 3r \
             / 4);                y[0] is 1r/2r; y[1] is 1r/4r; y[2] is 3r/4r\n    y = (1.0 / \
             2, 1.0 / 4, 3.0 / 4);             y[0] is 0.5; y[1] is 0.25; y[2] is 0.75\n    y = \
             (f64(1) / 2, f64(1) / 4, f64(3) / 4);    y[0] is 0.5; y[1] is 0.25; y[2] is 0.75 [1 \
             / 2]"
        ]
    );
    for fixed in [
        "y = (1r / 2, 1r / 4, 3r / 4);\n",
        "y = (1.0 / 2, 1.0 / 4, 3.0 / 4);\n",
        "y = (f64(1) / 2, f64(1) / 4, f64(3) / 4);\n",
    ] {
        assert_eq!(type_errors(fixed), Vec::<String>::new(), "{fixed}");
    }
    assert_eq!(
        value("y = (1r / 2, 1r / 4, 3r / 4);\n", "y"),
        "(1r/2r, 1r/4r, 3r/4r)"
    );
    assert_eq!(
        value("y = (1.0 / 2, 1.0 / 4, 3.0 / 4);\n", "y"),
        "(0.5, 0.25, 0.75)"
    );
}

#[test]
fn a_division_of_integer_literals_in_a_tuple_lists_its_menu() {
    assert_eq!(
        checked("y = ((1 + 2) / 3, 1);\n"),
        pairs(&[
            ("y = ((1r + 2) / 3, 1);", "y[0] is 1r"),
            ("y = ((1.0 + 2) / 3, 1);", "y[0] is 1.0"),
            ("y = ((f64(1) + 2) / 3, 1);", "y[0] is 1.0"),
        ])
    );
}

#[test]
fn a_division_bound_to_several_names_or_to_none_names_its_place() {
    assert_eq!(
        checked("a, b = (1 / 2, 1);\n"),
        pairs(&[
            ("a, b = (1r / 2, 1);", "a is 1r/2r"),
            ("a, b = (1.0 / 2, 1);", "a is 0.5"),
            ("a, b = (f64(1) / 2, 1);", "a is 0.5"),
        ])
    );
    assert_eq!(
        checked("_ = 1 / 2;\n"),
        pairs(&[
            ("_ = 1r / 2;", "the value is 1r/2r"),
            ("_ = 1.0 / 2;", "the value is 0.5"),
            ("_ = f64(1) / 2;", "the value is 0.5"),
        ])
    );
    assert_eq!(
        checked("_ = (1, 1 / 2);\n"),
        pairs(&[
            ("_ = (1, 1r / 2);", "component 1 of the value is 1r/2r"),
            ("_ = (1, 1.0 / 2);", "component 1 of the value is 0.5"),
            ("_ = (1, f64(1) / 2);", "component 1 of the value is 0.5"),
        ])
    );
}

#[test]
fn a_division_in_an_atom_payload_names_the_payload() {
    assert_eq!(
        checked("y = #bad(1 / 2);\n"),
        pairs(&[
            ("y = #bad(1r / 2);", "the payload of `#bad` is 1r/2r"),
            ("y = #bad(1.0 / 2);", "the payload of `#bad` is 0.5"),
            ("y = #bad(f64(1) / 2);", "the payload of `#bad` is 0.5"),
        ])
    );
    assert_eq!(
        checked("y = #bad(x: 1 / 2);\n"),
        pairs(&[
            ("y = #bad(x: 1r / 2);", "the field `x` of `#bad` is 1r/2r"),
            ("y = #bad(x: 1.0 / 2);", "the field `x` of `#bad` is 0.5"),
            ("y = #bad(x: f64(1) / 2);", "the field `x` of `#bad` is 0.5"),
        ])
    );
    assert_eq!(
        checked("y = #bad((1, 1 / 2));\n"),
        pairs(&[
            (
                "y = #bad((1, 1r / 2));",
                "component 1 of the payload of `#bad` is 1r/2r"
            ),
            (
                "y = #bad((1, 1.0 / 2));",
                "component 1 of the payload of `#bad` is 0.5"
            ),
            (
                "y = #bad((1, f64(1) / 2));",
                "component 1 of the payload of `#bad` is 0.5"
            ),
        ])
    );
    assert_eq!(rejected_at("y = (#bad(1 / 2), 1);\n"), ["1 / 2"]);
}

#[test]
fn a_division_in_a_block_a_hole_or_a_default_is_rejected() {
    assert_eq!(
        checked("y = { q = (1 / 2, 1); q };\n"),
        pairs(&[
            ("y = { q = (1r / 2, 1); q };", "q[0] is 1r/2r"),
            ("y = { q = (1.0 / 2, 1); q };", "q[0] is 0.5"),
            ("y = { q = (f64(1) / 2, 1); q };", "q[0] is 0.5"),
        ])
    );
    assert_eq!(
        checked("y = \"${(1, 1 / 2)}\";\n"),
        pairs(&[
            (
                "y = \"${(1, 1r / 2)}\";",
                "the literal is then exactly 1, a rat"
            ),
            (
                "y = \"${(1, 1.0f64 / 2)}\";",
                "the literal is then the f64 1.0"
            ),
        ])
    );
    assert_eq!(
        checked("f(x = (1 / 2, 1)) = x;\n"),
        pairs(&[
            ("f(x = (1r / 2, 1)) = x;", "x[0] is 1r/2r"),
            ("f(x = (1.0 / 2, 1)) = x;", "x[0] is 0.5"),
            ("f(x = (f64(1) / 2, 1)) = x;", "x[0] is 0.5"),
        ])
    );
}

#[test]
fn a_division_in_an_argument_at_a_type_variable_is_rejected() {
    let menu = |line: &str| {
        pairs(&[
            (
                &line.replacen("1 / 2", "1r / 2", 1),
                "the literal is then exactly 1, a rat",
            ),
            (
                &line.replacen("1 / 2", "1.0f64 / 2", 1),
                "the literal is then the f64 1.0",
            ),
        ])
    };
    let cases = [
        ("id(x) = x;\n", "y = id(x: 1 / 2);"),
        ("id(x) = x;\n", "y = id(x: (1, 1 / 2));"),
        ("first(p) = p[0];\n", "y = first(p: (1 / 2, 1));"),
        ("second(p) = p[1];\n", "y = second(p: (1 / 2, 1));"),
        ("two(a, b) = a;\n", "y = two(a: 1 / 2, b: 1);"),
        ("plus(p) = p[0] + 1;\n", "y = plus(p: (1 / 2, 1));"),
    ];
    for (def, line) in cases {
        assert_eq!(checked(&format!("{def}{line}\n")), menu(line), "{line}");
    }
    // Under an operation the literal is still the argument's.
    assert_eq!(
        rejected_at("id(x) = x;\ny = id(x: 1 / 2) * 2.0f64;\n"),
        ["1"]
    );
    assert_eq!(rejected_at("id(x) = x;\ny = id(x: 1 / 2) + 1;\n"), ["1"]);
}

/// The decimals the tests above once used to reach a rejection are accepted, at `f64`, in
/// each place (DESIGN.md step L1.26b, author decision 2026-11-12).
#[test]
fn an_unfixed_decimal_in_a_compound_value_takes_f64() {
    let cases = [
        ("y = (0.5, \"a\");\n", "(0.5, \"a\")"),
        ("y = (1, -0.5);\n", "(1, -0.5)"),
        ("y = (true, 1e3);\n", "(true, 1000.0)"),
        ("y = (1, 0.5 * 2);\n", "(1, 1.0)"),
        ("y = (1, (2, (3, 0.5)));\n", "(1, (2, (3, 0.5)))"),
        ("y = (0.5, 0.25, 0.75);\n", "(0.5, 0.25, 0.75)"),
        ("y, b = (0.5, 1);\n", "0.5"),
        ("y = #bad(0.5);\n", "#bad(0.5)"),
        ("y = #bad(x: 0.5);\n", "#bad(x: 0.5)"),
        ("y = #bad((1, 0.5));\n", "#bad((1, 0.5))"),
        ("y = { q = (0.5, 1); q };\n", "(0.5, 1)"),
        ("y = \"${(1, 0.5)}\";\n", "\"(1, 0.5)\""),
        ("f(x = (0.5, 1)) = x;\ny = f();\n", "(0.5, 1)"),
        ("id(x) = x;\ny = id(x: 0.5);\n", "0.5"),
        ("id(x) = x;\ny = id(x: (1, 0.5));\n", "(1, 0.5)"),
        ("first(p) = p[0];\ny = first(p: (0.5, 1));\n", "0.5"),
        ("second(p) = p[1];\ny = second(p: (0.5, 1));\n", "1"),
        ("two(a, b) = a;\ny = two(a: 0.5, b: 1);\n", "0.5"),
        ("plus(p) = p[0] + 1;\ny = plus(p: (0.5, 1));\n", "1.5"),
        ("id(x) = x;\ny = id(x: 0.5) + 1;\n", "1.5"),
        ("y = (1, (1, (1, 0.5)));\n", "(1, (1, (1, 0.5)))"),
        ("y = (1, 1, 1, 0.5);\n", "(1, 1, 1, 0.5)"),
    ];
    for (src, v) in cases {
        assert_eq!(type_errors(src), Vec::<String>::new(), "{src}");
        assert_eq!(value(src, "y"), v, "{src}");
    }
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

/// `y = (1, (1, … (1, 1 / 2) …))`, `n` tuples deep: one rejection, whose fixes each write the
/// line and name `y[1]…[1]`, `n` indexes. Negative control (run once, not committed): a
/// `value_parts` that wrote the path of each tuple from the root as it reached it, `O(n^2)`,
/// failed at n = 2,000 with 18.5 times the bytes; at n = 500 it passed, since the checker's
/// own work on each tuple hides it there.
pub(super) fn deep(n: usize) -> String {
    format!("y = {}1 / 2{};\n", "(1, ".repeat(n), ")".repeat(n))
}

/// `y = (1, 1, …, 1 / 2)`, `n` components with the division last, or the same tuple passed to a
/// generic `id`.
pub(super) fn wide(n: usize, call: bool) -> String {
    let t = format!("({}1 / 2)", "1, ".repeat(n));
    match call {
        false => format!("y = {t};\n"),
        true => format!("id(x) = x;\ny = id(x: {t});\n"),
    }
}

#[test]
fn a_division_nested_deep_in_tuples_is_one_rejection_naming_its_path() {
    // A small instance of the benchmark
    // `bench::tuples::a_deeply_nested_tuple_checks_in_linear_time`.
    assert_eq!(
        checked(&deep(2)),
        pairs(&[
            ("y = (1, (1, 1r / 2));", "y[1][1] is 1r/2r"),
            ("y = (1, (1, 1.0 / 2));", "y[1][1] is 0.5"),
            ("y = (1, (1, f64(1) / 2));", "y[1][1] is 0.5"),
        ])
    );
    let [e] = &type_errors(&deep(3))[..] else {
        panic!("one rejection")
    };
    assert!(e.contains("[1][1][1] is 0.5\n"), "{e}");
}

#[test]
fn the_division_of_a_wide_tuple_is_one_rejection_naming_its_component() {
    // Small instances of the benchmarks `bench::tuples::a_wide_tuple_checks_in_linear_time_*`.
    for call in [false, true] {
        assert_eq!(
            rejected_at(&wide(3, call)),
            [if call { "1" } else { "1 / 2" }]
        );
        let [e] = &type_errors(&wide(3, call))[..] else {
            panic!("one rejection")
        };
        assert!(call || e.contains("y[3] is 0.5\n"), "{e}");
    }
}

/// LIT-decimal-body: inside a function body that no use fixes, a `/` of integer literals alone
/// is rejected with its menu, whether it is the result, a component of the result or a
/// binding of a block, and each fix is accepted; a decimal there takes `f64` (DESIGN.md step
/// L1.26b, author decision 2026-11-12), as it does at the top level
/// (`an_unfixed_decimal_in_a_compound_value_takes_f64`).
#[test]
fn a_division_or_a_decimal_in_a_function_body_that_no_use_fixes() {
    let literal = |line: &str| {
        pairs(&[
            (
                &line.replacen("1 / 2", "1r / 2", 1),
                "the literal is then exactly 1, a rat",
            ),
            (
                &line.replacen("1 / 2", "1.0f64 / 2", 1),
                "the literal is then the f64 1.0",
            ),
        ])
    };
    for line in ["g() = 1 / 2;", "g(positional c: bool) = (1 / 2, c);"] {
        assert_eq!(checked(&format!("{line}\n")), literal(line), "{line}");
    }
    assert_eq!(
        checked("g() = { q = 1 / 2; q };\n"),
        pairs(&[
            ("g() = { q = 1r / 2; q };", "q is 1r/2r"),
            ("g() = { q = 1.0 / 2; q };", "q is 0.5"),
            ("g() = { q = f64(1) / 2; q };", "q is 0.5"),
        ])
    );
    let cases = [
        ("g() = 0.5;\ny = g();\n", "0.5"),
        (
            "g(positional c: bool) = (0.5, c);\ny = g(true);\n",
            "(0.5, true)",
        ),
        ("g() = { q = 0.5; q };\ny = g();\n", "0.5"),
    ];
    for (src, v) in cases {
        assert_eq!(type_errors(src), Vec::<String>::new(), "{src}");
        assert_eq!(value(src, "y"), v, "{src}");
    }
}
