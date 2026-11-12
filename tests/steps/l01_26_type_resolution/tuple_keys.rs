//! A tuple indexed by a computed key, `t[i]` (DESIGN.md sec:type_language, the `m[k]` row). A
//! tuple's keys are its positions `0..<n`, one integer interval with every key present, so the
//! result is the union of the components the key may select, with `#outOfBounds` when the key
//! may lie outside `0..<n`; a key that selects no component is a static error, as a literal one
//! is. At run time a key outside `0..<n`, negative or past the end, is `#outOfBounds`.

use zed_tests::scaling;

use super::{Resolved, sig, type_errors};
use zed_tests::step_helpers::l01_19_whole_file_ports::run;

/// A record read by a column number the user types.
const COLUMN: &str = "main(m: MainArgs) {\n  \
     person = (\"Ada\", 1815, \"London\");\n  \
     column = int(m.stdin[0]) else 0;\n  \
     m.stdout <- \"${person[column] else \"no such column\"}\";\n}\n";

/// What the program `COLUMN` writes when the user types `line`, run in test directory `name`:
/// the tests run at once, and each writes the program to its own directory.
fn column(name: &str, line: &str) -> String {
    let out = run(name, COLUMN, &format!("{line}\n"), &[]);
    assert_eq!((out.status, out.stderr.as_str()), (0, ""), "{line}");
    out.stdout
}

#[test]
fn a_column_number_typed_by_the_user_reads_that_column() {
    assert_eq!(column("tuple_keys_in", "0"), "Ada\n");
    assert_eq!(column("tuple_keys_in", "1"), "1815\n");
    // The last component.
    assert_eq!(column("tuple_keys_in", "2"), "London\n");
}

#[test]
fn a_column_number_outside_the_record_is_out_of_bounds() {
    // One past the end, negative, and beyond every machine integer.
    assert_eq!(column("tuple_keys_out", "3"), "no such column\n");
    assert_eq!(column("tuple_keys_out", "-1"), "no such column\n");
    assert_eq!(
        column("tuple_keys_out", "99999999999999999999"),
        "no such column\n"
    );
}

#[test]
fn the_result_is_the_union_of_the_components_and_out_of_bounds() {
    assert_eq!(
        sig("pick(t: (int, String, int), i: int) = t[i];", "pick"),
        "(t: (int, String, int), i: int) -> int | String | #outOfBounds"
    );
    // A key of two numbers, both in range, selects two components and cannot miss.
    assert_eq!(
        sig(
            "pick(t: (int, String, f64), b: bool) = t[if b { 1 } else { 2 }];",
            "pick"
        ),
        "(t: (int, String, f64), b: bool) -> f64 | String"
    );
    // One of the two numbers lies past the end.
    assert_eq!(
        sig(
            "pick(t: (int, String, f64), b: bool) = t[if b { 1 } else { 7 }];",
            "pick"
        ),
        "(t: (int, String, f64), b: bool) -> String | #outOfBounds"
    );
    // A string is no position of a tuple.
    assert_eq!(
        sig(
            "pick(t: (int, int), b: bool) = t[if b { 1 } else { \"one\" }];",
            "pick"
        ),
        "(t: (int, int), b: bool) -> int | #outOfBounds"
    );
}

#[test]
fn the_failures_of_the_key_pass_through() {
    assert_eq!(
        sig("pick(t: (int, int), s: String) = t[int(s)];", "pick"),
        "(t: (int, int), s: String) -> int | #invalid | #outOfBounds"
    );
    // A key that is only a failure selects nothing and passes it.
    assert_eq!(
        sig("pick(t: (int, int)) = t[#bad];", "pick"),
        "(t: (int, int)) -> #bad"
    );
}

#[test]
fn a_generic_function_indexes_the_tuple_it_is_called_with() {
    let src = "pick(t, i) = t[i];\n\
               main(m: MainArgs) {\n  \
               i = int(m.stdin[0]) else 0;\n  \
               m.stdout <- \"${pick(t: (\"a\", \"b\", \"c\"), i: i) else \"none\"}\";\n}\n";
    let at = |line: &str| run("tuple_keys_generic", src, &format!("{line}\n"), &[]).stdout;
    assert_eq!(
        (at("0"), at("2"), at("3"), at("-1")),
        (
            "a\n".to_string(),
            "c\n".to_string(),
            "none\n".to_string(),
            "none\n".to_string()
        )
    );
}

#[test]
fn a_key_that_selects_no_component_is_rejected() {
    assert_eq!(
        type_errors("pick(t: (int, int, int), b: bool) = t[if b { 5 } else { 7 }];"),
        [
            "(int, int, int) has no component 5 | 7: its components are at the positions 0 to 2, and this index is 5 | 7. [t[if b { 5 } else { 7 }]]"
        ]
    );
    // The empty tuple has no component at all.
    assert_eq!(
        type_errors("first(t: (), i: int) = t[i];"),
        [
            "() has no component int: the empty tuple has no components at all, and this index is int. [t[i]]"
        ]
    );
}

#[test]
fn a_possibly_missing_component_is_disposed_of_before_a_port() {
    let src = "main(m: MainArgs) {\n  \
               t = (10, 20, 30);\n  \
               i = int(m.stdin[0]) else 0;\n  \
               m.stdout <- \"${t[i]}\";\n}\n";
    let out = run("tuple_keys_undisposed", src, "1\n", &[]);
    assert_eq!(out.status, 1);
    assert!(
        out.stderr.contains(
            "a `Lines` port takes a `String` or a family of strings, not String | #outOfBounds"
        ),
        "{}",
        out.stderr
    );
}

/// A unit indexing a tuple of `n` components by an `int` key, and by a key of two numbers.
fn wide(n: usize) -> String {
    let ts: Vec<&str> = (0..n)
        .map(|j| if j % 2 == 0 { "int" } else { "String" })
        .collect();
    let ts = ts.join(", ");
    format!(
        "pick(t: ({ts}), i: int) = t[i];\n\
         ends(t: ({ts}), b: bool) = t[if b {{ 0 }} else {{ {} }}];\n",
        n - 1
    )
}

#[test]
fn indexing_a_wide_tuple_scales() {
    assert_eq!(type_errors(&wide(4)), Vec::<String>::new(), "{}", wide(4));
    let units: std::collections::BTreeMap<usize, Resolved> = [500, scaling::FACTOR * 500]
        .into_iter()
        .map(|m| (m, Resolved::new(&wide(m))))
        .collect();
    scaling::check_order(
        "a tuple of n components indexed by a computed key",
        500,
        1,
        |n| {
            let info = units[&n].check();
            assert!(info.errors.is_empty(), "{:?}", info.errors);
        },
    );
}
