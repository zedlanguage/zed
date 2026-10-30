//! Atoms with payloads: built and matched by position or by name.

use crate::l01_16_elaboration::{errors, term, value};

#[test]
fn a_named_payload_is_a_struct_whatever_the_written_order() {
    let src = "e = #parseError(line: 3, col: 7);\nred = #red == #red;\nf = #parseError(col: 7, line: 3);\n\
               same = e == f;\nother = e == #parseError(line: 3, col: 8);\n";
    assert_eq!(value(src, "e"), "#parseError(col: 7, line: 3)");
    assert_eq!(value(src, "same"), "true");
    assert_eq!(value(src, "other"), "false");
    assert_eq!(value(src, "red"), "true", "`==` compares atoms as data");
    assert_eq!(term(src, "e"), "#parseError(line: 3, col: 7)");
}

#[test]
fn a_positional_payload_holds_any_value_atoms_included() {
    let src = "sum = #add(1, (2, 3));\nwrapped = #some(#none);\nhole = #at(1 div 0);\n";
    assert_eq!(value(src, "sum"), "#add(1, (2, 3))");
    // A payload holds an atom as data: it is not passed through as a failure.
    assert_eq!(value(src, "wrapped"), "#some(#none)");
    assert_eq!(value(src, "hole"), "#at(#divByZero)");
}

#[test]
fn else_matches_a_payload_by_name_and_binds_its_fields() {
    let src = "parse(positional text) = if text == \"\" { #parseError(line: 1, col: 0) } else { 42 };\n\
               line = parse(\"\") else #parseError(line:) -> line;\n\
               both = parse(\"\") else #parseError(line:, col:) -> line * 100 + col;\n\
               ok = parse(\"x\") else #parseError(line:) -> line;\n\
               miss = parse(\"\") else #parseError(file:) -> 0;\n";
    assert_eq!(value(src, "line"), "1");
    assert_eq!(value(src, "both"), "100");
    assert_eq!(value(src, "ok"), "42");
    assert_eq!(
        value(src, "miss"),
        "#parseError(col: 0, line: 1)",
        "a field the payload lacks does not match"
    );
    assert_eq!(
        term(src, "line"),
        "match parse(\"\") { #parseError(line: line@2) -> line@2, $1 -> $1 }"
    );
}

#[test]
fn nested_atom_patterns_by_position_and_by_name() {
    let src = "a = #some(#none) else #some(#none) -> 0;\n\
               b = #some(#none) else #some(#other) -> 0;\n\
               c = #wrap(inner: #none) else #wrap(inner: #none) -> 1;\n\
               d = #wrap(inner: #none) else #wrap(#none) -> 1;\n";
    assert_eq!(value(src, "a"), "0");
    assert_eq!(value(src, "b"), "#some(#none)");
    assert_eq!(value(src, "c"), "1");
    assert_eq!(
        value(src, "d"),
        "#wrap(inner: #none)",
        "a pattern by position does not match a payload by name"
    );
}

#[test]
fn payload_errors() {
    let cases = [
        (
            "x = #e(1, code: 2);",
            "an atom's payload is all by position or all by name [#e(1, code: 2)]",
        ),
        (
            "x = #e(code: 1, ...);",
            "`...` curries a function's named parameters; an atom has none [#e(code: 1, ...)]",
        ),
        (
            "x = #e(code: 1) else #e(code: #a, code: #b) -> 0;",
            "the pattern names `code` twice [#e(code: #a, code: #b)]",
        ),
    ];
    for (src, want) in cases {
        assert_eq!(errors(&format!("{src}\n")), [want], "{src}");
    }
}
