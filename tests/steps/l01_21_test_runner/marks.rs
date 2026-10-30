//! The `// ✗` marks: a unit's expected diagnostics.

use super::checks;

const REBOUND: &str =
    "f(x) {\n  y = x + 1;\n  y = y * 2;  // ✗ rebinding in the same scope\n  y\n}\n";

#[test]
fn a_diagnostic_on_a_marked_line_passes() {
    assert_eq!(checks(REBOUND), ["3:3: ok"]);
}

#[test]
fn a_diagnostic_off_the_marked_line_fails_and_so_does_the_mark() {
    let src = REBOUND
        .replace("  // ✗ rebinding in the same scope", "")
        .replace("  y\n}", "  y  // ✗\n}");
    let got = checks(&src);
    assert_eq!(got.len(), 2, "{got:?}");
    assert!(
        got[0].starts_with("3:3: `y` is already bound in this scope"),
        "{got:?}"
    );
    assert_eq!(got[1], "4:1: the line is marked ✗ and has no diagnostic");
}

#[test]
fn a_mark_in_an_accepted_unit_fails() {
    let src = "f(x) = x + 1;  // ✗ claimed to be rejected\n";
    assert_eq!(
        checks(src),
        ["1:1: the line is marked ✗ and the unit is accepted"]
    );
}

#[test]
fn a_commented_variant_is_no_mark_and_a_rejected_unit_runs_no_row() {
    let src = "// y = 2;  ✗ a variant, checked by its own fixture\n\
               f(x) = x * 2 test { 1 -> 3 }\n\
               g(x) {\n  y = 1;\n  y = 2;  // ✗\n  y\n}\n";
    assert_eq!(checks(src), ["5:3: ok"]);
    assert_eq!(
        checks(&src.replace("y = 2;  // ✗", "z = 2;")),
        ["2:21: `1 -> 3` of `f`: the result is 2"]
    );
}

#[test]
fn a_marked_line_is_placed_at_its_first_diagnostic_and_others_stay_failures() {
    let src = "a = 1;\nb = missing1 + missing2;  // ✗\nc = missing3;\nd = missing4;  // ✗\n";
    let got = checks(src);
    assert_eq!(got.len(), 3, "{got:?}");
    assert_eq!(got[0], "2:5: ok");
    assert!(
        got[1].starts_with("3:5: `missing3` is not defined"),
        "{got:?}"
    );
    assert_eq!(got[2], "4:5: ok");
}
