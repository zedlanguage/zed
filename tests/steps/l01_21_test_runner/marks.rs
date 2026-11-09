//! The `// ✗` marks: a unit's expected diagnostics, each naming its row of the rejection table.

use super::checks;

const REBOUND: &str = "f(x) {\n  y = x + 1;\n  y = y * 2;  // ✗ Rebinding in the same scope: y is \
                       bound above\n  y\n}\n";

#[test]
fn a_diagnostic_on_a_marked_line_passes() {
    assert_eq!(checks(REBOUND), ["3:3: ok"]);
}

#[test]
fn a_diagnostic_off_the_marked_line_fails_and_so_does_the_mark() {
    let src = REBOUND
        .replace("  // ✗ Rebinding in the same scope: y is bound above", "")
        .replace(
            "  y\n}",
            "  y  // ✗ Rebinding in the same scope: not here\n}",
        );
    let got = checks(&src);
    assert_eq!(got.len(), 2, "{got:?}");
    assert!(
        got[0].starts_with(
            "3:3: `y` is already bound in this scope, and a scope binds each name once"
        ),
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
fn a_commented_variant_is_no_mark_and_a_rejected_unit_fails_each_row_it_cannot_run() {
    let src = "// y = 2;  ✗ a variant, checked by its own fixture\n\
               f(x) = x * 2 test { 1 -> 3 }\n\
               g(x) {\n  y = 1;\n  y = 2;  // ✗ Rebinding in the same scope: y = 1 above\n  \
               y\n}\n";
    assert_eq!(
        checks(src),
        [
            "2:21: `1 -> 3` of `f`: not run, since the unit is rejected",
            "5:3: ok"
        ]
    );
    // The row fails whether or not its expected value is right: it is not run.
    assert_eq!(
        checks(&src.replace("1 -> 3", "1 -> 2")),
        [
            "2:21: `1 -> 2` of `f`: not run, since the unit is rejected",
            "5:3: ok"
        ]
    );
    assert_eq!(
        checks(&src.replace(
            "y = 2;  // ✗ Rebinding in the same scope: y = 1 above",
            "z = 2;"
        )),
        ["2:21: `1 -> 3` of `f`: the result is 2"]
    );
}

#[test]
fn a_marked_line_is_placed_at_its_first_diagnostic_and_others_stay_failures() {
    let src = "a = 1;\n\
               a = 2; a = 3;  // ✗ Rebinding in the same scope: twice\n\
               c = missing3;\n\
               a = 4;  // ✗ Rebinding in the same scope: a = 1 above\n";
    let got = checks(src);
    assert_eq!(got.len(), 3, "{got:?}");
    assert_eq!(got[0], "2:1: ok");
    assert!(
        got[1].starts_with("3:5: `missing3` is not defined"),
        "{got:?}"
    );
    assert_eq!(got[2], "4:1: ok");
}
