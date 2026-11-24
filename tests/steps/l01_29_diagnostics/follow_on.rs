//! FAIL-diagnostics-follow-on (found by TEST-complete-diagnostics). A type the checker gives
//! a definition because of an error it already reported is no witness of a second failure
//! (DESIGN sec:diagnostics, "Every static rejection owes four things": the witnesses make the
//! failure real); the follow-on error is dropped, as NUM-huge-div drops the follow-on errors of
//! a misfit call. Expected: only the cause is reported, whatever the order of the items.

use super::rejected;
use zed_tests::step_helpers::l01_29_diagnostics::accepted_with_main;

/// The headlines of the rendered diagnostics `out`: the lines that do not start with a space.
fn headlines(out: &str) -> Vec<&str> {
    out.lines().filter(|l| !l.starts_with(' ')).collect()
}

#[test]
fn a_definition_whose_type_comes_from_a_reported_error_gives_no_second_error() {
    for (src, cause) in [
        (
            "t() = 1.e;\nmain(m: MainArgs) {\n    m.stdout <- \"${t()}\";\n}\n",
            "1:7: ",
        ),
        (
            "main(m: MainArgs) {\n    m.stdout <- \"${t()}\";\n}\nt() = 1.e;\n",
            "4:7: ",
        ),
    ] {
        let out = rejected(src);
        let h = headlines(&out);
        assert_eq!(h.len(), 1, "{out}");
        assert!(h[0].starts_with(cause), "{out}");
    }
}

#[test]
fn each_use_of_a_rejected_member_call_gives_no_second_error() {
    for use_ in [
        "t() + 1",
        "if t() > 0 { 1 } else { 2 }",
        "t() == 3",
        "-t()",
        "(t(), 2)[0]",
    ] {
        let src = format!(
            "t() = 1.e;\nu() = {use_};\nmain(m: MainArgs) {{\n    m.stdout <- \"${{u()}}\";\n}}\n"
        );
        let out = rejected(&src);
        let h = headlines(&out);
        assert_eq!(h, ["1:7: `e` is not defined."], "{src}\n{out}");
    }
}

/// A later error that does not depend on the rejected member's type is still reported: only
/// the follow-on errors are dropped (`member_end` in zedc-check's `check/walk.rs`;
/// TEST-assume-documented-gaps).
#[test]
fn an_error_beside_a_rejected_member_call_is_still_reported() {
    let src = "t() = 1.e;\nu() = t() + (\"a\" + 1);\nmain(m: MainArgs) {\n    m.stdout <- \"${u()}\";\n}\n";
    let out = rejected(src);
    let h = headlines(&out);
    assert_eq!(h.len(), 2, "{out}");
    assert_eq!(h[0], "1:7: `e` is not defined.", "{out}");
    assert!(h[1].starts_with("2:"), "{out}");
}

/// A cast of an operation on literals that nothing gives a carrier (A63) is reported by its
/// cause first, and the `Lines` port's rejection of the cast's atoms, whose repair `else ""`
/// does not make the program check, is left out (plan row MSG-cast-no-carrier-first). The
/// cause of `f64(1 / 2)` is the literal, and each fix offered checks. The cause of
/// `int(1.5 + 1)` is the value 2.5, not the literal: every carrier `1.5` could take leaves 2.5,
/// which no `int` equals. Its note shows the class of `1.5 + 1`, not `Never`, and its run-time
/// repair groups the operand before `.isFinite`. Its fixes, `round(1.5 + 1)` and the rest,
/// give `int | #NaN | #overflow`, which the port refuses, so they are checked at the push and
/// dropped there (`Ck::push_carried`), as for `int(1.5f64 + 1)`: no fix offered fails to
/// check.
#[test]
fn a_cast_of_a_literal_with_no_carrier_reports_the_cause_first() {
    for (cast, cause) in [
        (
            "String(f64(1 / 2))",
            "Nothing gives the literal `1` a carrier.",
        ),
        ("String(int(1.5 + 1))", "No `int` equals the value"),
        ("String(int(1.5f64 + 1))", "No `int` equals the value"),
    ] {
        let src = format!("main(m: MainArgs) {{\n    m.stdout <- {cast};\n}}\n");
        let out = rejected(&src);
        let h = headlines(&out);
        assert!(h.first().is_some_and(|h| h.contains(cause)), "{out}");
        assert!(!out.contains("else \"\""), "{out}");
        assert!(!out.contains("Never"), "{out}");
        assert!(!out.contains("1.5 + 1.isFinite"), "{out}");
        if cast.contains("int(1.5 + 1)") {
            assert!(out.contains("(1.5 + 1).isFinite"), "{out}");
        }
        let fixes: Vec<&str> = (out.lines())
            .skip_while(|l| !l.trim_start().starts_with("fixes, each checked here"))
            .skip(1)
            .filter_map(|l| l.strip_prefix("    ")?.split("    ").next())
            .collect();
        assert!(!fixes.is_empty() || cast.contains("int("), "{out}");
        for fix in fixes {
            let fixed = format!("main(m: MainArgs) {{\n    {}\n}}\n", fix.trim_end());
            assert!(accepted_with_main(&fixed), "{fixed}\n{out}");
        }
    }
}

/// Negative control of the drop at the push: a cast whose value no port takes keeps the fixes
/// that give `int | #NaN | #overflow` (plan row MSG-cast-no-carrier-first).
#[test]
fn a_cast_not_pushed_keeps_its_rounding_fixes() {
    let out = rejected("f() = int(1.5 + 1);\n");
    assert!(out.contains("No `int` equals the value"), "{out}");
    assert!(out.contains("round(1.5 + 1)"), "{out}");
}

#[test]
fn a_rejected_field_read_gives_no_second_error_at_its_use() {
    let src = "t(positional r) = r.e;\nmain(m: MainArgs) {\n    m.stdout <- \"${t(1)}\";\n}\n";
    let out = rejected(src);
    let h = headlines(&out);
    assert_eq!(h.len(), 1, "{out}");
    assert!(h[0].starts_with("1:19: "), "{out}");
}
