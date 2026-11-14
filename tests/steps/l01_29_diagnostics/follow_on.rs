//! FAIL-diagnostics-follow-on (found by TEST-complete-diagnostics). A type the checker gives
//! a definition because of an error it already reported is no witness of a second failure
//! (DESIGN sec:diagnostics, "Every static rejection owes four things": the witnesses make the
//! failure real); the follow-on error is dropped, as NUM-huge-div drops the follow-on errors of
//! a misfit call. Expected: only the cause is reported, whatever the order of the items.

use super::rejected;

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

#[test]
fn a_rejected_field_read_gives_no_second_error_at_its_use() {
    let src = "t(positional r) = r.e;\nmain(m: MainArgs) {\n    m.stdout <- \"${t(1)}\";\n}\n";
    let out = rejected(src);
    let h = headlines(&out);
    assert_eq!(h.len(), 1, "{out}");
    assert!(h[0].starts_with("1:19: "), "{out}");
}
