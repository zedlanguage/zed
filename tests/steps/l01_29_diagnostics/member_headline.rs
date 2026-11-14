//! FAIL-diagnostics-member-headline (found by TEST-complete-diagnostics). DESIGN
//! sec:diagnostics, "A short headline, the detail in the notes": the headlines of name
//! resolution are as short as `` `widht` is not defined. ``, the rule and the sites in the
//! notes. `1.e` calls `e` on `1`, and no `e` is in scope.

use super::rejected;

#[test]
fn a_member_call_of_a_name_in_no_scope_has_the_short_headline() {
    let out = rejected("t() = 1.e;\n");
    assert_eq!(
        out.lines().next(),
        Some("1:7: `e` is not defined."),
        "{out}"
    );
}

#[test]
fn a_member_call_on_each_kind_of_literal_has_the_short_headline_and_the_rule_in_a_note() {
    for (src, head) in [
        ("t() = \"ab\".e;\n", "1:7: `e` is not defined."),
        ("t() = true.e;\n", "1:7: `e` is not defined."),
        ("t() = #none.e;\n", "1:7: `e` is not defined."),
        ("t() = 2.e(3);\n", "1:7: `e` is not defined."),
        ("t() = 1.width;\n", "1:7: `width` is not defined."),
    ] {
        let out = rejected(src);
        let mut lines = out.lines();
        assert_eq!(lines.next(), Some(head), "{out}");
        assert!(
            out.contains("with the literal as its first argument, since a literal has no fields"),
            "{out}"
        );
        assert!(!out.contains("does not compile"), "{out}");
    }
}

#[test]
fn a_member_of_a_value_that_can_have_fields_keeps_the_field_read_clause() {
    // A parameter can hold a record, so `.e` may read its field, a form this zedc does not
    // compile yet; that is the error, not an undefined name.
    let out = rejected("t(r) = r.e;\n");
    assert!(
        out.lines()
            .next()
            .is_some_and(|h| h.contains("does not compile yet")),
        "{out}"
    );
    assert!(!out.contains("is not defined"), "{out}");
}

#[test]
fn a_member_call_of_a_function_in_scope_on_a_literal_is_accepted() {
    let p = zedc::run::load(
        b"twice(x: int) = 2 * x;\nt() = 1.twice;\nmain(m: MainArgs) {\n    m.stdout <- \"${t()}\";\n}\n",
    );
    assert!(p.is_ok(), "{:?}", p.err());
}
