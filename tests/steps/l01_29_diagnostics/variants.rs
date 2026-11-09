//! The ✗ fence variants of the spec (zed/fences/variants): what each gives at L1. None
//! reaches its documented error yet: the forms it needs come in later layers, so each is
//! pinned to the diagnostic it gives now, and the step that enables it changes the pin.

use zedc::testing::test;

const DIR: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/../zed/fences/variants");

/// The first failure of the variant `name`, or `pass` when every check passes.
fn first(name: &str) -> String {
    let text = std::fs::read_to_string(format!("{DIR}/{name}.zed")).unwrap();
    test(&text)
        .into_iter()
        .find_map(|o| o.failure.map(|f| format!("{}: {f}", o.line)))
        .unwrap_or_else(|| "pass".into())
}

#[test]
fn each_variant_gives_its_pinned_diagnostic_at_l1() {
    // Each whole-line variant names its row; a marked line the checker does not reject yet
    // has no diagnostic, and one it rejects for another reason gives a diagnostic in no row.
    let none = |line: usize| format!("{line}: the line is marked ✗ and has no diagnostic");
    let cases = [
        (
            "constructor-called-by-position",
            "6: the mark names the row \"Positional constructor call or pattern\", and the \
             diagnostic is in no row of the rejection table: `Point` is not defined: no definition, parameter or binding in scope has this name, and the prelude has none. Define `Point`, or correct the name if it is misspelled."
                .into(),
        ),
        (
            "dot-never-mutates",
            format!("8: {}", zed_tests::not_yet!("the declared result type `-> int`")),
        ),
        ("nullable-column-missing-none", none(36)),
        // Rejected already, in the row of two carriers; plan row LIT-bare moves the rejection to
        // its own row, and this pin with it.
        (
            "decimal-literal-at-int",
            "4: the mark names the row \"Numeric literal at a carrier that cannot take it\", and \
             the diagnostic is in the row \"Two numeric values with no common carrier\": `2.0` \
             is an f64 where `int` is expected; a literal takes no other carrier"
                .into(),
        ),
        ("numeric-is-not-binary-float", none(36)),
        (
            // The unit parses from step L2.2; resolution refuses its `type` declaration, which
            // comes before the marked line.
            "payload-built-by-position",
            format!("3: {}", zed_tests::not_yet!("a type declaration")),
        ),
        (
            "taint-reaches-clean-sink",
            "50: the mark names the row \"Taint at a sink whose parameter does not take it\", \
             and the diagnostic is in no row of the rejection table: expected '&' or '(' or '->' \
             or '->?' or '..' or ';' or '=' or '[' or 'for' or 'matching' or 'where' or \
             'with' or '|'"
                .into(),
        ),
        ("taint-through-concatenation", none(44)),
        (
            "two-writers-of-one-generation",
            format!("8: {}", zed_tests::not_yet!("the declared result type `-> int`")),
        ),
        ("unit-mismatch-force-energy", none(49)),
        ("unit-mismatch-in-sum", none(47)),
        (
            "value-binding-has-no-next-generation",
            format!("8: {}", zed_tests::not_yet!("the declared result type `-> int`")),
        ),
    ];
    let names: Vec<String> = std::fs::read_dir(DIR)
        .unwrap()
        .map(|e| {
            let p = e.unwrap().path();
            p.file_stem().unwrap().to_string_lossy().into_owned()
        })
        .collect();
    assert_eq!(names.len(), cases.len(), "{names:?}");
    let wrong: Vec<String> = cases
        .iter()
        .filter_map(|(name, want)| {
            let got = first(name);
            (got != *want).then(|| format!("{name}\n  got  {got}\n  want {want}"))
        })
        .collect();
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

#[test]
fn two_variants_are_rejected_for_a_reason_other_than_their_documented_error() {
    let rejected = |n: &str| {
        let text = std::fs::read_to_string(format!("{DIR}/{n}.zed")).unwrap();
        super::rejected(&text)
    };
    assert_eq!(
        rejected("constructor-called-by-position"),
        "6:5: `Point` is not defined: no definition, parameter or binding in scope has this name, and the prelude has none. Define `Point`, or correct the name if it is misspelled."
    );
    let e = rejected("taint-reaches-clean-sink");
    assert!(e.starts_with("50:1: expected "), "{e}");
}
