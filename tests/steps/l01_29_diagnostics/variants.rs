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
    // The whole-line variants of the spec name no row: each marked line fails on that until
    // the step that enables it names its row in the spec.
    let no_row = |line: usize| {
        format!(
            "{line}: the line is marked ✗ and its comment names no row of the rejection table: \
             write `// ✗ <row>: …` with the row's name"
        )
    };
    let cases = [
        ("constructor-called-by-position", no_row(6)),
        (
            "dot-never-mutates",
            "8: this form (ResultType) is built from layer L10".into(),
        ),
        ("nullable-column-missing-none", no_row(25)),
        ("numeric-is-not-binary-float", no_row(25)),
        (
            // The unit parses from step L2.2; resolution refuses its `type` declaration, which
            // comes before the marked line.
            "payload-built-by-position",
            "3: a type declaration is compiled from step L2.5".into(),
        ),
        ("taint-reaches-clean-sink", no_row(39)),
        ("taint-through-concatenation", no_row(44)),
        (
            "two-writers-of-one-generation",
            "8: this form (ResultType) is built from layer L10".into(),
        ),
        ("unit-mismatch-force-energy", no_row(49)),
        ("unit-mismatch-in-sum", no_row(36)),
        (
            "value-binding-has-no-next-generation",
            "8: this form (ResultType) is built from layer L10".into(),
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
        "6:5: `Point` is not defined"
    );
    let e = rejected("taint-reaches-clean-sink");
    assert!(e.starts_with("39:1: expected "), "{e}");
}
