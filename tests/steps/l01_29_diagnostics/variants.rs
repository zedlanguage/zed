//! The ✗ fence variants of the spec (zed/fences/variants): what each gives at L1. One,
//! decimal-literal-at-int, reaches its documented error; the others need forms of later
//! layers, so each is pinned to the diagnostic it gives now, and the step that enables it
//! changes the pin.

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
    // The four variants of the units-and-taint fence share its line 49, which has no `;`: the
    // parse recovers at line 50 (step L1.29d), so the declarations around it are checked, and
    // the first failure is the refusal of the grammar struct at line 3.
    let key_val = format!(
        "3: {}",
        zed_tests::not_yet!(
            "the struct declaration `struct KeyVal  grammar { key: Ident  \":\"  value: Json }`"
        )
    );
    let cases = [
        (
            "block-binding-never-read",
            format!(
                "2: {}",
                zed_tests::not_yet!("the declared result type `-> int`")
            ),
        ),
        (
            "constructor-called-by-position",
            "6: the mark names the row \"Positional constructor call or pattern\", and the \
             diagnostic is in no row of the rejection table: `Point` is not defined."
                .into(),
        ),
        (
            "dot-never-mutates",
            format!(
                "8: {}",
                zed_tests::not_yet!("the declared result type `-> int`")
            ),
        ),
        ("nullable-column-missing-none", key_val.clone()),
        // Rejected in the row its mark names (plan row LIT-bare).
        ("decimal-literal-at-int", "pass".into()),
        ("numeric-is-not-binary-float", key_val.clone()),
        (
            // The unit parses from step L2.2; resolution refuses its `type` declaration, which
            // comes before the marked line.
            "payload-built-by-position",
            format!("3: {}", zed_tests::not_yet!("a type declaration")),
        ),
        ("taint-reaches-clean-sink", key_val.clone()),
        (
            "point-unit-in-quotient",
            format!(
                "2: {}",
                zed_tests::not_yet!("the reduction `with units(\"°C\")`")
            ),
        ),
        ("taint-through-concatenation", none(44)),
        (
            "two-point-readings-added",
            format!(
                "2: {}",
                zed_tests::not_yet!("the reduction `with units(\"°C\")`")
            ),
        ),
        (
            "two-writers-of-one-generation",
            format!(
                "8: {}",
                zed_tests::not_yet!("the declared result type `-> int`")
            ),
        ),
        ("unit-mismatch-force-energy", none(49)),
        ("unit-mismatch-in-sum", key_val.clone()),
        (
            "units-differ-by-kind",
            format!(
                "2: {}",
                zed_tests::not_yet!("the reduction `with units(\"N\")`")
            ),
        ),
        (
            "value-binding-has-no-next-generation",
            format!(
                "8: {}",
                zed_tests::not_yet!("the declared result type `-> int`")
            ),
        ),
        // The logarithmic units and `without` of sec:facets (plan rows L12.2h and L12.2i).
        (
            "log-unit-product",
            format!(
                "2: {}",
                zed_tests::not_yet!("the reduction `with units(\"m\")`")
            ),
        ),
        (
            "log-unit-compared-with-number",
            format!(
                "2: {}",
                zed_tests::not_yet!("the reduction `with units(\"m\")`")
            ),
        ),
        (
            "exponential-base-differs",
            format!(
                "2: {}",
                zed_tests::not_yet!("the reduction `with units(\"m\")`")
            ),
        ),
        (
            "removed-fact-not-carried",
            format!(
                "2: {}",
                zed_tests::not_yet!("the reduction `with units(\"m\")`")
            ),
        ),
        (
            "removed-fact-not-removable",
            format!(
                "2: {}",
                zed_tests::not_yet!("the reduction `with units(\"m\")`")
            ),
        ),
        // The assumed units and the argument conversion of sec:facets (plan rows
        // UNITS-assumed-args and UNITS-text-lengths).
        (
            "argument-unit-not-convertible",
            format!(
                "2: {}",
                zed_tests::not_yet!("the reduction `with units(\"GiB\")`")
            ),
        ),
        (
            "text-length-in-bytes",
            format!(
                "2: {}",
                zed_tests::not_yet!("the reduction `with units(\"GiB\")`")
            ),
        ),
        (
            "byte-length-against-kilobytes",
            format!(
                "2: {}",
                zed_tests::not_yet!("the reduction `with units(\"GiB\")`")
            ),
        ),
        (
            "key-in-bytes-for-codepoints",
            format!(
                "2: {}",
                zed_tests::not_yet!("the reduction `with units(\"GiB\")`")
            ),
        ),
        // The comparisons across units of sec:facets (plan row UNITS-compare).
        (
            "unit-comparison-sum-still-strict",
            format!(
                "2: {}",
                zed_tests::not_yet!("the reduction `with units(\"GiB\")`")
            ),
        ),
        (
            "point-reading-against-kelvin",
            format!(
                "2: {}",
                zed_tests::not_yet!("the reduction `with units(\"GiB\")`")
            ),
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
        "6:5: `Point` is not defined."
    );
    let e = rejected("taint-reaches-clean-sink");
    // The syntax error at line 50 is reported with the refusals of the declarations around it.
    assert!(
        e.contains("\n50:1: Syntax error at `exec`. Try `exec : "),
        "{e}"
    );
    assert!(
        e.contains("expected '(' or '[' or 'matching' or '&'"),
        "{e}"
    );
}
