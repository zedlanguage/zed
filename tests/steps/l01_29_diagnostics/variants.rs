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
    let cases = [
        // Passes the mark check because `Point` is not defined: structs are L2.
        ("constructor-called-by-position", "pass"),
        (
            "dot-never-mutates",
            "2: this form (Decl) is built from layer L2",
        ),
        (
            "nullable-column-missing-none",
            "25: the line is marked ✗ and has no diagnostic",
        ),
        (
            "numeric-is-not-binary-float",
            "25: the line is marked ✗ and has no diagnostic",
        ),
        (
            "payload-built-by-position",
            "3: this form (Decl) is built from layer L2",
        ),
        // Passes the mark check because its marked line does not parse at L1.
        ("taint-reaches-clean-sink", "pass"),
        (
            "taint-through-concatenation",
            "44: the line is marked ✗ and has no diagnostic",
        ),
        (
            "two-writers-of-one-generation",
            "2: this form (Decl) is built from layer L2",
        ),
        (
            "unit-mismatch-force-energy",
            "49: the line is marked ✗ and has no diagnostic",
        ),
        (
            "unit-mismatch-in-sum",
            "36: the line is marked ✗ and has no diagnostic",
        ),
        (
            "value-binding-has-no-next-generation",
            "2: this form (Decl) is built from layer L2",
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
        .filter_map(|&(name, want)| {
            let got = first(name);
            (got != want).then(|| format!("{name}\n  got  {got}\n  want {want}"))
        })
        .collect();
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

#[test]
fn the_two_passing_variants_pass_for_a_reason_other_than_their_documented_error() {
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
