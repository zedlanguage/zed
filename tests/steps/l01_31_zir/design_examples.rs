//! Row SPEC-zir-text-grammar: the ```` ```zir ```` fences of DESIGN.md sec:ir (*The text form*),
//! read from the spec in place. Each is a whole module in the text form; [`round`] parses it,
//! validates it, prints it back byte for byte, reads its lines back in reverse order and
//! through the binary form, and gets the same graph each time. So a change to the reader or
//! the writer (crates/zedc-zir/src/zir/text.rs) that the spec's examples do not follow, or the
//! reverse, fails here.

use super::{rejected, round};
use zed_tests::spec;

/// The spec's ```` ```zir ```` fences, each ending in a newline as the writer ends a module.
fn fences() -> Vec<String> {
    let fences =
        zed_tools::spec::fence_texts(&spec::design_path(), "zir").unwrap_or_else(|e| panic!("{e}"));
    fences.into_iter().map(|f| format!("{f}\n")).collect()
}

#[test]
fn every_zir_fence_of_the_spec_reads_back_as_written() {
    let fences = fences();
    // sec:ir gives three examples: a fold over a family, an `if` with facts, two ports.
    assert!(
        fences.len() >= 3,
        "{} has {} zir fences, and sec:ir gives three",
        spec::design_path(),
        fences.len()
    );
    for f in &fences {
        round(f);
    }
}

/// Negative control: the test reads the fences and can fail. A fence with another version on
/// its first line, or with an operation the grammar does not have, is refused.
#[test]
fn a_changed_zir_fence_is_refused() {
    let first = fences().into_iter().next().expect("a zir fence");
    let other_version = first.replacen("zir 1\n", "zir 2\n", 1);
    assert!(rejected(&other_version).contains("the first line is `zir 1`"));
    let bad_op = first.replacen(" fam ", " family ", 1);
    assert_ne!(bad_op, first, "the first fence has a `fam` node");
    assert!(rejected(&bad_op).contains("`family` is not a ZIR operation"));
}
