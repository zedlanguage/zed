//! The fences are keyed by their section and their place in it, not by their line, so that an
//! edit of DESIGN.md in one section changes the expected outputs of no other section.

use std::path::Path;

use zed_tests::fences::{self, DocFence};
use zed_tests::scaling::check;
use zed_tools::spec::{Spec, zed_fences_in};

use super::doc_fences::{marks_by_key, tokens_by_key};
use zed_tests::step_helpers::m0_03_grammar_tools::{design, fence, spec_dir};

/// The section and place of each fence of the document `text`.
fn keys(text: &str) -> Vec<(String, usize)> {
    zed_fences_in(text, "DESIGN.md")
        .expect("the fences are closed")
        .into_iter()
        .map(|f| (f.section, f.index))
        .collect()
}

#[test]
fn a_fence_is_in_the_section_of_the_nearest_labeled_heading() {
    let text = "# Title\n\n```zed\na = 1;\n```\n\n## (sec:remap_law) The remap law\n\n\
                ```zed\nb = 2;\n```\n\n### The legal moves\n\n```zed\nc = 3;\n```\n\n\
                ```text\n# not a heading\n```\n\n```zed\nd = 4;\n```\n";
    assert_eq!(
        keys(text),
        [
            ("Title".to_string(), 1),
            ("sec:remap_law".to_string(), 1),
            ("sec:remap_law".to_string(), 2),
            ("sec:remap_law".to_string(), 3),
        ]
    );
}

#[test]
fn without_labels_a_fence_is_in_the_section_of_the_nearest_heading() {
    let text = "```zed\na = 1;\n```\n## 1. Programs and ports\n```zed\nb = 2;\n```\n\
                ## 2. Bindings\n#nospace is text\n```zed\nc = 3;\n```\n```zed\nd = 4;\n```\n";
    assert_eq!(
        keys(text),
        [
            (String::new(), 1),
            ("1. Programs and ports".to_string(), 1),
            ("2. Bindings".to_string(), 1),
            ("2. Bindings".to_string(), 2),
        ]
    );
}

#[test]
fn two_sections_of_one_name_count_on() {
    let text = "## Example\n```zed\na = 1;\n```\n## Example\n```zed\nb = 2;\n```\n";
    assert_eq!(
        keys(text),
        [("Example".to_string(), 1), ("Example".to_string(), 2)]
    );
}

/// A DESIGN.md of two sections with two fences each, `extra` written at the top of the first.
fn two_sections(extra: &str) -> String {
    design(&format!(
        "## (sec:first) First\n\n{extra}{}\nText.\n\n{}\n## (sec:second) Second\n\n### A part\n\n{}\n{}",
        fence("double(x: int) -> int = x * 2;"),
        fence("triple(x: int) -> int = x * 3;"),
        fence("half(x: int) -> int = x / 2;   // ✗ `/` is for f64 and rat only"),
        fence("one = 1;"),
    ))
}

/// The fences, as the tests read them, of the spec whose DESIGN.md is `text`.
fn read(name: &str, text: &str) -> Vec<DocFence> {
    let dir = spec_dir(name, text, "");
    let spec = Spec::open(&dir.root()).expect("the spec reads");
    fences::of_document(Path::new(&dir.at("DESIGN.md")), &spec)
}

#[test]
fn a_line_added_above_a_fence_changes_no_expected_output() {
    let before = read("keys_before", &two_sections(""));
    let after = read(
        "keys_after",
        &two_sections("A new paragraph.\n\nAnd another.\n\n"),
    );
    // The lines moved, in both sections ...
    let at = |fs: &[DocFence]| fs.iter().map(|f| f.at.clone()).collect::<Vec<_>>();
    assert_eq!(at(&before).len(), 4);
    assert!(at(&before).iter().zip(at(&after)).all(|(b, a)| *b != a));
    // ... and the expected outputs did not.
    assert_eq!(tokens_by_key(&after), tokens_by_key(&before));
    assert_eq!(marks_by_key(&after), marks_by_key(&before));
    assert_eq!(
        marks_by_key(&before),
        "DESIGN.md [sec:second] 1: ✗ [1] variants []"
    );
}

#[test]
fn a_fence_added_to_one_section_changes_only_its_keys() {
    let before = read("keys_one", &two_sections(""));
    let after = read("keys_two", &two_sections(&fence("zero = 0;")));
    let second = |fs: &[DocFence]| {
        fs.iter()
            .filter(|f| f.key.contains("[sec:second]"))
            .map(|f| (f.key.clone(), f.text.clone()))
            .collect::<Vec<_>>()
    };
    assert_eq!(second(&after), second(&before));
    assert_eq!(after.len(), before.len() + 1);
}

/// A document of `n` sections, each with a heading, a part and two fences.
fn sections_of(n: usize) -> String {
    (0..n)
        .map(|i| {
            format!(
                "## (sec:s{i}) Section {i}\n\nText.\n\n```zed\na{i} = {i};\n```\n\n### A part\n\n\
                 ```peg\n# a comment\n```\n\n```zed\nb{i} = {i};\n```\n\n"
            )
        })
        .collect()
}

#[test]
fn keying_scales_with_the_document() {
    let texts = [2000, 8 * 2000].map(|n| (n, sections_of(n)));
    check("fence keys, by sections", 2000, |n| {
        let (_, text) = texts
            .iter()
            .find(|t| t.0 == n)
            .expect("a size that was built");
        assert_eq!(keys(text).len(), 2 * n);
    });
}
