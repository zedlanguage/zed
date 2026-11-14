//! Completeness of the fence extractor (TEST-complete-lex, author P189): each line that opens or
//! closes a fence and each that only looks like one, the ✗ marks of each kind of line, the
//! `// layer Lk` label at its edges, and the spec tool's reading of the same fences. The case
//! list is `COMPLETENESS.md`.

use zed_tests::step_helpers::m0_03_grammar_tools::{design, spec_dir};
use zed_tools::spec::{Spec, zed_fences_in};
use zedc::fence::{Fence, Marks, extract, label, marks};

fn fence(line: usize, before: &str, text: &str) -> Fence {
    Fence {
        line,
        before: before.into(),
        text: text.into(),
    }
}

/// The texts of the fences of `md`, which must be closed, as the compiler's extractor and the
/// spec tool each read them: both follow DESIGN.md's "every fence tagged `zed`".
fn texts(md: &str) -> Vec<String> {
    let ours: Vec<String> = extract(md).into_iter().map(|f| f.text).collect();
    let tool: Vec<String> = zed_fences_in(md, "DESIGN.md")
        .unwrap_or_else(|e| panic!("{md:?}: {e}"))
        .into_iter()
        .map(|f| f.text)
        .collect();
    assert_eq!(ours, tool, "{md:?}");
    ours
}

#[test]
fn an_opening_line_is_three_backticks_and_zed_with_space_around_only() {
    assert_eq!(texts("```zed  \nx\n```"), ["x"]);
    assert_eq!(texts("\t```zed\nx\n\t```"), ["x"]);
    for open in [
        "```zedx",
        "```Zed",
        "````zed",
        "```zed title",
        "``` zed",
        "```",
        "```peg",
    ] {
        let md = format!("{open}\nx\n```");
        assert_eq!(texts(&md), Vec::<String>::new(), "{md:?}");
    }
}

#[test]
fn a_closing_line_is_three_backticks_with_space_around_only() {
    assert_eq!(texts("```zed\na\n  ```  \nb"), ["a"]);
    // Four backticks or a tag do not close it: they are lines of the fence.
    assert_eq!(texts("```zed\na\n````\nb\n```"), ["a\n````\nb"]);
    assert_eq!(texts("```zed\na\n```zed\nb\n```"), ["a\n```zed\nb"]);
}

#[test]
fn fences_at_the_edges_of_the_document_and_of_each_other() {
    assert_eq!(extract(""), []);
    assert_eq!(extract("```zed"), [fence(1, "", "")]);
    assert_eq!(
        extract("```zed\na\n```\n```zed\nb\n```"),
        [fence(1, "", "a"), fence(4, "```", "b")]
    );
    assert_eq!(texts("```zed\na\n```\n```zed\nb\n```"), ["a", "b"]);
}

#[test]
fn the_spec_tool_rejects_an_unclosed_fence_with_its_line() {
    // The compiler's extractor runs it to the end (`an_unclosed_fence_runs_to_the_end`).
    assert_eq!(
        zed_fences_in("a\n\n```zed\nx", "DESIGN.md").unwrap_err(),
        "DESIGN.md:3: the fence is not closed"
    );
}

#[test]
fn a_mark_on_a_line_that_is_not_wholly_a_line_comment_marks_the_line() {
    // DESIGN.md sec:lexical: only a ✗ on a line that is wholly a `//` comment marks a variant.
    for (text, lines, variants) in [
        ("/* ✗ */ x = 1;", vec![1], vec![]),
        ("s = \"✗\";", vec![1], vec![]),
        ("✗", vec![1], vec![]),
        ("//✗", vec![], vec![1]),
        ("\t// ✗", vec![], vec![1]),
        ("x = 1;\n\n// ✗\ny = 2; // ✗", vec![4], vec![3]),
        ("", vec![], vec![]),
    ] {
        assert_eq!(marks(text), Marks { lines, variants }, "{text:?}");
    }
}

#[test]
fn a_label_names_a_layer_in_digits_after_the_l() {
    assert_eq!(label("// layer L"), None);
    assert_eq!(label("// layer L03"), Some(3));
    assert_eq!(label("// layer L2 more"), Some(2));
    assert_eq!(label("// layer L2."), Some(2));
    assert_eq!(label("  // layer L4  "), Some(4));
    assert_eq!(label("//layer L2"), None);
    assert_eq!(label(""), None);
}

#[test]
fn the_spec_reads_the_fences_of_design_then_of_examples() {
    let dir = spec_dir(
        "fences_edges_all",
        &design("```zed\nx = 1;\n```\n"),
        "# Examples\n\n```zed\ny = 2;\n```\n",
    );
    let spec = Spec::open(&dir.root()).expect("the spec reads");
    let all: Vec<(String, String)> = spec
        .all_fences()
        .unwrap()
        .into_iter()
        .map(|f| (f.file, f.text))
        .collect();
    assert_eq!(
        all,
        [
            ("DESIGN.md".to_string(), "x = 1;".to_string()),
            ("EXAMPLES.md".to_string(), "y = 2;".to_string()),
        ]
    );
}

#[test]
fn a_spec_needs_its_three_grammars() {
    let dir = spec_dir("fences_edges_peg", "# T\n\n```peg\nA = 'a'\n```\n", "");
    let e = Spec::open(&dir.root()).unwrap_err();
    assert!(e.ends_with("has fewer than three peg fences"), "{e}");
}
