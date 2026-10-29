use std::path::Path;

use zed_tests::fences::{self, DocFence};
use zed_tests::tokens::render_lines;
use zedc::fence::{self, label, marks};
use zedc::lex::{lex, lex_fence};

fn golden_tokens(file: &str) -> String {
    let out: Vec<String> = fences::of(file)
        .iter()
        .map(|f| {
            let tokens = lex_fence(&f.text).unwrap_or_else(|e| {
                panic!("{} does not lex: {e} at {:?}", f.at, e.span);
            });
            format!(
                "== {} L{}\n{}",
                f.at,
                f.layer,
                render_lines(&f.text, &tokens)
            )
        })
        .collect();
    out.join("\n")
}

#[test]
fn every_design_fence_lexes() {
    insta::assert_snapshot!(golden_tokens("design.md"));
}

#[test]
fn every_examples_fence_lexes() {
    insta::assert_snapshot!(golden_tokens("examples.md"));
}

#[test]
fn every_fence_has_a_layer_no_lower_than_its_label() {
    let all = fences::all();
    assert_eq!(all.len(), 47 + 102);
    for f in &all {
        assert!((1..=29).contains(&f.layer), "{}", f.at);
        assert!(
            f.layer >= label(&f.text).unwrap_or(1),
            "{} is below its label",
            f.at
        );
    }
    let notation: Vec<&str> = all
        .iter()
        .filter(|f| f.notation)
        .map(|f| f.at.as_str())
        .collect();
    assert_eq!(notation.len(), 13, "{notation:?}");
}

#[test]
fn golden_marks() {
    let out: Vec<String> = fences::all()
        .iter()
        .filter_map(|f: &DocFence| {
            let m = marks(&f.text);
            (!m.lines.is_empty() || !m.variants.is_empty())
                .then(|| format!("{:<16} ✗ {:?} variants {:?}", f.at, m.lines, m.variants))
        })
        .collect();
    insta::assert_snapshot!(out.join("\n"));
}

#[test]
fn every_commented_variant_has_exactly_one_fixture() {
    let wanted: Vec<String> = fences::all()
        .iter()
        .flat_map(|f| {
            let lines: Vec<&str> = f.text.split('\n').collect();
            marks(&f.text)
                .variants
                .into_iter()
                .map(move |k| lines[k - 1].trim().to_string())
        })
        .collect();
    let variants = fences::variants();
    let mut have: Vec<String> = variants.iter().map(|v| v.of.clone()).collect();
    let mut want = wanted.clone();
    want.sort();
    have.sort();
    assert_eq!(have, want);
    for v in &variants {
        // The fixture makes its one variant live: one ✗ line outside a comment, and it lexes.
        assert_eq!(marks(&v.text).lines.len(), 1, "{}", v.name);
        lex_fence(&v.text).unwrap_or_else(|e| panic!("{} does not lex: {e}", v.name));
    }
}

#[test]
fn ellipsis_is_an_elision_only_in_a_fence() {
    let tokens = lex_fence("f(x) = …;\ns = \"a … b\"; // and …").unwrap();
    assert_eq!(
        zed_tests::tokens::render(&tokens),
        r#"f ( x ) = … ; s = str["a … b"] ;"#
    );
    assert!(lex("f(x) = …;").is_err());
}

/// The copies equal the spec's fences, where the spec repository is beside this one (it is not
/// in CI). Layers are not compared: `sync.py --check` recomputes them with the spec's tools.
#[test]
fn the_copies_match_the_spec_where_it_is_present() {
    let spec = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../zed");
    if !spec.join("DESIGN.md").exists() {
        eprintln!(
            "no spec repository at {}: drift not checked",
            spec.display()
        );
        return;
    }
    for (doc, copy) in [("DESIGN.md", "design.md"), ("EXAMPLES.md", "examples.md")] {
        let md = std::fs::read_to_string(spec.join(doc)).unwrap();
        let theirs: Vec<(String, String)> = fence::extract(&md)
            .into_iter()
            .map(|f| (format!("{doc}:{}", f.line), f.text))
            .collect();
        let ours: Vec<(String, String)> = fences::of(copy)
            .into_iter()
            .map(|f| (f.at, f.text))
            .collect();
        assert!(
            ours == theirs,
            "{copy} is out of date: run zed/fences/sync.py"
        );
    }
}
