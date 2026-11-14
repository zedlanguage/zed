use zed_tests::fences::{self, DocFence};
use zed_tests::tokens::render_lines;
use zedc::fence::{label, marks};
use zedc::lex::{lex, lex_fence};

/// The tokens of each of `fences`, under its key: the expected output of the lexer. A fence that
/// does not lex is named by its line.
pub(super) fn tokens_by_key(fences: &[DocFence]) -> String {
    let out: Vec<String> = fences
        .iter()
        .map(|f| {
            let tokens = lex_fence(&f.text).unwrap_or_else(|e| {
                panic!("{} ({}) does not lex: {e} at {:?}", f.at, f.key, e.span);
            });
            format!(
                "== {} L{}\n{}",
                f.key,
                f.layer,
                render_lines(&f.text, &tokens)
            )
        })
        .collect();
    out.join("\n")
}

/// The ✗ marks of each of `fences` that has any, under its key.
pub(super) fn marks_by_key(fences: &[DocFence]) -> String {
    let out: Vec<String> = fences
        .iter()
        .filter_map(|f| {
            let m = marks(&f.text);
            (!m.lines.is_empty() || !m.variants.is_empty())
                .then(|| format!("{}: ✗ {:?} variants {:?}", f.key, m.lines, m.variants))
        })
        .collect();
    out.join("\n")
}

#[test]
fn every_design_fence_lexes() {
    insta::assert_snapshot!(tokens_by_key(&fences::of("design.md")));
}

#[test]
fn every_examples_fence_lexes() {
    insta::assert_snapshot!(tokens_by_key(&fences::of("examples.md")));
}

#[test]
fn every_fence_key_is_its_own() {
    let all = fences::all();
    let keys: std::collections::HashSet<&str> = all.iter().map(|f| f.key.as_str()).collect();
    assert_eq!(keys.len(), all.len());
}

#[test]
fn every_fence_has_a_layer_no_lower_than_its_label() {
    let all = fences::all();
    assert_eq!(all.len(), 78 + 127);
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
fn expected_marks() {
    insta::assert_snapshot!(marks_by_key(&fences::all()));
}

/// `char` is not a unit name (UNITS-char16): a fence writes `units("char")` or `units("chars")`
/// only on a commented ✗ line, and some such line offers both units a reader may mean,
/// `units("char16")` and `units("codepoint")`.
#[test]
fn char_is_a_unit_only_on_a_rejected_line() {
    let mut offered = 0;
    for f in fences::all() {
        let variants = marks(&f.text).variants;
        for (k, line) in f.text.split('\n').enumerate() {
            if !(line.contains(r#"units("char")"#) || line.contains(r#"units("chars")"#)) {
                continue;
            }
            assert!(
                variants.contains(&(k + 1)),
                "{} line {}: {line}",
                f.at,
                k + 1
            );
            if line.contains(r#"units("char16")"#) && line.contains(r#"units("codepoint")"#) {
                offered += 1;
            }
        }
    }
    assert!(
        offered >= 1,
        "no ✗ line offers char16 and codepoint for char"
    );
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

/// Each fixture is its fence with the one commented ✗ line made live, and no other difference
/// but those `fences::CHANGES` names, so that each fixture follows each edit of its fence
/// (item VARIANT-sync).
#[test]
fn every_variant_agrees_with_its_fence() {
    let wrong = fences::disagreements(&fences::all(), &fences::variants(), fences::CHANGES);
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}
