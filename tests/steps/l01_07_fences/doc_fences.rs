use zed_tests::fences::{self, DocFence};
use zed_tests::tokens::render_lines;
use zedc::fence::{self, label, marks};
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

/// Every fence of DESIGN.md and EXAMPLES.md lexes. The tokens are not kept as an expected
/// output: that would copy the spec's fences into this repository.
#[test]
fn every_fence_lexes() {
    let all = fences::all();
    assert!(!all.is_empty());
    let tokens = tokens_by_key(&all);
    assert_eq!(tokens.matches("\n== ").count() + 1, all.len());
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
    assert_eq!(all.len(), 77 + 114);
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
fn every_commented_variant_has_exactly_one_entry() {
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
        // The variant makes its one ✗ line live: one ✗ line outside a comment, and it lexes.
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

/// The fences read from the spec are those the compiler's fence extractor finds in it: the same
/// lines and texts.
#[test]
fn the_fences_are_those_the_extractor_finds() {
    let spec = &fences::spec().root;
    let mut theirs = Vec::new();
    for doc in ["DESIGN.md", "EXAMPLES.md"] {
        let path = format!("{spec}/{doc}");
        let md = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
        theirs.extend(
            fence::extract(&md)
                .into_iter()
                .map(|f| (format!("{doc}:{}", f.line), f.text)),
        );
    }
    let ours: Vec<(String, String)> = fences::all().into_iter().map(|f| (f.at, f.text)).collect();
    assert!(
        ours == theirs,
        "the two readers of the spec's fences disagree"
    );
}

/// The table builds every variant from the spec: each entry names a fence the spec has, and
/// each piece of text it gives is held by one line of that fence (items VARIANT-sync and
/// SPEC-no-verbatim). An edit of a fence that moves or removes a line an entry names fails here,
/// with a message naming the entry and the fence's key.
#[test]
fn every_variant_is_built_from_its_fence() {
    let path = fences::table();
    let table =
        std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
    if let Err(errors) = fences::build(&table, &fences::all()) {
        panic!("{}", errors.join("\n"));
    }
}
