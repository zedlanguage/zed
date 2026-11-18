//! M0.4's own check (TEST-m0-layer-label): each corpus program's `// layer` label is the layer
//! its words and syntax enable. The `layer` tool reads the table of defined words of the spec's
//! DESIGN.md in place (feature `spec`) and this repository's grammars, `zed/grammar/`.
#![cfg(feature = "spec")]

use std::fs;

use zed_tests::step_helpers::m0_03_grammar_tools::Dir;
use zed_tools::layer;
use zed_tools::spec::Spec;

use super::corpus;

/// The `layer` report on `files` against this repository's grammars and the spec's table of
/// words.
fn report(files: &[String]) -> (Result<bool, String>, String) {
    let spec = Spec::open(&zed_tests::spec::root()).expect("the grammars and the table read");
    let files: Vec<&str> = files.iter().map(String::as_str).collect();
    let mut out = String::new();
    let outcome = layer::report(&spec, false, &files, &mut out);
    (outcome, out)
}

#[test]
fn every_corpus_program_enables_the_layer_of_its_label() {
    // Each program's main file: `NN-name.zed`, or `NN-name/main.zed` in its package root.
    let files: Vec<String> = zed_tests::oracle::corpus()
        .into_iter()
        .map(|(p, _)| p.to_str().expect("a UTF-8 path").to_string())
        .collect();
    assert_eq!(files.len(), 31, "{files:?}");
    let (outcome, out) = report(&files);
    assert_eq!(outcome, Ok(true), "{out}");
    // A header line and one line per program, each agreeing.
    assert_eq!(out.lines().count(), 32, "{out}");
    assert!(out.lines().skip(1).all(|l| l.contains(" yes")), "{out}");
}

/// A label below a word of the program, or none, fails the check; one above every word agrees.
#[test]
fn a_label_below_the_layer_a_program_enables_fails_the_check() {
    let text = fs::read_to_string(format!("{}/01-word-count.zed", corpus())).expect("program 01");
    assert!(text.starts_with("// layer L4\n"), "{text}");
    let dir = Dir::new("layer_labels");
    let below = dir.write("below.zed", &text.replacen("// layer L4", "// layer L3", 1));
    let (outcome, out) = report(&[below]);
    assert_eq!(outcome, Ok(false), "{out}");
    assert!(
        out.lines().nth(1).is_some_and(|l| l.ends_with(" NO")),
        "{out}"
    );
    let none = dir.write("none.zed", text.strip_prefix("// layer L4\n").unwrap());
    let (outcome, out) = report(&[none]);
    assert_eq!(outcome, Ok(false), "{out}");
    let above = dir.write("above.zed", &text.replacen("// layer L4", "// layer L9", 1));
    let (outcome, out) = report(&[above]);
    assert_eq!(outcome, Ok(true), "{out}");
    assert!(out.contains("yes (label above ring and table)"), "{out}");
}
