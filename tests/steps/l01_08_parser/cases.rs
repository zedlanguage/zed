//! The bracketing cases of `zed/grammar/cases.txt`: each line is `Rule[@ring] ::: text ::: tree`, and a tree of
//! `ERROR` means the text must not parse. A case is one line, so a line break in its text or tree
//! is written `⏎`.

use std::path::Path;

use zed_tests::trees::sx;
use zedc::lex::lex;
use zedc::parse::{TOP, parse};

fn grammar_dir() -> std::path::PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../zed/grammar")
}

/// The tree printed for `text` parsed as `start` at `ring`, or `ERROR` and why.
fn show(text: &str, start: &str, ring: u32) -> String {
    match lex(text) {
        Err(e) => format!("ERROR lexing: {e}"),
        Ok(tokens) => match parse(text, &tokens, start, ring) {
            Ok(tree) => sx(text, &tokens, &tree),
            Err(e) => format!("ERROR {e}"),
        },
    }
}

#[test]
fn every_bracketing_case_gives_its_tree() {
    let cases = std::fs::read_to_string(grammar_dir().join("cases.txt")).unwrap();
    let (mut n, mut wrong) = (0, Vec::new());
    for line in cases
        .lines()
        .filter(|l| !l.trim().is_empty() && !l.starts_with('#'))
    {
        let [start, text, want] = line.split(" ::: ").map(str::trim).collect::<Vec<_>>()[..] else {
            panic!("a case is `Rule ::: text ::: tree`: {line}");
        };
        let (start, ring) = match start.split_once('@') {
            Some((s, r)) => (s, r.parse().unwrap()),
            None => (start, TOP),
        };
        let got = show(&text.replace('⏎', "\n"), start, ring).replace('\n', "⏎");
        n += 1;
        if !(got == want || want == "ERROR" && got.starts_with("ERROR")) {
            wrong.push(format!(
                "{start}@{ring} | {text}\n  got  {got}\n  want {want}"
            ));
        }
    }
    // Every line that is not blank or a comment is checked above or panics, so the only
    // way this test can pass without checking anything is a cases.txt with no cases.
    assert!(
        n > 0,
        "cases.txt has no cases, so this test checked nothing"
    );
    assert!(
        wrong.is_empty(),
        "{} wrong:\n{}",
        wrong.len(),
        wrong.join("\n")
    );
}

#[test]
fn a_later_layer_operator_parses_only_at_its_ring() {
    // `><` is a reduction, which joins at L3 (sec:grammar, ReduceTail).
    let text = "total = prices >< (+);";
    let tokens = lex(text).unwrap();
    assert!(parse(text, &tokens, "Unit", 2).is_err());
    let tree = parse(text, &tokens, "Unit", 3).unwrap();
    let reduce = (0..tree.nodes.len())
        .find(|&n| tree.name(n) == "ReduceTail")
        .expect("a ReduceTail node");
    assert_eq!(tree.layer(reduce), 3);
    assert_eq!(
        sx(text, &tokens, &tree),
        "((total = (prices (>< (( + )))) ;) )"
    );
}

#[test]
fn a_string_hole_is_parsed_as_an_expression() {
    let text = r#"greeting = "Hello, ${name ++ "!"}";"#;
    let tokens = lex(text).unwrap();
    let tree = parse(text, &tokens, "Unit", 1).unwrap();
    assert_eq!(tree.holes.len(), 1);
    let hole = &tree.holes[0];
    assert_eq!(hole.name(hole.root), "Expr");
    let bad = r#"greeting = "Hello, ${name ++}";"#;
    let err = parse(bad, &lex(bad).unwrap(), "Unit", 1).unwrap_err();
    assert_eq!(&bad[err.span.start..err.span.end], "}");
}
