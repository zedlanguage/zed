//! Item MSG-parse-token-names: a parse error names what it expected in the program's words — a
//! name, a number, a string, an atom, an annotation, the end of the text, or the literal token
//! in quotes — never by the grammar's names for kinds of token (`IDENT`, `INT`, `END`, …), which
//! a programmer who knows only the language has never seen (DESIGN.md sec:diagnostics).

use std::path::Path;

use zedc::lex::lex;
use zedc::parse::{TOP, parse};

/// The grammar's names for kinds of token (`Kind::name`, and `HEAD`, which the grammar also
/// writes in capitals).
const GRAMMAR_NAMES: [&str; 12] = [
    "IDENT", "WILD", "INT", "FLOAT", "RAT", "STRING", "ATOM", "ANNOT", "KW", "OP", "END", "HEAD",
];

fn report(text: &str) -> String {
    let tokens = lex(text).unwrap();
    let err = parse(text, &tokens, "Unit", TOP).unwrap_err();
    let line = text[..err.span.start].matches('\n').count() + 1;
    format!(
        "{text:?}\n  line {line}, at {:?}: {err}",
        &text[err.span.start..err.span.end]
    )
}

/// Programs that fail at different points, each with the message it gets.
#[test]
fn each_expected_thing_is_named_in_the_programs_words() {
    let out = [
        // an operand missing before the `;`
        "total = price * ;",
        // an operand missing at the end of the file
        "f(x) = x +\n",
        // a stray token after a statement's value
        "x = 1;\ny = 2 3;",
        // a stray `}` at the top level
        "x = 1;\n}\n",
        // an annotation's arguments not closed
        "@test(1 x = 1;",
        // a list not closed
        "xs = [1, 2, 3;",
        // a type missing after `=`
        "type T = ;",
        // a lambda with no body
        "g = (a, b) -> ;",
        // a keyword where a name goes
        "match = 3;",
        // two names in a string's hole: the hole ends at its `}`
        "x = 1;\ns = \"v ${x x}\";",
    ]
    .map(report)
    .join("\n");
    insta::assert_snapshot!(out);
}

/// Whether `text` holds one of the grammar's names as a word of its own.
fn grammar_name_in(text: &str) -> Option<&'static str> {
    let words: Vec<&str> = text
        .split(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
        .collect();
    GRAMMAR_NAMES.into_iter().find(|n| words.contains(n))
}

/// Every bracketing case of `zed/grammar/cases.txt` cut short at each of its tokens, and with
/// each of its tokens left out, parsed by the rule and at the ring the case names: no message
/// holds a grammar name. The parse errors met are checked to expect each kind of token the
/// grammar names somewhere, so the scan meets every name it must not print.
#[test]
fn no_parse_error_names_a_kind_of_token_as_the_grammar_does() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("../zed/grammar/cases.txt");
    let cases = std::fs::read_to_string(path).unwrap();
    let mut seen: Vec<String> = Vec::new();
    let (mut errors, mut wrong) = (0, Vec::new());
    for line in cases
        .lines()
        .filter(|l| !l.trim().is_empty() && !l.starts_with('#'))
    {
        let [start, text, _] = line.split(" ::: ").map(str::trim).collect::<Vec<_>>()[..] else {
            panic!("a case is `Rule ::: text ::: tree`: {line}");
        };
        let (start, ring) = match start.split_once('@') {
            Some((s, r)) => (s, r.parse().unwrap()),
            None => (start, TOP),
        };
        let text = text.replace('⏎', "\n");
        let Ok(tokens) = lex(&text) else { continue };
        let mut variants = Vec::new();
        for t in &tokens {
            variants.push(text[..t.span.start].to_string());
            variants.push(format!("{}{}", &text[..t.span.start], &text[t.span.end..]));
        }
        variants.push(text.clone());
        for v in variants {
            let Ok(toks) = lex(&v) else { continue };
            let Err(e) = parse(&v, &toks, start, ring) else {
                continue;
            };
            errors += 1;
            for x in &e.expected {
                if !x.starts_with('\'') && !seen.contains(x) {
                    seen.push(x.clone());
                }
            }
            let message = e.to_string();
            if let Some(n) = grammar_name_in(&message) {
                wrong.push(format!("{start}@{ring} | {v:?}\n  names {n}: {message}"));
            }
        }
    }
    assert!(errors > 1000, "only {errors} parse errors were met");
    seen.sort();
    assert_eq!(
        seen,
        [
            "ANNOT", "ATOM", "END", "FLOAT", "IDENT", "INT", "RAT", "STRING", "WILD"
        ],
        "the kinds of token the errors met expect"
    );
    assert!(
        wrong.is_empty(),
        "{} of {errors} messages name a kind of token as the grammar does:\n{}",
        wrong.len(),
        wrong[..wrong.len().min(20)].join("\n")
    );
}

/// The scan above finds a grammar name that a message holds.
#[test]
fn the_scan_finds_a_grammar_name() {
    assert_eq!(grammar_name_in("expected ')' or IDENT"), Some("IDENT"));
    assert_eq!(grammar_name_in("expected ')' or END"), Some("END"));
    assert_eq!(grammar_name_in("expected 'else' or a name"), None);
    assert_eq!(grammar_name_in("expected the end of the text"), None);
}
