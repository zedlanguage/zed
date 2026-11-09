//! The prelude words the corpus uses: `min` and `max` are L1 words, `mix` is L19's staging word
//! and `Stream` is L7's type of a port's values (DESIGN.md, "Defined words by layer"), so no
//! corpus file reports one of them as not defined.

use super::{alone, describe, errors, later};
use zedc::ast::unit;
use zedc::lex::lex;
use zedc::parse::{TOP, parse};
use zedc::resolve::{Alone, resolve_in};

fn corpus(path: &str) -> String {
    std::fs::read_to_string(zed_tests::oracle::corpus_dir().join(path)).unwrap()
}

#[test]
fn min_and_max_in_the_corpus_are_prelude_words() {
    let text = corpus("03-edit-distance.zed");
    let r = alone(&text);
    assert_eq!(errors(&text), Vec::<String>::new());
    assert_eq!(describe(&text, &r, "min", 0), ["prelude min"]);
    assert_eq!(describe(&text, &r, "min", 1), ["prelude min"]);
    let text = corpus("05-max-prefix-sum.zed");
    let r = alone(&text);
    assert_eq!(errors(&text), Vec::<String>::new());
    assert_eq!(describe(&text, &r, "max", 1), ["prelude max"]);
    let text = corpus("31-typechecker/ast.zed");
    let r = alone(&text);
    assert!(
        !errors(&text).iter().any(|e| e.contains("max")),
        "{:?}",
        errors(&text)
    );
    assert_eq!(describe(&text, &r, "max", 0), ["prelude max"]);
}

#[test]
fn mix_is_the_staging_word_of_l19() {
    let errors = errors(&corpus("10-regex-matcher.zed"));
    assert!(
        errors.contains(
            &concat!(zed_tests::not_yet!("the prelude word `mix`"), " [mix]").to_string()
        ),
        "{errors:?}"
    );
    assert!(
        !errors.iter().any(|e| e.contains("not defined")),
        "{errors:?}"
    );
}

#[test]
fn stream_is_the_prelude_type_of_l7() {
    for path in ["18-socket-wordfreq.zed", "29-late-dedup.zed"] {
        assert_eq!(
            errors(&corpus(path)),
            [concat!(
                zed_tests::not_yet!("the prelude type `Stream`"),
                " [Stream]"
            )],
            "{path}"
        );
    }
    assert_eq!(
        errors("f(s: Stream(int)) = s;\n"),
        [concat!(
            zed_tests::not_yet!("the prelude type `Stream`"),
            " [Stream]"
        )]
    );
    assert_eq!(
        errors("f(s: Strem) = s;\n"),
        [
            "the type `Strem` is not defined: no type in scope has this name, and the prelude has none. Correct the name if it is misspelled, or write a type of the prelude, such as `int` or `String`. [Strem]"
        ]
    );
}

#[test]
fn a_type_of_the_program_named_stream_is_its_own() {
    let text = "type Stream = int;\nf(s: Stream) = s;\n";
    assert_eq!(errors(text), Vec::<String>::new());
}

/// Every corpus file that reaches resolution names only defined words; a word of a later layer
/// is reported as one this zedc does not compile yet. A file that does not reach resolution holds a form of a
/// later layer, or is the control that does not parse; any other such file fails the test.
#[test]
fn no_corpus_file_uses_an_undefined_name() {
    let dir = zed_tests::oracle::corpus_dir();
    let mut files = Vec::new();
    let mut todo = vec![dir.clone()];
    while let Some(d) = todo.pop() {
        for e in std::fs::read_dir(&d).unwrap() {
            let p = e.unwrap().path();
            if p.is_dir() && !p.ends_with("ref") {
                todo.push(p);
            } else if p.extension().is_some_and(|e| e == "zed") {
                files.push(p);
            }
        }
    }
    files.sort();
    let (mut resolved, mut later_layer) = (0, 0);
    let mut undefined = Vec::new();
    for p in &files {
        let name = p.strip_prefix(&dir).unwrap().display().to_string();
        let text = std::fs::read_to_string(p).unwrap();
        let tokens = lex(&text).unwrap_or_else(|e| panic!("{name} does not lex: {e:?}"));
        let tree = match parse(&text, &tokens, "Unit", TOP) {
            Ok(tree) => tree,
            Err(_) if name == "controls/neg-parse-error.zed" => continue,
            Err(e) => panic!("{name} does not parse: {e}"),
        };
        let stmts = match unit(&text, &tokens, &tree) {
            Ok(stmts) => stmts,
            Err(e) if zed_tests::is_not_yet(&e.to_string()) => {
                later_layer += 1;
                continue;
            }
            Err(e) => panic!("{name} does not build: {e}"),
        };
        resolved += 1;
        let r = resolve_in(&stmts, &Alone);
        for e in r.errors.iter().chain(&r.later) {
            if !later(&e.message) && e.message.contains("is not defined") {
                undefined.push(format!("{name}: {}", e.message));
            }
        }
    }
    assert_eq!(undefined, Vec::<String>::new());
    assert_eq!(
        (resolved, later_layer, files.len()),
        (39, 10, 50),
        "files resolved, files holding a later layer's form, files"
    );
}
