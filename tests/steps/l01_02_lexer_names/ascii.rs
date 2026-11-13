//! The keywords and every name the prelude declares are ASCII names, `[A-Za-z_][A-Za-z0-9_]*`
//! (DESIGN.md sec:lexical; NAME-ascii-only, 2026-11-12, which takes in NAME-ascii-library). The
//! lexer rejects a name beyond ASCII in any program, the standard library's included, so the
//! tool `ascii_names` that checked a libzed checkout for such names was removed: a name it
//! reported (`π`, `@größe`, `#café`) is now an error of the lexer, while the same characters in a
//! comment or a string are still text.

use zedc::lex::{KEYWORDS, lex, name_end};
use zedc::resolve::{ANNOTATIONS, LATER_TYPES, TYPES, WORDS};

/// Whether `w` is one ASCII name and nothing more.
fn is_ascii_name(w: &str) -> bool {
    name_end(w, 0) == Some(w.len())
}

#[test]
fn every_keyword_is_an_ascii_name() {
    for k in KEYWORDS {
        assert!(is_ascii_name(k), "{k:?}");
    }
}

#[test]
fn every_word_type_and_annotation_the_resolver_gives_the_prelude_is_an_ascii_name() {
    let names = WORDS
        .iter()
        .chain(LATER_TYPES)
        .chain(ANNOTATIONS)
        .map(|&(w, _)| w)
        .chain(TYPES.iter().copied());
    for w in names {
        assert!(is_ascii_name(w), "{w:?}");
    }
}

#[test]
fn every_file_of_the_prelude_source_lexes() {
    let prelude = format!("{}/zed/prelude", zed_tools::impl_root());
    let mut files = 0;
    for entry in std::fs::read_dir(&prelude).expect("the prelude directory") {
        let path = entry.expect("a directory entry").path();
        if path.extension().is_some_and(|x| x == "zed") {
            let text = std::fs::read_to_string(&path).expect("a prelude file");
            if let Err(e) = lex(&text) {
                panic!("{}: {e}", path.display());
            }
            files += 1;
        }
    }
    assert!(files >= 7, "{files} prelude files in {prelude}");
}

#[test]
fn a_name_atom_or_annotation_beyond_ascii_in_code_is_rejected_and_text_is_not() {
    // The cases of the removed tool's test.
    for (text, word) in [
        ("π = 3.14;\n", "π"),
        ("s = \"π ${ä} π\";\n", "ä"),
        ("@größe f() -> int { 1 }\n", "@größe"),
        ("f() -> int { #café }\n", "#café"),
    ] {
        let e = lex(text).expect_err(text);
        assert_eq!(&text[e.span.start..e.span.end], word, "{text:?}");
    }
    assert!(lex("// π, #café and @größe in a comment are text.\nx = \"π\";\n").is_ok());
}
