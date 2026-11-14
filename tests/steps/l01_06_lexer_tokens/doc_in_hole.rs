//! A hole holds code, so a `///` comment in it is a doc comment (FAIL-lex-doc-in-hole, found by
//! TEST-complete-lex, author P189).
//!
//! DESIGN.md sec:lexical, the comment row: "a doc comment starts with exactly three `/`", and
//! "after parsing, a block of doc comments attaches to the declaration that follows it, a block
//! that attaches to none is reported". `lex_with_docs` is the only list of doc comments the
//! front end receives (crates/zedc/src/front.rs `recovered`), so it must list the ones in holes.
//! Whether they attach is tested in l01_26_type_resolution/docs.rs.

use zedc::lex::lex_with_docs;

/// The texts of the doc comments of `src`, in the order listed.
fn docs(src: &str) -> Vec<String> {
    let (_, docs) = lex_with_docs(src).unwrap_or_else(|e| panic!("{src:?}: {e}"));
    docs.into_iter().map(|d| d.text).collect()
}

#[test]
fn a_doc_comment_in_a_hole_is_listed() {
    for src in [
        "s = \"\"\"\n${x /// d\n}\n\"\"\";",
        "s = \"\"\"\n${\n/// d\nx}\n\"\"\";",
    ] {
        assert_eq!(docs(src), ["d"], "{src:?}");
    }
}

/// Doc comments outside strings, in holes, and in a hole of a string in a hole are listed in text
/// order, each with its span.
#[test]
fn doc_comments_in_and_out_of_holes_are_listed_in_text_order() {
    let src = "/// a\ns = \"\"\"\n${\"\"\"\n${1 /// b\n}\n\"\"\" /// c\n}${2 /// d\n}\n\"\"\";\n/// e\nt = 1;";
    let (_, list) = lex_with_docs(src).unwrap();
    let texts: Vec<&str> = list.iter().map(|d| d.text.as_str()).collect();
    assert_eq!(texts, ["a", "b", "c", "d", "e"]);
    for d in &list {
        assert_eq!(&src[d.span.start..d.span.end], format!("/// {}", d.text));
    }
}

/// In a hole as outside one, `////` and a block comment are no doc comments, and a `///` inside
/// the text of a string is text (controls).
#[test]
fn ordinary_comments_and_string_text_in_a_hole_are_no_doc_comments() {
    for src in [
        "s = \"\"\"\n${x //// d\n}\n\"\"\";",
        "s = \"\"\"\n${x /** d */}\n\"\"\";",
        "s = \"\"\"\n/// d ${x}\n\"\"\";",
        "s = \"/// d ${x /* d */}\";",
    ] {
        assert!(docs(src).is_empty(), "{src:?}");
    }
}
