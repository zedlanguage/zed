//! A union, intersection or difference written bare as a key, guarantee or permission (DESIGN.md
//! sec:grammar, author P222; row "Union, intersection or difference written bare as a key,
//! guarantee or permission" of sec:diagnostics): `|`, `&` and `\` bind tighter than `->`, and
//! `Arrow` takes a `TypeNot` before `->`, `->?` and `..`, so `int | #a -> int` is refused. The
//! error is reported at the connective, shows the type as written, and offers each reading that
//! parses: `(int | #a) -> int`, and, where the type has one arrow, `int | (#a -> int)`.

use zedc::rejection::Row;

use super::reserved::refusal;

/// Checks that `src` is refused at the connective at byte `at`, with `message` and the notes
/// `notes` after the first, which says why.
fn refused(src: &str, at: usize, message: &str, notes: &[&str]) {
    let e = refusal(src);
    assert_eq!(e.row, Some(Row::BareKey), "{src}");
    assert_eq!(e.message, message, "{src}");
    assert_eq!(e.span.start, at, "{src}");
    assert!(
        matches!(&src[e.span.start..e.span.end], "|" | "&" | "\\"),
        "{src}"
    );
    let got: Vec<&str> = e.notes.iter().map(|n| n.text.as_str()).collect();
    assert_eq!(&got[1..], notes, "{src}");
    for n in &e.notes {
        assert_eq!(n.span, e.span, "{src}");
    }
}

/// Checks that `src` parses.
fn accepted(src: &str) {
    let tokens = zedc::lex::lex(src).unwrap();
    if let Err(e) = zedc::parse::parse(src, &tokens, "Unit", zedc::parse::TOP) {
        panic!("{src}: {e}");
    }
}

#[test]
fn a_bare_union_key_is_refused_with_both_readings() {
    let src = "f(x: int | #a -> int) = 0;\n";
    refused(
        src,
        9,
        "Union written bare as a key: `int | #a -> int`. Try `(int | #a) -> int` instead.",
        &[
            "repair: `(int | #a) -> int`, with the key `int | #a`",
            "repair: `int | (#a -> int)`, with the key `#a`",
        ],
    );
    let why = &refusal(src).notes[0].text;
    assert_eq!(
        why,
        "a union as a key is written in parentheses, which say whether `|` or `->` groups first"
    );
    // Each reading parses.
    accepted("f(x: (int | #a) -> int) = 0;\n");
    accepted("f(x: int | (#a -> int)) = 0;\n");
}

#[test]
fn a_bare_key_of_a_partial_family_is_refused_with_both_readings() {
    refused(
        "type M = String | #a ->? int;\n",
        16,
        "Union written bare as a key: `String | #a ->? int`. Try `(String | #a) ->? int` instead.",
        &[
            "repair: `(String | #a) ->? int`, with the key `String | #a`",
            "repair: `String | (#a ->? int)`, with the key `#a`",
        ],
    );
}

#[test]
fn the_second_reading_takes_the_last_operand_of_several() {
    refused(
        "f(x: int | String | #a -> int) = 0;\n",
        9,
        "Union written bare as a key: `int | String | #a -> int`. Try `(int | String | #a) -> \
         int` instead.",
        &[
            "repair: `(int | String | #a) -> int`, with the key `int | String | #a`",
            "repair: `int | String | (#a -> int)`, with the key `#a`",
        ],
    );
}

#[test]
fn a_bare_intersection_and_a_bare_difference_are_refused_too() {
    refused(
        "f(x: Pos & Even -> int) = 0;\n",
        9,
        "Intersection written bare as a key: `Pos & Even -> int`. Try `(Pos & Even) -> int` \
         instead.",
        &[
            "repair: `(Pos & Even) -> int`, with the key `Pos & Even`",
            "repair: `Pos & (Even -> int)`, with the key `Even`",
        ],
    );
    refused(
        "f(x: _ \\ #a -> int) = 0;\n",
        7,
        "Difference written bare as a key: `_ \\ #a -> int`. Try `(_ \\ #a) -> int` instead.",
        &[
            "repair: `(_ \\ #a) -> int`, with the key `_ \\ #a`",
            "repair: `_ \\ (#a -> int)`, with the key `#a`",
        ],
    );
}

/// In a morphism type `L .. U -> V`, only the parenthesized reading parses: `int .. int` is no
/// type, so `int .. int | (String -> bool)` is not offered.
#[test]
fn a_bare_permission_is_refused_with_the_one_reading_that_parses() {
    refused(
        "f(m: int .. int | String -> bool, k: bool) = m[k];\n",
        16,
        "Union written bare as a permission: `int .. int | String -> bool`. Try `int .. (int | \
         String) -> bool` instead.",
        &["repair: `int .. (int | String) -> bool`, with the permission `int | String`"],
    );
    refused(
        "f(x: #a | #c .. #a -> int) = 0;\n",
        8,
        "Union written bare as a guarantee: `#a | #c .. #a -> int`. Try `(#a | #c) .. #a -> int` \
         instead.",
        &["repair: `(#a | #c) .. #a -> int`, with the guarantee `#a | #c`"],
    );
}

/// Where the type has several bare keys, guarantees or permissions, the repair parenthesizes
/// them all, so that the parse gets past it.
#[test]
fn every_bare_key_of_the_type_is_parenthesized_in_the_repair() {
    refused(
        "f(x: #a | #c .. #a | #b -> int) = 0;\n",
        8,
        "Union written bare as a guarantee: `#a | #c .. #a | #b -> int`. Try `(#a | #c) .. (#a \
         | #b) -> int` instead.",
        &[
            "repair: `(#a | #c) .. (#a | #b) -> int`, with each key, guarantee and permission in \
           parentheses",
        ],
    );
    refused(
        "f(x: int | #a -> #b | #c -> int) = 0;\n",
        9,
        "Union written bare as a key: `int | #a -> #b | #c -> int`. Try `(int | #a) -> (#b | #c) \
         -> int` instead.",
        &[
            "repair: `(int | #a) -> (#b | #c) -> int`, with each key, guarantee and permission in \
           parentheses",
        ],
    );
}

/// The forms P222 keeps: a union after `->`, a union after `is`, a pattern `(is T) ->` in a
/// `match` (in parentheses since L2.7b; bare, it is refused as a bare pattern, in
/// l02_07b_or_patterns), and a parenthesized key.
#[test]
fn a_union_where_the_grammar_takes_one_parses() {
    accepted("f(x: int -> int | #a) = 0;\n");
    accepted("f(x: (int | #a) -> int | #b) = 0;\n");
    accepted("f(x: (int | #a) .. (int | #a | #b) -> int) = 0;\n");
    accepted("f(x) = x is int | #a;\n");
    accepted("f(x) = match x { (is int | bool) -> 1, _ -> 2 };\n");
}

/// `n` definitions, then a bare key.
pub(super) fn definitions_before_a_bare_key(n: usize) -> String {
    let mut src: String = (0..n).map(|i| format!("g{i}(x: int) = x;\n")).collect();
    src += "f(x: int | #a -> int) = 0;\n";
    src
}

/// A bare key of `n + 1` operands.
pub(super) fn a_bare_key_of_many_operands(n: usize) -> String {
    let atoms: String = (0..n).map(|i| format!(" | #a{i}")).collect();
    format!("f(x: int{atoms} -> int) = 0;\n")
}

/// A type of `n` arrows, each with a bare key of two operands.
pub(super) fn many_bare_keys(n: usize) -> String {
    let keys: String = (0..n).map(|i| format!("#a{i} | #b{i} -> ")).collect();
    format!("f(x: {keys}int) = 0;\n")
}

/// A bare key after many definitions, a bare key of many operands and a type of many bare keys
/// are each refused at their first connective, with the repairs that parse. The time each takes
/// is held linear in `bench/bare_key.rs`.
#[test]
fn a_bare_key_is_found_after_many_definitions_and_in_long_types() {
    for n in [1, 2, 9] {
        let src = definitions_before_a_bare_key(n);
        let e = refusal(&src);
        assert_eq!(e.row, Some(Row::BareKey), "{src}");
        assert_eq!(e.notes.len(), 3, "{src}");
        let src = a_bare_key_of_many_operands(n);
        let e = refusal(&src);
        assert_eq!(e.row, Some(Row::BareKey), "{src}");
        let atoms: String = (0..n).map(|i| format!(" | #a{i}")).collect();
        assert_eq!(
            e.notes[1].text,
            format!("repair: `(int{atoms}) -> int`, with the key `int{atoms}`"),
            "{src}"
        );
        assert_eq!(e.notes.len(), 3, "{src}");
        let src = many_bare_keys(n);
        let e = refusal(&src);
        assert_eq!(e.row, Some(Row::BareKey), "{src}");
        assert_eq!(e.span.start, 9, "{src}");
        let grouped: String = (0..n).map(|i| format!("(#a{i} | #b{i}) -> ")).collect();
        assert!(
            e.notes[1]
                .text
                .starts_with(&format!("repair: `{grouped}int`")),
            "{src}"
        );
        // Two readings where the type has one arrow, one where it has more.
        assert_eq!(e.notes.len(), if n == 1 { 3 } else { 2 }, "{src}");
    }
}

/// A connective with no operand on one side is no union, intersection or difference, so the
/// plain syntax error reports it.
#[test]
fn a_connective_missing_an_operand_is_a_syntax_error() {
    for src in [
        "f(x: int | -> int) = 0;\n",
        "f(x: | #a -> int) = 0;\n",
        "f(x: int & -> int) = 0;\n",
        "f(m: int .. int | -> bool) = 0;\n",
    ] {
        assert_eq!(refusal(src).row, Some(Row::SyntaxError), "{src}");
    }
}
