//! Invisible and look-alike characters (DESIGN.md sec:lexical, sec:grammar `Space`,
//! `Comment`, `Char`, `Name`). A character that is neither a space nor an identifier character
//! starts no token: U+FEFF after the start of the file, NUL, a zero-width joiner before a name,
//! and every `Bidi_Control` character are lexical errors in code, the code of a hole included,
//! and are taken by `ANY` in a comment and in the text of a string literal. A message names an
//! invisible character by its code point and writes it in its escape form, never as itself.

use zedc::lex::{ErrorKind, Tok, lex};

/// The `Bidi_Control` characters DESIGN.md sec:lexical lists.
const BIDI: [char; 12] = [
    '\u{61C}', '\u{200E}', '\u{200F}', '\u{202A}', '\u{202B}', '\u{202C}', '\u{202D}', '\u{202E}',
    '\u{2066}', '\u{2067}', '\u{2068}', '\u{2069}',
];

/// The kind, the byte span and the message of the error lexing `text` stops at.
fn error(text: &str) -> (ErrorKind, (usize, usize), String) {
    let e = lex(text).expect_err(text);
    (e.kind.clone(), (e.span.start, e.span.end), e.to_string())
}

/// The message for the invisible character with code point `hex`, as written in its escape.
fn invisible(hex: &str) -> String {
    let padded = format!("{hex:0>4}");
    format!(
        "the character U+{padded}, which may not show on screen, starts no name, number, \
         operator or other part of a Zed program. Remove it, or, if it is meant as text, write \
         it inside a string, as `\"\\u{{{hex}}}\"`."
    )
}

#[test]
fn a_byte_order_mark_after_the_start_is_an_error_in_code() {
    let message = "the character U+FEFF, which may not show on screen, starts no name, number, \
                   operator or other part of a Zed program. Remove it, or, if it is meant as \
                   text, write it inside a string, as `\"\\u{FEFF}\"`.";
    assert_eq!(
        error("a = 1;\u{feff}"),
        (
            ErrorKind::Unexpected('\u{feff}'),
            (6, 9),
            message.to_string()
        )
    );
    // Inside a name it ends the name, which it cannot continue.
    assert_eq!(
        error("a\u{feff}b = 1;"),
        (
            ErrorKind::Unexpected('\u{feff}'),
            (1, 4),
            message.to_string()
        )
    );
}

#[test]
fn nul_is_an_error_in_code_and_is_never_printed_as_itself() {
    let message = "the character U+0000, which may not show on screen, starts no name, number, \
                   operator or other part of a Zed program. Remove it, or, if it is meant as \
                   text, write it inside a string, as `\"\\u{0}\"`.";
    let (kind, span, text) = error("a = 1;\u{0}");
    assert_eq!(
        (kind, span, text.as_str()),
        (ErrorKind::Unexpected('\u{0}'), (6, 7), message)
    );
    assert!(!text.contains('\u{0}'));
}

#[test]
fn a_zero_width_joiner_starts_no_name() {
    assert_eq!(
        error("\u{200d}b = 1;"),
        (ErrorKind::Unexpected('\u{200d}'), (0, 3), invisible("200D"))
    );
}

#[test]
fn a_zero_width_joiner_or_non_joiner_inside_a_name_is_part_of_it() {
    // UAX #31 puts U+200C and U+200D in XID_Continue (Unicode 15.1), and DESIGN.md's `Name`
    // rule takes XID_CONTINUE, so `a\u{200d}b` is one name, distinct from `ab` though it looks
    // the same. Whether a joiner should be allowed only where it changes how a word is written
    // (UAX #31 section 2.3) is an open question in QUESTIONS.md ("A zero-width joiner inside a
    // name"); this test pins what DESIGN.md states now.
    for name in ["a\u{200d}b", "a\u{200c}b"] {
        let toks = lex(name).unwrap_or_else(|e| panic!("{name:?}: {e}"));
        assert_eq!(toks.len(), 1, "{name:?}");
        assert_eq!(toks[0].tok, Tok::Name(name.into()));
    }
}

#[test]
fn a_cyrillic_letter_before_a_latin_one_is_a_mixed_script_name() {
    // `і` is U+0456 CYRILLIC SMALL LETTER BYELORUSSIAN-UKRAINIAN I, so `іf` is a name and not
    // the keyword `if`.
    let message = "the name `\u{456}f` mixes letters of the scripts Cyrillic and Latin, and a \
                   name is written in one script, so that no name looks like another and is a \
                   different one. Write it in one script: a letter that looks Latin may be, for \
                   instance, a Cyrillic or Greek letter of the same shape.";
    assert_eq!(
        error("\u{456}f x { 1 } else { 2 }"),
        (
            ErrorKind::MixedScript("\u{456}f".into()),
            (0, 3),
            message.to_string()
        )
    );
}

#[test]
fn bidi_controls_are_errors_in_code_in_a_name_and_in_a_hole() {
    for c in BIDI {
        let hex = format!("{:X}", c as u32);
        let width = c.len_utf8();
        for (text, at) in [
            (format!("a = 1 {c};"), 6),
            (format!("a{c} = 1;"), 1),
            (format!("a = \"${{b {c}}}\";"), 9),
        ] {
            let (kind, span, message) = error(&text);
            assert_eq!(
                (kind, span, &message),
                (ErrorKind::Unexpected(c), (at, at + width), &invisible(&hex)),
                "{text:?}"
            );
            assert!(!message.contains(c), "{text:?}");
        }
    }
}

#[test]
fn invisible_characters_are_taken_in_comments_and_in_string_text() {
    let mut taken: Vec<char> = BIDI.to_vec();
    taken.extend(['\u{feff}', '\u{0}', '\u{200d}']);
    for c in taken {
        for text in [
            format!("a = 1; // {c} x\n"),
            format!("/* {c} */ a = 1;"),
            format!("a = \"x{c}y\";"),
            format!("a = \"${{b}}{c}\";"),
        ] {
            assert!(
                lex(&text).is_ok(),
                "{text:?}: {}",
                lex(&text).err().unwrap()
            );
        }
    }
}

#[test]
fn a_loaded_file_gives_the_line_and_column_of_the_character() {
    for (text, expected) in [
        ("a = 1;\u{feff}", format!("1:7: {}", invisible("FEFF"))),
        ("a = 1;\n\u{0}", format!("2:1: {}", invisible("0"))),
        (
            "a = \"${b \u{202e}}\";",
            format!("1:10: {}", invisible("202E")),
        ),
    ] {
        match zedc::run::load(text.as_bytes()) {
            Err(message) => assert_eq!(message, expected, "{text:?}"),
            Ok(_) => panic!("{text:?} loaded"),
        }
    }
}

#[test]
fn a_quoted_line_with_characters_of_no_width_does_not_stop_the_compiler() {
    // A file with no `main` is refused with the line quoted under its message; on a line whose
    // characters outnumber its columns, finding a column past the line's end once subtracted
    // below zero (crates/zedc/src/front.rs, `layout`).
    for text in [
        "a = \"x\u{feff}y\";",
        "a = 1; // \u{0}\n",
        "a\u{200d}b = 1;",
        "a = 1; // \u{202e}\n",
        "a = \"q\u{307}\";",
    ] {
        let result = std::panic::catch_unwind(|| zedc::run::load(text.as_bytes()));
        assert!(matches!(result, Ok(Err(_))), "{text:?}");
    }
}
