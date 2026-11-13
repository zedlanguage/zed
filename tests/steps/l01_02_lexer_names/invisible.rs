//! Invisible and look-alike characters (DESIGN.md sec:lexical, sec:grammar `Space`,
//! `Comment`, `Char`, `Name`). A character that is neither a space nor a name character
//! starts no token: U+FEFF after the start of the file, NUL, a zero-width joiner anywhere in a
//! name, and every `Bidi_Control` character are lexical errors in code, the code of a hole
//! included, and are taken by `ANY` in a comment and in the text of a string literal. A message
//! names an invisible character by its code point and writes it in its escape form, never as
//! itself. The module `ignorable` tests every Default_Ignorable_Code_Point character.

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
pub(super) fn invisible(hex: &str) -> String {
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
fn a_zero_width_joiner_or_non_joiner_inside_a_name_is_an_error() {
    // A name is ASCII (NAME-ascii-only), so `a\u{200d}b` cannot be a name other than `ab` that
    // looks the same. The name `a` ends before the joiner, which starts no token: a blank
    // character is not read into a word beyond ASCII, and keeps its own message.
    for (c, hex) in [('\u{200d}', "200D"), ('\u{200c}', "200C")] {
        let text = format!("a{c}b = 1;");
        let (kind, span, message) = error(&text);
        assert_eq!(
            (kind, span, &message),
            (ErrorKind::Unexpected(c), (1, 4), &invisible(hex)),
            "{text:?}"
        );
        assert!(!message.contains(c), "{text:?}");
    }
    // The name before the joiner is still read as a name: `ab` alone is one.
    assert_eq!(lex("ab").unwrap()[0].tok, Tok::Name("ab".into()));
}

#[test]
fn a_cyrillic_letter_that_looks_like_a_keyword_is_no_name() {
    // `і` is U+0456 CYRILLIC SMALL LETTER BYELORUSSIAN-UKRAINIAN I, so `іf` looks like the
    // keyword `if`. It is rejected and named by its code point; its lookalike `if` is a keyword,
    // so `if_2` is offered.
    let message = "`\u{456}f` is no name: `\u{456}` (U+0456) is not ASCII. Try `if_2` instead.";
    assert_eq!(
        error("\u{456}f x { 1 } else { 2 }"),
        (
            ErrorKind::NonAsciiName {
                word: "\u{456}f".into(),
                repair: Some("if_2".into()),
            },
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

#[test]
fn a_space_or_format_character_other_than_a_plain_space_between_two_tokens_is_an_error() {
    // `Space` takes only U+0020, tab and the line breaks: a no-break space, an ideographic
    // space, a byte order mark after the start, a word joiner and a soft hyphen are errors.
    for (c, hex) in [
        ('\u{a0}', "A0"),
        ('\u{3000}', "3000"),
        ('\u{feff}', "FEFF"),
        ('\u{2060}', "2060"),
        ('\u{ad}', "AD"),
    ] {
        let text = format!("a ={c}1;");
        let (kind, span, message) = error(&text);
        assert_eq!(
            (kind, span, &message),
            (
                ErrorKind::Unexpected(c),
                (3, 3 + c.len_utf8()),
                &invisible(hex)
            ),
            "{text:?}"
        );
        assert!(!message.contains(c), "{text:?}");
    }
}
