//! Lexing names is of order n log n in the length of the text: many names among text beyond
//! ASCII, one long name, and the error for a long word beyond ASCII with the name it offers,
//! whether the letter beyond ASCII ends a long ASCII run, the whole word is in another script,
//! or the offer must pass n names it may not take (DESIGN.md Part G).

use zed_tests::scaling::{check, inputs};
use zedc::lex::{ErrorKind, lex};

/// The offer of the error for the text `text`, which must be rejected.
fn offer(text: &str) -> Option<String> {
    match lex(text).unwrap_err().kind {
        ErrorKind::NonAsciiName { repair, .. } => repair,
        k => panic!("{k:?}"),
    }
}

#[test]
fn many_names_among_text_beyond_ascii_scale() {
    // A name, a string holding German, a prime, the wildcard, a name starting with `_` and a
    // comment in Chinese: five tokens.
    let line = "grosse \"gr\u{f6}\u{df}e\" x' _ _y // \u{9762}\u{7a4d}\n";
    let texts = inputs(2_000, |n| line.repeat(n));
    check("lexing 5n tokens", 2_000, |n| {
        assert_eq!(lex(&texts[&n]).unwrap().len(), 5 * n);
    });
}

#[test]
fn one_long_name_scales() {
    let texts = inputs(20_000, |n| "ab".repeat(n));
    check("lexing a name of 2n letters", 20_000, |n| {
        assert_eq!(lex(&texts[&n]).unwrap().len(), 1);
    });
}

#[test]
fn a_long_name_ending_in_a_letter_beyond_ascii_scales() {
    // The ASCII run is read by bytes, then read again as a word: twice, not once per letter.
    let texts = inputs(20_000, |n| "ab".repeat(n) + "\u{e9}");
    check("rejecting a name of 2n letters and `é`", 20_000, |n| {
        assert_eq!(offer(&texts[&n]).unwrap().len(), 2 * n + 1);
    });
}

#[test]
fn a_long_word_in_another_script_scales() {
    // Hangul `한글` n times, transliterated as a whole.
    let texts = inputs(20_000, |n| "\u{d55c}\u{ae00}".repeat(n));
    check("rejecting a Hangul word of 2n letters", 20_000, |n| {
        assert_eq!(offer(&texts[&n]).unwrap(), "HanGeul".repeat(n));
    });
}

#[test]
fn an_offer_past_many_taken_names_scales() {
    // `cafe`, `cafe_2`, ..., `cafe_n` are taken, so `café` is offered `cafe_{n+1}`: n suffixes
    // are tried, each one hash lookup.
    let texts = inputs(2_000, |n| {
        let mut t = "cafe = 1;\n".to_string();
        for k in 2..=n {
            t += &format!("cafe_{k} = 1;\n");
        }
        t + "caf\u{e9} = 1;\n"
    });
    check("offering a name past n taken names", 2_000, |n| {
        assert_eq!(offer(&texts[&n]), Some(format!("cafe_{}", n + 1)));
    });
}
