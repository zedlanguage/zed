//! Lexing names is of order n log n in the length of the text: many names, one long name, one long
//! name of letters past the ASCII range, and a long name that mixes scripts only at its end
//! (DESIGN.md Part G).

use zed_tests::scaling::{check, inputs};
use zedc::lex::lex;

#[test]
fn many_names_in_many_scripts_scale() {
    // German, French, Chinese, Japanese, Latin with Han, a prime, the wildcard and a name
    // starting with `_`: eight tokens.
    let line = "gr\u{f6}\u{df}e na\u{ef}ve \u{9762}\u{7a4d} \u{30e6}\u{30fc}\u{30b6}\u{30fc}\u{540d} \
                user\u{540d} x' _ _y ";
    let texts = inputs(2_000, |n| line.repeat(n));
    check("lexing 8n names", 2_000, |n| {
        assert_eq!(lex(&texts[&n]).unwrap().len(), 8 * n);
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
fn one_long_name_that_mixes_scripts_at_its_end_scales() {
    // Cyrillic `длина` n times, then a Latin `x`: one name in two scripts.
    let texts = inputs(20_000, |n| {
        "\u{434}\u{43b}\u{438}\u{43d}\u{430}".repeat(n) + "x"
    });
    check("lexing a name of 5n letters mixing scripts", 20_000, |n| {
        assert!(lex(&texts[&n]).is_err());
    });
}

#[test]
fn one_long_name_of_letters_past_the_ascii_range_scales() {
    // Hangul `한글` n times: every letter is looked up in the table of excluded characters
    // (crates/zedc-syntax/src/lex/name.rs, `is_default_ignorable`), which ASCII skips.
    let texts = inputs(20_000, |n| "\u{d55c}\u{ae00}".repeat(n));
    check("lexing a Hangul name of 2n letters", 20_000, |n| {
        assert_eq!(lex(&texts[&n]).unwrap().len(), 1);
    });
}
