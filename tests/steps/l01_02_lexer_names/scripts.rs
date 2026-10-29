//! The one-script rule: names in every script lex, a name that mixes scripts is rejected.

use zedc::lex::{ErrorKind, Tok, is_single_script, lex};

#[test]
fn names_in_one_script_lex() {
    for name in [
        // German, French, Greek, Russian, Hebrew, Arabic, Hindi.
        "größe",
        "naïve",
        "πλάτος",
        "длина",
        "אורך",
        "طول",
        "लंबाई",
        // Chinese, Japanese mixing Han with both kana and the long-vowel mark, Korean.
        "面積",
        "ユーザー名",
        "ひらがな漢字カタカナ",
        "사용자",
        // Latin joined with one East Asian writing system.
        "user名",
        "itemの価格",
        "total합계",
        // Digits and `_` share every script.
        "длина_2",
        "面積1",
        "x'",
    ] {
        let toks = lex(name).unwrap_or_else(|e| panic!("{name}: {e}"));
        assert_eq!(toks.len(), 1, "{name}");
        assert_eq!(toks[0].tok, Tok::Name(name.into()));
    }
}

#[test]
fn lookalike_letters_from_another_script_are_rejected() {
    let cases = [
        // `а` is CYRILLIC SMALL LETTER A.
        ("p\u{430}ypal", "Latin, Cyrillic"),
        // `е` and `х` Cyrillic, the rest Latin.
        ("\u{435}\u{445}ample", "Cyrillic, Latin"),
        // `ο` is GREEK SMALL LETTER OMICRON.
        ("c\u{3bf}unt", "Latin, Greek"),
        // A physics name mixing Greek and Latin is rejected too: write `deltaT` or `ΔΘ`.
        ("\u{394}T", "Greek, Latin"),
        // Hangul with kana is no one writing system.
        ("사용자ユーザー", "Hangul, Katakana"),
    ];
    for (name, scripts) in cases {
        let text = format!("total {name}");
        let e = lex(&text).unwrap_err();
        assert_eq!(e.kind, ErrorKind::MixedScript(name.into()));
        assert_eq!((e.span.start, e.span.end), (6, text.len()));
        assert_eq!(
            e.to_string(),
            format!("the name {name:?} mixes scripts: {scripts}")
        );
    }
}

#[test]
fn the_prime_is_not_read_as_a_script() {
    assert!(lex("длина'").is_ok());
    assert!(!is_single_script("p\u{430}y"));
    assert!(is_single_script("pay"));
}
