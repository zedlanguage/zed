//! A name is ASCII (NAME-ascii-only, 2026-11-12): a word that would be a name but for a letter,
//! digit or combining mark beyond ASCII is a lexical error, which names the first such
//! character and offers an ASCII name for the word when the tables give one. These words were
//! names under the one-script rule, which this replaces.

use zedc::lex::{ErrorKind, Tok, lex};

/// The message for the word `word` that holds `held`, with the offer `repair`.
fn message(word: &str, held: &str, repair: Option<&str>) -> String {
    let what = match word.chars().next() {
        Some('#') => "atom",
        Some('@') => "annotation",
        _ => "name",
    };
    let head = format!("`{word}` is no {what}: {held} is not ASCII.");
    match repair {
        Some(r) => format!("{head} Try `{r}` instead."),
        None => format!("{head} Write the {what} in ASCII letters, digits and `_`."),
    }
}

/// Checks that `word`, lexed after `total `, is rejected over its whole span with the message
/// naming `held` and offering `repair`.
fn rejected(word: &str, held: &str, repair: Option<&str>) {
    let text = format!("total {word}");
    let e = lex(&text).unwrap_err();
    assert_eq!(
        e.kind,
        ErrorKind::NonAsciiName {
            word: word.into(),
            repair: repair.map(Into::into),
        },
        "{word}"
    );
    assert_eq!((e.span.start, e.span.end), (6, text.len()), "{word}");
    assert_eq!(e.to_string(), message(word, held, repair), "{word}");
}

#[test]
fn names_in_other_scripts_are_rejected_and_transliterated_as_a_whole() {
    // Tier 3 for a word with no ASCII letter: the any_ascii tables, over the whole word.
    for (word, held, repair) in [
        // German and French: Latin, so tier 1 (`ö`, `ï`) and tier 3 (`ß`) per character.
        ("größe", "`ö` (U+00F6)", "grosse"),
        ("naïve", "`ï` (U+00EF)", "naive"),
        // Greek, Russian, Hebrew, Arabic, Hindi.
        ("πλάτος", "`π` (U+03C0)", "platos"),
        ("длина", "`д` (U+0434)", "dlina"),
        ("אורך", "`א` (U+05D0)", "vrkh"),
        ("طول", "`ط` (U+0637)", "twl"),
        ("लंबाई", "`ल` (U+0932)", "lmbai"),
        // Chinese, Japanese with Han, kana and the long-vowel mark (which gives no name
        // character), Korean, and a word in two East Asian writing systems.
        ("面積", "`面` (U+9762)", "MianJi"),
        ("ユーザー名", "`ユ` (U+30E6)", "yuzaMing"),
        (
            "ひらがな漢字カタカナ",
            "`ひ` (U+3072)",
            "hiraganaHanZikatakana",
        ),
        ("사용자", "`사` (U+C0AC)", "SaYongJa"),
        ("사용자ユーザー", "`사` (U+C0AC)", "SaYongJayuza"),
        // Digits, `_` and a prime are kept.
        ("длина_2", "`д` (U+0434)", "dlina_2"),
        ("面積1", "`面` (U+9762)", "MianJi1"),
        ("длина'", "`д` (U+0434)", "dlina'"),
        // A word wholly of Cyrillic lookalikes is transliterated, not read as lookalikes.
        ("\u{441}\u{43e}\u{440}", "`с` (U+0441)", "sor"),
        // Greek letters alone are transliterated too.
        ("α", "`α` (U+03B1)", "a"),
        ("Δ", "`Δ` (U+0394)", "D"),
    ] {
        rejected(word, held, Some(repair));
    }
}

#[test]
fn accents_are_dropped_and_compatibility_forms_decomposed() {
    // Tier 1: NFKD, without combining marks.
    for (word, held, repair) in [
        ("café", "`é` (U+00E9)", "cafe"),
        ("\u{fb01}le", "`ﬁ` (U+FB01)", "file"),
        ("\u{ff41}b", "`ａ` (U+FF41)", "ab"),
        ("x²", "`²` (U+00B2)", "x2"),
        ("x\u{2081}", "`₁` (U+2081)", "x1"),
        ("_é", "`é` (U+00E9)", "_e"),
        ("é_", "`é` (U+00E9)", "e_"),
        // A combining mark is an accent on the letter before it, and is dropped; it is named by
        // its code point, since alone it may not show.
        (
            "ne\u{301}e",
            "the character U+0301, which may not show on screen,",
            "nee",
        ),
    ] {
        rejected(word, held, Some(repair));
    }
}

#[test]
fn lookalike_letters_become_the_ascii_letters_they_look_like() {
    // Tier 2: the confusables data of UTS #39, in a word with an ASCII letter.
    for (word, held, repair) in [
        // `а` is CYRILLIC SMALL LETTER A.
        ("p\u{430}ypal", "`а` (U+0430)", "paypal"),
        // `е` and `х` Cyrillic, the rest Latin.
        ("\u{435}\u{445}ample", "`е` (U+0435)", "example"),
        // `ο` is GREEK SMALL LETTER OMICRON.
        ("c\u{3bf}unt", "`ο` (U+03BF)", "count"),
        ("p\u{430}\u{3bf}l", "`а` (U+0430)", "paol"),
        ("\u{2113}en", "`ℓ` (U+2113)", "len"),
    ] {
        rejected(word, held, Some(repair));
    }
}

#[test]
fn latin_letters_beyond_ascii_are_transliterated() {
    // Tier 3 for a Latin letter that tiers 1 and 2 leave: `ß` has no decomposition.
    for (word, held, repair) in [
        ("Straße", "`ß` (U+00DF)", "Strasse"),
        ("ß", "`ß` (U+00DF)", "ss"),
    ] {
        rejected(word, held, Some(repair));
    }
}

#[test]
fn a_letter_of_another_script_beside_ascii_letters_gets_no_offer() {
    // No table gives a lookalike, and a transliteration would read as ASCII letters the
    // program did not write: `ΔT` is `deltaT` or `dT` by the program's choice.
    for (word, held) in [
        ("\u{394}T", "`Δ` (U+0394)"),
        ("δt", "`δ` (U+03B4)"),
        ("Ωmega", "`Ω` (U+03A9)"),
        ("user名", "`名` (U+540D)"),
        ("itemの価格", "`の` (U+306E)"),
        ("total합계", "`합` (U+D569)"),
        ("x\u{663}", "`٣` (U+0663)"),
    ] {
        rejected(word, held, None);
    }
}

#[test]
fn an_offer_that_would_be_no_name_is_not_made() {
    // Arabic-Indic digits transliterate to `123`, which starts with a digit.
    rejected("\u{661}\u{662}\u{663}", "`١` (U+0661)", None);
}

#[test]
fn the_offer_is_a_new_name_with_the_least_suffix() {
    // The offer is no word of the text, no keyword, and gets the least `_2`, `_3`, ... that
    // makes it new.
    let e = lex("cafe = 1; café").unwrap_err();
    assert_eq!((e.span.start, e.span.end), (10, 15));
    assert_eq!(
        e.to_string(),
        message("café", "`é` (U+00E9)", Some("cafe_2"))
    );
    let e = lex("cafe = 1; cafe_2 = 2; café").unwrap_err();
    assert_eq!(
        e.to_string(),
        message("café", "`é` (U+00E9)", Some("cafe_3"))
    );
    // `ѕ` is CYRILLIC SMALL LETTER DZE; `test` is a keyword.
    let e = lex("te\u{455}t").unwrap_err();
    assert_eq!(
        e.to_string(),
        message("teѕt", "`ѕ` (U+0455)", Some("test_2"))
    );
    // A keyword followed by a letter beyond ASCII is one word.
    let e = lex("ifé").unwrap_err();
    assert_eq!(e.to_string(), message("ifé", "`é` (U+00E9)", Some("ife")));
}

#[test]
fn the_offer_is_no_prelude_name() {
    // The lexer does not know the prelude; the front end refuses its names in the offer.
    let src = "main(m: MainArgs) {\n  \u{2113}en = 1;\n}\n";
    let out = zedc::run::load(src.as_bytes()).err().expect("rejected");
    assert_eq!(
        out.lines().next().unwrap(),
        format!("2:3: {}", message("ℓen", "`ℓ` (U+2113)", Some("len_2")))
    );
}

#[test]
fn atoms_and_annotations_are_offered_their_ascii_spelling() {
    let e = lex("#café").unwrap_err();
    assert_eq!((e.span.start, e.span.end), (0, 6));
    assert_eq!(
        e.to_string(),
        message("#café", "`é` (U+00E9)", Some("#cafe"))
    );
    // `@test` is an annotation, though `test` is a keyword.
    let e = lex("@tést").unwrap_err();
    assert_eq!(
        e.to_string(),
        message("@tést", "`é` (U+00E9)", Some("@test"))
    );
    // Another atom of the program is not offered.
    let e = lex("x = #cafe; y = #café").unwrap_err();
    assert_eq!(
        e.to_string(),
        message("#café", "`é` (U+00E9)", Some("#cafe_2"))
    );
}

#[test]
fn ascii_names_with_a_prime_lex() {
    for name in ["x'", "x_1", "_y", "__", "Pt'"] {
        let toks = lex(name).unwrap_or_else(|e| panic!("{name}: {e}"));
        assert_eq!(toks.len(), 1, "{name}");
        assert_eq!(toks[0].tok, Tok::Name(name.into()));
    }
}

#[test]
fn the_grammar_engine_rejects_a_name_beyond_ascii_and_takes_it_in_text() {
    use zed_tests::step_helpers::m0_03_grammar_tools::{design, spec_dir};
    let dir = spec_dir("non_ascii_names", &design(""), "");
    let spec = zed_tools::spec::Spec::open(&dir.root()).expect("the spec reads");
    let engine = |text: &str| zed_tools::syntax::lex(&spec.lexical, text);
    for text in ["cafe = 1;", "x' = #cafe;", "_y = 1;"] {
        assert!(engine(text).is_ok(), "{text:?}");
    }
    for text in [
        "caf\u{e9} = 1;",
        "\u{3c0} = 1;",
        "x = #caf\u{e9};",
        "p\u{430}y = 1;",
    ] {
        assert!(engine(text).is_err(), "{text:?}");
    }
    for text in ["x = \"caf\u{e9}\";", "x = 1; // \u{3c0}\n"] {
        assert!(engine(text).is_ok(), "{text:?}");
    }
}

#[test]
fn the_messages_read_so() {
    let says = |text: &str| lex(text).unwrap_err().to_string();
    assert_eq!(
        says("caf\u{e9} = 1;"),
        "`café` is no name: `é` (U+00E9) is not ASCII. Try `cafe` instead."
    );
    assert_eq!(
        says("\u{394}T = 1;"),
        "`ΔT` is no name: `Δ` (U+0394) is not ASCII. Write the name in ASCII letters, digits \
         and `_`."
    );
    assert_eq!(
        says("ne\u{301}e = 1;"),
        "`ne\u{301}e` is no name: the character U+0301, which may not show on screen, is not \
         ASCII. Try `nee` instead."
    );
    assert_eq!(
        says("x = #caf\u{e9};"),
        "`#café` is no atom: `é` (U+00E9) is not ASCII. Try `#cafe` instead."
    );
    assert_eq!(
        says("@t\u{e9}st f() -> int { 1 }"),
        "`@tést` is no annotation: `é` (U+00E9) is not ASCII. Try `@test` instead."
    );
}
