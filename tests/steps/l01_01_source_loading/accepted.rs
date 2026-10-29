//! Files that load, and the text the lexer then reads.

use zedc::source::load;

const LF: &str = "// invoice\nrate = 3;\ntotal = rate * 4;\n";

#[test]
fn windows_and_classic_mac_line_endings_load_as_the_unix_file() {
    assert_eq!(load(LF.as_bytes()).unwrap(), LF);
    assert_eq!(load(LF.replace('\n', "\r\n").as_bytes()).unwrap(), LF);
    assert_eq!(load(LF.replace('\n', "\r").as_bytes()).unwrap(), LF);
    // A file edited on both systems: each `\r\n`, `\r` and `\n` is one break, so `\n\r` is
    // two.
    assert_eq!(load(b"a\r\nb\rc\n\rd").unwrap(), "a\nb\nc\n\nd");
}

#[test]
fn nfc_text_in_many_scripts_loads_unchanged() {
    for text in [
        // Precomposed Latin, Vietnamese with two marks on one letter, Greek, Cyrillic.
        "name = \"Jos\u{e9}\"; city = \"H\u{1ea1}\u{301} N\u{1ed9}i\";",
        "// \u{3b1}\u{3b2}\u{3b3} \u{43f}\u{440}\u{438}\u{432}\u{435}\u{442}",
        // A precomposed Hangul syllable, and `q` with a dot above, which has no precomposed
        // form and so stays two characters in NFC.
        "word = \"\u{d55c}\u{ae00}\"; mark = \"q\u{307}\";",
        // An emoji sequence joined by U+200D, and an empty file.
        "family = \"\u{1f468}\u{200d}\u{1f469}\u{200d}\u{1f467}\";",
        "",
    ] {
        assert_eq!(load(text.as_bytes()).unwrap(), text);
    }
}

#[test]
fn a_byte_order_mark_after_the_start_is_left_to_the_lexer() {
    assert!(load("a = 1;\u{feff}".as_bytes()).is_ok());
}
