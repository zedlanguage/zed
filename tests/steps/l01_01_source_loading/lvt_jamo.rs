//! A file not in NFC is rejected at the first sequence NFC changes, with that sequence's NFC
//! spelling (DESIGN.md sec:lexical). The sequence is a whole run that NFC joins: a Hangul
//! syllable written as its jamo, a letter with its marks (FAIL-source-lvt-jamo, found by
//! TEST-complete-lex, author P189).

use unicode_normalization::UnicodeNormalization;
use zedc::source::{Reject, Span, load};

/// The rejection of `text`, which must be one for not being NFC: its span and NFC spelling.
fn not_nfc(text: &str) -> (usize, usize, String) {
    match load(text.as_bytes()) {
        Err(Reject::NotNfc { span, nfc }) => (span.start, span.end, nfc),
        other => panic!("{text:?}: {other:?}"),
    }
}

/// Conjoining jamo L, V and T compose into one syllable: NFC changes all three, so the span is
/// the three and the NFC spelling is the syllable, which fixes the file. Naming only L and V
/// offers U+AC00, and U+AC00 followed by the T jamo U+11A8 is still not NFC.
#[test]
fn a_hangul_syllable_of_three_jamo_is_named_whole() {
    let text = "// \u{1100}\u{1161}\u{11a8}\n";
    let r = load(text.as_bytes()).unwrap_err();
    assert_eq!(
        r,
        Reject::NotNfc {
            span: Span { start: 3, end: 12 },
            nfc: "\u{ac01}".into()
        }
    );
}

/// The neighbors: two jamo L V (control, right before the fix too), a precomposed LV syllable
/// with a T jamo after it, the three jamo between other text, and a mark between the vowel and
/// the final jamo, which blocks the final jamo from joining, so the final jamo is left out; a
/// final jamo after a character it cannot compose with is a sequence of its own; and the
/// ANGSTROM SIGN, which NFC
/// replaces and never joins to the text before it, after a space and after an Oriya vowel sign.
#[test]
fn every_run_that_nfc_joins_is_named_whole() {
    let cases = [
        ("\u{1100}\u{1161}", (0, 6), "\u{ac00}"),
        ("\u{ac00}\u{11a8}", (0, 6), "\u{ac01}"),
        ("x\u{1100}\u{1161}\u{11a8}y", (1, 10), "\u{ac01}"),
        ("\u{1100}\u{1161}\u{301}\u{11a8}", (0, 8), "\u{ac00}\u{301}"),
        (" \u{11a8}\u{344} ", (1, 6), "\u{11a8}\u{308}\u{301}"),
        ("\u{e1}\u{11a8}\u{344}", (2, 7), "\u{11a8}\u{308}\u{301}"),
        ("e\u{301} e\u{301}", (0, 3), "\u{e9}"),
        ("a \u{212b}", (2, 5), "\u{c5}"),
        ("\u{b47}\u{212b}", (3, 6), "\u{c5}"),
    ];
    for (text, (start, end), nfc) in cases {
        assert_eq!(not_nfc(text), (start, end, nfc.to_string()), "{text:?}");
    }
}

/// Putting each named sequence's NFC spelling in its place, one rejection after another, ends in
/// the NFC of the file, and every repair is at or after the one before: no repair leaves its
/// own sequence still not NFC.
#[test]
fn repairing_each_named_sequence_in_turn_gives_the_nfc_file() {
    for text in [
        "\u{1100}\u{1161}\u{11a8}\u{1100}\u{1161}",
        "a\u{301}\u{ac00}\u{11a8} \u{1112}\u{1161}\u{11ab}",
        "\u{1100}\u{1161}\u{301}\u{11a8}o\u{308}\u{304}",
        "\u{212b}\u{1100}\u{1161}\u{11a8}\u{11a8}",
    ] {
        let mut fixed = text.to_string();
        let mut at = 0;
        while let Err(Reject::NotNfc { span, nfc }) = load(fixed.as_bytes()) {
            assert!(span.start >= at, "{text:?}: {span:?} after {at}");
            fixed.replace_range(span.start..span.end, &nfc);
            at = span.start + nfc.len();
        }
        assert_eq!(fixed, text.nfc().collect::<String>(), "{text:?}");
    }
}
