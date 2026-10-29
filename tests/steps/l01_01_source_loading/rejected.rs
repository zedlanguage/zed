//! Files that are rejected, each as an editor or a tool would write it, with the golden
//! rejection: position, message and span.

use unicode_normalization::char::canonical_combining_class;
use unicode_normalization::{UnicodeNormalization, is_nfc};
use zedc::source::{Reject, Span, load};

/// The files, by what produced them.
const FILES: &[(&str, &[u8])] = &[
    // Saved as ISO-8859-1 by an editor configured for a Western European locale.
    ("latin1_comment", b"// prix du caf\xe9\nprice = 3;\n"),
    // A customer name pasted from a macOS file name, which stores `e` then U+0301.
    (
        "decomposed_name",
        "greeting = \"Bonjour\";\nname = \"Jose\u{301}\";\n".as_bytes(),
    ),
    // Notepad's UTF-8 with a byte order mark.
    ("byte_order_mark", "\u{feff}total = 1;\n".as_bytes()),
    // A download cut off inside the three bytes of `€`.
    ("truncated_download", b"unit = \"\xe2\x82"),
    // Java's modified UTF-8 writes a surrogate pair as two three-byte sequences.
    (
        "cesu8_surrogates",
        b"emoji = \"\xed\xa0\xbd\xed\xb8\x80\";\n",
    ),
    // An overlong encoding of `/`.
    ("overlong_slash", b"path = \"a\xc0\xafb\";\n"),
    // U+212B ANGSTROM SIGN, which NFC replaces by U+00C5.
    (
        "angstrom_sign",
        "// wavelength in \u{212b}\nlambda = 5500;\n".as_bytes(),
    ),
    // Two marks under and over `a`, typed above first: NFC orders them by combining class.
    (
        "marks_out_of_order",
        "word = \"a\u{301}\u{323}\";\n".as_bytes(),
    ),
    // Conjoining Hangul jamo, which NFC composes to one syllable.
    ("hangul_jamo", "// \u{1100}\u{1161}\n".as_bytes()),
    // A Windows file whose second line holds a decomposed character: the column counts the
    // scalars of that line, and `\r\n` is one line break.
    (
        "crlf_then_decomposed",
        "a = 1;\r\nb = \"n\u{303}\";\r\n".as_bytes(),
    ),
];

fn show(name: &str, bytes: &[u8]) -> String {
    match load(bytes) {
        Ok(_) => format!("{name}: accepted"),
        Err(r) => {
            let Span { start, end } = r.span();
            format!("{name}: {} [bytes {start}..{end}]", r.render(bytes))
        }
    }
}

#[test]
fn golden_rejections() {
    let out: Vec<String> = FILES.iter().map(|(n, b)| show(n, b)).collect();
    insta::assert_snapshot!(out.join("\n"));
}

#[test]
fn a_non_nfc_rejection_names_the_nfc_spelling_and_fixing_it_loads() {
    for (name, bytes) in FILES {
        if let Err(Reject::NotNfc { span, nfc }) = load(bytes) {
            let mut fixed = bytes[..span.start].to_vec();
            fixed.extend_from_slice(nfc.as_bytes());
            fixed.extend_from_slice(&bytes[span.end..]);
            assert!(
                load(&fixed).is_ok(),
                "{name}: the repaired file still fails"
            );
        }
    }
}

/// A fixed-seed generator, so a failure reproduces.
struct Lcg(u64);

impl Lcg {
    fn next(&mut self, n: usize) -> usize {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        ((self.0 >> 33) as usize) % n
    }
}

/// Over random text built from characters that compose, reorder or are replaced by NFC, the
/// span of every rejection is the first part of the text NFC changes: the text before it is
/// NFC, the span is not, and no shorter end of the span that starts at a character of combining
/// class 0 is not. (An end starting at a mark is not text a person writes: the span starts at the
/// mark's base.)
#[test]
fn the_span_is_the_first_text_nfc_changes() {
    let alphabet = [
        'a', 'e', 'n', 'x', ' ', '\u{301}', '\u{303}', '\u{323}', '\u{307}', '\u{212b}', '\u{c5}',
        '\u{1100}', '\u{1161}', '\u{11a8}', '\u{ac00}', '\u{b47}', '\u{b3e}', '\u{344}',
    ];
    let mut rng = Lcg(29);
    let (mut rejected, mut accepted) = (0, 0);
    for _ in 0..20_000 {
        let len = 1 + rng.next(8);
        let s: String = (0..len)
            .map(|_| alphabet[rng.next(alphabet.len())])
            .collect();
        match load(s.as_bytes()) {
            Ok(text) => {
                assert!(is_nfc(&s), "{s:?} accepted but not NFC");
                assert_eq!(text, s);
                accepted += 1;
            }
            Err(Reject::NotNfc { span, nfc }) => {
                assert!(!is_nfc(&s), "{s:?} rejected but NFC");
                assert!(
                    is_nfc(&s[..span.start]),
                    "{s:?}: text before the span is not NFC"
                );
                assert!(!is_nfc(&s[span.start..span.end]), "{s:?}: the span is NFC");
                let spanned = s[span.start..span.end].char_indices().skip(1);
                for (b, _) in spanned.filter(|&(_, c)| canonical_combining_class(c) == 0) {
                    let tail = &s[span.start + b..span.end];
                    assert!(is_nfc(tail), "{s:?}: the span {span:?} could start later");
                }
                assert_eq!(nfc, s[span.start..span.end].nfc().collect::<String>());
                rejected += 1;
            }
            Err(r) => panic!("{s:?}: {r}"),
        }
    }
    assert!(
        rejected > 5_000 && accepted > 1_000,
        "{rejected} rejected, {accepted} accepted"
    );
}
