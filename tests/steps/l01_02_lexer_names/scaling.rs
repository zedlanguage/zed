//! The long texts the benchmarks of `bench.rs` lex, and what lexing each must give, checked
//! here at small sizes (TEST-bench-move-rest, P170): every check a benchmark makes besides its
//! ratio has an instance among these correctness tests.

use zedc::lex::{ErrorKind, lex};

/// The offer of the error for the text `text`, which must be rejected.
fn offer(text: &str) -> Option<String> {
    match lex(text).unwrap_err().kind {
        ErrorKind::NonAsciiName { repair, .. } => repair,
        k => panic!("{k:?}"),
    }
}

/// `n` lines of a name, a string holding German, a prime, the wildcard, a name starting with
/// `_` and a comment in Chinese: five tokens each.
pub(super) fn names_among_text_beyond_ascii(n: usize) -> String {
    "grosse \"gr\u{f6}\u{df}e\" x' _ _y // \u{9762}\u{7a4d}\n".repeat(n)
}

pub(super) fn lexes_five_tokens_a_line(text: &str, n: usize) {
    assert_eq!(lex(text).unwrap().len(), 5 * n);
}

/// One name of `2n` letters.
pub(super) fn long_name(n: usize) -> String {
    "ab".repeat(n)
}

pub(super) fn lexes_one_name(text: &str, _: usize) {
    assert_eq!(lex(text).unwrap().len(), 1);
}

/// A name of `2n` letters and `é`. The ASCII run is read by bytes, then read again as a word:
/// twice, not once per letter.
pub(super) fn long_name_ending_beyond_ascii(n: usize) -> String {
    "ab".repeat(n) + "\u{e9}"
}

pub(super) fn offers_the_ascii_spelling(text: &str, n: usize) {
    assert_eq!(offer(text).unwrap().len(), 2 * n + 1);
}

/// Hangul `한글` n times, transliterated as a whole.
pub(super) fn hangul_word(n: usize) -> String {
    "\u{d55c}\u{ae00}".repeat(n)
}

pub(super) fn offers_the_transliteration(text: &str, n: usize) {
    assert_eq!(offer(text).unwrap(), "HanGeul".repeat(n));
}

/// `cafe`, `cafe_2`, ..., `cafe_n` are taken, so `café` is offered `cafe_{n+1}`: n suffixes
/// are tried, each one hash lookup.
pub(super) fn taken_names(n: usize) -> String {
    let mut t = "cafe = 1;\n".to_string();
    for k in 2..=n {
        t += &format!("cafe_{k} = 1;\n");
    }
    t + "caf\u{e9} = 1;\n"
}

pub(super) fn offers_the_first_free_suffix(text: &str, n: usize) {
    assert_eq!(offer(text), Some(format!("cafe_{}", n + 1)));
}

#[test]
fn each_benchmark_text_lexes_as_its_benchmark_expects_at_small_sizes() {
    type Case = (fn(usize) -> String, fn(&str, usize));
    let cases: [Case; 5] = [
        (names_among_text_beyond_ascii, lexes_five_tokens_a_line),
        (long_name, lexes_one_name),
        (long_name_ending_beyond_ascii, offers_the_ascii_spelling),
        (hangul_word, offers_the_transliteration),
        (taken_names, offers_the_first_free_suffix),
    ];
    for (make, expect) in cases {
        for n in [1, 2, 9] {
            expect(&make(n), n);
        }
    }
}
