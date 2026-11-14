//! The long inputs the benchmarks of `bench.rs` load, and what loading each must give, checked
//! here at small sizes (TEST-bench-move-rest, P170): every check a benchmark makes besides its
//! ratio has an instance among these correctness tests.

use zedc::source::{Lines, Reject, load};

/// `n` lines of NFC text: a name with a dot above, a string with an accent and a Hangul
/// syllable, a comment with a letter carrying two marks; `\r\n`, `\n` and `\r` line ends.
pub(super) fn nfc_lines(n: usize) -> Vec<u8> {
    "q\u{307}me = \"Jos\u{e9} \u{d55c}\";\r\n// \u{1ea1}\u{301}\r"
        .repeat(n)
        .into_bytes()
}

/// Loading `nfc_lines(n)` gives its `2n` lines.
pub(super) fn loads_nfc_lines(bytes: &[u8], n: usize) {
    let text = load(bytes).unwrap();
    assert_eq!(text.lines().count(), 2 * n);
}

/// One base and `n` marks of alternating combining classes (230 for U+0301, 220 for U+0323).
pub(super) fn base_with_marks(n: usize) -> Vec<u8> {
    let marks = (0..n).map(|i| if i % 2 == 0 { '\u{301}' } else { '\u{323}' });
    std::iter::once('x')
        .chain(marks)
        .collect::<String>()
        .into_bytes()
}

/// NFC sorts the run by combining class, so the first piece that is not NFC is the whole run,
/// and its NFC spelling is the run sorted.
pub(super) fn rejects_base_with_marks(bytes: &[u8]) {
    let Err(Reject::NotNfc { span, nfc }) = load(bytes) else {
        panic!("a run of marks out of order is not NFC")
    };
    assert_eq!((span.start, span.end), (0, bytes.len()));
    assert!(
        nfc.starts_with("x\u{323}"),
        "{:?}",
        nfc.chars().take(4).collect::<String>()
    );
}

/// Starters of NFC quick check Maybe that join nothing, each of which `first_not_nfc` tests by
/// normalizing the text before it (FAIL-source-lvt-jamo): a base with `n` marks then a final
/// jamo, `n` final jamo, and last a syllable LV with a final jamo T, which compose.
pub(super) fn maybe_starters(n: usize) -> Vec<u8> {
    let mut s = String::from("x");
    s.extend(std::iter::repeat_n('\u{323}', n));
    s.extend(std::iter::repeat_n('\u{11a8}', n + 1));
    s.push_str("\u{ac00}\u{11a8}");
    s.into_bytes()
}

/// The rejection of `maybe_starters(n)` is the syllable and its final jamo at the end.
pub(super) fn rejects_maybe_starters(bytes: &[u8]) {
    let Err(Reject::NotNfc { span, nfc }) = load(bytes) else {
        panic!("a syllable LV with a final jamo after it is not NFC")
    };
    assert_eq!(
        (span.start, span.end, nfc.as_str()),
        (bytes.len() - 6, bytes.len(), "\u{ac01}")
    );
}

/// `n` lines, then a byte that is not UTF-8.
pub(super) fn late_bad_byte(n: usize) -> Vec<u8> {
    let mut bytes = "a\u{303} = 1;\n".repeat(n).into_bytes();
    bytes.push(0xff);
    bytes
}

/// The rejection of `late_bad_byte(n)` is at its last byte.
pub(super) fn rejects_late_bad_byte(bytes: &[u8]) {
    let Err(Reject::NotUtf8 { span }) = load(bytes) else {
        panic!("0xff is not UTF-8")
    };
    assert_eq!(span.start, bytes.len() - 1);
}

/// `n` lines of five bytes and a `\n`.
pub(super) fn crlf_lines(n: usize) -> Vec<u8> {
    "ab\u{e9}\r\n".repeat(n).into_bytes()
}

/// Line k holds the five bytes before its `\n`, and the `\n` starts line k + 1 as the `\r`
/// before it ends line k, so the lines of every offset of `crlf_lines(n)` add up to
/// `3n(n + 1) + n`.
pub(super) fn places_every_offset(bytes: &[u8], n: usize) {
    let lines = Lines::new(bytes);
    let sum: usize = (0..bytes.len()).map(|i| lines.line_start(i).1).sum();
    assert_eq!(sum, 3 * n * (n + 1) + n);
}

#[test]
fn nfc_text_with_line_breaks_of_every_kind_loads() {
    for n in [0, 1, 7] {
        loads_nfc_lines(&nfc_lines(n), n);
    }
}

#[test]
fn one_base_with_a_run_of_marks_of_mixed_classes_is_rejected_whole() {
    for n in [2, 3, 50] {
        rejects_base_with_marks(&base_with_marks(n));
    }
}

#[test]
fn a_byte_that_is_not_utf8_after_many_lines_is_placed() {
    for n in [0, 1, 50] {
        rejects_late_bad_byte(&late_bad_byte(n));
    }
}

#[test]
fn every_offset_of_crlf_lines_is_placed() {
    for n in [0, 1, 50] {
        places_every_offset(&crlf_lines(n), n);
    }
}

#[test]
fn starters_that_join_nothing_are_cut_and_the_syllable_at_the_end_is_named() {
    for n in [0, 1, 50] {
        rejects_maybe_starters(&maybe_starters(n));
    }
}
