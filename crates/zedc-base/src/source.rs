//! Source loading (DESIGN.md sec:lexical; step L1.1): a file's bytes become the text the lexer
//! reads, or are rejected with a span.
//!
//! The file must be UTF-8 in Normalization Form C. A file that is not NFC is rejected rather
//! than normalized, since two spellings that look the same must not hash differently. A
//! leading byte order mark is rejected for the same reason. Line endings normalize to `\n`:
//! `\r\n` and a lone `\r` are each one line break.
//!
//! A span is a byte range of the file as read. Every rejection happens before the line endings
//! are normalized, so its span indexes the bytes the author has.

use std::fmt;

use unicode_normalization::char::{canonical_combining_class, compose};
use unicode_normalization::{IsNormalized, UnicodeNormalization, is_nfc, is_nfc_quick};

/// A byte range of the file as read.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Span {
    /// The first byte.
    pub start: usize,
    /// One past the last byte.
    pub end: usize,
}

/// Why a file was rejected.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Reject {
    /// The bytes at `span` are not UTF-8: an invalid or overlong sequence, an encoded
    /// surrogate, or a sequence cut off by the end of the file.
    NotUtf8 {
        /// The bytes of the first invalid sequence.
        span: Span,
    },
    /// The file starts with a byte order mark.
    ByteOrderMark {
        /// The mark's three bytes.
        span: Span,
    },
    /// The characters at `span` are not in NFC; `nfc` is their NFC spelling.
    NotNfc {
        /// The first sequence of characters that NFC changes.
        span: Span,
        /// Its NFC spelling.
        nfc: String,
    },
}

impl Reject {
    /// The span of the rejection.
    pub fn span(&self) -> Span {
        match self {
            Reject::NotUtf8 { span }
            | Reject::ByteOrderMark { span }
            | Reject::NotNfc { span, .. } => *span,
        }
    }

    /// The rejection as `line:column: message`, with the position of its span's start in
    /// `bytes`, the file it was found in; a UTF-8 rejection shows the bytes in hexadecimal.
    pub fn render(&self, bytes: &[u8]) -> String {
        let (line, col) = line_col(bytes, self.span().start);
        format!("{line}:{col}: {}", self.message(bytes))
    }

    /// The rejection's message with no position, its bytes in `bytes`, the file it was found
    /// in, shown in hexadecimal when they are not UTF-8.
    pub fn message(&self, bytes: &[u8]) -> String {
        let Span { start, end } = self.span();
        match self {
            Reject::NotUtf8 { .. } => {
                let hex: Vec<String> = bytes[start..end]
                    .iter()
                    .map(|b| format!("{b:02X}"))
                    .collect();
                format!(
                    "a Zed file is UTF-8 text, and the bytes here, {} in hexadecimal, are not a \
                     UTF-8 character, so the file cannot be read. Save the file as UTF-8 in your \
                     editor, or replace these bytes with the character they were meant to be.",
                    hex.join(" ")
                )
            }
            _ => self.to_string(),
        }
    }
}

impl fmt::Display for Reject {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Reject::NotUtf8 { .. } => write!(
                f,
                "a Zed file is UTF-8 text, and the bytes here are not a UTF-8 character, so the \
                 file cannot be read. Save the file as UTF-8 in your editor, or replace these \
                 bytes with the character they were meant to be."
            ),
            Reject::ByteOrderMark { .. } => write!(
                f,
                "the file starts with a byte order mark (the bytes EF BB BF), and a Zed file may \
                 not, since the same program would then be stored in two ways. Save the file as \
                 UTF-8 without a byte order mark (in many editors this is \"UTF-8\" rather than \
                 \"UTF-8 with BOM\")."
            ),
            Reject::NotNfc { nfc, .. } => write!(
                f,
                "these characters are not in Unicode Normalization Form C (NFC), which spells \
                 them as {}. A Zed file must be in NFC, so that two names that look the same are \
                 the same name. Retype the characters, or have your editor save the file in NFC.",
                scalars(nfc)
            ),
        }
    }
}

/// The reason the system gave for an input or output error `e`, in words, without the system's
/// own error number: `No such file or directory`, not `No such file or directory (os error 2)`.
pub fn io_reason(e: &std::io::Error) -> String {
    let text = e.to_string();
    match text.rfind(" (os error ") {
        Some(at) if text.ends_with(')') => text[..at].to_string(),
        _ => text,
    }
}

/// Why zedc could not read the file at `path`, which the command line names, with the repair.
pub fn unreadable(path: &str, e: &std::io::Error) -> String {
    format!(
        "{path}: zedc could not read this file: {}. Check the path and that you may read the file.",
        io_reason(e)
    )
}

/// `s` as code points, `U+0065 U+0301`.
fn scalars(s: &str) -> String {
    s.chars()
        .map(|c| format!("U+{:04X}", c as u32))
        .collect::<Vec<_>>()
        .join(" ")
}

/// The text of a file: its bytes checked and its line endings normalized.
pub fn load(bytes: &[u8]) -> Result<String, Reject> {
    let text = match std::str::from_utf8(bytes) {
        Ok(text) => text,
        Err(e) => {
            let start = e.valid_up_to();
            let end = start + e.error_len().unwrap_or(bytes.len() - start);
            return Err(Reject::NotUtf8 {
                span: Span { start, end },
            });
        }
    };
    if text.starts_with('\u{feff}') {
        return Err(Reject::ByteOrderMark {
            span: Span { start: 0, end: 3 },
        });
    }
    if !is_nfc(text) {
        let span = first_not_nfc(text);
        let nfc = text[span.start..span.end].nfc().collect();
        return Err(Reject::NotNfc { span, nfc });
    }
    Ok(unified_newlines(text))
}

/// `text` with each `\r\n` and each lone `\r` written `\n`, the one line end the lexer reads.
/// `\r\n` is replaced first, so it becomes one `\n`, not two. O(the length of `text`).
pub fn unified_newlines(text: &str) -> String {
    text.replace("\r\n", "\n").replace('\r', "\n")
}

/// The first sequence of `text` that NFC changes, for a `text` that is not NFC. The text is cut
/// before each character that NFC never joins to the text before it: one whose canonical
/// decomposition starts with a character of combining class 0 whose NFC quick check is Yes
/// (UAX #15, "Stable Code Points" and "Detecting Normalization Forms"; ICU calls this a
/// composition boundary). NFC of the text is then NFC of each piece, joined, so the span is the
/// first piece that is not NFC, and its NFC spelling, put in its place, leaves no change there.
/// A character of combining class 0 whose quick check is Maybe, such as a Hangul vowel or final
/// jamo, joins the text before it exactly when the last character of NFC of that text is of
/// combining class 0 and composes with it (any character between blocks a starter), so a
/// syllable written as its three jamo L V T is one piece and a final jamo after a space is cut
/// from it. A character NFC replaces, quick check No, is tested by the first character of its
/// decomposition: the ANGSTROM SIGN U+212B, which decomposes to `A` and a ring, is cut before.
// Complexity tradeoff: the earlier form cut before every character of combining class 0 and
// tried each piece and each pair of adjacent pieces; it was O(N) too, but wrong for three
// pieces that compose into one (L V T jamo). Here a character whose quick check is Yes is its
// own decomposition's first character for this test (checked for every code point by
// `nfc_never_joins_a_cut_character_to_the_text_before_it`), so only a character of quick
// check No, rare in text, is decomposed: a few table lookups per character. A Maybe starter
// costs NFC of the piece so far; when it does not join, the piece ends there, and it joins
// only by composing with the piece's last character, which a chain of compositions allows at
// most twice in a row (L V T), so each piece is normalized a bounded number of times: O(N) in
// all, as are the NFC checks of the pieces, with no memory beyond the scan. The naive exact
// form, NFC of the text before each candidate cut, is O(N²).
fn first_not_nfc(text: &str) -> Span {
    let quick = |c: char| is_nfc_quick(std::iter::once(c));
    let mut start = 0;
    for (i, c) in text.char_indices().skip(1) {
        let first = match quick(c) {
            IsNormalized::No => std::iter::once(c).nfd().next().unwrap_or(c),
            _ => c,
        };
        let boundary = canonical_combining_class(first) == 0
            && (quick(first) == IsNormalized::Yes
                || !text[start..i].nfc().last().is_some_and(|last| {
                    canonical_combining_class(last) == 0 && compose(last, first).is_some()
                }));
        if boundary {
            if !is_nfc(&text[start..i]) {
                return Span { start, end: i };
            }
            start = i;
        }
    }
    debug_assert!(!is_nfc(&text[start..]), "the text is not NFC");
    Span {
        start,
        end: text.len(),
    }
}

/// The 1-based line and column of byte `offset` of `bytes`, the column counted in Unicode
/// scalars. `\r\n`, `\r` and `\n` each end a line. The bytes before `offset` must be UTF-8,
/// as they are for the start of every rejection's span. For many offsets in one text, make
/// its [`Lines`] once. One pass, with no allocation (`zed_kernel::sites::line_col`).
pub fn line_col(bytes: &[u8], offset: usize) -> (usize, usize) {
    zed_kernel::sites::line_col(bytes, offset)
}

/// The lines of `text` that hold bytes `from..to`: the start of the line holding `from` and
/// the end, before its line break, of the line holding `to`. `\r\n`, `\r` and `\n` each end
/// a line, as for [`line_col`]; [`load`] leaves only `\n`, and a text that did not pass
/// through it (a test's, a tool's) still breaks where [`line_col`] counts a new line.
/// `from` and `to` must be character boundaries of `text`; slicing it panics at any other
/// offset ("is not a char boundary"). O(length of those lines).
pub fn line_bounds(text: &str, from: usize, to: usize) -> (usize, usize) {
    let breaks = ['\r', '\n'];
    let start = text[..from].rfind(breaks).map_or(0, |i| i + 1);
    let end = text[to..].find(breaks).map_or(text.len(), |i| to + i);
    (start, end)
}

/// Where the lines of a text start, found once, so that the line and column of an offset cost
/// a binary search and a count of the scalars before it on its line, not a decoding of the
/// text up to it.
// Complexity tradeoff (COMPLEXITY.md F8): the naive `line_col` decodes the text from byte 0
// for each offset, O(k · N) for k offsets in a text of N bytes; the line starts found once,
// O(N) time and O(lines) memory, place an offset in O(log lines) plus a count of the scalars
// before it on its line. That count is still O(line length) per offset, so many offsets on
// one long line cost O(k · line), the size of the output that shows that line per offset
// (row F30).
pub struct Lines {
    /// The byte offsets after a line break, each with the 1-based number of the line it
    /// starts, in increasing order, beginning with `(0, 1)`. Inside a `\r\n` both the offset
    /// after `\r` and the one after `\n` start the next line.
    starts: Vec<(usize, usize)>,
}

impl Lines {
    /// The line starts of `bytes`.
    pub fn new(bytes: &[u8]) -> Self {
        let mut starts = vec![(0, 1)];
        for (i, &b) in bytes.iter().enumerate() {
            match b {
                b'\n' if i > 0 && bytes[i - 1] == b'\r' => {
                    starts.push((i + 1, starts.last().unwrap().1))
                }
                b'\r' | b'\n' => starts.push((i + 1, starts.last().unwrap().1 + 1)),
                _ => {}
            }
        }
        Lines { starts }
    }

    /// The start of the line holding byte `offset`, and that line's number.
    pub fn line_start(&self, offset: usize) -> (usize, usize) {
        let k = self.starts.partition_point(|&(start, _)| start <= offset);
        self.starts[k - 1]
    }

    /// The 1-based line and column of byte `offset` of `bytes`, the text these are the lines
    /// of; the bytes of its line before `offset` must be UTF-8.
    pub fn line_col(&self, bytes: &[u8], offset: usize) -> (usize, usize) {
        let (start, line) = self.line_start(offset);
        let before =
            std::str::from_utf8(&bytes[start..offset]).expect("the bytes before a span are UTF-8");
        (line, before.chars().count() + 1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_line_end_becomes_one_newline() {
        let ends = "a\r\nb\rc\nd\r\r\n\n\r";
        assert_eq!(unified_newlines(ends), "a\nb\nc\nd\n\n\n\n");
        assert_eq!(unified_newlines(""), "");
        assert_eq!(unified_newlines("é\r"), "é\n");
    }

    /// A lone `\r` ends a line, as `\n` and `\r\n` do (D5 of REPORT-dryA3: the copies this
    /// replaced looked for `\n` alone and took `a\rb` as one line).
    #[test]
    fn line_bounds_ends_a_line_at_every_break() {
        let text = "a = 1;\rb = 2;\r\nc = 3;\nd";
        let b = text.find('b').unwrap();
        let (s, e) = line_bounds(text, b, b);
        assert_eq!(&text[s..e], "b = 2;");
        let c = text.find('c').unwrap();
        let (s, e) = line_bounds(text, b, c + 1);
        assert_eq!(&text[s..e], "b = 2;\r\nc = 3;");
        assert_eq!(line_bounds(text, 0, 0), (0, 6));
        assert_eq!(
            line_bounds(text, text.len(), text.len()),
            (text.len() - 1, text.len())
        );
        // The line and column agree with the bounds.
        assert_eq!(line_col(text.as_bytes(), b), (2, 1));
    }

    /// `line_bounds` read directly: back from `from` to the character after the last `\r` or
    /// `\n` before it, forward from `to` to the first at or after it.
    fn naive_bounds(text: &str, from: usize, to: usize) -> (usize, usize) {
        let b = text.as_bytes();
        let brk = |c: u8| c == b'\r' || c == b'\n';
        let mut s = from;
        while s > 0 && !brk(b[s - 1]) {
            s -= 1;
        }
        let mut e = to;
        while e < b.len() && !brk(b[e]) {
            e += 1;
        }
        (s, e)
    }

    /// Every text of up to five parts from `a`, `\r`, `\n`, `\r\n`, `é` and a space:
    /// 1 + 6 + 6^2 + ... + 6^5 = 9331 texts.
    fn short_texts() -> Vec<String> {
        let parts = ["a", "\r", "\n", "\r\n", "é", " "];
        let mut level = vec![String::new()];
        let mut all = level.clone();
        for _ in 0..5 {
            level = (level.iter())
                .flat_map(|t| parts.iter().map(move |p| format!("{t}{p}")))
                .collect();
            all.extend(level.iter().cloned());
        }
        all
    }

    /// Plan row RT-internal-fault: the one-pass `line_col`, which a handler of signals calls,
    /// agrees with `Lines` at every boundary of every text of [`short_texts`], and at the
    /// offset between the `\r` and the `\n` of a `\r\n`.
    #[test]
    fn line_col_agrees_with_lines_at_every_boundary() {
        for text in short_texts() {
            let lines = Lines::new(text.as_bytes());
            for i in (0..=text.len()).filter(|&i| text.is_char_boundary(i)) {
                let want = lines.line_col(text.as_bytes(), i);
                assert_eq!(line_col(text.as_bytes(), i), want, "{text:?} at {i}");
            }
        }
    }

    /// TEST-dry-shared-units: the bounds agree with the rule read directly at every ordered
    /// pair of character boundaries of every text of up to five parts from `a`, `\r`, `\n`,
    /// `\r\n`, `é` (two bytes) and a space, 9331 texts. Negative control:
    /// `a_bound_past_the_line_break_is_caught`.
    #[test]
    fn line_bounds_agree_with_the_rule_read_directly() {
        let texts = short_texts();
        assert_eq!(texts.len(), 9331);
        for text in texts {
            let cuts: Vec<usize> = (0..=text.len())
                .filter(|&i| text.is_char_boundary(i))
                .collect();
            for &from in &cuts {
                for &to in cuts.iter().filter(|&&to| to >= from) {
                    assert_eq!(line_bounds(&text, from, to), naive_bounds(&text, from, to));
                }
            }
        }
        assert_eq!(line_bounds("", 0, 0), (0, 0));
        assert_eq!(line_bounds("\n", 1, 1), (1, 1));
        assert_eq!(line_bounds("\r\n", 1, 1), (1, 1));
    }

    /// Negative control: bounds that take only `\n` as a break, as the copies DRY-text-shared
    /// replaced did, differ from the rule on some text, so the test above can fail.
    #[test]
    fn a_bound_past_the_line_break_is_caught() {
        let only_newline = |text: &str, from: usize, to: usize| {
            let start = text[..from].rfind('\n').map_or(0, |i| i + 1);
            let end = text[to..].find('\n').map_or(text.len(), |i| to + i);
            (start, end)
        };
        assert!(short_texts().iter().any(|t| {
            (0..=t.len())
                .filter(|&i| t.is_char_boundary(i))
                .any(|i| only_newline(t, i, i) != naive_bounds(t, i, i))
        }));
    }

    /// The documented precondition broken: an offset inside a character.
    #[test]
    #[should_panic(expected = "is not a char boundary")]
    fn a_bound_inside_a_character_is_refused() {
        line_bounds("éx", 1, 1);
    }

    /// `first_not_nfc` cuts before a character of combining class 0 whose NFC quick check is
    /// Yes. That cut is exact only if NFC never joins such a character to the text before it:
    /// its canonical decomposition must start with a character of combining class 0 (else
    /// reordering could move it) whose quick check is not Maybe (else it could compose with
    /// the starter before it). Checked here for every code point of the pinned tables.
    #[test]
    fn nfc_never_joins_a_cut_character_to_the_text_before_it() {
        let quick = |c: char| is_nfc_quick(std::iter::once(c));
        for c in (0..=0x10FFFF).filter_map(char::from_u32) {
            if canonical_combining_class(c) != 0 || quick(c) != IsNormalized::Yes {
                continue;
            }
            let first = std::iter::once(c)
                .nfd()
                .next()
                .expect("a decomposition is not empty");
            assert_eq!(canonical_combining_class(first), 0, "U+{:04X}", c as u32);
            assert_ne!(quick(first), IsNormalized::Maybe, "U+{:04X}", c as u32);
        }
    }

    /// The cost of `first_not_nfc` rests on this: a character composes with the starters of
    /// quick check Maybe at most twice in a row (L V T), so a piece is normalized a bounded
    /// number of times. Checked for every code point of the pinned tables.
    #[test]
    fn starters_compose_at_most_twice_in_a_row() {
        let all = || (0..=0x10FFFF).filter_map(char::from_u32);
        let maybe: Vec<char> = all()
            .filter(|&c| {
                canonical_combining_class(c) == 0
                    && is_nfc_quick(std::iter::once(c)) == IsNormalized::Maybe
            })
            .collect();
        let next = |a: char| maybe.iter().filter_map(move |&m| compose(a, m));
        for a in all() {
            for b in next(a) {
                for c in next(b) {
                    assert_eq!(next(c).next(), None, "U+{:04X}", a as u32);
                }
            }
        }
    }
}
