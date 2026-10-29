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

use unicode_normalization::char::canonical_combining_class;
use unicode_normalization::{UnicodeNormalization, is_nfc};

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
        let Span { start, end } = self.span();
        let (line, col) = line_col(bytes, start);
        match self {
            Reject::NotUtf8 { .. } => {
                let hex: Vec<String> = bytes[start..end]
                    .iter()
                    .map(|b| format!("{b:02X}"))
                    .collect();
                format!("{line}:{col}: {self}: {}", hex.join(" "))
            }
            _ => format!("{line}:{col}: {self}"),
        }
    }
}

impl fmt::Display for Reject {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Reject::NotUtf8 { .. } => write!(f, "not UTF-8"),
            Reject::ByteOrderMark { .. } => write!(f, "the file starts with a byte order mark"),
            Reject::NotNfc { nfc, .. } => {
                write!(
                    f,
                    "not in Unicode Normalization Form C; write {}",
                    scalars(nfc)
                )
            }
        }
    }
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
    Ok(text.replace("\r\n", "\n").replace('\r', "\n"))
}

/// The first sequence of `text` that NFC changes, for a `text` that is not NFC. The text is cut
/// before each character of combining class 0. NFC changes text only within one piece or
/// across the boundary of two adjacent pieces (two such characters that compose, as Hangul
/// jamo do), so the span is the first piece that is not NFC, or the first pair of pieces that is
/// not, whichever ends first.
fn first_not_nfc(text: &str) -> Span {
    let mut cuts: Vec<usize> = text
        .char_indices()
        .filter(|&(i, c)| i == 0 || canonical_combining_class(c) == 0)
        .map(|(i, _)| i)
        .collect();
    cuts.push(text.len());
    for i in 0..cuts.len() - 1 {
        if !is_nfc(&text[cuts[i]..cuts[i + 1]]) {
            return Span {
                start: cuts[i],
                end: cuts[i + 1],
            };
        }
        if i > 0 && !is_nfc(&text[cuts[i - 1]..cuts[i + 1]]) {
            return Span {
                start: cuts[i - 1],
                end: cuts[i + 1],
            };
        }
    }
    unreachable!("text that is not NFC has a piece or a pair of pieces that is not")
}

/// The 1-based line and column of byte `offset` of `bytes`, the column counted in Unicode
/// scalars. `\r\n`, `\r` and `\n` each end a line. The bytes before `offset` must be UTF-8,
/// as they are for the start of every rejection's span.
pub fn line_col(bytes: &[u8], offset: usize) -> (usize, usize) {
    let before = std::str::from_utf8(&bytes[..offset]).expect("the bytes before a span are UTF-8");
    let (mut line, mut col) = (1, 1);
    let mut chars = before.chars().peekable();
    while let Some(c) = chars.next() {
        match c {
            '\r' if chars.peek() == Some(&'\n') => {}
            '\r' | '\n' => (line, col) = (line + 1, 1),
            _ => col += 1,
        }
    }
    (line, col)
}
