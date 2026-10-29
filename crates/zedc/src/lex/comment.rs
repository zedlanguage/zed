//! Comments:
//!
//! ```peg
//! Comment      = '//' (!'\n' ANY)* | BlockComment
//! BlockComment = '/*' (BlockComment | !'*/' ANY)* '*/'
//! ```
//!
//! Block comments nest, so commenting out a region that already holds one works.

use super::{Error, ErrorKind, Span};

/// The end of the comment starting at byte `pos` of `text`, if one starts there.
pub(super) fn comment(text: &str, pos: usize) -> Option<Result<usize, Error>> {
    let rest = &text[pos..];
    if rest.starts_with("//") {
        return Some(Ok(rest.find('\n').map_or(text.len(), |k| pos + k)));
    }
    if !rest.starts_with("/*") {
        return None;
    }
    let mut depth = 0;
    let mut i = pos;
    while i < text.len() {
        if text[i..].starts_with("/*") {
            depth += 1;
            i += 2;
        } else if text[i..].starts_with("*/") {
            depth -= 1;
            i += 2;
            if depth == 0 {
                return Some(Ok(i));
            }
        } else {
            i += text[i..].chars().next().map_or(1, char::len_utf8);
        }
    }
    Some(Err(Error {
        kind: ErrorKind::BadComment(format!(
            "the block comment is not closed ({depth} `*/` missing)"
        )),
        span: Span {
            start: pos,
            end: text.len(),
        },
    }))
}
