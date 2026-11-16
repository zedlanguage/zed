//! Comments:
//!
//! ```peg
//! Comment      = '//' (!'\n' TextChar)* | BlockComment
//! BlockComment = '/*' (BlockComment | !'*/' TextChar)* '*/'
//! TextChar     = !BidiControl ANY
//! ```
//!
//! Block comments nest, so commenting out a region that already holds one works. A comment
//! holds no `Bidi_Control` character (DESIGN.md sec:lexical): one is an error at the character,
//! whose repair is the comment without it.

use super::token::{Error, ErrorKind, Span, first_bidi_control, is_bidi_control};

/// The end of the comment starting at byte `pos` of `text`, if one starts there; or the error
/// at the first `Bidi_Control` character in it. O(n) for a comment of n bytes.
pub(super) fn comment(text: &str, pos: usize) -> Option<Result<usize, Error>> {
    let end = match end(text, pos)? {
        Ok(end) => end,
        Err(e) => return Some(Err(e)),
    };
    let body = &text[pos..end];
    let Some((k, c)) = first_bidi_control(body) else {
        return Some(Ok(end));
    };
    // The repair is quoted on one line, as a headline quotes it: a comment over several lines,
    // or one holding a backtick, which would end the quotation, gets none.
    let repaired: String = body.chars().filter(|&c| !is_bidi_control(c)).collect();
    let repair = Some(repaired).filter(|r| !r.contains(['\n', '`']));
    Some(Err(Error {
        kind: ErrorKind::TextDirection {
            c,
            in_string: false,
            repair,
        },
        span: Span {
            start: pos + k,
            end: pos + k + c.len_utf8(),
        },
    }))
}

/// The end of the comment starting at byte `pos` of `text`, if one starts there, whatever
/// characters it holds.
fn end(text: &str, pos: usize) -> Option<Result<usize, Error>> {
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
        kind: ErrorKind::BadComment(match depth {
            1 => "this block comment, opened with `/*`, is not closed before the end of the file. \
                  Write `*/` where the comment should end."
                .to_string(),
            _ => format!(
                "this block comment, opened with `/*`, is not closed before the end of the file: \
                 block comments nest, so each `/*` inside it needs its own `*/`, and {depth} \
                 `*/` are missing. Write the missing `*/`, the last where the comment should end."
            ),
        }),
        span: Span {
            start: pos,
            end: text.len(),
        },
    }))
}
