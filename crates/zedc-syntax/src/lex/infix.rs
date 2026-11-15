//! Infix calls (DESIGN.md sec:lexical, sec:power; author, Q36):
//!
//! ```peg
//! InfixName = '~' Name '~'
//! ```
//!
//! `~f~` is one token, a tilde, a name and a tilde with no space inside; `a ~f~ b` is the call
//! `f(a, b)`. A `~` starts nothing else, so every `~` is read here, and one that starts no
//! infix call is an error with its own text: a space inside (`~ f~`, `~f ~`), no closing `~`
//! (`~f`), or a lone `~`.

use super::name::{self, Word};
use super::name_or_error;
use super::token::{Error, ErrorKind, Span};

/// The end of the infix call token starting with the `~` at byte `pos` of `text`, and the name
/// between its tildes.
///
/// A qualified name, `~geometry.plus~`, is read as one token holding the dotted name, though
/// the grammar's `Name` holds no `.`: the syntax tree then rejects it with the call
/// `geometry.plus(p, v)` as the repair, written from both operands, which the lexer cannot see.
pub(super) fn infix(text: &str, pos: usize) -> Result<(usize, String), Error> {
    let at = pos + 1;
    let Some(w) = name::word(text, at) else {
        return Err(spaced_open(text, pos).unwrap_or_else(|| lone(pos)));
    };
    let mut end = name_or_error(text, at, w)?;
    // Complexity tradeoff: each `.name` part is read once, so the token is read in O(its
    // length); a name with no `.` costs one look at the byte after it.
    while text[end..].starts_with('.') {
        match name::word(text, end + 1) {
            Some(Word::Name(e)) => end = e,
            Some(w @ Word::Foreign(_)) => end = name_or_error(text, end + 1, w)?,
            None => break,
        }
    }
    let written = &text[at..end];
    if text[end..].starts_with('~') {
        return Ok((end + 1, written.to_string()));
    }
    let blanks = spaces(text, end);
    let span = Span { start: pos, end };
    if blanks > end && text[blanks..].starts_with('~') {
        return Err(bad(
            format!(
                "`{}` is no infix call: a space stands before the closing `~`. Try `~{written}~` \
                 instead.",
                &text[pos..=blanks]
            ),
            Span {
                start: pos,
                end: blanks + 1,
            },
        ));
    }
    Err(bad(
        format!(
            "`~{written}` is no infix call: the name must be closed by a `~` right after it, as \
             in `a ~{written}~ b`. For the bitwise complement, write `bitNot({written})`."
        ),
        span,
    ))
}

/// The end of the run of spaces and tabs from byte `pos` of `text`.
fn spaces(text: &str, pos: usize) -> usize {
    pos + text[pos..]
        .bytes()
        .position(|b| b != b' ' && b != b'\t')
        .unwrap_or(text.len() - pos)
}

/// The error for `~ f~`, a `~`, spaces, a name and a `~`, if `text` holds one from `pos`.
fn spaced_open(text: &str, pos: usize) -> Option<Error> {
    let at = spaces(text, pos + 1);
    if at == pos + 1 {
        return None;
    }
    let Some(Word::Name(end)) = name::word(text, at) else {
        return None;
    };
    let close = spaces(text, end);
    if !text[close..].starts_with('~') {
        return None;
    }
    let written = &text[at..end];
    Some(bad(
        format!(
            "`{}` is no infix call: a space stands after the opening `~`. Try `~{written}~` \
             instead.",
            &text[pos..=close]
        ),
        Span {
            start: pos,
            end: close + 1,
        },
    ))
}

/// The error for a `~` that starts no infix call.
fn lone(pos: usize) -> Error {
    bad(
        "`~` stands only around the name of a function written between its two arguments, as in \
         `p ~plus~ v`, and means nothing alone. Remove it, or write the call as `~name~`."
            .into(),
        Span {
            start: pos,
            end: pos + 1,
        },
    )
}

fn bad(why: String, span: Span) -> Error {
    Error {
        kind: ErrorKind::BadInfix(why),
        span,
    }
}
