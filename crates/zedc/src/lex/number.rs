//! Number literals (steps L1.3 and L1.4):
//!
//! ```peg
//! Number  = (Rational | Float | Integer) !XID_CONTINUE
//! Integer = '0x' Hex ('_'? Hex)* | '0o' [0-7] ('_'? [0-7])* | '0b' [01] ('_'? [01])* | Decimal
//! Decimal = [0-9] ('_'? [0-9])*
//! ```
//!
//! A literal keeps its digits, with the `_` removed, and its base: its width is chosen later
//! from its use (sec:domains), so the lexer never rounds or overflows. A number that runs into a
//! character that continues a name is one error over the number and that run, since no other
//! rule reads a token starting with a digit: `200ms`, `1__000`, `1_000_`, `0b102`, `0x`.

use unicode_ident::is_xid_continue;

use super::{Error, ErrorKind, Span, Tok};

/// The end and token of the number starting at byte `pos` of `text`, if one starts there.
pub(super) fn number(text: &str, pos: usize) -> Option<Result<(usize, Tok), Error>> {
    let b = text.as_bytes();
    if !b.get(pos)?.is_ascii_digit() {
        return None;
    }
    let prefixed = |p: u8| b.get(pos) == Some(&b'0') && b.get(pos + 1) == Some(&p);
    let radix = [(b'x', 16), (b'o', 8), (b'b', 2)]
        .into_iter()
        .find(|&(p, r)| prefixed(p) && b.get(pos + 2).is_some_and(|&d| digit(d, r)))
        .map_or(10, |(_, r)| r);
    let start = if radix == 10 { pos } else { pos + 2 };
    let end = digits(b, start, radix);
    match text[end..].chars().next() {
        Some(c) if is_xid_continue(c) => Some(Err(run_on(text, pos, end, radix))),
        _ => {
            let digits = text[start..end].replace('_', "");
            Some(Ok((end, Tok::Int { radix, digits })))
        }
    }
}

fn digit(d: u8, radix: u32) -> bool {
    (d as char).is_digit(radix)
}

/// The end of the digits of base `radix` starting at `pos`, a digit, with single `_` between.
fn digits(b: &[u8], pos: usize, radix: u32) -> usize {
    let mut end = pos + 1;
    loop {
        match b.get(end) {
            Some(&d) if digit(d, radix) => end += 1,
            Some(b'_') if b.get(end + 1).is_some_and(|&d| digit(d, radix)) => end += 2,
            _ => return end,
        }
    }
}

/// The error for a number from `pos` to `end` followed by a character continuing a name.
fn run_on(text: &str, pos: usize, end: usize, radix: u32) -> Error {
    let run = text[end..]
        .char_indices()
        .find(|&(_, c)| !is_xid_continue(c))
        .map_or(text.len(), |(i, _)| end + i);
    let next = text[end..].chars().next().expect("a character follows");
    let base = if radix == 2 { "a binary" } else { "an octal" };
    let why = if next == '_' {
        "`_` goes only between two digits".to_string()
    } else if radix == 10 && end == pos + 1 && text[pos..].starts_with('0') && "xob".contains(next)
    {
        format!("`0{next}` must be followed by a digit")
    } else if radix < 10 && next.is_ascii_digit() {
        format!("{next} is not {base} digit")
    } else {
        format!("a number must not run into a name: `{}`", &text[end..run])
    };
    Error {
        kind: ErrorKind::BadNumber(why),
        span: Span {
            start: pos,
            end: run,
        },
    }
}
