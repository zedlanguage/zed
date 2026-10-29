//! String literals (step L1.5):
//!
//! ```peg
//! String   = '"""' (!'"""' Char)* '"""' | '"' (!'"' !'\n' Char)* '"'
//! Char     = Escape | Hole | !('\\' | '${') ANY
//! Escape   = '\\' ([ntr0\\"$] | 'u{' Hex+ '}')
//! Hole     = '${' HoleText '}'
//! HoleText = (String | Comment | '{' HoleText '}' | !'}' ANY)*
//! ```
//!
//! A string is its parts: decoded text, and holes, each lexed into the tokens of its
//! expression. A `"` string has no line break, its holes included, so a `//` comment in a hole
//! of a one-line string is an error rather than a comment that swallows the `}`.
//!
//! A `"""` string whose opening `"""` ends its line and whose closing `"""` begins its line
//! after spaces and tabs only is stripped of that indentation: the line breaks after the
//! opening and before the closing delimiter are dropped, each line loses the indentation, a line
//! of only spaces and tabs becomes empty, and a line indented less is an error. A line that
//! begins inside a hole is not a line of the string. Escapes are decoded after stripping, so
//! `\n` and `\t` are never stripped. Any other `"""` string is kept as written.

use super::{Error, ErrorKind, Part, Span, Tok, comment, lex_from};

/// A part before decoding: a range of literal source text, or a hole.
enum Raw {
    Lit(usize, usize),
    Hole(Vec<super::Token>, Span),
}

/// The end and token of the string starting at byte `pos` of `text`, if one starts there.
pub(super) fn string(text: &str, pos: usize) -> Option<Result<(usize, Tok), Error>> {
    text[pos..].starts_with('"').then(|| {
        let (end, parts) = scan(text, pos, true)?;
        Ok((end, Tok::Str(parts)))
    })
}

/// Scans the string at `pos`, returning its end and, when `lex_holes`, its parts.
fn scan(text: &str, pos: usize, lex_holes: bool) -> Result<(usize, Vec<Part>), Error> {
    let triple = text[pos..].starts_with("\"\"\"");
    let close = if triple { "\"\"\"" } else { "\"" };
    let content = pos + close.len();
    let mut raw = Vec::new();
    let (mut i, mut lit) = (content, content);
    loop {
        let rest = &text[i..];
        if rest.starts_with(close) {
            raw.push(Raw::Lit(lit, i));
            break;
        }
        match rest.chars().next() {
            None => return Err(bad(pos, i, "the string is not closed")),
            Some('\n') if !triple => {
                return Err(bad(
                    pos,
                    i,
                    "a `\"` string ends on its line; a string over several lines is written `\"\"\"`",
                ));
            }
            Some('\\') => i = escape(text, i)?,
            Some('$') if rest.starts_with("${") => {
                raw.push(Raw::Lit(lit, i));
                let end = hole_end(text, i, !triple)?;
                let tokens = if lex_holes {
                    lex_from(&text[..end], i + 2)?
                } else {
                    Vec::new()
                };
                raw.push(Raw::Hole(
                    tokens,
                    Span {
                        start: i,
                        end: end + 1,
                    },
                ));
                i = end + 1;
                lit = i;
            }
            Some(c) => i += c.len_utf8(),
        }
    }
    if !lex_holes {
        return Ok((i + close.len(), Vec::new()));
    }
    let cuts = if triple {
        strip(text, content, &raw)?
    } else {
        Vec::new()
    };
    let parts = raw
        .into_iter()
        .filter_map(|r| match r {
            Raw::Lit(start, end) => Some(decode(text, start, end, &cuts))
                .filter(|s| !s.is_empty())
                .map(Part::Text),
            Raw::Hole(tokens, span) => Some(Part::Hole { tokens, span }),
        })
        .collect();
    Ok((i + close.len(), parts))
}

/// The end of the escape at `i`, a `\`.
fn escape(text: &str, i: usize) -> Result<usize, Error> {
    let rest = &text[i + 1..];
    match rest.chars().next() {
        Some('n' | 't' | 'r' | '0' | '\\' | '"' | '$') => Ok(i + 2),
        Some('u') => {
            let digits = rest[1..]
                .strip_prefix('{')
                .map(|h| h.bytes().take_while(u8::is_ascii_hexdigit).count());
            let close = i + 3 + digits.unwrap_or(0);
            match digits {
                Some(n) if n > 0 && text[close..].starts_with('}') => {
                    let value = u32::from_str_radix(&text[i + 3..close], 16).ok();
                    match value.and_then(char::from_u32) {
                        Some(_) => Ok(close + 1),
                        None => Err(bad(
                            i,
                            close + 1,
                            "this is no Unicode scalar value: a code point is at most 10FFFF and not a surrogate (D800 to DFFF)",
                        )),
                    }
                }
                _ => Err(bad(i, i + 2, "a code point is written `\\u{1F600}`")),
            }
        }
        other => Err(bad(
            i,
            i + 1 + other.map_or(0, char::len_utf8),
            "no such escape; the escapes are \\n \\t \\r \\0 \\\\ \\\" \\$ \\u{…}",
        )),
    }
}

/// The position of the `}` closing the hole whose `${` is at `open`.
fn hole_end(text: &str, open: usize, one_line: bool) -> Result<usize, Error> {
    let mut depth = 0;
    let mut i = open + 2;
    loop {
        let rest = &text[i..];
        let next = match rest.chars().next() {
            None => return Err(bad(open, i, "the `${` hole is not closed")),
            Some('}') if depth == 0 => return Ok(i),
            Some('}') => {
                depth -= 1;
                i + 1
            }
            Some('{') => {
                depth += 1;
                i + 1
            }
            Some('"') => scan(text, i, false)?.0,
            Some('/') if one_line && rest.starts_with("//") => {
                return Err(bad(
                    i,
                    text[i..].find('\n').map_or(text.len(), |k| i + k),
                    "a `//` comment in a hole of a `\"` string runs to the end of the line, past the `}`; write `/* … */`",
                ));
            }
            Some('/') if comment::comment(text, i).is_some() => {
                comment::comment(text, i).expect("a comment starts here")?
            }
            Some(c) => i + c.len_utf8(),
        };
        if one_line && text[i..next].contains('\n') {
            return Err(bad(open, i, "a hole in a `\"` string closes on its line"));
        }
        i = next;
    }
}

/// The ranges `strip` removes from the literal text of a `"""` string whose text starts at
/// `content`, as the module comment describes.
fn strip(text: &str, content: usize, raw: &[Raw]) -> Result<Vec<(usize, usize)>, Error> {
    let lits: Vec<(usize, usize)> = raw
        .iter()
        .filter_map(|r| match *r {
            Raw::Lit(start, end) => Some((start, end)),
            Raw::Hole(..) => None,
        })
        .collect();
    let (first, last) = (lits[0], lits[lits.len() - 1]);
    if first.0 != content || !text[content..].starts_with('\n') {
        return Ok(Vec::new());
    }
    let Some(nl) = text[last.0..last.1].rfind('\n').map(|k| last.0 + k) else {
        return Ok(Vec::new());
    };
    let indent = &text[nl + 1..last.1];
    if !indent.bytes().all(|b| b == b' ' || b == b'\t') {
        return Ok(Vec::new());
    }
    let mut cuts = vec![(content, content + 1), (nl, last.1)];
    // Each line's start and the end of the literal text it is in.
    let mut lines = Vec::new();
    for &(start, end) in &lits {
        for (k, _) in text[start..end].match_indices('\n') {
            if start + k < nl {
                lines.push((start + k + 1, end));
            }
        }
    }
    for (p, end) in lines {
        let stop = text[p..end].find('\n').map_or(end, |k| p + k);
        let line = &text[p..stop];
        if line.starts_with(indent) {
            cuts.push((p, p + indent.len()));
        } else if line.bytes().all(|b| b == b' ' || b == b'\t') && stop < end {
            cuts.push((p, stop));
        } else {
            let ws = line.len() - line.trim_start_matches([' ', '\t']).len();
            return Err(bad(
                p,
                p + ws,
                "this line is indented less than the closing `\"\"\"`",
            ));
        }
    }
    Ok(cuts)
}

/// The literal text from `start` to `end`, less the `cuts`, with its escapes decoded.
fn decode(text: &str, start: usize, end: usize, cuts: &[(usize, usize)]) -> String {
    let mut chars = text[start..end]
        .char_indices()
        .filter(|&(k, _)| !cuts.iter().any(|&(a, b)| a <= start + k && start + k < b))
        .map(|(_, c)| c);
    let mut out = String::new();
    while let Some(c) = chars.next() {
        if c != '\\' {
            out.push(c);
            continue;
        }
        out.push(match chars.next().expect("an escape was checked") {
            'n' => '\n',
            't' => '\t',
            'r' => '\r',
            '0' => '\0',
            'u' => {
                let hex: String = chars.by_ref().skip(1).take_while(|&c| c != '}').collect();
                char::from_u32(u32::from_str_radix(&hex, 16).expect("checked")).expect("checked")
            }
            other => other,
        });
    }
    out
}

fn bad(start: usize, end: usize, why: &str) -> Error {
    Error {
        kind: ErrorKind::BadString(why.into()),
        span: Span { start, end },
    }
}
