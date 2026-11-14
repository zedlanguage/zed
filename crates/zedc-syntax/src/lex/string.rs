//! String literals (step L1.5):
//!
//! ```peg
//! String        = '"""' (!'"""' Char)* '"""' | '"' (!'"' !'\n' Char1)* '"'
//! String1       = '"""' (!'"""' !'\n' Char1)* '"""' | '"' (!'"' !'\n' Char1)* '"'
//! Char          = Escape | Hole | !('\\' | '${') ANY
//! Char1         = Escape | &('${' HoleText1 '}') Hole | !('\\' | '${') ANY
//! Escape        = '\\' ([ntr0\\"$] | 'u{' Hex+ '}')
//! Hole          = '${' HoleText '}'
//! HoleText      = (String | Comment | '{' HoleText '}' | !'}' ANY)*
//! HoleText1     = (String1 | '//' (!'\n' ANY)* | BlockComment1 | '{' HoleText1 '}' | !'}' !'\n' ANY)*
//! BlockComment1 = '/*' (BlockComment1 | !'*/' !'\n' ANY)* '*/'
//! ```
//!
//! A string is its parts: decoded text, and holes, each lexed into the tokens of its
//! expression. A `"` string has no line break, its holes included: a line break in such a hole,
//! in a block comment or a `"""` string in it, or in a hole of that `"""` string, is an error,
//! and so is a `//` comment in any of these holes, which runs to the end of the line and so past
//! the `}`. Each of these has its own message.
//!
//! A `"""` string whose opening `"""` ends its line and whose closing `"""` begins its line
//! after spaces and tabs only is stripped of that indentation: the line breaks after the
//! opening and before the closing delimiter are dropped, each line loses the indentation, a line
//! of only spaces and tabs becomes empty, and a line indented less is an error. A line that
//! begins inside a hole is not a line of the string. Escapes are decoded after stripping, so
//! `\n` and `\t` are never stripped. Any other `"""` string is kept as written.

use std::collections::HashMap;
use std::sync::Arc;

use super::comment;
use super::token::{Error, ErrorKind, Part, Span, Tok, Token, may_not_show};

/// A part before decoding: a range of literal source text, or a hole.
enum Raw {
    Lit(usize, usize),
    Hole(Vec<Token>, Span),
}

/// What is known of the holes of one text, so that a hole nested in others is scanned once,
/// not once for each hole around it: the end of each hole found, by the position of its `${`,
/// and the positions of the text's line breaks.
// Complexity tradeoff (COMPLEXITY.md F15, F63): the naive lexer scans a hole for its `}`
// again from each hole around it and searches each nested string's text for a line break at
// each level, O(N · depth); and a pass over the line breaks per comment or inner string
// costs O(B) each. Here each hole's end is found once and kept by the position of its `${`,
// and a line break is found by binary search in the B breaks, O(log B). Memory: one map
// entry per hole and one position per line break of the text.
pub(super) struct Holes {
    ends: HashMap<usize, usize>,
    breaks: Vec<usize>,
}

impl Holes {
    pub(super) fn new(text: &str) -> Holes {
        Holes {
            ends: HashMap::new(),
            breaks: text.match_indices('\n').map(|(k, _)| k).collect(),
        }
    }

    /// The position of the first line break in the text from `from` to `to`, if it holds one.
    fn first_break(&self, from: usize, to: usize) -> Option<usize> {
        let k = self.breaks.partition_point(|&b| b < from);
        self.breaks.get(k).copied().filter(|&b| b < to)
    }
}

/// A string being scanned: where it starts, and how far the scan has got.
struct Scan {
    pos: usize,
    triple: bool,
    i: usize,
}

impl Scan {
    fn new(text: &str, pos: usize) -> Scan {
        let triple = text[pos..].starts_with("\"\"\"");
        Scan {
            pos,
            triple,
            i: pos + Scan::close(triple).len(),
        }
    }

    fn close(triple: bool) -> &'static str {
        if triple { "\"\"\"" } else { "\"" }
    }

    /// Scans on to the next hole, returning the position of its `${`, or to the closing
    /// delimiter, returning `None`.
    fn next_hole(&mut self, text: &str) -> Result<Option<usize>, Error> {
        let close = Scan::close(self.triple);
        loop {
            let i = self.i;
            let rest = &text[i..];
            if rest.starts_with(close) {
                return Ok(None);
            }
            match rest.chars().next() {
                None => {
                    let close = if self.triple { "\"\"\"" } else { "\"" };
                    let why = format!(
                        "this string is not closed before the end of the file. Write the closing \
                         `{close}` where its text ends."
                    );
                    return Err(bad(self.pos, i, &why));
                }
                Some('\n') if !self.triple => {
                    return Err(bad(
                        self.pos,
                        i,
                        "this `\"` string reaches the end of its line without its closing `\"`, \
                         and a `\"` string ends on its line. Close it on this line, or write a \
                         string over several lines as `\"\"\"`.",
                    ));
                }
                Some('\\') => self.i = escape(text, i)?,
                Some('$') if rest.starts_with("${") => return Ok(Some(i)),
                Some(c) => self.i += c.len_utf8(),
            }
        }
    }

    /// The end of the string, once `next_hole` has found its closing delimiter.
    fn end(&self) -> usize {
        self.i + Scan::close(self.triple).len()
    }
}

/// The string the lexer is reading: its scan, and its parts so far.
pub(super) struct Reading {
    scan: Scan,
    lit: usize,
    raw: Vec<Raw>,
}

/// Where a [`Reading`] stopped.
pub(super) enum Stop {
    /// At the end of the string.
    Closed(usize),
    /// At a hole, whose `${` and `}` are at these positions.
    Hole(usize, usize),
}

impl Reading {
    /// The string starting at byte `pos` of `text`, a `"`.
    pub(super) fn new(text: &str, pos: usize) -> Reading {
        let scan = Scan::new(text, pos);
        let lit = scan.i;
        Reading {
            scan,
            lit,
            raw: Vec::new(),
        }
    }

    /// Where the string starts.
    pub(super) fn start(&self) -> usize {
        self.scan.pos
    }

    /// Reads on to the next hole or the end of the string.
    pub(super) fn next(&mut self, text: &str, holes: &mut Holes) -> Result<Stop, Error> {
        match self.scan.next_hole(text)? {
            Some(open) => {
                self.raw.push(Raw::Lit(self.lit, open));
                let end = hole_end(text, open, !self.scan.triple, holes)?;
                Ok(Stop::Hole(open, end))
            }
            None => {
                self.raw.push(Raw::Lit(self.lit, self.scan.i));
                Ok(Stop::Closed(self.scan.end()))
            }
        }
    }

    /// Records the hole `next` stopped at, as `tokens`.
    pub(super) fn hole(&mut self, tokens: Vec<Token>, open: usize, end: usize) {
        let span = Span {
            start: open,
            end: end + 1,
        };
        self.raw.push(Raw::Hole(tokens, span));
        self.scan.i = end + 1;
        self.lit = end + 1;
    }

    /// The token of the string, once `next` has returned [`Stop::Closed`].
    pub(super) fn finish(self, text: &str) -> Result<Tok, Error> {
        let content = self.scan.pos + Scan::close(self.scan.triple).len();
        let cuts = if self.scan.triple {
            strip(text, content, &self.raw)?
        } else {
            Vec::new()
        };
        let parts = self
            .raw
            .into_iter()
            .filter_map(|r| match r {
                Raw::Lit(start, end) => Some(decode(text, start, end, &cuts))
                    .filter(|s| !s.is_empty())
                    .map(|s| Part::Text(Arc::new(s))),
                Raw::Hole(tokens, span) => Some(Part::Hole { tokens, span }),
            })
            .collect();
        Ok(Tok::Str(parts))
    }
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
                            &format!(
                                "`{}` names no Unicode character: a code point is at most 10FFFF \
                                 and is not a surrogate, D800 to DFFF. Write the code point of \
                                 the character meant.",
                                &text[i..close + 1]
                            ),
                        )),
                    }
                }
                _ => Err(bad(
                    i,
                    i + 2,
                    "`\\u` starts a code point, written as hexadecimal digits in braces, as \
                     `\\u{1F600}`, and no braced digits follow it. Write the code point in \
                     braces, or `\\\\u` for a backslash followed by `u`.",
                )),
            }
        }
        other => Err(bad(
            i,
            i + 1 + other.map_or(0, char::len_utf8),
            &match other {
                // A character that may not show on screen, such as a line break or a tab, is
                // named by its code point and never printed (DESIGN.md sec:lexical), as the
                // lexer's other messages do ([`may_not_show`]).
                Some(c) if may_not_show(c) => format!(
                    "`\\` followed by the character U+{:04X}, which may not show on screen, is \
                     no escape. The escapes are `\\n`, `\\t`, `\\r`, `\\0`, `\\\\`, `\\\"`, `\\$` \
                     and `\\u{{…}}`. Write `\\\\` for a backslash itself.",
                    c as u32
                ),
                Some(c) => format!(
                    "`\\{c}` is no escape. The escapes are `\\n`, `\\t`, `\\r`, `\\0`, `\\\\`, \
                     `\\\"`, `\\$` and `\\u{{…}}`. Write `\\\\` for a backslash itself."
                ),
                None => "the file ends after a `\\`, which starts an escape in a string. Write \
                         the escape, or `\\\\` for a backslash itself, and close the string."
                    .to_string(),
            },
        )),
    }
}

/// A level of what `hole_end` is inside.
enum Inside {
    /// A hole: its `${`, whether it closes on its line, and the `{` open in it.
    Hole {
        open: usize,
        one_line: bool,
        depth: usize,
    },
    /// A string in a hole, and whether that hole closes on its line: if it does, so do the
    /// string and the holes in it (`String1`, `Char1`, `HoleText1`).
    Str { scan: Scan, one_line: bool },
}

/// The position of the `}` closing the hole whose `${` is at `open`. Each hole found on the way
/// is recorded in `holes`.
fn hole_end(text: &str, open: usize, one_line: bool, holes: &mut Holes) -> Result<usize, Error> {
    if let Some(&end) = holes.ends.get(&open) {
        return Ok(end);
    }
    let mut stack = vec![Inside::Hole {
        open,
        one_line,
        depth: 0,
    }];
    // The position in the innermost hole.
    let mut i = open + 2;
    loop {
        match stack.last_mut().expect("the outermost hole returns") {
            Inside::Str { scan, one_line } => match scan.next_hole(text)? {
                Some(open) => match holes.ends.get(&open) {
                    Some(&end) => scan.i = end + 1,
                    None => {
                        let one_line = *one_line || !scan.triple;
                        stack.push(Inside::Hole {
                            open,
                            one_line,
                            depth: 0,
                        });
                        i = open + 2;
                    }
                },
                None => {
                    let (start, end, one_line) = (scan.pos, scan.end(), *one_line);
                    stack.pop();
                    // A `"` string stopped at its own line break, so this one is a `"""`.
                    if one_line && let Some(nl) = holes.first_break(start, end) {
                        return Err(bad(
                            start,
                            nl,
                            "this `\"\"\"` string is inside a `${…}` hole of a `\"` string, and \
                             everything in that hole ends on the line of the `\"` string, which \
                             is one line. Close the `\"\"\"` string on this line, or make the \
                             outer string a `\"\"\"` string.",
                        ));
                    }
                    i = end;
                }
            },
            Inside::Hole {
                open,
                one_line,
                depth,
            } => {
                let rest = &text[i..];
                let next = match rest.chars().next() {
                    None => {
                        return Err(bad(
                            *open,
                            i,
                            "this `${` opens a hole in a string, and the file ends before the \
                             `}` that closes it. Write `}` after the expression in the hole, or \
                             `\\${` for the text `${` itself.",
                        ));
                    }
                    Some('}') if *depth == 0 => {
                        holes.ends.insert(*open, i);
                        stack.pop();
                        match stack.last_mut() {
                            None => return Ok(i),
                            Some(Inside::Str { scan, .. }) => scan.i = i + 1,
                            Some(Inside::Hole { .. }) => {
                                unreachable!("a hole here is inside a string")
                            }
                        }
                        continue;
                    }
                    Some('}') => {
                        *depth -= 1;
                        i + 1
                    }
                    Some('{') => {
                        *depth += 1;
                        i + 1
                    }
                    Some('"') => {
                        let one_line = *one_line;
                        stack.push(Inside::Str {
                            scan: Scan::new(text, i),
                            one_line,
                        });
                        continue;
                    }
                    Some('/') if *one_line && rest.starts_with("//") => {
                        return Err(bad(
                            i,
                            text[i..].find('\n').map_or(text.len(), |k| i + k),
                            "this `//` comment is inside a `${…}` hole of a `\"` string, and a \
                             `//` comment runs to the end of the line, past the `}` that closes \
                             the hole. Write the comment as `/* … */`, or move it out of the \
                             string.",
                        ));
                    }
                    Some('/') if let Some(end) = comment::comment(text, i) => {
                        let end = end?;
                        if *one_line && let Some(nl) = holes.first_break(i, end) {
                            return Err(bad(
                                i,
                                nl,
                                "this `/* … */` comment is inside a `${…}` hole of a `\"` \
                                 string, and everything in that hole ends on the line of the \
                                 `\"` string, which is one line. Close the comment on this line, \
                                 or move it out of the string.",
                            ));
                        }
                        end
                    }
                    Some('\n') if *one_line => {
                        return Err(bad(
                            *open,
                            i,
                            "this `${` hole of a `\"` string reaches the end of the line without \
                             its closing `}`, and a `\"` string, with its holes, is one line. \
                             Write the `}` on this line, or make the string a `\"\"\"` string, \
                             which may run over several lines.",
                        ));
                    }
                    Some(c) => i + c.len_utf8(),
                };
                i = next;
            }
        }
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
        // A line of only spaces and tabs becomes empty, whether it is shorter than the
        // indentation, as long, or longer; one that a hole ends (`stop == end`) is not such a
        // line, since the line goes on in the hole.
        if line.bytes().all(|b| b == b' ' || b == b'\t') && stop < end {
            cuts.push((p, stop));
        } else if line.starts_with(indent) {
            cuts.push((p, p + indent.len()));
        } else {
            let ws = line.len() - line.trim_start_matches([' ', '\t']).len();
            return Err(bad(
                p,
                p + ws,
                "this line of a `\"\"\"` string is indented less than the closing `\"\"\"`, \
                 whose indentation is removed from every line of the string. Indent this line \
                 at least as far as the closing `\"\"\"`, or move the closing `\"\"\"` left.",
            ));
        }
    }
    // The cuts do not overlap; in order, `decode` passes each once.
    cuts.sort_unstable();
    Ok(cuts)
}

/// The literal text from `start` to `end`, less the `cuts`, which are sorted and do not
/// overlap, with its escapes decoded.
// Complexity tradeoff (COMPLEXITY.md F14): the naive decoder asks every cut at every
// character (`cuts.iter().any`), O(chars · lines); with the cuts sorted once and not
// overlapping, each piece finds its first cut by binary search and passes the cuts in step
// with its characters, O(chars + pieces · log lines). Precondition: the cuts are sorted and
// disjoint, as the caller makes them.
fn decode(text: &str, start: usize, end: usize, cuts: &[(usize, usize)]) -> String {
    // The first cut not ending before each character, found by search and then advanced.
    let mut next = cuts.partition_point(|&(_, b)| b <= start);
    let mut chars = text[start..end]
        .char_indices()
        .filter(|&(k, _)| {
            let p = start + k;
            while next < cuts.len() && cuts[next].1 <= p {
                next += 1;
            }
            !(next < cuts.len() && cuts[next].0 <= p)
        })
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
