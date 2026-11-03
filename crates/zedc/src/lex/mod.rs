//! The lexer (DESIGN.md sec:lexical, its lexical grammar; steps L1.2–L1.6): the loaded text
//! (`crate::source`) becomes tokens, each with its span, a byte range of that text.
//!
//! Tokens are read by ordered choice, as the lexical grammar orders them. A character no rule
//! reads is an error at that character, and lexing stops there.

mod comment;
mod name;
mod number;
mod punct;
mod string;

use std::fmt;

pub use name::is_single_script;
pub use punct::{KEYWORDS, OPERATORS};
use string::{Holes, Reading, Stop};

/// A byte range of the loaded text.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Span {
    /// The first byte.
    pub start: usize,
    /// One past the last byte.
    pub end: usize,
}

/// A token's kind and the value it carries.
#[derive(Debug, PartialEq, Eq)]
pub enum Tok {
    /// A name, with its trailing `'` when it has one (`x'`).
    Name(String),
    /// The discard wildcard `_`.
    Wildcard,
    /// An integer: its base (2, 8, 10 or 16) and its digits, without `_`.
    Int {
        /// The base.
        radix: u32,
        /// The digits.
        digits: String,
    },
    /// A float, as its decimal text without `_` (`1.5e-3`).
    Float(String),
    /// An exact rational, as its decimal text without `_` and the `r` (`0.1`).
    Rat(String),
    /// A string: its text and its holes, in order, never two text parts in a row.
    Str(Vec<Part>),
    /// An atom `#name`, without the `#`.
    Atom(String),
    /// An annotation `@name`, without the `@`.
    Annot(String),
    /// A keyword.
    Keyword(&'static str),
    /// An operator or punctuation mark.
    Op(&'static str),
}

/// A doc comment: its text after `///` and one space, and its span.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Doc {
    /// The text.
    pub text: String,
    /// The span, from the first `/` to the end of the line.
    pub span: Span,
}

/// A part of a string literal.
pub enum Part {
    /// Text, with its escapes decoded and, in a `"""` string, its indentation stripped.
    Text(String),
    /// A `${…}` hole: the tokens of its expression, and the span of the whole hole.
    Hole {
        /// The tokens between `${` and `}`.
        tokens: Vec<Token>,
        /// The span from `$` to `}`.
        span: Span,
    },
}

/// A token and its span.
#[derive(Debug, PartialEq, Eq)]
pub struct Token {
    /// The kind.
    pub tok: Tok,
    /// The span.
    pub span: Span,
}

/// Why lexing stopped.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ErrorKind {
    /// A character that starts no token.
    Unexpected(char),
    /// A name whose characters are not all of one script (UTS #39, "Highly Restrictive").
    MixedScript(String),
    /// A malformed number, and what is wrong with it.
    BadNumber(String),
    /// A malformed string, and what is wrong with it.
    BadString(String),
    /// A block comment that is not closed.
    BadComment(String),
}

/// A lexical error and its span.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Error {
    /// The kind.
    pub kind: ErrorKind,
    /// The span.
    pub span: Span,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            ErrorKind::Unexpected(c) => {
                write!(f, "no token starts with {c:?} (U+{:04X})", *c as u32)
            }
            ErrorKind::BadNumber(why) => write!(f, "malformed number: {why}"),
            ErrorKind::BadString(why) => write!(f, "malformed string: {why}"),
            ErrorKind::BadComment(why) => write!(f, "{why}"),
            ErrorKind::MixedScript(name) => {
                write!(
                    f,
                    "the name {name:?} mixes scripts: {}",
                    name::scripts_of(name)
                )
            }
        }
    }
}

/// The tokens of `text`, a loaded source text.
pub fn lex(text: &str) -> Result<Vec<Token>, Error> {
    lex_from(text, 0, &mut Vec::new(), false, &mut Holes::new(text))
}

/// The tokens of `text`, a fence of the documentation, where `…` outside strings and comments
/// marks elided code and is read as the name `…` (DESIGN.md sec:grammar, "Documentation
/// notation"). No program can write that name.
pub fn lex_fence(text: &str) -> Result<Vec<Token>, Error> {
    lex_from(text, 0, &mut Vec::new(), true, &mut Holes::new(text))
}

/// The tokens of `text` and its doc comments: a comment that starts with exactly three `/`
/// (`////` is an ordinary comment). Doc comments inside a string's hole are not collected.
pub fn lex_with_docs(text: &str) -> Result<(Vec<Token>, Vec<Doc>), Error> {
    let mut docs = Vec::new();
    let tokens = lex_from(text, 0, &mut docs, false, &mut Holes::new(text))?;
    Ok((tokens, docs))
}

/// The comments of `text`, lexed as `tokens`, in order: those between tokens, since a comment
/// in a string's hole is part of the string's token.
pub fn comments(text: &str, tokens: &[Token]) -> Vec<Span> {
    let mut out = Vec::new();
    let mut pos = 0;
    let end = Span {
        start: text.len(),
        end: text.len(),
    };
    for next in tokens.iter().map(|t| t.span).chain([end]) {
        while pos < next.start {
            match comment::comment(text, pos) {
                Some(Ok(e)) => {
                    out.push(Span { start: pos, end: e });
                    pos = e;
                }
                _ => pos += text[pos..].chars().next().map_or(1, char::len_utf8),
            }
        }
        pos = next.end;
    }
    out
}

/// A string whose hole is being lexed: the text and tokens around the string, and the hole.
struct Level<'t> {
    text: &'t str,
    out: Vec<Token>,
    string: Reading,
    open: usize,
}

/// The tokens of `text` from byte `pos` to its end, with spans in `text`, and its doc
/// comments pushed onto `docs`; with `elisions`, `…` is a name. A hole is lexed as text of its
/// own ending at its `}`, with neither doc comments nor elisions; holes nest, so the strings
/// around the current text are on a stack.
fn lex_from<'t>(
    mut text: &'t str,
    mut pos: usize,
    docs: &mut Vec<Doc>,
    elisions: bool,
    holes: &mut Holes,
) -> Result<Vec<Token>, Error> {
    let mut out = Vec::new();
    let mut levels: Vec<Level<'t>> = Vec::new();
    let mut reading: Option<Reading> = None;
    loop {
        if let Some(mut string) = reading.take() {
            match string.next(text, holes)? {
                Stop::Closed(end) => {
                    let start = string.start();
                    out.push(Token {
                        tok: string.finish(text)?,
                        span: Span { start, end },
                    });
                    pos = end;
                }
                Stop::Hole(open, end) => {
                    levels.push(Level {
                        text,
                        out: std::mem::take(&mut out),
                        string,
                        open,
                    });
                    text = &text[..end];
                    pos = open + 2;
                }
            }
            continue;
        }
        let Some(c) = text[pos..].chars().next() else {
            let Some(mut level) = levels.pop() else {
                return Ok(out);
            };
            let tokens = std::mem::replace(&mut out, level.out);
            level.string.hole(tokens, level.open, text.len());
            text = level.text;
            reading = Some(level.string);
            continue;
        };
        let start = pos;
        let top = levels.is_empty();
        let tok = if matches!(c, ' ' | '\t' | '\r' | '\n') {
            pos += 1;
            None
        } else if let Some(end) = comment::comment(text, pos) {
            pos = end?;
            let body = &text[start..pos];
            if let Some(doc) = body
                .strip_prefix("///")
                .filter(|d| top && !d.starts_with('/'))
            {
                docs.push(Doc {
                    text: doc.strip_prefix(' ').unwrap_or(doc).into(),
                    span: Span { start, end: pos },
                });
            }
            None
        } else if let Some(number) = number::number(text, pos) {
            let (end, tok) = number?;
            pos = end;
            Some(tok)
        } else if c == '"' {
            reading = Some(Reading::new(text, pos));
            None
        } else if let Some(end) = matches!(c, '#' | '@')
            .then(|| name::name(text, pos + 1))
            .flatten()
        {
            pos = end;
            let word = checked(text, start + 1, end)?;
            Some(if c == '#' {
                Tok::Atom(word)
            } else {
                Tok::Annot(word)
            })
        } else if let Some(end) = name::name(text, pos) {
            if let Some(k) = punct::keyword(text[start..end].trim_end_matches('\'')) {
                pos = start + k.len();
                Some(Tok::Keyword(k))
            } else {
                pos = end;
                Some(Tok::Name(checked(text, start, end)?))
            }
        } else if let Some(end) = name::wildcard(text, pos) {
            pos = end;
            Some(Tok::Wildcard)
        } else if elisions && top && c == '…' {
            pos += c.len_utf8();
            Some(Tok::Name(c.into()))
        } else if let Some(op) = punct::operator(text, pos) {
            pos += op.len();
            Some(Tok::Op(op))
        } else {
            let span = Span {
                start,
                end: start + c.len_utf8(),
            };
            return Err(Error {
                kind: ErrorKind::Unexpected(c),
                span,
            });
        };
        if let Some(tok) = tok {
            out.push(Token {
                tok,
                span: Span { start, end: pos },
            });
        }
    }
}

/// The name from `start` to `end` of `text`, if its characters are of one script.
fn checked(text: &str, start: usize, end: usize) -> Result<String, Error> {
    let word = &text[start..end];
    if is_single_script(word.trim_end_matches('\'')) {
        Ok(word.into())
    } else {
        Err(Error {
            kind: ErrorKind::MixedScript(word.into()),
            span: Span { start, end },
        })
    }
}

impl Drop for Part {
    /// Frees nested holes from a stack: each level of a string's holes would be a level of the
    /// thread's stack otherwise.
    fn drop(&mut self) {
        let mut stack = Vec::new();
        take_tokens(self, &mut stack);
        while let Some(tokens) = stack.pop() {
            for token in tokens {
                if let Tok::Str(mut parts) = token.tok {
                    for part in &mut parts {
                        take_tokens(part, &mut stack);
                    }
                }
            }
        }
    }
}

/// Moves the tokens of `part`, a hole, onto `stack`.
fn take_tokens(part: &mut Part, stack: &mut Vec<Vec<Token>>) {
    if let Part::Hole { tokens, .. } = part {
        stack.push(std::mem::take(tokens));
    }
}

impl fmt::Debug for Part {
    /// The output of `#[derive(Debug)]`, from a stack, since holes nest.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        enum Show<'a> {
            Put(&'static str),
            Span(Span),
            Part(&'a Part),
            Tokens(&'a [Token]),
            Parts(&'a [Part]),
        }
        let mut stack = vec![Show::Part(self)];
        while let Some(show) = stack.pop() {
            match show {
                Show::Put(s) => f.write_str(s)?,
                Show::Span(s) => write!(f, "{s:?}")?,
                Show::Part(Part::Text(s)) => write!(f, "Text({s:?})")?,
                Show::Part(Part::Hole { tokens, span }) => {
                    f.write_str("Hole { tokens: [")?;
                    stack.extend([Show::Put(" }"), Show::Span(*span)]);
                    stack.extend([Show::Put("], span: "), Show::Tokens(tokens)]);
                }
                Show::Tokens([]) | Show::Parts([]) => {}
                Show::Tokens([first, rest @ ..]) => {
                    if !rest.is_empty() {
                        stack.extend([Show::Tokens(rest), Show::Put(", ")]);
                    }
                    let Tok::Str(parts) = &first.tok else {
                        write!(f, "{first:?}")?;
                        continue;
                    };
                    f.write_str("Token { tok: Str([")?;
                    stack.extend([Show::Put(" }"), Show::Span(first.span)]);
                    stack.extend([Show::Put("]), span: "), Show::Parts(parts)]);
                }
                Show::Parts([first, rest @ ..]) => {
                    if !rest.is_empty() {
                        stack.extend([Show::Parts(rest), Show::Put(", ")]);
                    }
                    stack.push(Show::Part(first));
                }
            }
        }
        Ok(())
    }
}

impl PartialEq for Part {
    /// Compares nested holes from a stack.
    fn eq(&self, other: &Part) -> bool {
        let mut stack = vec![(self, other)];
        while let Some(pair) = stack.pop() {
            let (a, b, x, y) = match pair {
                (Part::Text(a), Part::Text(b)) if a == b => continue,
                (Part::Hole { tokens: a, span: x }, Part::Hole { tokens: b, span: y }) => {
                    (a, b, x, y)
                }
                (Part::Text(_) | Part::Hole { .. }, Part::Text(_) | Part::Hole { .. }) => {
                    return false;
                }
            };
            if x != y || a.len() != b.len() {
                return false;
            }
            for (a, b) in a.iter().zip(b) {
                if a.span != b.span {
                    return false;
                }
                match (&a.tok, &b.tok) {
                    (Tok::Str(p), Tok::Str(q)) if p.len() == q.len() => {
                        stack.extend(p.iter().zip(q));
                    }
                    // At most one is a string, or their lengths differ: this does not nest.
                    (p, q) => {
                        if p != q {
                            return false;
                        }
                    }
                }
            }
        }
        true
    }
}

impl Eq for Part {}
