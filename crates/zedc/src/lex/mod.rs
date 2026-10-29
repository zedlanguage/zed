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

/// A byte range of the loaded text.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Span {
    /// The first byte.
    pub start: usize,
    /// One past the last byte.
    pub end: usize,
}

/// A token's kind and the value it carries.
#[derive(Clone, Debug, PartialEq, Eq)]
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
#[derive(Clone, Debug, PartialEq, Eq)]
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
#[derive(Clone, Debug, PartialEq, Eq)]
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
    lex_from(text, 0, &mut Vec::new(), false)
}

/// The tokens of `text`, a fence of the documentation, where `…` outside strings and comments
/// marks elided code and is read as the name `…` (DESIGN.md sec:grammar, "Documentation
/// notation"). No program can write that name.
pub fn lex_fence(text: &str) -> Result<Vec<Token>, Error> {
    lex_from(text, 0, &mut Vec::new(), true)
}

/// The tokens of `text` and its doc comments: a comment that starts with exactly three `/`
/// (`////` is an ordinary comment). Doc comments inside a string's hole are not collected.
pub fn lex_with_docs(text: &str) -> Result<(Vec<Token>, Vec<Doc>), Error> {
    let mut docs = Vec::new();
    let tokens = lex_from(text, 0, &mut docs, false)?;
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

/// The tokens of `text` from byte `pos` to its end, with spans in `text`, and its doc
/// comments pushed onto `docs`; with `elisions`, `…` is a name.
fn lex_from(
    text: &str,
    mut pos: usize,
    docs: &mut Vec<Doc>,
    elisions: bool,
) -> Result<Vec<Token>, Error> {
    let mut out = Vec::new();
    while let Some(c) = text[pos..].chars().next() {
        let start = pos;
        let tok = if matches!(c, ' ' | '\t' | '\r' | '\n') {
            pos += 1;
            None
        } else if let Some(end) = comment::comment(text, pos) {
            pos = end?;
            let body = &text[start..pos];
            if let Some(doc) = body.strip_prefix("///").filter(|d| !d.starts_with('/')) {
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
        } else if let Some(string) = string::string(text, pos) {
            let (end, tok) = string?;
            pos = end;
            Some(tok)
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
        } else if elisions && c == '…' {
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
    Ok(out)
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
