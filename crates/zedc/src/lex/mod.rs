//! The lexer (DESIGN.md sec:lexical, its lexical grammar; steps L1.2–L1.6): the loaded text
//! (`crate::source`) becomes tokens, each with its span, a byte range of that text.
//!
//! Tokens are read by ordered choice, as the lexical grammar orders them. A character no rule
//! reads is an error at that character, and lexing stops there.

mod name;

use std::fmt;

pub use name::is_single_script;

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
    let mut out = Vec::new();
    let mut pos = 0;
    while let Some(c) = text[pos..].chars().next() {
        let start = pos;
        let tok = if matches!(c, ' ' | '\t' | '\r' | '\n') {
            pos += 1;
            None
        } else if let Some(end) = name::name(text, pos) {
            pos = end;
            let word = &text[start..end];
            if !is_single_script(word.trim_end_matches('\'')) {
                let span = Span { start, end };
                return Err(Error {
                    kind: ErrorKind::MixedScript(word.into()),
                    span,
                });
            }
            Some(Tok::Name(word.into()))
        } else if let Some(end) = name::wildcard(text, pos) {
            pos = end;
            Some(Tok::Wildcard)
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
