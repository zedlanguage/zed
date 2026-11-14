//! The lexer (DESIGN.md sec:lexical, its lexical grammar; steps L1.2–L1.6): the loaded text
//! (`zedc_base::source`) becomes tokens, each with its span, a byte range of that text.
//!
//! Tokens are read by ordered choice, as the lexical grammar orders them. A character no rule
//! reads is an error at that character, and lexing stops there.

mod comment;
mod name;
mod number;
mod punct;
mod string;
mod token;

pub use name::name as name_end;
pub use name::{ascii_name, is_name_continue, is_name_start, is_word_char};
pub use punct::{KEYWORDS, OPERATORS};
use string::{Holes, Reading, Stop};
pub use token::{
    Digits, Doc, Error, ErrorKind, Part, Span, Tok, Token, UNICODE_VERSION, is_blank,
    is_default_ignorable, is_format, may_not_show, unread_literal,
};

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
/// (`////` is an ordinary comment), in text order, those in a string's hole included: a hole
/// holds code, and a doc comment there is reported when it documents no declaration (DESIGN.md
/// sec:lexical, the comment row).
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
/// own ending at its `}`, with its doc comments but no elisions; holes nest, so the strings
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
        } else if c == '"' {
            reading = Some(Reading::new(text, pos));
            None
        } else if let Some(w) = matches!(c, '#' | '@')
            .then(|| name::word(text, pos + 1))
            .flatten()
        {
            pos = name_or_error(text, start, w)?;
            let word = text[start + 1..pos].to_string();
            Some(if c == '#' {
                Tok::Atom(word)
            } else {
                Tok::Annot(word)
            })
        } else if let Some(w) = name::word(text, pos) {
            let end = name_or_error(text, start, w)?;
            if let Some(k) = punct::keyword(text[start..end].trim_end_matches('\'')) {
                pos = start + k.len();
                Some(Tok::Keyword(k))
            } else {
                pos = end;
                Some(Tok::Name(text[start..end].into()))
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

/// The end of the name `w` read from `start` of `text`, or the error for a word that is a name
/// but for a character beyond ASCII, which offers an ASCII name for it.
fn name_or_error(text: &str, start: usize, w: name::Word) -> Result<usize, Error> {
    match w {
        name::Word::Name(end) => Ok(end),
        name::Word::Foreign(end) => {
            let mut e = Error {
                kind: ErrorKind::NonAsciiName {
                    word: text[start..end].into(),
                    repair: None,
                },
                span: Span { start, end },
            };
            e.avoid_names(text, &|_| false);
            Err(e)
        }
    }
}
