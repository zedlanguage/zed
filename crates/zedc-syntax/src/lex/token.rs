//! The lexer's output and its errors: tokens, their spans and kinds, the parts of a string
//! literal, and why lexing stopped. The lexer (`super`) and its readers of comments, numbers
//! and strings all make these, so they are kept in a file below all of them.

use std::fmt;
use std::sync::Arc;

use zed_kernel::num::{TooLarge, bytes_of};

use super::name;

/// A number literal's digits, without `_`: one copy of the source text, made in memory asked
/// for first, and shared by the token and the syntax tree, which never copy it again.
pub type Digits = Arc<String>;

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
        digits: Digits,
    },
    /// A decimal literal (`1.5e-3`, `0.1f64`).
    Float {
        /// Its decimal text, without `_` and the suffix.
        digits: Digits,
        /// Whether it is written with the suffix `f64`, which forces that format.
        forced: bool,
    },
    /// An exact rational, as its decimal text without `_` and the `r` (`0.1`).
    Rat(Digits),
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
    /// Text, with its escapes decoded and, in a `"""` string, its indentation stripped, shared
    /// with the syntax tree ([`crate::ast::StrPart::Text`]), which copies none of it.
    Text(Arc<String>),
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
    /// A number literal whose digits the system refused the memory to copy.
    Unread(TooLarge),
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
            ErrorKind::Unexpected(c) => f.write_str(&unexpected(*c)),
            ErrorKind::BadNumber(why) | ErrorKind::BadString(why) | ErrorKind::BadComment(why) => {
                write!(f, "{why}")
            }
            ErrorKind::Unread(r) => write!(f, "{}", unread_literal(r)),
            ErrorKind::MixedScript(name) => write!(
                f,
                "the name `{name}` mixes letters of the scripts {}, and a name is written in one \
                 script, so that no name looks like another and is a different one. Write it in \
                 one script: a letter that looks Latin may be, for instance, a Cyrillic or Greek \
                 letter of the same shape.",
                name::scripts_of(name)
            ),
        }
    }
}

/// The message for the character `c`, which starts no token where it stands. `#` and `@`
/// start an atom and an annotation only before a name, and `'` ends a name, so each of those
/// has its own text.
fn unexpected(c: char) -> String {
    match c {
        '#' => "`#` starts an atom, and the atom's name must follow it at once, as in `#none`. \
                Write the name right after the `#`, with no space between."
            .into(),
        '@' => "`@` starts an annotation, and the annotation's name must follow it at once, as \
                in `@test`. Write the name right after the `@`, with no space between."
            .into(),
        '\'' => "`'` stands only right after a name, once, as in `x'`, and starts nothing by \
                 itself. Remove this `'`, or write it right after the name it marks."
            .into(),
        _ => {
            let code = c as u32;
            let quoted = match c {
                '`' => "`` ` ``".to_string(),
                _ => format!("`{c}`"),
            };
            let text = match c {
                '\\' => "`\"\\\\\"`".to_string(),
                '`' => "`` \"`\" ``".to_string(),
                _ if c.is_control() || c.is_whitespace() => format!("`\"\\u{{{code:X}}}\"`"),
                _ => format!("`\"{c}\"`"),
            };
            format!(
                "the character {quoted} (U+{code:04X}) starts no name, number, operator or \
                 other part of a Zed program. Remove it, or, if it is meant as text, write it \
                 inside a string, as {text}."
            )
        }
    }
}

/// The message for a numeric literal whose digits the system refused the memory to read. It
/// does not quote the literal, which may be millions of digits long.
pub fn unread_literal(r: &TooLarge) -> String {
    format!(
        "this literal has so many digits that the system refused the {} bytes of memory zedc \
         asked for to read it. A literal has no size limit, but this machine cannot hold this \
         one's value. Write it with fewer digits.",
        bytes_of(&r.bits)
    )
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
