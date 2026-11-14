//! Doc comments after parsing (DESIGN.md sec:grammar, comments): a block of `///` lines
//! attaches to the declaration that follows it, a block that attaches to none is reported, and
//! a `[name]` link in one must resolve.

use std::collections::HashSet;

use crate::resolve::{Resolution, is_prelude_name};
use zedc_syntax::ast::Error;
use zedc_syntax::lex::{Doc, Part, Span, Tok, Token};

/// The errors of the doc comments `docs` of `text`, lexed as `tokens` and resolved as `res`,
/// in text order. A block is the doc comments that the same token follows, in the same hole of
/// a string or outside every hole; it attaches when that token starts a declaration, and a
/// block at the end of a hole attaches to none. A link `[name]`, outside a backtick span and
/// not the text of a Markdown link `[text](url)`, resolves when `name` is bound anywhere in the
/// unit or is a prelude word or type. The cost is `O(T + D log T + C)` for `D` doc comments of
/// `C` characters over `T` tokens, the tokens of holes counted.
pub fn check(text: &str, tokens: &[Token], docs: &[Doc], res: &Resolution) -> Vec<Error> {
    if docs.is_empty() {
        return Vec::new();
    }
    let names: HashSet<&str> = res.binders.iter().map(|b| b.name.as_str()).collect();
    let places = places(tokens);
    let mut out = Vec::new();
    let mut block: Option<(usize, Span)> = None;
    for d in docs {
        let next = places.partition_point(|&p| p < d.span.end);
        match &mut block {
            Some((n, span)) if *n == next => span.end = d.span.end,
            _ => {
                if let Some((n, span)) = block {
                    attach(&places, n, span, res, &mut out);
                }
                block = Some((next, d.span));
            }
        }
        links(text, d.span, &names, &mut out);
    }
    if let Some((n, span)) = block {
        attach(&places, n, span, res, &mut out);
    }
    out.sort_by_key(|e| e.span);
    out
}

/// What can follow a doc comment, in text order: the start of every token, those in the holes
/// of strings included, and the position of each hole's closing `}`, which ends the hole's code
/// and starts no declaration. A string's token comes before the tokens of its holes, so the
/// positions increase.
// Complexity tradeoff: the tokens form a tree (a string token holds its holes' tokens), walked
// once with an explicit stack, since holes nest as deep as the input: O(T) time and O(T)
// memory for the positions, after which each doc comment finds what follows it by binary
// search, O(log T). The naive form, a search of each string's parts for the hole around each
// doc comment, costs O(parts) per doc comment, O(D · P) in all. A tree needs no visited set:
// each token is reached once, from its one parent.
fn places(tokens: &[Token]) -> Vec<usize> {
    /// A level of the walk: tokens, with the position of the `}` that ends them when they are a
    /// hole's, or the parts of a string.
    enum Level<'a> {
        Tokens(std::slice::Iter<'a, Token>, Option<usize>),
        Parts(std::slice::Iter<'a, Part>),
    }
    let mut out = Vec::with_capacity(tokens.len());
    let mut stack = vec![Level::Tokens(tokens.iter(), None)];
    while let Some(level) = stack.last_mut() {
        match level {
            Level::Tokens(it, close) => match it.next() {
                Some(t) => {
                    out.push(t.span.start);
                    if let Tok::Str(parts) = &t.tok {
                        stack.push(Level::Parts(parts.iter()));
                    }
                }
                None => {
                    out.extend(*close);
                    stack.pop();
                }
            },
            Level::Parts(it) => match it.next() {
                Some(Part::Hole { tokens, span }) => {
                    stack.push(Level::Tokens(tokens.iter(), Some(span.end - 1)));
                }
                Some(Part::Text(_)) => {}
                None => {
                    stack.pop();
                }
            },
        }
    }
    out
}

/// The error of the block `span` when `places[next]`, what follows it, starts no declaration.
fn attach(places: &[usize], next: usize, span: Span, res: &Resolution, out: &mut Vec<Error>) {
    let message = match places.get(next) {
        Some(p) if res.decls.contains(p) => return,
        Some(_) => {
            "this doc comment documents no declaration; a `///` block comes right before a \
             binding, a function or another declaration"
        }
        None => "this doc comment documents no declaration; it is at the end of the unit",
    };
    out.push(Error {
        menu: String::new(),
        span,
        message: message.into(),
        notes: Vec::new(),
        row: None,
    });
}

/// The errors of the links of the doc comment at `span` that name nothing in `names` or the
/// prelude.
fn links(text: &str, span: Span, names: &HashSet<&str>, out: &mut Vec<Error>) {
    let line = &text[span.start..span.end];
    let bytes = line.as_bytes();
    let mut code = false;
    let mut i = 3;
    while i < bytes.len() {
        match bytes[i] {
            b'`' => code = !code,
            b'[' if !code => {
                let name_end = i
                    + 1
                    + line[i + 1..]
                        .find(|c: char| !is_name_char(c))
                        .unwrap_or(line.len() - i - 1);
                let name = &line[i + 1..name_end];
                let closed = bytes.get(name_end) == Some(&b']');
                let markdown = bytes.get(name_end + 1) == Some(&b'(');
                let first = name.chars().next();
                if closed
                    && !markdown
                    && first.is_some_and(|c| c.is_alphabetic() || c == '_')
                    && !names.contains(name)
                    && !is_prelude_name(name)
                {
                    out.push(Error {
                        menu: String::new(),
                        span: Span {
                            start: span.start + i,
                            end: span.start + name_end + 1,
                        },
                        message: format!("The doc link `[{name}]` names nothing in scope."),
                        notes: Vec::new(),
                        row: None,
                    });
                }
                i = name_end;
                continue;
            }
            _ => {}
        }
        i += 1;
    }
}

fn is_name_char(c: char) -> bool {
    c.is_alphanumeric() || c == '_'
}
