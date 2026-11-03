//! Doc comments after parsing (DESIGN.md sec:grammar, comments): a block of `///` lines
//! attaches to the declaration that follows it, a block that attaches to none is reported, and
//! a `[name]` link in one must resolve.

use std::collections::HashSet;

use crate::ast::Error;
use crate::lex::{Doc, Span, Token};
use crate::resolve::{Resolution, is_prelude_name};

/// The errors of the doc comments `docs` of `text`, lexed as `tokens` and resolved as `res`,
/// in text order. A block is the doc comments that the same token follows; it attaches when
/// that token starts a declaration. A link `[name]`, outside a backtick span and not the text
/// of a Markdown link `[text](url)`, resolves when `name` is bound anywhere in the unit or is a
/// prelude word or type. The cost is `O(D log T + C)` for `D` doc comments of `C` characters
/// over `T` tokens.
pub fn check(text: &str, tokens: &[Token], docs: &[Doc], res: &Resolution) -> Vec<Error> {
    let names: HashSet<&str> = res.binders.iter().map(|b| b.name.as_str()).collect();
    let mut out = Vec::new();
    let mut block: Option<(usize, Span)> = None;
    for d in docs {
        let next = tokens.partition_point(|t| t.span.start < d.span.end);
        match &mut block {
            Some((n, span)) if *n == next => span.end = d.span.end,
            _ => {
                if let Some((n, span)) = block {
                    attach(tokens, n, span, res, &mut out);
                }
                block = Some((next, d.span));
            }
        }
        links(text, d.span, &names, &mut out);
    }
    if let Some((n, span)) = block {
        attach(tokens, n, span, res, &mut out);
    }
    out.sort_by_key(|e| e.span);
    out
}

/// The error of the block `span` when `tokens[next]`, the token after it, starts no
/// declaration.
fn attach(tokens: &[Token], next: usize, span: Span, res: &Resolution, out: &mut Vec<Error>) {
    let message = match tokens.get(next) {
        Some(t) if res.decls.contains(&t.span.start) => return,
        Some(_) => {
            "this doc comment documents no declaration; a `///` block comes right before a \
             binding, a function or another declaration"
        }
        None => "this doc comment documents no declaration; it is at the end of the unit",
    };
    out.push(Error {
        span,
        message: message.into(),
        notes: Vec::new(),
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
                        span: Span {
                            start: span.start + i,
                            end: span.start + name_end + 1,
                        },
                        message: format!(
                            "the doc link `[{name}]` names nothing: no binding or function of \
                             this unit and no prelude word or type is `{name}`"
                        ),
                        notes: Vec::new(),
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
