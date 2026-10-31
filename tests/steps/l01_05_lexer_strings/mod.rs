//! Step L1.5: string literals, their escapes, `"""` indentation stripping, and `${…}` holes
//! split into parts, each hole lexed into its tokens.

mod holes;
mod scaling;
mod strings;

use zedc::lex::{Part, Tok, lex};

/// The parts of the one string in `text`, a hole shown as `${` its tokens `}`.
fn parts(text: &str) -> Vec<String> {
    let toks = lex(text).unwrap_or_else(|e| panic!("{text:?}: {e}"));
    let [tok] = toks.as_slice() else {
        panic!("{text:?}: {toks:?}")
    };
    let Tok::Str(parts) = &tok.tok else {
        panic!("{text:?}: {tok:?}")
    };
    parts
        .iter()
        .map(|p| match p {
            Part::Text(s) => s.clone(),
            Part::Hole { tokens, .. } => {
                let inner: Vec<String> = tokens.iter().map(|t| format!("{:?}", t.tok)).collect();
                format!("${{{}}}", inner.join(" "))
            }
        })
        .collect()
}

/// The one text part of the string in `text`, or `""` for an empty string.
fn text(text: &str) -> String {
    let p = parts(text);
    assert!(p.len() <= 1, "{text:?}: {p:?}");
    p.into_iter().next().unwrap_or_default()
}
