//! Step L1.6: atoms, annotations, comments and doc comments, every operator, and the 36
//! keywords: the lexical grammar whole.

mod program;
mod words;

use zedc::lex::{Part, Tok, Token};

/// `tokens` as text: a keyword in `«»`, a string as its parts.
fn render(tokens: &[Token]) -> String {
    let out: Vec<String> = tokens.iter().map(|t| one(&t.tok)).collect();
    out.join(" ")
}

fn one(tok: &Tok) -> String {
    match tok {
        Tok::Name(n) => n.clone(),
        Tok::Wildcard => "_".into(),
        Tok::Keyword(k) => format!("«{k}»"),
        Tok::Op(o) => (*o).into(),
        Tok::Atom(a) => format!("#{a}"),
        Tok::Annot(a) => format!("@{a}"),
        Tok::Int { radix, digits } => format!("{digits}₍{radix}₎"),
        Tok::Float(f) => format!("{f}f"),
        Tok::Rat(r) => format!("{r}r"),
        Tok::Str(parts) => {
            let inner: Vec<String> = parts
                .iter()
                .map(|p| match p {
                    Part::Text(s) => format!("{s:?}"),
                    Part::Hole { tokens, .. } => format!("${{{}}}", render(tokens)),
                })
                .collect();
            format!("str[{}]", inner.join(" "))
        }
    }
}
