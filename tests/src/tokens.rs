//! Tokens as text, for golden snapshots: a keyword in `«»`, an integer with its base, a string
//! as its parts.

use zedc::lex::{Part, Tok, Token};

/// `tokens` on one line.
pub fn render(tokens: &[Token]) -> String {
    let out: Vec<String> = tokens.iter().map(|t| one(&t.tok)).collect();
    out.join(" ")
}

/// `tokens` of `text`, one rendered line per line of `text` that starts a token, each after
/// its line number; a token belongs to the line it starts on.
pub fn render_lines(text: &str, tokens: &[Token]) -> String {
    let mut out = Vec::new();
    let mut start = 0;
    for (k, line) in text.split('\n').enumerate() {
        let end = start + line.len() + 1;
        let on: Vec<Token> = tokens
            .iter()
            .filter(|t| (start..end).contains(&t.span.start))
            .cloned()
            .collect();
        if !on.is_empty() {
            out.push(format!("{:>3} | {}", k + 1, render(&on)));
        }
        start = end;
    }
    out.join("\n")
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
