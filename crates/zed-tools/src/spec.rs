//! A specification checkout: the directory holding `DESIGN.md` and `EXAMPLES.md`, and the
//! grammars of the appendix sec:grammar. Its first ```` ```peg ```` fence is the lexical grammar
//! over characters, the second the syntactic grammar over tokens, and the third the
//! documentation notation.

use zedc::parse::Grammar;

use crate::text::{base_name, read_text, strip};

/// One ```` ```zed ```` fence: the document's file name, the line of its opening fence, its
/// text.
#[derive(Clone, Debug)]
pub struct Fence {
    /// The document's file name.
    pub file: String,
    /// The line of the opening fence, from 1.
    pub line: usize,
    /// The text between the fence lines.
    pub text: String,
}

/// The fences of kind `kind` in the document `text` read from `path`: the line of each, and its
/// text.
fn fenced(text: &str, kind: &str, path: &str) -> Result<Vec<(usize, String)>, String> {
    let open = format!("```{kind}");
    let mut out = Vec::new();
    let mut lines = text.split('\n').enumerate();
    while let Some((i, l)) = lines.next() {
        if strip(l) != open {
            continue;
        }
        let mut body = Vec::new();
        loop {
            match lines.next() {
                Some((_, l)) if strip(l) == "```" => break,
                Some((_, l)) => body.push(l),
                None => return Err(format!("{path}:{}: the fence is not closed", i + 1)),
            }
        }
        out.push((i + 1, body.join("\n")));
    }
    Ok(out)
}

/// The fences of kind `kind` in the document at `path`: the text of each.
pub fn fence_texts(path: &str, kind: &str) -> Result<Vec<String>, String> {
    let found = fenced(&read_text(path)?, kind, path)?;
    Ok(found.into_iter().map(|(_, t)| t).collect())
}

/// The ```` ```zed ```` fences of the document at `path`.
pub fn zed_fences(path: &str) -> Result<Vec<Fence>, String> {
    let file = base_name(path);
    let found = fenced(&read_text(path)?, "zed", path)?;
    let to_fence = |(line, text)| Fence {
        file: file.into(),
        line,
        text,
    };
    Ok(found.into_iter().map(to_fence).collect())
}

/// A specification checkout and its grammars.
#[derive(Clone, Debug)]
pub struct Spec {
    /// The checkout's directory.
    pub root: String,
    /// The path of `DESIGN.md`.
    pub design: String,
    /// The text of the lexical grammar.
    pub lex_text: String,
    /// The text of the syntactic grammar.
    pub syn_text: String,
    /// The text of the documentation notation.
    pub doc_text: String,
    /// The lexical grammar.
    pub lexical: Grammar,
    /// The syntactic grammar.
    pub syntactic: Grammar,
    /// The syntactic grammar and the documentation notation together. Its first rules are the
    /// syntactic grammar's, in the same order, so a node of either grammar is named by this one.
    pub all: Grammar,
}

impl Spec {
    /// Reads the grammars of the checkout at `root`.
    pub fn open(root: &str) -> Result<Spec, String> {
        let design = format!("{root}/DESIGN.md");
        let mut fences = fence_texts(&design, "peg")?.into_iter();
        let (Some(lex_text), Some(syn_text), Some(doc_text)) =
            (fences.next(), fences.next(), fences.next())
        else {
            return Err(format!("{design} has fewer than three peg fences"));
        };
        Ok(Spec {
            root: root.into(),
            lexical: Grammar::read_open(&[&lex_text])?,
            syntactic: Grammar::read_open(&[&syn_text])?,
            all: Grammar::read_open(&[&syn_text, &doc_text])?,
            lex_text,
            syn_text,
            doc_text,
            design,
        })
    }

    /// The fences of `DESIGN.md`, then of `EXAMPLES.md`.
    pub fn all_fences(&self) -> Result<Vec<Fence>, String> {
        let mut out = zed_fences(&self.design)?;
        out.extend(zed_fences(&format!("{}/EXAMPLES.md", self.root))?);
        Ok(out)
    }
}
