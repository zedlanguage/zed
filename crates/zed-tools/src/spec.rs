//! A specification checkout: the directory holding `DESIGN.md` and `EXAMPLES.md`, and the
//! grammars of the appendix sec:grammar. Its first ```` ```peg ```` fence is the lexical grammar
//! over characters, the second the syntactic grammar over tokens, and the third the
//! documentation notation.

use std::collections::HashMap;

use zedc::parse::Grammar;

use crate::text::{base_name, read_text, strip};

/// One ```` ```zed ```` fence: the document's file name, the line of its opening fence, its
/// section and place in it, its text.
#[derive(Clone, Debug)]
pub struct Fence {
    /// The document's file name.
    pub file: String,
    /// The line of the opening fence, from 1.
    pub line: usize,
    /// The section it is in: the label of the nearest heading above it that has one
    /// (`## (sec:remap_law) …` gives `sec:remap_law`), or else the text of the nearest heading
    /// above it, or else the empty string.
    pub section: String,
    /// Its place among the fences of the document whose section has the same name, from 1.
    pub index: usize,
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

/// The section of each of the lines `at` of `text` (ascending, from 1), and the line's place
/// among those lines in a section of that name, from 1: the names are as [`Fence::section`]
/// says. A line starting with `#` inside a fence is not a heading.
fn sections<'t>(text: &'t str, at: &[usize]) -> Vec<(&'t str, usize)> {
    let mut out = Vec::with_capacity(at.len());
    let mut wanted = at.iter().copied().peekable();
    let mut seen: HashMap<&str, usize> = HashMap::new();
    let (mut labeled, mut heading) = (None, None);
    let mut in_fence = false;
    for (i, l) in text.split('\n').enumerate() {
        if wanted.peek() == Some(&(i + 1)) {
            wanted.next();
            let name = labeled.or(heading).unwrap_or("");
            let index = seen.entry(name).or_insert(0);
            *index += 1;
            out.push((name, *index));
        }
        let s = strip(l);
        if in_fence {
            in_fence = s != "```";
        } else if s.starts_with("```") {
            in_fence = true;
        } else if let Some(title) = l.trim_start_matches('#').strip_prefix(' ')
            && l.starts_with('#')
        {
            let title = strip(title);
            heading = Some(title);
            let label = title
                .strip_prefix('(')
                .and_then(|t| t.split_once(')'))
                .map(|(label, _)| label)
                .filter(|label| label.starts_with("sec:"));
            labeled = label.or(labeled);
        }
    }
    out
}

/// The ```` ```zed ```` fences of the document at `path`.
pub fn zed_fences(path: &str) -> Result<Vec<Fence>, String> {
    zed_fences_in(&read_text(path)?, path)
}

/// The ```` ```zed ```` fences of the document `text` read from `path`.
pub fn zed_fences_in(text: &str, path: &str) -> Result<Vec<Fence>, String> {
    let file = base_name(path);
    let found = fenced(text, "zed", path)?;
    let at: Vec<usize> = found.iter().map(|(line, _)| *line).collect();
    let keys = sections(text, &at);
    let to_fence = |((line, text), (section, index)): ((usize, String), (&str, usize))| Fence {
        file: file.into(),
        line,
        section: section.into(),
        index,
        text,
    };
    Ok(found.into_iter().zip(keys).map(to_fence).collect())
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
