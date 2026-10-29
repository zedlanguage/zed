//! Parse trees printed as the bracketing cases of `tools/grammar/cases.txt` print them.

use zedc::lex::Token;
use zedc::parse::Tree;

/// The s-expression of `tree`, parsed from `tokens` of `text`: a node is its tokens, with
/// each child bracketed in its place, and a node with one child spanning all of it is that
/// child; a node with no child is its tokens' texts.
pub fn sx(text: &str, tokens: &[Token], tree: &Tree) -> String {
    let mut words: Vec<&str> = tokens
        .iter()
        .map(|t| &text[t.span.start..t.span.end])
        .collect();
    words.push("");
    node(tree.root, tree, &words)
}

fn node(n: usize, tree: &Tree, words: &[&str]) -> String {
    let at = &tree.nodes[n];
    if at.kids.is_empty() {
        return words[at.start..at.end].join(" ");
    }
    if let [k] = at.kids[..]
        && (tree.nodes[k].start, tree.nodes[k].end) == (at.start, at.end)
    {
        return node(k, tree, words);
    }
    let mut parts: Vec<String> = Vec::new();
    let mut pos = at.start;
    for &k in &at.kids {
        parts.extend(
            words[pos..tree.nodes[k].start]
                .iter()
                .map(|w| w.to_string()),
        );
        parts.push(node(k, tree, words));
        pos = tree.nodes[k].end;
    }
    parts.extend(words[pos..at.end].iter().map(|w| w.to_string()));
    format!("({})", parts.join(" "))
}
