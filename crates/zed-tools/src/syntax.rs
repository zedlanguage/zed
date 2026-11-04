//! Lexing and parsing by the spec's grammars: the lexical grammar over characters, the syntactic
//! grammar over tokens, a string's `${…}` holes as expressions at the same ring.

use zedc::parse::{Expected, Grammar, Input, Kind, Node, Parser, TOP, literal_matches};

use crate::text::{prefix, repr};

/// A token: its kind, its text, its line, and for a string the text of each `${…}` hole.
#[derive(Clone, Debug)]
pub struct Token {
    /// Its kind.
    pub kind: Kind,
    /// Its text.
    pub text: String,
    /// Its line, from 1.
    pub line: usize,
    /// The text of each hole.
    pub holes: Vec<String>,
}

/// The tokens of a text, then `END`.
#[derive(Clone, Debug)]
pub struct Tokens(pub Vec<Token>);

impl Input for Tokens {
    fn len(&self) -> usize {
        self.0.len()
    }

    fn lit(&self, pos: usize, text: &str) -> Option<usize> {
        let t = self.0.get(pos)?;
        literal_matches(t.kind, &t.text, text).then_some(pos + 1)
    }

    fn kind(&self, pos: usize, k: Kind) -> bool {
        self.0.get(pos).is_some_and(|t| t.kind == k)
    }

    fn char_at(&self, _: usize) -> Option<char> {
        None
    }
}

/// A parse tree: its nodes and its root. The rule numbers of the syntactic grammar and of that
/// grammar with the documentation notation are the same, since the notation's rules come after.
#[derive(Clone, Debug)]
pub struct Tree {
    /// The nodes; a node's children come before it.
    pub nodes: Vec<Node>,
    /// The root.
    pub root: usize,
}

impl Tree {
    /// The node `n`.
    pub fn node(&self, n: usize) -> &Node {
        &self.nodes[n]
    }

    /// Every node of rule `rule` under `from`, `from` included, in preorder.
    pub fn find(&self, from: usize, rule: usize) -> Vec<usize> {
        let mut out = Vec::new();
        let mut stack = vec![from];
        while let Some(n) = stack.pop() {
            let node = &self.nodes[n];
            if node.rule == rule {
                out.push(n);
            }
            stack.extend(node.kids.iter().rev());
        }
        out
    }

    /// Every (rule, alternative) in the tree.
    pub fn lines(&self, seen: &mut std::collections::HashSet<(usize, usize)>) {
        let mut stack = vec![self.root];
        while let Some(n) = stack.pop() {
            let node = &self.nodes[n];
            seen.insert((node.rule, node.alt));
            stack.extend(&node.kids);
        }
    }

    /// Whether two trees are the same: rule, alternative, span, inner choices and children.
    pub fn same(&self, other: &Tree) -> bool {
        let mut stack = vec![(self.root, other.root)];
        while let Some((a, b)) = stack.pop() {
            let (x, y) = (&self.nodes[a], &other.nodes[b]);
            let shallow = x.rule == y.rule
                && x.alt == y.alt
                && x.start == y.start
                && x.end == y.end
                && x.branches == y.branches
                && x.kids.len() == y.kids.len();
            if !shallow {
                return false;
            }
            stack.extend(x.kids.iter().copied().zip(y.kids.iter().copied()));
        }
        true
    }
}

/// What `expected` holds, as a report writes it, in code point order.
pub fn expected_strings<'g>(expected: impl IntoIterator<Item = Expected<'g>>) -> Vec<String> {
    let mut out: Vec<String> = expected
        .into_iter()
        .map(|e| match e {
            Expected::Lit(s) => repr(s),
            Expected::Name(n) => n.into(),
            Expected::Class => "class".into(),
        })
        .collect();
    out.sort();
    out
}

/// The token kind of a `Number`'s child rule.
fn number_kind(rule: &str) -> Option<Kind> {
    match rule {
        "Rational" => Some(Kind::Rat),
        "Float" => Some(Kind::Float),
        // A generic integer, `1n`, parses as an integer (DESIGN.md L1.26a).
        "Integer" | "Generic" => Some(Kind::Int),
        _ => None,
    }
}

/// The token kind of a `Token`'s child rule.
fn token_kind(rule: &str) -> Option<Kind> {
    match rule {
        "String" => Some(Kind::Str),
        "AtomLit" => Some(Kind::Atom),
        "AnnotLit" => Some(Kind::Annot),
        "Keyword" => Some(Kind::Keyword),
        "Wildcard" => Some(Kind::Wild),
        "Ident" => Some(Kind::Ident),
        "Operator" => Some(Kind::Op),
        _ => None,
    }
}

/// The tokens of `text`, then `END`; the error is where the lexical grammar stops.
pub fn lex(lexical: &Grammar, text: &str) -> Result<Tokens, String> {
    let cs: Vec<char> = text.chars().collect();
    // newlines[i]: the newlines before code point i.
    let mut newlines = Vec::with_capacity(cs.len() + 1);
    let mut count = 0;
    newlines.push(0);
    for &c in &cs {
        count += usize::from(c == '\n');
        newlines.push(count);
    }
    let slice = |s: usize, e: usize| cs[s..e].iter().collect::<String>();
    let rule = |name: &str| {
        lexical
            .rule(name)
            .ok_or_else(|| format!("the lexical grammar has no rule {name}"))
    };
    let mut p = Parser::new(lexical, TOP, cs.as_slice());
    let (end, root) = match p.rule_node(rule("Source")?, 0, false) {
        Some((end, root)) if end == cs.len() => (end, root),
        _ => {
            let to = (p.far + 20).min(cs.len());
            return Err(format!(
                "lex error at line {}: {}",
                newlines[p.far] + 1,
                repr(&slice(p.far, to))
            ));
        }
    };
    debug_assert_eq!(end, cs.len());
    let tree = Tree {
        root,
        nodes: std::mem::take(&mut p.nodes),
    };
    let names = &lexical.rules;
    let hole_text = lexical.rule("HoleText");
    let hole = rule("Hole")?;
    let mut toks = Vec::new();
    for tok in tree.find(tree.root, rule("Token")?) {
        let sub = tree.node(tree.node(tok).kids[0]);
        let name = names[sub.rule].name.as_str();
        let kind = if name == "Number" {
            number_kind(&names[tree.node(sub.kids[0]).rule].name)
        } else {
            token_kind(name)
        };
        let kind = kind.ok_or_else(|| format!("no token kind for {name}"))?;
        let mut holes = Vec::new();
        if kind == Kind::Str {
            for h in tree.find(tree.node(tok).kids[0], hole) {
                for &c in &tree.node(h).kids {
                    let c = tree.node(c);
                    if Some(c.rule) == hole_text {
                        holes.push(slice(c.start, c.end));
                    }
                }
            }
        }
        toks.push(Token {
            kind,
            text: slice(sub.start, sub.end),
            line: newlines[sub.start] + 1,
            holes,
        });
    }
    toks.push(Token {
        kind: Kind::End,
        text: String::new(),
        line: newlines[cs.len()] + 1,
        holes: Vec::new(),
    });
    Ok(Tokens(toks))
}

/// Matches `start` then `END` at the start of `p`'s input: the end and the node of `start`.
pub fn then_end<'g>(
    g: &'g Grammar,
    p: &mut Parser<'g, Tokens>,
    toks: &Tokens,
    start: &'g str,
) -> Option<(usize, usize)> {
    let Some(r) = g.rule(start) else {
        p.fail(0, Expected::Name(start));
        return None;
    };
    let (end, node) = p.rule_node(r, 0, false)?;
    if toks.kind(end, Kind::End) {
        Some((end + 1, node))
    } else {
        p.fail(end, Expected::Name("END"));
        None
    }
}

/// Where and why a parse failed.
pub fn describe_fail(far: usize, expected: &[String], toks: &Tokens, line_base: usize) -> String {
    let t = &toks.0[far.min(toks.0.len() - 1)];
    format!(
        "line {} near {}; expected {}",
        t.line + line_base,
        repr(&t.text),
        prefix(&expected.join(" "), 200)
    )
}

/// The tree of `toks` from `start` at `ring`, or a description of why there is none. Every hole
/// is parsed as an `Expr` at the same ring, and a failure in a hole is reported in that hole's
/// tokens, at the line of its string.
pub fn parse(
    g: &Grammar,
    lexical: &Grammar,
    toks: &Tokens,
    ring: u32,
    start: &str,
) -> Result<Tree, String> {
    let mut p = Parser::new(g, ring, toks);
    let r = g
        .rule(start)
        .ok_or_else(|| format!("the grammar has no rule {start}"))?;
    let root = match p.rule_node(r, 0, false) {
        Some((end, node)) if end == toks.0.len() => node,
        _ => {
            let expected = expected_strings(p.expected.iter().copied());
            return Err(describe_fail(p.far, &expected, toks, 0));
        }
    };
    for t in &toks.0 {
        for h in &t.holes {
            let ht = lex(lexical, h)?;
            let mut q = Parser::new(g, ring, &ht);
            if then_end(g, &mut q, &ht, "Expr").is_none_or(|(end, _)| end != ht.0.len()) {
                let expected = expected_strings(q.expected.iter().copied());
                return Err(describe_fail(q.far, &expected, &ht, t.line - 1));
            }
        }
    }
    Ok(Tree {
        nodes: p.nodes,
        root,
    })
}
