//! The parser (step L1.8): tokens become a tree of the rules of DESIGN.md sec:grammar.
//!
//! The parser runs that grammar itself, copied into `zed/grammar/`, as a packrat parser: each
//! rule tries its alternatives in order and memoizes its result at each token. So the
//! precedence ladder is the grammar's, rung for rung, and its trees are the trees
//! `tools/grammar/check.py` builds. A parse is at a ring: only the alternatives of that layer
//! and below are tried. Each node records its alternative, so a node of a later layer than the
//! program's is found later, by the elaborator, not here.
//!
//! A literal in the grammar matches a keyword, an operator or a name with its text, so the
//! positional words `where` and `sep` are names the grammar matches by their text.

mod grammar;

use std::collections::{BTreeSet, HashMap};
use std::fmt;
use std::sync::OnceLock;

pub use grammar::{Expr, Grammar, Kind, Rule};

use crate::lex::{Part, Span, Tok, Token};

/// The highest layer, and the ring at which every alternative is tried.
pub const TOP: u32 = 29;

/// The grammar of sec:grammar: its syntactic grammar and its documentation notation.
pub fn grammar() -> &'static Grammar {
    static G: OnceLock<Grammar> = OnceLock::new();
    G.get_or_init(|| {
        Grammar::read(&[
            include_str!("../../../../zed/grammar/syntax.peg"),
            include_str!("../../../../zed/grammar/notation.peg"),
        ])
        .expect("the copied grammar reads")
    })
}

/// A node: the rule it matched, by index, the alternative, and the tokens it spans.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Node {
    /// The rule.
    pub rule: usize,
    /// The alternative, counted from 0 among all of the rule's alternatives.
    pub alt: usize,
    /// The first token.
    pub start: usize,
    /// One past the last token.
    pub end: usize,
    /// The child nodes, in order.
    pub kids: Vec<usize>,
}

/// A parse tree: its nodes, the root's index, and the trees of the string holes in its tokens.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Tree {
    /// The nodes; a node's children come before it.
    pub nodes: Vec<Node>,
    /// The root.
    pub root: usize,
    /// The tree of each `${…}` hole, in the order of the tokens, each parsed as an `Expr`.
    pub holes: Vec<Tree>,
}

impl Tree {
    /// The rule name of node `n`.
    pub fn name(&self, n: usize) -> &'static str {
        &grammar().rules[self.nodes[n].rule].name
    }

    /// The layer of the alternative node `n` matched.
    pub fn layer(&self, n: usize) -> u32 {
        let node = &self.nodes[n];
        grammar().rules[node.rule].alts[node.alt].1
    }
}

/// Why a parse failed: the furthest token any alternative reached, and what it expected there.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Error {
    /// The span of that token (empty at the end of the text).
    pub span: Span,
    /// The literals (quoted) and token kinds expected there, sorted.
    pub expected: Vec<String>,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "expected {}", self.expected.join(" or "))
    }
}

/// Parses `tokens`, lexed from `text`, as the rule `start` at `ring`, to the end of the tokens.
pub fn parse(text: &str, tokens: &[Token], start: &str, ring: u32) -> Result<Tree, Error> {
    let end = Span {
        start: text.len(),
        end: text.len(),
    };
    parse_to(text, tokens, start, ring, end)
}

/// Parses as `parse` does; `end` is the span reported for an error at the end of `tokens`.
fn parse_to(
    text: &str,
    tokens: &[Token],
    start: &str,
    ring: u32,
    end: Span,
) -> Result<Tree, Error> {
    let start = grammar()
        .rule(start)
        .unwrap_or_else(|| panic!("no rule {start}"));
    let mut toks: Vec<(Kind, &str)> = tokens
        .iter()
        .map(|t| (kind(&t.tok), &text[t.span.start..t.span.end]))
        .collect();
    toks.push((Kind::End, ""));
    let span = |i: usize| tokens.get(i).map_or(end, |t| t.span);
    let mut p = Parser {
        g: grammar(),
        ring,
        toks: &toks,
        memo: HashMap::new(),
        nodes: Vec::new(),
        far: 0,
        expected: BTreeSet::new(),
    };
    let mut kids = Vec::new();
    let matched = match p.rule(start, 0, false, &mut kids) {
        Some(e) if e == toks.len() => Some(e),
        Some(e) if e + 1 == toks.len() => Some(e),
        Some(e) => {
            p.fail(e, "END".into());
            None
        }
        None => None,
    };
    if matched.is_none() {
        return Err(Error {
            span: span(p.far),
            expected: p.expected.into_iter().collect(),
        });
    }
    let mut holes = Vec::new();
    for t in tokens {
        if let Tok::Str(parts) = &t.tok {
            for part in parts {
                if let Part::Hole { tokens, span } = part {
                    let close = Span {
                        start: span.end - 1,
                        end: span.end,
                    };
                    holes.push(parse_to(text, tokens, "Expr", ring, close)?);
                }
            }
        }
    }
    Ok(Tree {
        nodes: p.nodes,
        root: kids[0],
        holes,
    })
}

fn kind(tok: &Tok) -> Kind {
    match tok {
        Tok::Name(_) => Kind::Ident,
        Tok::Wildcard => Kind::Wild,
        Tok::Int { .. } => Kind::Int,
        Tok::Float(_) => Kind::Float,
        Tok::Rat(_) => Kind::Rat,
        Tok::Str(_) => Kind::Str,
        Tok::Atom(_) => Kind::Atom,
        Tok::Annot(_) => Kind::Annot,
        Tok::Keyword(_) => Kind::Keyword,
        Tok::Op(_) => Kind::Op,
    }
}

struct Parser<'a> {
    g: &'a Grammar,
    ring: u32,
    toks: &'a [(Kind, &'a str)],
    /// (rule, token, head) to the end and node of its match, or `None` for no match.
    memo: HashMap<(usize, usize, bool), Option<(usize, usize)>>,
    nodes: Vec<Node>,
    far: usize,
    expected: BTreeSet<String>,
}

impl Parser<'_> {
    fn fail(&mut self, pos: usize, what: String) -> Option<usize> {
        if pos > self.far {
            self.far = pos;
            self.expected.clear();
        }
        if pos == self.far {
            self.expected.insert(what);
        }
        None
    }

    /// Matches rule `r` at `pos`, pushing its node onto `kids`.
    fn rule(&mut self, r: usize, pos: usize, head: bool, kids: &mut Vec<usize>) -> Option<usize> {
        let key = (r, pos, head);
        if let Some(&res) = self.memo.get(&key) {
            let (end, node) = res?;
            kids.push(node);
            return Some(end);
        }
        // A left-recursive call fails, as in check.py; the grammar has none.
        self.memo.insert(key, None);
        let g = self.g;
        let mut res = None;
        for (alt, (e, layer)) in g.rules[r].alts.iter().enumerate() {
            if *layer > self.ring {
                continue;
            }
            let mut sub = Vec::new();
            if let Some(end) = self.m(e, pos, head, &mut sub) {
                self.nodes.push(Node {
                    rule: r,
                    alt,
                    start: pos,
                    end,
                    kids: sub,
                });
                res = Some((end, self.nodes.len() - 1));
                break;
            }
        }
        self.memo.insert(key, res);
        let (end, node) = res?;
        kids.push(node);
        Some(end)
    }

    fn m(&mut self, e: &Expr, pos: usize, head: bool, kids: &mut Vec<usize>) -> Option<usize> {
        match e {
            Expr::Lit(s) => {
                let (k, text) = self.toks[pos];
                if matches!(k, Kind::Keyword | Kind::Op | Kind::Ident) && text == s {
                    Some(pos + 1)
                } else {
                    self.fail(pos, format!("'{s}'"))
                }
            }
            Expr::Rule(r) => self.rule(*r, pos, head, kids),
            Expr::Kind(k) => {
                if self.toks[pos].0 == *k {
                    Some(pos + 1)
                } else {
                    self.fail(pos, k.name().into())
                }
            }
            Expr::Head => head.then_some(pos),
            Expr::Seq(items) => {
                let mark = kids.len();
                let mut at = pos;
                for x in items {
                    match self.m(x, at, head, kids) {
                        Some(e) => at = e,
                        None => {
                            kids.truncate(mark);
                            return None;
                        }
                    }
                }
                Some(at)
            }
            Expr::Choice(alts) => alts.iter().find_map(|x| self.m(x, pos, head, kids)),
            Expr::Star(x) | Expr::Plus(x) => {
                // An iteration that matches nothing ends the loop, kept only if it is the first.
                let (mut at, mut n) = (pos, 0);
                loop {
                    let mark = kids.len();
                    match self.m(x, at, head, kids) {
                        Some(e) if e == at && n > 0 => {
                            kids.truncate(mark);
                            break;
                        }
                        Some(e) => {
                            n += 1;
                            if e == at {
                                break;
                            }
                            at = e;
                        }
                        None => break,
                    }
                }
                (n > 0 || matches!(e, Expr::Star(_))).then_some(at)
            }
            Expr::Opt(x) => Some(self.m(x, pos, head, kids).unwrap_or(pos)),
            Expr::And(x) => {
                let mark = kids.len();
                let hit = self.m(x, pos, head, kids).is_some();
                kids.truncate(mark);
                hit.then_some(pos)
            }
            Expr::Not(x) => {
                let (far, expected) = (self.far, self.expected.clone());
                let mark = kids.len();
                let hit = self.m(x, pos, head, kids).is_some();
                kids.truncate(mark);
                (self.far, self.expected) = (far, expected);
                (!hit).then_some(pos)
            }
            Expr::SetHead(x) => self.m(x, pos, true, kids),
            Expr::ClearHead(x) => self.m(x, pos, false, kids),
        }
    }
}
