//! The parser (step L1.8): tokens become a tree of the rules of DESIGN.md sec:grammar.
//!
//! The parser runs that grammar itself, copied into `zed/grammar/`, as a packrat parser: each
//! rule tries its alternatives in order and memoizes its result at each token. So the
//! precedence ladder is the grammar's, rung for rung, and its trees are the trees
//! `tools/grammar/lib/check.dart` builds. A parse is at a ring: only the alternatives of that layer
//! and below are tried. Each node records its alternative, so a node of a later layer than the
//! program's is found later, by the elaborator, not here.
//!
//! A literal in the grammar matches a keyword, an operator or a name with its text, so the
//! positional words `where` and `sep` are names the grammar matches by their text.
//!
//! A left-recursive rule grows from a failed seed, by the Squirrel parser's algorithm
//! (`squirrel_parser.tex`, fig. Code); a grammar with no left recursion never reaches that code.

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
    parse_to(grammar(), text, tokens, start, ring, end)
}

/// Parses as [`parse`] does, by the grammar `g`, which needs a rule `Expr` for a string's holes.
pub fn parse_with(
    g: &Grammar,
    text: &str,
    tokens: &[Token],
    start: &str,
    ring: u32,
) -> Result<Tree, Error> {
    let end = Span {
        start: text.len(),
        end: text.len(),
    };
    parse_to(g, text, tokens, start, ring, end)
}

/// Parses as `parse` does; `end` is the span reported for an error at the end of `tokens`.
fn parse_to(
    g: &Grammar,
    text: &str,
    tokens: &[Token],
    start: &str,
    ring: u32,
    end: Span,
) -> Result<Tree, Error> {
    let start = g.rule(start).unwrap_or_else(|| panic!("no rule {start}"));
    let mut toks: Vec<(Kind, &str)> = tokens
        .iter()
        .map(|t| (kind(&t.tok), &text[t.span.start..t.span.end]))
        .collect();
    toks.push((Kind::End, ""));
    let span = |i: usize| tokens.get(i).map_or(end, |t| t.span);
    let mut p = Parser {
        g,
        ring,
        toks: &toks,
        memo: HashMap::new(),
        versions: vec![0; toks.len() + 1],
        open: vec![0; toks.len() + 1],
        low: u32::MAX,
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
                    holes.push(parse_to(g, text, tokens, "Expr", ring, close)?);
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

/// A rule's result at a token: the end and node of its match, or `None` for no match.
type Res = Option<(usize, usize)>;

/// What is known of a rule at a token.
#[derive(Clone, Copy, Default)]
struct Entry {
    /// The longest result so far, once there is one.
    best: Option<Res>,
    /// The rule is being matched here, on the current path of calls.
    in_path: bool,
    /// A call on that path reached this entry again: the rule is left-recursive here.
    left_rec: bool,
    /// How many rules were on that path at this token, this one included, when this match
    /// began.
    depth: u32,
    /// The match read the seed of a rule further out, or another rule read its seed. It holds
    /// only for that seed, or a later match may enter the cycle through that other rule. Any
    /// other entry cannot go stale: all it read is indexed by token and no seed changed it.
    reads_seed: bool,
    /// The token's version when `best` was last computed.
    version: usize,
}

struct Parser<'a> {
    g: &'a Grammar,
    ring: u32,
    toks: &'a [(Kind, &'a str)],
    /// (rule, token, head) to what is known there.
    memo: HashMap<(usize, usize, bool), Entry>,
    /// How many times a left-recursive match has grown at each token, for both values of
    /// `head`. An entry with `reads_seed` behind its token's version may read a longer seed
    /// now, so it is matched again.
    versions: Vec<usize>,
    /// How many rules are on the path of calls at each token.
    open: Vec<u32>,
    /// The least `depth` of a seed the current match read, or `u32::MAX` for none. 0 is
    /// below every rule at the token.
    low: u32,
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
        let now = self.versions[pos];
        let entry = self.memo.entry(key).or_default();
        let res = match entry.best {
            _ if entry.in_path => {
                // Left recursion: the first time, this call fails, which seeds the growth.
                if entry.best.is_none() {
                    entry.left_rec = true;
                    entry.best = Some(None);
                }
                self.low = self.low.min(entry.depth);
                entry.best.flatten()
            }
            Some(res) if !entry.reads_seed => res,
            Some(res) if entry.version == now => {
                // Which seed it read is not kept, so it counts as the outermost at this token.
                if self.open[pos] > 0 {
                    self.low = 0;
                }
                res
            }
            _ => {
                entry.in_path = true;
                entry.depth = self.open[pos] + 1;
                self.grow(key)
            }
        };
        let (end, node) = res?;
        kids.push(node);
        Some(end)
    }

    /// Matches the rule of `key`, and while it is left-recursive there and its match gets
    /// longer, matches it again over that match. A match is never replaced by a shorter one.
    /// When this returns, this rule's own seed is finished, so its own reads do not mark the
    /// entry. Any other read does, for good, since `best` may keep what that read gave, and
    /// passes one rule outward, within the token.
    fn grow(&mut self, key: (usize, usize, bool)) -> Res {
        let (r, pos, head) = key;
        self.open[pos] += 1;
        let caller = std::mem::replace(&mut self.low, u32::MAX);
        loop {
            let res = self.alternatives(r, pos, head);
            let entry = self.memo.get_mut(&key).expect("`rule` made this entry");
            let end = |res: Res| res.map(|(end, _)| end);
            let longer = entry.best.is_none_or(|best| end(res) > end(best));
            if longer {
                entry.best = Some(res);
            }
            if !longer || !entry.left_rec {
                entry.in_path = false;
                entry.version = self.versions[pos];
                entry.reads_seed |= self.low < entry.depth;
                self.open[pos] = entry.depth - 1;
                self.low = if entry.reads_seed && entry.depth > 1 {
                    caller.min(self.low.min(entry.depth - 1).saturating_sub(1))
                } else {
                    caller
                };
                return entry.best.flatten();
            }
            self.versions[pos] += 1;
        }
    }

    /// The first alternative of rule `r` that matches at `pos`, as a node.
    fn alternatives(&mut self, r: usize, pos: usize, head: bool) -> Res {
        let g = self.g;
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
                return Some((end, self.nodes.len() - 1));
            }
        }
        None
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
