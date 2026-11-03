//! The parser (step L1.8): tokens become a tree of the rules of DESIGN.md sec:grammar.
//!
//! The parser runs that grammar itself, copied into `zed/grammar/`, as a packrat parser: each
//! rule tries its alternatives in order and memoizes its result at each token. So the
//! precedence ladder is the grammar's, rung for rung, and its trees are the trees
//! `tools/grammar/lib/check.dart` builds. A parse is at a ring: only the alternatives of that layer
//! and below are tried. Each node records its alternative, so a node of a later layer than the
//! program's is found later, by the elaborator, not here. An alternative marked `~` builds no
//! node, and the rule's match is the node of the marked rule.
//!
//! A literal in the grammar matches a keyword, an operator or a name with its text, so the
//! positional words `where` and `sep` are names the grammar matches by their text.
//!
//! A left-recursive rule grows from a failed seed, by the Squirrel parser's algorithm
//! (`squirrel_parser.tex`, fig. Code); a grammar with no left recursion never reaches that code.

mod grammar;

use std::collections::{BTreeSet, HashMap};
use std::fmt;
use std::mem;
use std::sync::OnceLock;

pub use grammar::{Alt, Expr, Grammar, Kind, Rule};

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
#[derive(Debug)]
pub struct Tree {
    /// The nodes; a node's children come before it.
    pub nodes: Vec<Node>,
    /// The root.
    pub root: usize,
    /// The tree of each `${…}` hole, in the order of the tokens, each parsed as an `Expr`.
    pub holes: Vec<Tree>,
}

/// Holes nest as deep as the source does: each is moved to a work list before its parent goes.
impl Drop for Tree {
    fn drop(&mut self) {
        let mut stack = mem::take(&mut self.holes);
        while let Some(mut t) = stack.pop() {
            stack.append(&mut t.holes);
        }
    }
}

impl Tree {
    /// The rule name of node `n`.
    pub fn name(&self, n: usize) -> &'static str {
        &grammar().rules[self.nodes[n].rule].name
    }

    /// The layer of the alternative node `n` matched.
    pub fn layer(&self, n: usize) -> u32 {
        let node = &self.nodes[n];
        grammar().rules[node.rule].alts[node.alt].layer
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
/// [`Tree::name`] and [`Tree::layer`] read [`grammar`], so they do not apply to this tree; a
/// node's `rule` and `alt` index `g`.
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

/// A tree whose holes are being parsed: those left, each with the span of its `}`.
struct Open<'t> {
    tree: Tree,
    holes: std::vec::IntoIter<(&'t [Token], Span)>,
}

/// Parses as `parse` does; `end` is the span reported for an error at the end of `tokens`.
/// Holes nest, so the open trees are on a stack. An error stops the parse at the first failure
/// in the order of the text, each tree before its holes.
fn parse_to(
    g: &Grammar,
    text: &str,
    tokens: &[Token],
    start: &str,
    ring: u32,
    end: Span,
) -> Result<Tree, Error> {
    let start = g.rule(start).unwrap_or_else(|| panic!("no rule {start}"));
    let mut stack = vec![parse_one(g, text, tokens, start, ring, end)?];
    let hole = g.rule("Expr");
    loop {
        let top = stack.last_mut().expect("the outermost tree returns");
        if let Some((tokens, close)) = top.holes.next() {
            let hole = hole.expect("the grammar has a rule `Expr` for a string's holes");
            stack.push(parse_one(g, text, tokens, hole, ring, close)?);
            continue;
        }
        let done = stack.pop().expect("the top was read above").tree;
        match stack.last_mut() {
            Some(parent) => parent.tree.holes.push(done),
            None => return Ok(done),
        }
    }
}

/// Parses `tokens` as rule `start`, its holes left for `parse_to`.
fn parse_one<'t>(
    g: &Grammar,
    text: &str,
    tokens: &'t [Token],
    start: usize,
    ring: u32,
    end: Span,
) -> Result<Open<'t>, Error> {
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
        kids: Vec::new(),
        far: 0,
        expected: BTreeSet::new(),
        saved: Vec::new(),
    };
    let matched = match p.run(start) {
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
                    holes.push((tokens.as_slice(), close));
                }
            }
        }
    }
    Ok(Open {
        tree: Tree {
            nodes: p.nodes,
            root: p.kids[0],
            holes: Vec::new(),
        },
        holes: holes.into_iter(),
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
    /// The match read the seed of a rule further out, another rule read its seed, or it read
    /// an entry with this mark, at this token or a later one. It holds only for those seeds,
    /// or a later match may enter the cycle through that other rule. Any other entry cannot
    /// go stale: no seed reached anything it read.
    reads_seed: bool,
    /// The token's version when `best` was last computed.
    version: usize,
}

/// An open expression with work left once its operand has matched or failed. The operand's
/// result goes to the frame on top of the stack, so nesting costs heap and not thread stack.
#[derive(Clone, Copy)]
enum Frame<'a> {
    /// The alternatives of rule `r` at `pos`. `next` is the first not yet tried, `base` is the
    /// height of the kids stack below this match's kids, and `caller` is the `low` of the match
    /// this one began in.
    Rule {
        r: usize,
        pos: usize,
        head: bool,
        next: usize,
        base: usize,
        caller: u32,
    },
    /// The items of a sequence not yet matched.
    Seq {
        rest: &'a [Expr],
        head: bool,
        mark: usize,
    },
    /// The branches of a choice not yet tried, the last excluded: it runs with no frame.
    Choice {
        rest: &'a [Expr],
        pos: usize,
        head: bool,
    },
    /// A `*` or `+` at `at`. An iteration that matches nothing ends the loop, kept only if it is
    /// the first; `some` says an iteration was kept, and `star` says none need be.
    Loop {
        x: &'a Expr,
        at: usize,
        mark: usize,
        some: bool,
        star: bool,
        head: bool,
    },
    Opt {
        pos: usize,
    },
    And {
        pos: usize,
        mark: usize,
    },
    /// A `!`, whose saved failures are on `Parser::saved`.
    Not {
        pos: usize,
        mark: usize,
    },
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
    /// below every rule, so it marks every rule on the path, at every token.
    low: u32,
    nodes: Vec<Node>,
    /// The kids of every open match, innermost on top.
    kids: Vec<usize>,
    far: usize,
    expected: BTreeSet<String>,
    /// `far` and `expected` as each open `!` found them.
    saved: Vec<(usize, BTreeSet<String>)>,
}

impl<'a> Parser<'a> {
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

    /// Calls rule `r` at `pos`. A result known here is returned, with the node pushed onto
    /// `kids`. Otherwise this opens a [`Frame::Rule`] and returns `None`, which that frame reads
    /// as "try your next alternative".
    fn call(
        &mut self,
        r: usize,
        pos: usize,
        head: bool,
        stack: &mut Vec<Frame<'a>>,
    ) -> Option<usize> {
        let now = self.versions[pos];
        let entry = self.memo.entry((r, pos, head)).or_default();
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
                // Which seed it read is not kept, so it counts as the outermost.
                self.low = 0;
                res
            }
            _ => {
                entry.in_path = true;
                entry.depth = self.open[pos] + 1;
                self.open[pos] += 1;
                stack.push(Frame::Rule {
                    r,
                    pos,
                    head,
                    next: 0,
                    base: self.kids.len(),
                    caller: std::mem::replace(&mut self.low, u32::MAX),
                });
                return None;
            }
        };
        let (end, node) = res?;
        self.kids.push(node);
        Some(end)
    }

    /// Records a finished pass over the alternatives of the rule of `key`. While it is
    /// left-recursive there and its match gets longer, this returns `None`: match it again over
    /// that match. A match is never replaced by a shorter one. Otherwise it returns the rule's
    /// result. Then this rule's own seed is finished, so its own reads do not mark the entry.
    /// Any other read does, for good, since `best` may keep what that read gave. A marked entry
    /// marks every rule on the path, at earlier tokens too, since each of them may keep what it
    /// read from this one.
    fn grown(&mut self, key: (usize, usize, bool), res: Res, caller: u32) -> Option<Res> {
        let pos = key.1;
        let entry = self.memo.get_mut(&key).expect("`call` made this entry");
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
            self.low = if entry.reads_seed { 0 } else { caller };
            return Some(entry.best.flatten());
        }
        self.versions[pos] += 1;
        None
    }

    /// Matches rule `start` at the first token, leaving its node on `kids`. Each turn gives the
    /// result in `done` to the top frame, until a frame names an expression to match; matching
    /// that gives the next result, or opens a frame and starts on its first operand.
    fn run(&mut self, start: usize) -> Option<usize> {
        let g = self.g;
        let mut stack = Vec::new();
        let mut done = self.call(start, 0, false, &mut stack);
        loop {
            let (mut e, pos, mut head) = loop {
                let Some(top) = stack.last_mut() else {
                    return done;
                };
                match top {
                    Frame::Rule {
                        r,
                        pos,
                        head,
                        next,
                        base,
                        caller,
                    } => {
                        let res = match done {
                            Some(end) => {
                                let (i, alt) = (*next - 1, &g.rules[*r].alts[*next - 1]);
                                let node = if alt.pass {
                                    self.kids[*base]
                                } else {
                                    self.nodes.push(Node {
                                        rule: *r,
                                        alt: i,
                                        start: *pos,
                                        end,
                                        kids: self.kids[*base..].to_vec(),
                                    });
                                    self.nodes.len() - 1
                                };
                                self.kids.truncate(*base);
                                Some((end, node))
                            }
                            None => {
                                self.kids.truncate(*base);
                                let ring = self.ring;
                                let alts = &g.rules[*r].alts[*next..];
                                if let Some(i) = alts.iter().position(|a| a.layer <= ring) {
                                    *next += i + 1;
                                    break (&alts[i].expr, *pos, *head);
                                }
                                None
                            }
                        };
                        let key = (*r, *pos, *head);
                        match self.grown(key, res, *caller) {
                            Some(res) => {
                                stack.pop();
                                done = res.map(|(end, node)| {
                                    self.kids.push(node);
                                    end
                                });
                            }
                            None => {
                                *next = 0;
                                done = None;
                            }
                        }
                    }
                    Frame::Seq { rest, head, mark } => match (done, rest.split_first()) {
                        (None, _) => {
                            self.kids.truncate(*mark);
                            stack.pop();
                        }
                        (Some(_), None) => {
                            stack.pop();
                        }
                        (Some(at), Some((x, more))) => {
                            *rest = more;
                            break (x, at, *head);
                        }
                    },
                    Frame::Choice { rest, pos, head } => {
                        if done.is_some() {
                            stack.pop();
                        } else {
                            let (pos, head) = (*pos, *head);
                            let (x, more) = rest.split_first().expect("a branch is left");
                            *rest = more;
                            if more.is_empty() {
                                stack.pop();
                            }
                            break (x, pos, head);
                        }
                    }
                    Frame::Loop {
                        x,
                        at,
                        mark,
                        some,
                        star,
                        head,
                    } => {
                        match done {
                            Some(end) if end == *at && *some => self.kids.truncate(*mark),
                            Some(end) if end == *at => *some = true,
                            Some(end) => {
                                *some = true;
                                *at = end;
                                *mark = self.kids.len();
                                break (*x, end, *head);
                            }
                            None => {}
                        }
                        done = (*some || *star).then_some(*at);
                        stack.pop();
                    }
                    Frame::Opt { pos } => {
                        done = Some(done.unwrap_or(*pos));
                        stack.pop();
                    }
                    Frame::And { pos, mark } => {
                        self.kids.truncate(*mark);
                        done = done.map(|_| *pos);
                        stack.pop();
                    }
                    Frame::Not { pos, mark } => {
                        self.kids.truncate(*mark);
                        (self.far, self.expected) = self.saved.pop().expect("saved by `!`");
                        done = done.is_none().then_some(*pos);
                        stack.pop();
                    }
                }
            };
            done = loop {
                match e {
                    Expr::Lit(s) => {
                        let (k, text) = self.toks[pos];
                        break if matches!(k, Kind::Keyword | Kind::Op | Kind::Ident) && text == s {
                            Some(pos + 1)
                        } else {
                            self.fail(pos, format!("'{s}'"))
                        };
                    }
                    Expr::Rule(r) => break self.call(*r, pos, head, &mut stack),
                    Expr::Kind(k) => {
                        break if self.toks[pos].0 == *k {
                            Some(pos + 1)
                        } else {
                            self.fail(pos, k.name().into())
                        };
                    }
                    Expr::Head => break head.then_some(pos),
                    Expr::Seq(items) => {
                        let Some((x, rest)) = items.split_first() else {
                            break Some(pos);
                        };
                        let mark = self.kids.len();
                        stack.push(Frame::Seq { rest, head, mark });
                        e = x;
                    }
                    Expr::Choice(alts) => {
                        let (x, rest) = alts.split_first().expect("a choice has branches");
                        if !rest.is_empty() {
                            stack.push(Frame::Choice { rest, pos, head });
                        }
                        e = x;
                    }
                    Expr::Star(x) | Expr::Plus(x) => {
                        stack.push(Frame::Loop {
                            x,
                            at: pos,
                            mark: self.kids.len(),
                            some: false,
                            star: matches!(e, Expr::Star(_)),
                            head,
                        });
                        e = x;
                    }
                    Expr::Opt(x) => {
                        stack.push(Frame::Opt { pos });
                        e = x;
                    }
                    Expr::And(x) => {
                        let mark = self.kids.len();
                        stack.push(Frame::And { pos, mark });
                        e = x;
                    }
                    Expr::Not(x) => {
                        self.saved.push((self.far, self.expected.clone()));
                        let mark = self.kids.len();
                        stack.push(Frame::Not { pos, mark });
                        e = x;
                    }
                    Expr::SetHead(x) => {
                        head = true;
                        e = x;
                    }
                    Expr::ClearHead(x) => {
                        head = false;
                        e = x;
                    }
                }
            };
        }
    }
}
