//! The packrat engine of the layered grammars: each rule tries its alternatives in order and
//! memoizes its result at each position. It runs over tokens for the compiler's parser and the
//! grammar tools, and over characters for the grammar tools' lexer ([`Input`]).
//!
//! A left-recursive rule grows from a failed seed, by the Squirrel parser's algorithm
//! (`squirrel_parser.tex`, fig. Code); a grammar with no left recursion never reaches that code.

use std::collections::BTreeSet;

use super::grammar::{Expr, Grammar, Kind};

/// What the engine reads: a sequence of positions.
pub trait Input {
    /// How many positions there are.
    fn len(&self) -> usize;

    /// Whether there are no positions.
    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// The position after the literal `text` at `pos`, if it is there.
    fn lit(&self, pos: usize, text: &str) -> Option<usize>;

    /// Whether the token at `pos` is of kind `k`. Characters have no kinds.
    fn kind(&self, pos: usize, k: Kind) -> bool;

    /// The character at `pos`. Tokens have none.
    fn char_at(&self, pos: usize) -> Option<char>;
}

/// Whether a token of kind `k` and text `t` is the literal `text`: a literal in the syntactic
/// grammar matches a keyword, an operator or a name.
pub fn literal_matches(k: Kind, t: &str, text: &str) -> bool {
    matches!(k, Kind::Keyword | Kind::Op | Kind::Ident) && t == text
}

/// Tokens as a grammar reads them: each one's kind and text.
impl Input for [(Kind, &str)] {
    fn len(&self) -> usize {
        <[_]>::len(self)
    }

    fn lit(&self, pos: usize, text: &str) -> Option<usize> {
        let &(k, t) = self.get(pos)?;
        literal_matches(k, t, text).then_some(pos + 1)
    }

    fn kind(&self, pos: usize, k: Kind) -> bool {
        self.get(pos).is_some_and(|t| t.0 == k)
    }

    fn char_at(&self, _: usize) -> Option<char> {
        None
    }
}

/// A text as a grammar over characters reads it.
impl Input for [char] {
    fn len(&self) -> usize {
        <[_]>::len(self)
    }

    fn lit(&self, pos: usize, text: &str) -> Option<usize> {
        let mut at = pos;
        for c in text.chars() {
            if self.get(at) != Some(&c) {
                return None;
            }
            at += 1;
        }
        Some(at)
    }

    fn kind(&self, _: usize, _: Kind) -> bool {
        false
    }

    fn char_at(&self, pos: usize) -> Option<char> {
        self.get(pos).copied()
    }
}

/// A node: the rule it matched, by index, the alternative, and the positions it spans.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Node {
    /// The rule.
    pub rule: usize,
    /// The alternative, counted from 0 among all of the rule's alternatives.
    pub alt: usize,
    /// The first position.
    pub start: usize,
    /// One past the last position.
    pub end: usize,
    /// The child nodes, in order.
    pub kids: Vec<usize>,
    /// Which branch each inner choice took: how many child nodes came before it, and the
    /// branch. Two trees with the same nodes can differ only here.
    pub branches: Vec<(u32, u32)>,
}

/// What a failed match expected.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Expected<'g> {
    /// A literal.
    Lit(&'g str),
    /// A token kind or a built-in class, by name.
    Name(&'g str),
    /// A character class.
    Class,
}

/// A child of a node while it is being matched: a node's index, or with [`BRANCH`] set the
/// branch an inner choice took.
const BRANCH: usize = 1 << (usize::BITS - 1);

/// A rule's result at a position: the end and node of its match, or `None` for no match.
type Res = Option<(usize, usize)>;

/// No entry: the end of a position's list of entries.
const NO_ENTRY: usize = usize::MAX;

/// What is known of a rule at a position.
#[derive(Clone, Copy, Default)]
struct Entry {
    /// The rule and `head`, as `2 * rule + head`.
    slot: usize,
    /// The entry made before this one at its position, or [`NO_ENTRY`].
    prev: usize,
    /// The longest result so far, once there is one.
    best: Option<Res>,
    /// The rule is being matched here, on the current path of calls.
    in_path: bool,
    /// A call on that path reached this entry again: the rule is left-recursive here.
    left_rec: bool,
    /// How many rules were on that path at this position, this one included, when this match
    /// began.
    depth: u32,
    /// The match read the seed of a rule further out, another rule read its seed, or it read
    /// an entry with this mark, at this position or a later one. It holds only for those seeds,
    /// or a later match may enter the cycle through that other rule. Any other entry cannot
    /// go stale: no seed reached anything it read.
    reads_seed: bool,
    /// The position's version when `best` was last computed.
    version: usize,
}

/// An open expression with work left once its operand has matched or failed. The operand's
/// result goes to the frame on top of the stack, so nesting costs heap and not thread stack.
#[derive(Clone, Copy)]
enum Frame<'g> {
    /// The alternatives of rule `r` at `pos`. `next` is the first not yet tried, `base` is the
    /// height of the kids stack below this match's kids, `caller` is the `low` of the match
    /// this one began in, and `at` is the rule's entry in `Parser::memo`.
    Rule {
        r: usize,
        pos: usize,
        head: bool,
        next: usize,
        base: usize,
        caller: u32,
        at: usize,
    },
    /// The items of a sequence not yet matched.
    Seq {
        rest: &'g [Expr],
        head: bool,
        mark: usize,
    },
    /// The branches of a choice not yet tried. `taken` counts those tried, and `mark` is the
    /// height of the kids stack below the record of the branch being tried.
    Choice {
        rest: &'g [Expr],
        taken: usize,
        pos: usize,
        head: bool,
        mark: usize,
    },
    /// The first operand of `e % sep` at `pos`, matched before its loop over `sep e`; `body`
    /// is that loop's body, and `mark` the height of the kids stack below the match.
    Sep {
        body: &'g [Expr],
        head: bool,
        mark: usize,
    },
    /// A `*`, `+` or the loop of a `%` at `at`, over the sequence `body`. An iteration that
    /// matches nothing ends the loop, kept only if it is the first; `some` says an iteration was
    /// kept, and `star` says none need be.
    Loop {
        body: &'g [Expr],
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

/// A packrat parser of one input at one ring.
pub struct Parser<'g, I: Input + ?Sized> {
    g: &'g Grammar,
    ring: u32,
    input: &'g I,
    /// What is known of a rule at a position, in the order first called. The entries of one
    /// position form a list through `prev`, from the last one made there, which `last` holds.
    memo: Vec<Entry>,
    /// The last entry made at each position, or [`NO_ENTRY`].
    last: Vec<usize>,
    /// How many times a left-recursive match has grown at each position, for both values of
    /// `head`. An entry with `reads_seed` behind its position's version may read a longer seed
    /// now, so it is matched again.
    versions: Vec<usize>,
    /// How many rules are on the path of calls at each position.
    open: Vec<u32>,
    /// The least `depth` of a seed the current match read, or `u32::MAX` for none. 0 is
    /// below every rule, so it marks every rule on the path, at every position.
    low: u32,
    /// The nodes built; a node's children come before it.
    pub nodes: Vec<Node>,
    /// The kids of every open match, innermost on top.
    kids: Vec<usize>,
    /// The farthest position a match failed at.
    pub far: usize,
    /// What was expected there, once for each failure there: most failures are at `far`, and a
    /// push costs less than an insert into a set. [`Parser::expected`] gives each once.
    expected: Vec<Expected<'g>>,
    /// `far` and `expected` as each open `!` found them. The list is moved here, not copied:
    /// what the `!` adds to the empty list left behind is dropped when the `!` ends, and nothing
    /// reads `expected` before the parse ends.
    saved: Vec<(usize, Vec<Expected<'g>>)>,
}

impl<'g, I: Input + ?Sized> Parser<'g, I> {
    /// A parser of `input` by the alternatives of `g` of layer at most `ring`.
    pub fn new(g: &'g Grammar, ring: u32, input: &'g I) -> Self {
        Parser {
            g,
            ring,
            input,
            memo: Vec::new(),
            last: vec![NO_ENTRY; input.len() + 1],
            versions: vec![0; input.len() + 1],
            open: vec![0; input.len() + 1],
            low: u32::MAX,
            nodes: Vec::new(),
            kids: Vec::new(),
            far: 0,
            expected: Vec::new(),
            saved: Vec::new(),
        }
    }

    /// What was expected at [`Parser::far`], each once.
    pub fn expected(&self) -> BTreeSet<Expected<'g>> {
        self.expected.iter().copied().collect()
    }

    /// Records that `what` was expected at `pos`.
    pub fn fail(&mut self, pos: usize, what: Expected<'g>) -> Option<usize> {
        if pos > self.far {
            self.far = pos;
            self.expected.clear();
        }
        if pos == self.far {
            self.expected.push(what);
        }
        None
    }

    /// Matches rule `r` at `pos`: its end and node.
    pub fn rule_node(&mut self, r: usize, pos: usize, head: bool) -> Res {
        let mut stack = Vec::new();
        let first = self.call(r, pos, head, &mut stack);
        let end = self.run(first, stack)?;
        let node = self.kids.pop().expect("a matched rule leaves its node");
        Some((end, node))
    }

    /// Matches `e` at `pos` and throws away what it built: a lookahead asked from outside.
    pub fn holds(&mut self, e: &'g Expr, pos: usize, head: bool) -> bool {
        let stack = vec![Frame::Seq {
            rest: std::slice::from_ref(e),
            head,
            mark: 0,
        }];
        let end = self.run(Some(pos), stack);
        self.kids.clear();
        end.is_some()
    }

    /// Calls rule `r` at `pos`. A result known here is returned, with the node pushed onto
    /// `kids`. Otherwise this opens a [`Frame::Rule`] and returns `None`, which that frame reads
    /// as "try your next alternative".
    fn call(
        &mut self,
        r: usize,
        pos: usize,
        head: bool,
        stack: &mut Vec<Frame<'g>>,
    ) -> Option<usize> {
        let now = self.versions[pos];
        // A position holds at most one entry for each rule and value of `head`, so this walk is
        // bounded by the grammar, not by the input: on the scaling texts of steps L1.16, L1.26
        // and L1.26a a position holds 4.6 to 13.6 entries on average and at most 67
        // (COMPLEXITY.md F86). A hash map keyed by position and rule took 6% to 27% more
        // instructions and, its table scattered over memory, 1.9 times the cycles.
        let slot = 2 * r + usize::from(head);
        let mut at = self.last[pos];
        while at != NO_ENTRY && self.memo[at].slot != slot {
            at = self.memo[at].prev;
        }
        if at == NO_ENTRY {
            at = self.memo.len();
            self.memo.push(Entry {
                slot,
                prev: self.last[pos],
                ..Entry::default()
            });
            self.last[pos] = at;
        }
        let entry = &mut self.memo[at];
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
                    at,
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
    /// marks every rule on the path, at earlier positions too, since each of them may keep what
    /// it read from this one.
    fn grown(&mut self, at: usize, pos: usize, res: Res, caller: u32) -> Option<Res> {
        let entry = &mut self.memo[at];
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

    /// Runs the open frames in `stack` to the end, `done` being the result for the top one, and
    /// gives the result of the bottom one. Each turn gives the result in `done` to the top frame,
    /// until a frame names an expression to match; matching that gives the next result, or opens
    /// a frame and starts on its first operand.
    fn run(&mut self, mut done: Option<usize>, mut stack: Vec<Frame<'g>>) -> Option<usize> {
        let g = self.g;
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
                        at,
                    } => {
                        let res = match done {
                            Some(end) => {
                                let (i, alt) = (*next - 1, &g.rules[*r].alts[*next - 1]);
                                let node = if alt.pass {
                                    self.kids[*base]
                                } else {
                                    let (kids, branches) = split_kids(&self.kids[*base..]);
                                    self.nodes.push(Node {
                                        rule: *r,
                                        alt: i,
                                        start: *pos,
                                        end,
                                        kids,
                                        branches,
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
                        match self.grown(*at, *pos, res, *caller) {
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
                    Frame::Choice {
                        rest,
                        taken,
                        pos,
                        head,
                        mark,
                    } => {
                        if done.is_some() {
                            stack.pop();
                        } else {
                            self.kids.truncate(*mark);
                            match rest.split_first() {
                                Some((x, more)) => {
                                    *rest = more;
                                    self.kids.push(BRANCH | *taken);
                                    *taken += 1;
                                    break (x, *pos, *head);
                                }
                                None => {
                                    stack.pop();
                                }
                            }
                        }
                    }
                    Frame::Sep { body, head, mark } => match done {
                        None => {
                            self.kids.truncate(*mark);
                            stack.pop();
                        }
                        Some(at) => {
                            let (body, head, mark) = (*body, *head, self.kids.len());
                            *top = Frame::Loop {
                                body,
                                at,
                                mark,
                                some: false,
                                star: true,
                                head,
                            };
                            break (iteration(&mut stack, body, head, mark), at, head);
                        }
                    },
                    Frame::Loop {
                        body,
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
                                let (body, head, mark) = (*body, *head, *mark);
                                break (iteration(&mut stack, body, head, mark), end, head);
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
                        let end = self.input.lit(pos, s);
                        break end.or_else(|| self.fail(pos, Expected::Lit(s)));
                    }
                    Expr::Rule(r) => break self.call(*r, pos, head, &mut stack),
                    Expr::Kind(k) => {
                        break if self.input.kind(pos, *k) {
                            Some(pos + 1)
                        } else {
                            self.fail(pos, Expected::Name(k.name()))
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
                        let mark = self.kids.len();
                        stack.push(Frame::Choice {
                            rest,
                            taken: 1,
                            pos,
                            head,
                            mark,
                        });
                        self.kids.push(BRANCH);
                        e = x;
                    }
                    Expr::Star(x) | Expr::Plus(x) => {
                        let x: &'g Expr = x;
                        stack.push(Frame::Loop {
                            body: std::slice::from_ref(x),
                            at: pos,
                            mark: self.kids.len(),
                            some: false,
                            star: matches!(e, Expr::Star(_)),
                            head,
                        });
                        e = x;
                    }
                    Expr::Sep(items) => {
                        stack.push(Frame::Sep {
                            body: &items[..],
                            head,
                            mark: self.kids.len(),
                        });
                        e = &items[1];
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
                        self.saved
                            .push((self.far, std::mem::take(&mut self.expected)));
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
                    Expr::Class(ranges) => {
                        let c = self.input.char_at(pos);
                        break if c.is_some_and(|c| ranges.iter().any(|&(a, b)| a <= c && c <= b)) {
                            Some(pos + 1)
                        } else {
                            self.fail(pos, Expected::Class)
                        };
                    }
                    Expr::Any => break self.char_class(pos, "ANY", |_| true),
                    Expr::XidStart => {
                        break self.char_class(pos, "XID_START", unicode_ident::is_xid_start);
                    }
                    Expr::XidContinue => {
                        break self.char_class(pos, "XID_CONTINUE", unicode_ident::is_xid_continue);
                    }
                    Expr::Undefined(name) => break self.fail(pos, Expected::Name(name)),
                }
            };
        }
    }

    /// Matches one character for which `hit` holds.
    fn char_class(
        &mut self,
        pos: usize,
        name: &'static str,
        hit: impl Fn(char) -> bool,
    ) -> Option<usize> {
        if self.input.char_at(pos).is_some_and(hit) {
            Some(pos + 1)
        } else {
            self.fail(pos, Expected::Name(name))
        }
    }
}

/// Opens an iteration of a loop over the sequence `body`, whose kids start at `mark`, and gives
/// its first item: the rest wait in a [`Frame::Seq`], which drops the iteration's kids if it
/// fails.
fn iteration<'g>(
    stack: &mut Vec<Frame<'g>>,
    body: &'g [Expr],
    head: bool,
    mark: usize,
) -> &'g Expr {
    let (first, rest) = body.split_first().expect("a loop body is not empty");
    if !rest.is_empty() {
        stack.push(Frame::Seq { rest, head, mark });
    }
    first
}

/// The kids of a finished match: its child nodes, and for each inner choice how many child nodes
/// came before it and the branch it took.
fn split_kids(kids: &[usize]) -> (Vec<usize>, Vec<(u32, u32)>) {
    let mut nodes = Vec::with_capacity(kids.len());
    let mut branches = Vec::new();
    for &k in kids {
        if k & BRANCH == 0 {
            nodes.push(k);
        } else {
            branches.push((nodes.len() as u32, (k & !BRANCH) as u32));
        }
    }
    (nodes, branches)
}
