//! The parser (step L1.8): tokens become a tree of the rules of DESIGN.md sec:grammar.
//!
//! The parser runs that grammar itself, copied into `zed/grammar/`, as a packrat parser: each
//! rule tries its alternatives in order and memoizes its result at each token. So the
//! precedence ladder is the grammar's, rung for rung, and its trees are the trees
//! the `check` tool of `crates/zed-tools` builds, with this same parser. A parse is at a ring:
//! only the alternatives of that layer and below are tried. Each node records its alternative,
//! so a node of a later layer than the program's is found later, by the elaborator, not here. An alternative marked `~` builds no
//! node, and the rule's match is the node of the marked rule.
//!
//! A literal in the grammar matches a keyword, an operator or a name with its text, so the
//! positional words `where`, `sep` and `initial` are names the grammar matches by their text.
//!
//! A left-recursive rule grows from a failed seed, by the Squirrel parser's algorithm
//! (`squirrel_parser.tex`, fig. Code); a grammar with no left recursion never reaches that code.

pub mod engine;
mod grammar;

use std::fmt;
use std::mem;
use std::sync::OnceLock;

pub use engine::{Expected, Input, Node, Parser, literal_matches};
pub use grammar::{Alt, Expr, Grammar, Kind, Line, Rule, is_space, marked_rule, split_line};

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
    /// The span of that token (empty at the end of the text), or of the `..` that [`DOTS`]
    /// is about.
    pub span: Span,
    /// The literals (quoted) and token kinds expected there, sorted.
    pub expected: Vec<String>,
    /// A message that says more than the expected tokens: [`DOTS`] for a `..` in a list.
    pub message: Option<&'static str>,
    /// The boundary item written with neither `initial` nor an index that the parse stopped
    /// at, as `with x = 0`; the error's span is its `=`.
    pub bare: Option<Box<Bare>>,
}

/// A boundary item with neither `initial` nor an index, as `with x = 0` (row "Boundary item
/// with neither `initial` nor an index", DESIGN.md sec:generations).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Bare {
    /// The variable.
    pub name: String,
    /// The text of the value, `…` when there is none.
    pub value: String,
    /// The item, from its name to the end of its value.
    pub item: Span,
    /// The statement it stands on, its `;` included where there is one.
    pub stmt: Span,
    /// For an indexed definition of the variable over one key `i in lo..`, the key of the entry
    /// below the domain: `lo - 1`, worked out when `lo` is an integer literal.
    pub below: Option<String>,
}

impl Bare {
    /// What the error says.
    pub fn message(&self) -> String {
        let Bare { name, value, .. } = self;
        format!(
            "`with {name} = {value}` gives `{name}` no sentinel value: a boundary item is \
             written `initial {name} = {value}`, which gives the sentinel value, or with an \
             index, as `{name}[k] = {value}`. Without `initial`, `with {name} = {value}` reads \
             as though `{name}` took the value `{value}` anew on every step, while a boundary \
             item gives `{name}` one value, below its first step or index, once."
        )
    }
}

/// The message for a `..` written in a list with other items, as `(int, ..)`, `#a(int, ..)` or
/// `{x: int, ..}`: the kind-wide types hold `..` alone (DESIGN.md sec:type_language).
pub const DOTS: &str = "`..` stands alone between its brackets: `(..)` is every tuple, `{..}` \
                        every struct and `#a(..)` the atom `#a` with any payload, and no list \
                        with other items holds `..`";

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(b) = &self.bare {
            return f.write_str(&b.message());
        }
        match self.message {
            Some(m) => f.write_str(m),
            None => write!(f, "expected {}", self.expected.join(" or ")),
        }
    }
}

/// The index of the `..` that a parse failing at token `far` of `toks` stopped at or just
/// after, when it stands in a list with other items: after a `,` (`(int, ..)`), or alone after
/// an opening bracket and followed by more than the closing one (`(.., int)`). No rule takes a
/// `..` after a `,`, or after `(` or `{` but before a token other than the closing bracket.
fn dots_in_list(toks: &[(Kind, &str)], far: usize) -> Option<usize> {
    let text = |i: usize| toks.get(i).map(|t| t.1);
    if text(far) == Some("..") && far > 0 && text(far - 1) == Some(",") {
        return Some(far);
    }
    let d = far.checked_sub(1)?;
    let opened = d > 0 && matches!(text(d - 1), Some("(" | "{"));
    (text(d) == Some("..") && opened).then_some(d)
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
/// [`Tree::name`] and [`Tree::layer`] read [`grammar()`], so they do not apply to this tree; a
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
    let toks: Vec<(Kind, &str)> = tokens
        .iter()
        .map(|t| (kind(&t.tok), &text[t.span.start..t.span.end]))
        .chain([(Kind::End, "")])
        .collect();
    let span = |i: usize| tokens.get(i).map_or(end, |t| t.span);
    let mut p = Parser::new(g, ring, toks.as_slice());
    let matched = match p.rule_node(start, 0, false) {
        Some((e, node)) if e + 1 >= toks.len() => Some(node),
        Some((e, _)) => {
            p.fail(e, Expected::Name("END"));
            None
        }
        None => None,
    };
    let Some(root) = matched else {
        let mut expected: Vec<String> = p.expected().iter().map(shown).collect();
        expected.sort();
        let dots = dots_in_list(&toks, p.far);
        let bare = bare_item(g, ring, start, &toks, p.far)
            .map(|n| Box::new(bare(text, tokens, &toks, n, end)));
        return Err(Error {
            span: span(dots.unwrap_or(p.far)),
            expected,
            message: dots.map(|_| DOTS),
            bare,
        });
    };
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
            root,
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
        Tok::Float { .. } => Kind::Float,
        Tok::Rat(_) => Kind::Rat,
        Tok::Str(_) => Kind::Str,
        Tok::Atom(_) => Kind::Atom,
        Tok::Annot(_) => Kind::Annot,
        Tok::Keyword(_) => Kind::Keyword,
        Tok::Op(_) => Kind::Op,
    }
}

/// How an error names what was expected.
fn shown(e: &Expected<'_>) -> String {
    match e {
        Expected::Lit(s) => format!("'{s}'"),
        Expected::Name(n) => (*n).into(),
        Expected::Class => unreachable!("a grammar over tokens holds no character class"),
    }
}

/// The index of the name of a boundary item written with neither `initial` nor an index, as
/// `with x = 0` or `, x = 0` in a boundary clause, at whose `=` a parse of `toks` as rule
/// `start` failed (token `far`). Such an item is one exactly when the parse gets past that `=`
/// once `initial` is written before the name, so a failure at an `=` after `with x` that is no
/// boundary item, as in a push `p <- e with x = 0`, gives no item. The second parse runs only
/// when the first has failed, at the cost of one parse.
fn bare_item(
    g: &Grammar,
    ring: u32,
    start: usize,
    toks: &[(Kind, &str)],
    far: usize,
) -> Option<usize> {
    let n = far.checked_sub(1).filter(|&n| n > 0)?;
    let shaped = toks.get(far).is_some_and(|t| t.1 == "=")
        && toks[n].0 == Kind::Ident
        && matches!(toks[n - 1].1, "with" | ",");
    if !shaped {
        return None;
    }
    let mut fixed = Vec::with_capacity(toks.len() + 1);
    fixed.extend_from_slice(&toks[..n]);
    fixed.push((Kind::Ident, "initial"));
    fixed.extend_from_slice(&toks[n..]);
    let mut p = Parser::new(g, ring, fixed.as_slice());
    let reached = match p.rule_node(start, 0, false) {
        Some((e, _)) => e.max(p.far),
        None => p.far,
    };
    // The `=` is at `far + 1` in `fixed`.
    (reached > far + 1).then_some(n)
}

/// How the bracket depth changes at a token: up at an opening bracket, down at a closing one.
fn depth(t: &str) -> i32 {
    match t {
        "(" | "[" | "{" => 1,
        ")" | "]" | "}" => -1,
        _ => 0,
    }
}

/// The [`Bare`] item whose name is token `n` of `toks`, lexed from `text` as `tokens`; `end` is
/// the span of the end of the tokens. The value runs from the `=` to the next `,` or `;` at its
/// own bracket depth; the statement from the token after the `;` or unmatched opening bracket
/// before the item to the `;` after it. Each scan stops at the statement's ends, so the cost is
/// the statement's length.
fn bare(text: &str, tokens: &[Token], toks: &[(Kind, &str)], n: usize, end: Span) -> Bare {
    let span = |i: usize| tokens.get(i).map_or(end, |t| t.span);
    let mut d = 0;
    let mut last = n + 2;
    while last < tokens.len() {
        let t = toks[last].1;
        if d == 0 && matches!(t, "," | ";") || d + depth(t) < 0 {
            break;
        }
        d += depth(t);
        last += 1;
    }
    let value = if last > n + 2 {
        text[span(n + 2).start..span(last - 1).end].to_string()
    } else {
        "…".to_string()
    };
    let mut stop = last;
    let mut d = 0;
    while stop < tokens.len() && !(d == 0 && toks[stop].1 == ";") && d + depth(toks[stop].1) >= 0 {
        d += depth(toks[stop].1);
        stop += 1;
    }
    let close = if stop < tokens.len() && toks[stop].1 == ";" {
        stop
    } else {
        stop.saturating_sub(1)
    };
    let mut first = n;
    let mut d = 0;
    while first > 0 {
        let t = toks[first - 1].1;
        if d == 0 && t == ";" || d - depth(t) < 0 {
            break;
        }
        d -= depth(t);
        first -= 1;
    }
    Bare {
        name: toks[n].1.to_string(),
        value,
        item: Span {
            start: span(n).start,
            end: span(last.max(n + 3) - 1).end,
        },
        stmt: Span {
            start: span(first).start,
            end: span(close).end,
        },
        below: below(&toks[first..n], toks[n].1),
    }
}

/// The key of the entry below the domain of the indexed definition `stmt` of `name`, the
/// tokens before its boundary item, when it has one key `i in lo..<hi`, `lo..=hi` or `lo..`:
/// `lo - 1`, worked out when `lo` is an integer literal, possibly negated.
fn below(stmt: &[(Kind, &str)], name: &str) -> Option<String> {
    let [(_, f), (_, "["), (Kind::Ident, _), (_, "in"), rest @ ..] = stmt else {
        return None;
    };
    if *f != name {
        return None;
    }
    let mut d = 0;
    let mut range = None;
    let mut close = None;
    for (i, &(_, t)) in rest.iter().enumerate() {
        if d == 0 && range.is_none() && matches!(t, ".." | "..<" | "..=") {
            range = Some(i);
        }
        if d + depth(t) < 0 {
            close = Some(i);
            break;
        }
        d += depth(t);
    }
    let (range, close) = (range?, close?);
    if range == 0 || rest.get(close + 1).map(|t| t.1) != Some("=") {
        return None;
    }
    let lo = &rest[..range];
    let int = |t: &str| t.replace('_', "").parse::<i128>().ok();
    let folded = match lo {
        [(Kind::Int, t)] => int(t).and_then(|v| v.checked_sub(1)),
        [(_, "-"), (Kind::Int, t)] => int(t).and_then(|v| (-v).checked_sub(1)),
        _ => None,
    };
    let words: Vec<&str> = lo.iter().map(|t| t.1).collect();
    Some(match (folded, lo.len()) {
        (Some(v), _) => v.to_string(),
        (None, 1) => format!("{} - 1", words[0]),
        (None, _) => format!("({}) - 1", words.join(" ")),
    })
}
