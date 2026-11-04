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
//! positional words `where` and `sep` are names the grammar matches by their text.
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
}

/// The message for a `..` written in a list with other items, as `(int, ..)`, `#a(int, ..)` or
/// `{x: int, ..}`: the kind-wide types hold `..` alone (DESIGN.md sec:type_language).
pub const DOTS: &str = "`..` stands alone between its brackets: `(..)` is every tuple, `{..}` \
                        every struct and `#a(..)` the atom `#a` with any payload, and no list \
                        with other items holds `..`";

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
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
        let mut expected: Vec<String> = p.expected.iter().map(shown).collect();
        expected.sort();
        let dots = dots_in_list(&toks, p.far);
        return Err(Error {
            span: span(dots.unwrap_or(p.far)),
            expected,
            message: dots.map(|_| DOTS),
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
        Tok::Int { .. } | Tok::Generic { .. } => Kind::Int,
        Tok::Float(_) => Kind::Float,
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
