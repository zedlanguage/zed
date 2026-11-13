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

mod case;
mod clause;
pub mod engine;
mod grammar;
mod recover;

use std::collections::BTreeSet;
use std::fmt;
use std::mem;
use std::ops::Range;
use std::sync::OnceLock;

use clause::kind;
pub use clause::{Clause, RESERVED};
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
    /// The tree of each `${…}` hole, in the order of the tokens, each parsed as an `Expr`; the
    /// holes in a skipped declaration have none.
    pub holes: Vec<Tree>,
    /// The token ranges of the declarations a unit parsed by [`parse_unit`] left out, each with
    /// its syntax error, in the order of the text (step L1.29d).
    pub skipped: Vec<Range<usize>>,
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

    /// Whether token `i` lies in a declaration the parse skipped. O(log s) for s skipped.
    pub fn skips(&self, i: usize) -> bool {
        let k = self.skipped.partition_point(|r| r.end <= i);
        self.skipped.get(k).is_some_and(|r| r.start <= i)
    }
}

/// Why a parse failed: the furthest token any alternative reached, and what it expected there.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Error {
    /// The span of that token (empty at the end of the text), or of the `..` that [`DOTS`]
    /// is about.
    pub span: Span,
    /// The literals (quoted) and token kinds expected there, each once, in the order the
    /// grammar tries the alternatives that expect them, as the grammar writes them (`'+'`,
    /// `IDENT`); the message names the kinds in the program's words instead.
    pub expected: Vec<String>,
    /// A message that says more than the expected tokens: [`DOTS`] for a `..` in a list.
    pub message: Option<&'static str>,
    /// The row and message for a parse that stopped in a `with` clause that gives a sentinel
    /// value, as `with initial x = 0` or `with x = 0`, or at a reserved word written where a
    /// name stands, as `without = 3;`; `span` is then the span of the item or the word.
    pub clause: Option<Box<Clause>>,
    /// The notes, repairs and names of a failing declaration (step L1.29d), boxed as `clause`
    /// is, so a `Result` that holds an `Error` stays small.
    pub recovery: Box<Recovery>,
}

/// What recovery from a syntax error adds to the [`Error`] of a failing declaration.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Recovery {
    /// Notes beside the message, each a span with its text, outermost first: where the failing
    /// declaration begins and each bracket it leaves open.
    pub notes: Vec<(Span, String)>,
    /// The repairs: each the source line it rewrites, as it reads after the repair, at the
    /// place of the edit; each parses.
    pub repairs: Vec<(Span, String)>,
    /// The names the failing declaration would define had it parsed.
    pub defines: Vec<String>,
}

/// The message for a `..` written in a list with other items, as `(int, ..)`, `#a(int, ..)` or
/// `{x: int, ..}`: the kind-wide types hold `..` alone (DESIGN.md sec:type_language).
pub const DOTS: &str = "`..` stands alone between its brackets: `(..)` is every tuple, `{..}` \
                        every struct and `#a(..)` the atom `#a` with any payload, and no list \
                        with other items holds `..`";

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(c) = &self.clause {
            return f.write_str(&c.message);
        }
        match self.message {
            Some(m) => f.write_str(m),
            None => {
                // In the order of the grammar, each in the program's words, once: `INT`,
                // `FLOAT` and `RAT` are all "a number". O(k log k) for k expected tokens.
                let mut seen = BTreeSet::new();
                let shown: Vec<&str> = self
                    .expected
                    .iter()
                    .map(|e| match KINDS.iter().find(|(name, _)| name == e) {
                        Some((_, words)) => *words,
                        None => e.as_str(),
                    })
                    .filter(|e| seen.insert(*e))
                    .collect();
                f.write_str("expected ")?;
                for (i, e) in shown.iter().enumerate() {
                    if i > 0 {
                        f.write_str(" or ")?;
                    }
                    f.write_str(e)?;
                }
                Ok(())
            }
        }
    }
}

/// Each kind of token the grammar names, by that name, with what a message calls it: the
/// program's words, never the grammar's names. `WILD` is the one token `_`, so it is shown as
/// the literal. `KW` and `OP` are no expected kind: the grammar writes a keyword or an operator
/// as its literal.
const KINDS: [(&str, &str); 9] = [
    ("WILD", "'_'"),
    ("IDENT", "a name"),
    ("INT", "a number"),
    ("FLOAT", "a number"),
    ("RAT", "a number"),
    ("STRING", "a string"),
    ("ATOM", "an atom such as `#name`"),
    ("ANNOT", "an annotation such as `@name`"),
    ("END", "the end of the text"),
];

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

/// The span an error at the end of `text` is reported at.
fn end_of(text: &str) -> Span {
    Span {
        start: text.len(),
        end: text.len(),
    }
}

/// Parses `tokens`, lexed from `text`, as the rule `start` at `ring`, to the end of the tokens.
/// A unit is parsed as [`parse_unit`] does, and its error is the first in the order of the text.
pub fn parse(text: &str, tokens: &[Token], start: &str, ring: u32) -> Result<Tree, Error> {
    parse_to(grammar(), text, tokens, start, ring, end_of(text))
}

/// Parses `tokens`, lexed from `text`, as a unit at `ring`, declaration by declaration: the
/// tree of the declarations that parse, its `skipped` the token ranges of those that do not,
/// and the error of each of those, in the order of the text (step L1.29d). Linear in the unit.
pub fn parse_unit(text: &str, tokens: &[Token], ring: u32) -> (Tree, Vec<Error>) {
    let g = grammar();
    let unit = g.rule("Unit").expect("the grammar has a rule `Unit`");
    let item = g.rule("Item").expect("the grammar has a rule `Item`");
    recover::recovering(g, text, tokens, unit, item, ring, end_of(text))
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
    parse_to(g, text, tokens, start, ring, end_of(text))
}

/// A tree whose holes are being parsed: those left, each with the span of its `}`.
struct Open<'t> {
    tree: Tree,
    holes: std::vec::IntoIter<(&'t [Token], Span)>,
}

/// Parses as `parse` does; `end` is the span reported for an error at the end of `tokens`. A
/// rule `Unit` of a grammar with a rule `Item` is parsed with recovery; any other rule stops at
/// its first failure, in the order of the text, the tree before its holes.
fn parse_to(
    g: &Grammar,
    text: &str,
    tokens: &[Token],
    start: &str,
    ring: u32,
    end: Span,
) -> Result<Tree, Error> {
    let rule = g.rule(start).unwrap_or_else(|| panic!("no rule {start}"));
    if start == "Unit"
        && let Some(item) = g.rule("Item")
    {
        let (tree, errors) = recover::recovering(g, text, tokens, rule, item, ring, end);
        return match errors.into_iter().next() {
            Some(e) => Err(e),
            None => Ok(tree),
        };
    }
    let Open { mut tree, holes } = parse_one(g, text, tokens, rule, ring, end)?;
    tree.holes = parse_holes(g, text, holes.collect(), ring)?;
    Ok(tree)
}

/// The `${…}` holes in the strings of `tokens`, in the order of the text, each with the span of
/// its `}`. O(the tokens and their string parts).
fn holes_of(tokens: &[Token]) -> Vec<(&[Token], Span)> {
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
    holes
}

/// The tree of each hole of `holes`, parsed as an `Expr` with its own holes. Holes nest as deep
/// as the source does, so the open trees are on a stack; the first failure in the order of the
/// text, each tree before its holes, stops the parse.
fn parse_holes<'t>(
    g: &Grammar,
    text: &str,
    holes: Vec<(&'t [Token], Span)>,
    ring: u32,
) -> Result<Vec<Tree>, Error> {
    let mut done = Vec::new();
    if holes.is_empty() {
        return Ok(done);
    }
    let hole = g
        .rule("Expr")
        .expect("the grammar has a rule `Expr` for a string's holes");
    let mut outer = holes.into_iter();
    let mut stack: Vec<Open<'t>> = Vec::new();
    loop {
        let next = match stack.last_mut() {
            Some(top) => top.holes.next(),
            None => outer.next(),
        };
        if let Some((tokens, close)) = next {
            // A hole's tokens end at its `}`, so where the parse expected their end, the
            // program needs that `}`.
            let open = parse_one(g, text, tokens, hole, ring, close).map_err(|mut e| {
                for x in &mut e.expected {
                    if x == "END" {
                        *x = "'}'".into();
                    }
                }
                e
            })?;
            stack.push(open);
            continue;
        }
        let Some(top) = stack.pop() else {
            return Ok(done);
        };
        match stack.last_mut() {
            Some(parent) => parent.tree.holes.push(top.tree),
            None => done.push(top.tree),
        }
    }
}

/// Parses `tokens` as rule `start`, its holes left for [`parse_holes`].
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
        let expected: Vec<String> = p.expected_in_order().iter().map(shown).collect();
        let dots = dots_in_list(&toks, p.far);
        let t = clause::Toks {
            g,
            ring,
            start,
            text,
            tokens,
            toks: &toks,
            end,
        };
        // A boundary clause in a test case first: there the clause is refused whole, not item
        // by item as on a statement.
        let found = case::case_item(&t, p.far).or_else(|| clause::clause(&t, p.far));
        return Err(Error {
            span: span(dots.unwrap_or(p.far)),
            expected,
            message: dots.map(|_| DOTS),
            clause: found.map(Box::new),
            recovery: Box::default(),
        });
    };
    Ok(Open {
        tree: Tree {
            nodes: p.nodes,
            root,
            holes: Vec::new(),
            skipped: Vec::new(),
        },
        holes: holes_of(tokens).into_iter(),
    })
}

/// How an error names what was expected.
fn shown(e: &Expected<'_>) -> String {
    match e {
        Expected::Lit(s) => format!("'{s}'"),
        Expected::Name(n) => (*n).into(),
        Expected::Class => unreachable!("a grammar over tokens holds no character class"),
    }
}
