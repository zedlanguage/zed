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
mod tree;

pub use clause::{Clause, RESERVED};
pub use engine::{Expected, Input, Node, Parser, literal_matches};
pub use grammar::{Alt, Expr, Grammar, Kind, Line, Rule, is_space, marked_rule, split_line};

pub use tree::{DOTS, Error, Recovery, Tree, grammar};
use tree::{Open, parse_holes, parse_one};

use crate::lex::{Span, Token};

/// The highest layer, and the ring at which every alternative is tried.
pub const TOP: u32 = 29;

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
