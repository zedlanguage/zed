//! The row "Display in body position" (DESIGN.md sec:diagnostics, and the brace rules of
//! sec:lexical): a brace after a signature, `if`, `else`, `loop`, `for`, a lambda's `->` or a
//! match arm's `->` is a block whatever it contains, so a display there is written in
//! parentheses. Two braces there read as a display and are rejected after parsing: one that
//! `Block`'s second alternative parses as a `Display` (a top-level comma, a field `name: e`,
//! or an entry `k -> v` whose key is not a lambda's parameters), and a block whose whole
//! content is one unparenthesized lambda, `{ k -> v }`, which reads as the one-entry map.
//! The rejection names the form whose body the brace is, the comma or entry that reads as a
//! display, and offers the display in parentheses and the block with its value grouped.
//!
//! The check reads the top level of one brace: the node's alternative, and for a block its
//! one child and that child's rule, so it costs O(1) per brace. A rejection lists the parent
//! of every node once, in one walk of the tree, to name the form the brace is the body of.

use super::builder::Builder;
use super::{Error, Expr, Note};
use crate::lex::Span;
use zedc_base::rejection::Row;

/// What in a brace reads as a display.
enum Reading {
    /// One unparenthesized lambda, the brace's whole content.
    Lambda,
    /// A display that `Block`'s `Display` alternative parsed: whether it is a record, whether a
    /// map, and its entries' token ranges.
    Display {
        record: bool,
        map: bool,
        entries: Vec<(usize, usize)>,
    },
}

impl Builder<'_, '_> {
    /// The block of node `n`, a `Block`, or the rejection of a display in its place.
    pub(super) fn body_block(&mut self, n: usize) -> Result<Expr, Error> {
        let tree = self.tree;
        let node = &tree.nodes[n];
        let reading = match node.kids[..] {
            // `Block = … | Display`: the display's own build is not needed.
            [d] if node.alt == 1 => {
                self.take(d);
                Some(Reading::Display {
                    record: tree.layer(d) == 2,
                    map: tree.nodes[d]
                        .kids
                        .first()
                        .is_some_and(|&e| self.kids(e).len() == 2),
                    entries: self.entries(d),
                })
            }
            [e] if tree.name(e) == "Expr" && tree.name(self.kids(e)[0]) == "Lambda" => {
                Some(Reading::Lambda)
            }
            _ => None,
        };
        match reading {
            None => self.block(n),
            Some(r) => Err(self.display_in_body(n, &r)),
        }
    }

    /// The token ranges of the entries of the `Display` node `d`. A record's field is its
    /// `Name` node, then its value's node when one follows the `:`; a family's entry is its
    /// `Entry` node.
    fn entries(&self, d: usize) -> Vec<(usize, usize)> {
        let tree = self.tree;
        let kids = &tree.nodes[d].kids;
        if tree.layer(d) != 2 {
            return kids
                .iter()
                .map(|&k| (tree.nodes[k].start, tree.nodes[k].end))
                .collect();
        }
        let mut out: Vec<(usize, usize)> = Vec::new();
        for &k in kids {
            let (start, end) = (tree.nodes[k].start, tree.nodes[k].end);
            match out.last_mut() {
                // A value starts at the token after its field's `:`.
                Some(last) if last.1 == start => last.1 = end,
                _ => out.push((start, end + 1)),
            }
        }
        out
    }

    /// The rejection of the brace `n`, which reads as `reading`.
    fn display_in_body(&self, n: usize, reading: &Reading) -> Error {
        let tree = self.tree;
        let node = &tree.nodes[n];
        let brace = self.span(n);
        let text =
            |s: usize, e: usize| &self.text[self.tokens[s].span.start..self.tokens[e - 1].span.end];
        let tok_span = |i: usize| self.tokens[i].span;
        let range_span = |s: usize, e: usize| Span {
            start: self.tokens[s].span.start,
            end: self.tokens[e - 1].span.end,
        };
        let written = text(node.start, node.end);
        let contents = text(node.start + 1, node.end - 1);
        let position = self.body_of(n);
        let site = Note {
            span: tok_span(node.start - 1),
            text: format!(
                "the brace follows {position}, so it is a block whatever it contains (sec:lexical)"
            ),
        };
        let display = |kind: &str| Note {
            span: brace,
            text: format!("repair: `({written})`, the {kind} display in parentheses"),
        };
        let (message, notes) = match reading {
            Reading::Lambda => (
                format!(
                    "a brace after {position} whose one content is the lambda `{contents}`: \
                     a brace there is a block, so this is a block whose value is that lambda, \
                     while `{written}` reads as a one-entry map; write the reading you mean"
                ),
                vec![
                    site,
                    Note {
                        span: range_span(node.start + 1, node.end - 1),
                        text: format!(
                            "`{contents}` reads as a map entry `key -> value`; in a block it \
                             is a lambda, and the block's value"
                        ),
                    },
                    display("map"),
                    Note {
                        span: brace,
                        text: format!(
                            "repair: `{{ ({contents}) }}`, the block whose value is the lambda"
                        ),
                    },
                ],
            ),
            Reading::Display {
                record,
                map,
                entries,
            } => {
                let kind = if *record {
                    "record"
                } else if *map {
                    "map"
                } else {
                    "set"
                };
                let (first_start, first_end) = entries[0];
                let cause = if self.word(first_end) == "," {
                    Note {
                        span: tok_span(first_end),
                        text: "a comma at the top level of the brace separates the entries of \
                               a display; a block separates its statements with `;`"
                            .into(),
                    }
                } else {
                    let entry = text(first_start, first_end);
                    let what = if *record {
                        "a record field, `name: value`"
                    } else {
                        "a map entry, `key -> value`"
                    };
                    Note {
                        span: range_span(first_start, first_end),
                        text: format!("`{entry}` is {what}, not an expression"),
                    }
                };
                let block = if *record || *map {
                    "repair: a block, its statements ended by `;` and its value one expression \
                     written last; an entry `name: value` or `key -> value` is not an expression"
                        .to_string()
                } else if let [(s, e)] = entries[..] {
                    let one = text(s, e);
                    format!("repair: `{{ {one} }}`, the block whose value is `{one}`")
                } else {
                    let items = text(first_start, entries[entries.len() - 1].1);
                    format!("repair: `{{ ({items}) }}`, the block whose value is the tuple")
                };
                (
                    format!(
                        "a {kind} display in body position: the brace after {position} is a \
                         block whatever it contains, and `{written}` reads as a {kind} \
                         display; write the reading you mean"
                    ),
                    vec![
                        site,
                        cause,
                        display(kind),
                        Note {
                            span: brace,
                            text: block,
                        },
                    ],
                )
            }
        };
        Error {
            row: Some(Row::DisplayInBody),
            menu: String::new(),
            span: brace,
            message,
            notes,
        }
    }

    /// The form whose body the brace `n` is, as a message names it.
    fn body_of(&self, n: usize) -> &'static str {
        let tree = self.tree;
        let parents = self.parents.get_or_init(|| {
            // One walk from the root lists each node's parent; the parser's abandoned nodes are
            // not reached, so none of them is taken for a parent.
            let mut parents = vec![usize::MAX; tree.nodes.len()];
            let mut stack = vec![tree.root];
            while let Some(k) = stack.pop() {
                for &c in &tree.nodes[k].kids {
                    parents[c] = k;
                    stack.push(c);
                }
            }
            parents
        });
        let Some(&p) = parents.get(n).filter(|&&p| p != usize::MAX) else {
            return "a body position";
        };
        match tree.name(p) {
            "If" if tree.nodes[p].kids[1] == n => "the head of an `if`",
            "If" => "the `else` of an `if`",
            "ElseTail" => "a fallback's `else`",
            "Lambda" => "a lambda's `->`",
            "Arm" => "a match arm's `->`",
            "For" => "the head of a `for`",
            "Loop" => "`loop`",
            "Body" => "a signature",
            "Proof" => "`proof`",
            _ => "a body position",
        }
    }
}
