//! Infix calls (DESIGN.md sec:power, tier 6; sec:grammar's desugar row `Infix`; author, Q36):
//! `a ~f~ b` is the call `f(a, b)`, with the same resolution, overloads, defaults and errors.
//! The name between the tildes is a plain name; a qualified one, `p ~geometry.plus~ v`, is
//! rejected with the call written out, `geometry.plus(p, v)`.
//!
//! An arithmetic operator written without parentheses in an operand is rejected where the text
//! has two readings, that is, where the operator's operand could be the infix call or one of the
//! call's operands (DESIGN.md tier 6 and the row "Arithmetic operator written without
//! parentheses in an operand of an infix call"; orchestrator decision, P13):
//!
//! - in the left operand, a binary operator or a prefix `-` or `!` at its right edge:
//!   `a + b ~f~ c` is `(a + b) ~f~ c` or `a + (b ~f~ c)`, and `-p ~plus~ v` is `(-p) ~plus~ v`
//!   or `-(p ~plus~ v)`;
//! - in the right operand, a binary operator at its left edge: `p ~scale~ k * 2` is
//!   `(p ~scale~ k) * 2` or `p ~scale~ (k * 2)`. A prefix there has one reading, since nothing
//!   before the call can be its operand: `p ~scale~ -1` is `scale(p, -1)` and is accepted.
//!
//! Parentheses leave no node in the syntax tree's expression (sec:grammar's `Group`), so the
//! test reads the parse tree, where a `Group` node is a leaf of this walk.

use super::builder::Builder;
use super::{Error, Expr, ExprKind, Note};
use crate::lex::{Span, Tok};
use zedc_base::rejection::Row;

/// The parse-tree nodes of a binary arithmetic operator, below `Infix` in the grammar.
const BINARY: [&str; 3] = ["Additive", "Multiplicative", "Power"];

impl Builder<'_, '_> {
    /// The call that the `Infix` node `n`, `a ~f~ b`, is.
    pub(super) fn infix_call(&mut self, n: usize) -> Result<Expr, Error> {
        // Shape: see "Why the shape of a node is known" (`ast/mod.rs`), here and at the INFIX
        // token below: the `~Additive` alternative makes no `Infix` node.
        let [l, r] = self.kids(n)[..] else {
            unreachable!("Infix = Infix INFIX Additive | ~Additive")
        };
        // The INFIX token is the one before the right operand.
        let at = self.tree.nodes[r].start - 1;
        let Tok::Infix(f) = &self.tokens[at].tok else {
            unreachable!("Infix = Infix INFIX Additive")
        };
        let name_span = self.tokens[at].span;
        if f.contains('.') {
            return Err(self.qualified(n, l, r, f, name_span));
        }
        if let Some(e) = self.two_readings(n, l, r, f) {
            return Err(e);
        }
        let (a, b) = (self.node(l)?, self.node(r)?);
        Ok(Expr {
            kind: ExprKind::Call {
                callee: Box::new(Expr {
                    kind: ExprKind::Name(f.clone()),
                    span: name_span,
                }),
                positional: vec![a, b],
                named: Vec::new(),
                curry: false,
                infix: true,
            },
            span: self.span(n),
        })
    }

    /// Whether the parse-tree node `n` is a prefix `-` or `!`; `Prefix = AnnotExpr` is not.
    fn is_prefix_op(&self, n: usize) -> bool {
        self.tree.name(n) == "Prefix" && self.tree.name(self.tree.nodes[n].kids[0]) != "AnnotExpr"
    }

    /// The rejection of the infix call `n`, of function `f` and operands `l` and `r`, when an
    /// arithmetic operator in an operand gives the text a second reading (module comment).
    ///
    /// Complexity tradeoff: the walk follows one edge of each operand, so it costs the depth of
    /// that edge. In a chain `a ~f~ b ~g~ c` the left operand of the outer call is the inner
    /// call, where the walk stops at once, so the walks of a chain of n calls cost O(n) plus the
    /// operands' sizes, each edge node visited once. Checking every operator inside an operand
    /// would also reject the ones parentheses already enclose; the edge walk is what the two
    /// readings are made of.
    fn two_readings(&self, n: usize, l: usize, r: usize, f: &str) -> Option<Error> {
        let tree = self.tree;
        // The left operand's right edge: the innermost operator and the leaf next to the call.
        let (mut op, mut x) = (None, l);
        loop {
            if BINARY.contains(&tree.name(x)) {
                let right = tree.nodes[x].kids[1];
                op = Some(tree.nodes[right].start - 1);
                x = right;
            } else if self.is_prefix_op(x) {
                op = Some(tree.nodes[x].start);
                x = tree.nodes[x].kids[0];
            } else {
                break;
            }
        }
        if let Some(op) = op {
            return Some(self.clash(n, l, r, f, op, x, true));
        }
        // The right operand's left edge: only a binary operator there gives a second reading.
        let (mut op, mut x) = (None, r);
        loop {
            if BINARY.contains(&tree.name(x)) {
                // Shape: see "Why the shape of a node is known" (`ast/mod.rs`): each of the
                // three rules' node-building alternatives is operand, operator literal, operand.
                let [left, right] = tree.nodes[x].kids[..] else {
                    unreachable!("a binary arithmetic node has two operands")
                };
                op = Some(tree.nodes[right].start - 1);
                x = left;
            } else if self.is_prefix_op(x) {
                x = tree.nodes[x].kids[0];
            } else {
                break;
            }
        }
        op.map(|op| self.clash(n, l, r, f, op, x, false))
    }

    /// The rejection of the infix call `n` for the operator token `op`, whose operand on the
    /// side of the call is the leaf `x` of the left operand (`left`) or of the right one.
    #[allow(clippy::too_many_arguments)]
    fn clash(
        &self,
        n: usize,
        l: usize,
        r: usize,
        f: &str,
        op: usize,
        x: usize,
        left: bool,
    ) -> Error {
        let text = |s: usize, e: usize| &self.text[s..e];
        let (call, ls, rs, xs) = (self.span(n), self.span(l), self.span(r), self.span(x));
        let (a, b) = (text(ls.start, ls.end), text(rs.start, rs.end));
        let leaf = text(xs.start, xs.end);
        // Each reading as written and as the call it is; the one that starts with `(` first.
        let readings = if left {
            [
                (
                    format!("({}){}", text(call.start, ls.end), text(ls.end, call.end)),
                    format!("{f}({a}, {b})"),
                ),
                (
                    format!(
                        "{}({})",
                        text(call.start, xs.start),
                        text(xs.start, call.end)
                    ),
                    format!("{}{f}({leaf}, {b})", text(call.start, xs.start)),
                ),
            ]
        } else {
            [
                (
                    format!("({}){}", text(call.start, xs.end), text(xs.end, call.end)),
                    format!(
                        "{f}({a}, {}){}",
                        text(rs.start, xs.end),
                        text(xs.end, call.end)
                    ),
                ),
                (
                    format!(
                        "{}({})",
                        text(call.start, rs.start),
                        text(rs.start, call.end)
                    ),
                    format!("{f}({a}, {b})"),
                ),
            ]
        };
        let written = text(call.start, call.end);
        let sym = self.op(op);
        let at = self.tokens[op].span;
        let [(first, first_call), (second, second_call)] = &readings;
        Error {
            row: Some(Row::InfixOperand),
            menu: String::new(),
            span: at,
            message: format!("Infix call next to `{sym}`: `{written}`. Try `{first}` instead."),
            notes: vec![
                Note {
                    span: call,
                    text: format!(
                        "the two readings give different calls: `{first}` is `{first_call}`, \
                         and `{second}` is `{second_call}`"
                    ),
                },
                Note {
                    span: call,
                    text: format!("repair: `{first}`"),
                },
                Note {
                    span: call,
                    text: format!("repair: `{second}`"),
                },
            ],
        }
    }

    /// The rejection of the infix call `n`, whose function `f`, written at `at`, is qualified.
    fn qualified(&self, n: usize, l: usize, r: usize, f: &str, at: Span) -> Error {
        let text = |s: Span| &self.text[s.start..s.end];
        let (written, a, b) = (text(self.span(n)), text(self.span(l)), text(self.span(r)));
        let repair = format!("{f}({a}, {b})");
        Error {
            row: None,
            menu: String::new(),
            span: at,
            message: format!(
                "Qualified name in an infix call: `{written}`. Try `{repair}` instead."
            ),
            notes: vec![
                Note {
                    span: at,
                    text: "an infix call names its function by a plain name; a qualified \
                           function is called in the ordinary way"
                        .into(),
                },
                Note {
                    span: at,
                    text: format!("repair: `{repair}`"),
                },
            ],
        }
    }
}
