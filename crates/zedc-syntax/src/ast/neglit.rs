//! The row "Prefix `-` on a numeric literal's postfix chain" (DESIGN.md sec:diagnostics, and
//! tier 3 of the precedence table): a postfix chain binds tighter than a prefix `-`, so
//! `-1.abs` parses as `-(1.abs)`, which is `-1`, while it reads as `(-1).abs`. Such an
//! expression parses and is rejected after parsing. The rejection shows the chain and the
//! value each grouping gives, and offers both groupings written out. A chain whose base is
//! grouped, `-(1).abs`, or that is grouped whole, `-(1.abs)`, is not rejected, and neither is
//! a chain whose base is a name, `-x.abs`.

use std::collections::HashSet;

use zed_kernel::num::literal_f64;
use zed_kernel::{Prim, Rat, Term, Value, eval};

use super::builder::Builder;
use super::{Error, Expr, ExprKind, Note};
use crate::lex::Tok;
use zedc_base::interp;
use zedc_base::rejection::Row;

impl Builder<'_, '_> {
    /// The rejection of the `Prefix` node `n`, whose operand built to `operand`, when its
    /// operator is `-` and its operand is a postfix chain whose base is a numeric literal.
    /// The walk down the chain visits each `Postfix` node once, and a `Postfix` node is the
    /// operand of at most one `Prefix`, so the walks of a unit cost its size.
    pub(super) fn negated_literal_chain(&self, n: usize, operand: &Expr) -> Option<Error> {
        let tree = self.tree;
        let node = &tree.nodes[n];
        let chain = node.kids[0];
        if self.op(node.start) != "-" || tree.name(chain) != "Postfix" {
            return None;
        }
        let mut base = chain;
        while tree.name(base) == "Postfix" {
            base = tree.nodes[base].kids[0];
        }
        if tree.name(base) != "Literal"
            || !matches!(
                self.tokens[tree.nodes[base].start].tok,
                Tok::Int { .. } | Tok::Float { .. } | Tok::Rat(_)
            )
        {
            return None;
        }
        let (lit, chain, whole) = (self.span(base), self.span(chain), self.span(n));
        let (num, rest) = (
            &self.text[lit.start..lit.end],
            &self.text[lit.end..chain.end],
        );
        let chain_text = &self.text[chain.start..chain.end];
        let first = format!("(-{num}){rest}");
        let last = format!("-({chain_text})");
        let (v_first, v_last) = self.groupings(operand);
        let which = |v: Option<Result<Value, String>>| match v {
            Some(Ok(v)) => format!(", which is {v}"),
            Some(Err(e)) => format!(", which fails: {e}"),
            None => String::new(),
        };
        let (w_first, w_last) = (which(v_first), which(v_last));
        Some(Error {
            row: Some(Row::PrefixMinus),
            menu: String::new(),
            span: whole,
            message: format!(
                "a prefix `-` stands before a postfix chain whose base is the number \
                 `{num}`, and the chain binds tighter than the `-`, so this is \
                 `{last}`{w_last}, not `{first}`{w_first}. Write the grouping you mean."
            ),
            notes: vec![
                Note {
                    span: lit,
                    text: format!("the chain starts at the numeric literal `{num}`"),
                },
                Note {
                    span: chain,
                    text: format!(
                        "the postfix chain `{chain_text}` binds tighter than a prefix `-` \
                         (precedence tiers 1 and 3)"
                    ),
                },
                Note {
                    span: whole,
                    text: format!("so the `-` applies to the whole chain: `{last}`{w_last}"),
                },
                Note {
                    span: whole,
                    text: format!("repair: `{first}`, the chain started at `-{num}`{w_first}"),
                },
                Note {
                    span: whole,
                    text: format!("repair: `{last}`, the meaning as written{w_last}"),
                },
            ],
        })
    }

    /// The values of the two groupings of `-` and the chain `operand`, the `-` applied to the
    /// literal first and last, when the chain is a numeric literal followed by members that
    /// each name an L1 prelude word that no binder of the unit can shadow; `None` for a chain
    /// with any other suffix, whose value depends on what it names. A value that fails gives
    /// the failure.
    #[allow(clippy::type_complexity)]
    fn groupings(
        &self,
        operand: &Expr,
    ) -> (Option<Result<Value, String>>, Option<Result<Value, String>>) {
        let mut prims = Vec::new();
        let mut e = operand;
        while let ExprKind::Member {
            of,
            name,
            safe: false,
        } = &e.kind
        {
            match interp::prim(name) {
                Some(p) if !self.written_bare(name) => prims.push(p),
                _ => return (None, None),
            }
            e = of;
        }
        let Some(v) = number(e) else {
            return (None, None);
        };
        // `prims` is in the order from the end of the chain back to its base.
        let apply = |t: Term| prims.iter().rev().fold(t, |t, &p| Term::Prim(p, vec![t]));
        let run = |t: Term| eval(&t).map_err(|e| e.to_string());
        let neg = |t: Term| Term::Prim(Prim::Neg, vec![t]);
        (
            Some(run(apply(neg(Term::Lit(v.clone()))))),
            Some(run(neg(apply(Term::Lit(v))))),
        )
    }

    /// Whether `name` is written somewhere in the source as a name that does not follow a
    /// `.`, so that a binder of the unit may give it a meaning other than the prelude word's.
    /// A binder is never written after a `.`. A word inside a comment or a string counts too,
    /// which only leaves the values out. The names are listed once per source, on the first
    /// rejection, in one pass over it.
    fn written_bare(&self, name: &str) -> bool {
        self.bare
            .get_or_init(|| bare_names(self.text))
            .contains(name)
    }
}

/// The names in `text` whose last non-space character before them is not a `.`: each maximal
/// run of letters, digits, `_` and `'` that does not start with a digit.
fn bare_names(text: &str) -> HashSet<&str> {
    let ident = |c: char| c.is_alphanumeric() || c == '_' || c == '\'';
    let mut out = HashSet::new();
    let mut after_dot = false;
    let mut start = None;
    for (i, c) in text.char_indices().chain([(text.len(), ' ')]) {
        match (ident(c), start) {
            (true, None) => start = Some(i),
            (true, Some(_)) => {}
            (false, Some(s)) => {
                let word = &text[s..i];
                if !after_dot && !word.starts_with(|c: char| c.is_ascii_digit()) {
                    out.insert(word);
                }
                start = None;
                after_dot = false;
            }
            (false, None) => {}
        }
        if !ident(c) && !c.is_whitespace() {
            after_dot = c == '.';
        }
    }
    out
}

/// The value of the numeric literal `e`, as elaboration reads it; `None` for any other
/// expression, for a float literal that does not round to a finite non-zero `f64`, and for a
/// literal the system refuses the memory to read, which elaboration reports where it reads
/// the literal. The lexer has removed the `_` from the digits, so they are read where they are.
fn number(e: &Expr) -> Option<Value> {
    match &e.kind {
        ExprKind::Int { radix, digits, .. } => Value::int_text(digits, *radix).ok().flatten(),
        ExprKind::Float { digits, .. } => literal_f64(digits).ok().map(Value::float),
        ExprKind::Rat(s) => Rat::decimal(s).ok().flatten().map(Value::rat),
        _ => None,
    }
}
