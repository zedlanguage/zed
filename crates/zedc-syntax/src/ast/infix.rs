//! Infix calls (DESIGN.md sec:power, tier 6; sec:grammar's desugar row `Infix`; author, Q36):
//! `a ~f~ b` is the call `f(a, b)`, with the same resolution, overloads, defaults and errors.
//! The name between the tildes is a plain name; a qualified one, `p ~geometry.plus~ v`, is
//! rejected with the call written out, `geometry.plus(p, v)`.

use super::builder::Builder;
use super::{Error, Expr, ExprKind, Note};
use crate::lex::{Span, Tok};

impl Builder<'_, '_> {
    /// The call that the `Infix` node `n`, `a ~f~ b`, is.
    pub(super) fn infix_call(&mut self, n: usize) -> Result<Expr, Error> {
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
            },
            span: self.span(n),
        })
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
