//! Statements and blocks (step L1.11): bindings with their targets, and `return`.

use std::fmt;

use super::{Builder, Error, Expr, ExprKind};
use crate::lex::Span;

/// A statement and its span.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stmt {
    /// What it is.
    pub kind: StmtKind,
    /// Its text, its `;` included.
    pub span: Span,
}

/// The kinds of statement.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StmtKind {
    /// `a = e;`, or `a, b = e;` destructuring a tuple.
    Bind {
        /// The targets, in order.
        targets: Vec<Target>,
        /// The value.
        value: Expr,
    },
    /// `return e;` or `return a, b;`, the block's export; a trailing expression is `return e;`.
    Return(Vec<Expr>),
}

/// A binding target.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Target {
    /// A name bound.
    Name(String),
    /// `_`, the component discarded.
    Wild,
}

impl Builder<'_> {
    /// The block of node `n`, a `Block`: its statements, of which exactly one is a `return`.
    pub(super) fn block(&self, n: usize) -> Result<Expr, Error> {
        let mut stmts = Vec::new();
        let mut export: Option<Span> = None;
        for &k in self.kids(n) {
            let s = if self.tree.name(k) == "Item" {
                self.item(k)?
            } else {
                let e = self.node(k)?;
                Stmt {
                    span: e.span,
                    kind: StmtKind::Return(vec![e]),
                }
            };
            if let StmtKind::Return(_) = s.kind {
                if let Some(first) = export {
                    return Err(Error {
                        span: s.span,
                        message: format!(
                            "a block exports once; its export is already at byte {}",
                            first.start
                        ),
                    });
                }
                export = Some(s.span);
            }
            stmts.push(s);
        }
        let span = self.span(n);
        if export.is_none() {
            return Err(Error {
                span,
                message: "this block exports nothing: end it with an expression or `return e;`"
                    .into(),
            });
        }
        Ok(Expr {
            kind: ExprKind::Block(stmts),
            span,
        })
    }

    /// The statement of node `n`, an `Item`.
    fn item(&self, n: usize) -> Result<Stmt, Error> {
        let node = &self.tree.nodes[n];
        if node.alt != 3 {
            return Err(self.later(n));
        }
        let d = node.kids[0];
        let kids = self.kids(d);
        let kind = match (self.tree.nodes[d].alt, kids) {
            (7, _) => StmtKind::Return(
                kids.iter()
                    .map(|&k| self.node(k))
                    .collect::<Result<_, _>>()?,
            ),
            (15, &[b]) if self.tree.nodes[b].alt == 1 => {
                let (&value, targets) = self.kids(b).split_last().expect("Binding ends in a value");
                StmtKind::Bind {
                    targets: targets
                        .iter()
                        .map(|&t| match self.kids(t) {
                            [_] => Target::Name(self.word(self.tree.nodes[t].start).into()),
                            _ => Target::Wild,
                        })
                        .collect(),
                    value: self.node(value)?,
                }
            }
            (11 | 14 | 15, &[k]) => return Err(self.later(k)),
            _ => return Err(self.later(d)),
        };
        Ok(Stmt {
            kind,
            span: self.span(n),
        })
    }
}

/// `(= (a b) e)`, `(= (_) e)`, `(return a b)`.
impl fmt::Display for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            StmtKind::Bind { targets, value } => {
                let ts: Vec<&str> = targets
                    .iter()
                    .map(|t| match t {
                        Target::Name(n) => n.as_str(),
                        Target::Wild => "_",
                    })
                    .collect();
                write!(f, "(= ({}) {value})", ts.join(" "))
            }
            StmtKind::Return(es) => {
                f.write_str("(return")?;
                for e in es {
                    write!(f, " {e}")?;
                }
                f.write_str(")")
            }
        }
    }
}
