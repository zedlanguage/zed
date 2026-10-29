//! Statements and blocks (step L1.11): bindings with their targets, and `return`; and
//! declarations (step L1.12): functions with their `test` tables, and the push `p <- e`.

use std::fmt;

use super::{Builder, Error, Expr, ExprKind, Param, Type};
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
    /// A function declaration.
    Function(Function),
    /// `p <- e;`, the whole value `e` pushed to the port `p`.
    Push {
        /// The port.
        port: String,
        /// The value.
        value: Expr,
    },
}

/// A function: `f(params) = e;` or `f(params) { … }`, either followed by `test` tables.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Function {
    /// Its name.
    pub name: String,
    /// Its parameters.
    pub params: Vec<Param>,
    /// Its output ports, `-> (stdout: Lines)`, if declared.
    pub ports: Option<Vec<(String, Type)>>,
    /// Whether its body is an equation `= e`; otherwise it is a block, which may export
    /// nothing, as a `main` that only pushes does.
    pub equation: bool,
    /// Its body.
    pub body: Expr,
    /// The cases of its `test` tables, `input -> expected`, in written order.
    pub tests: Vec<(Expr, Expr)>,
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
    /// The block of node `n`, a `Block`: its statements, of which at most one is a `return`,
    /// and exactly one when `export_needed`, as for a block that is an expression.
    pub(super) fn block(&self, n: usize, export_needed: bool) -> Result<Expr, Error> {
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
        if export_needed && export.is_none() {
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
    pub(super) fn item(&self, n: usize) -> Result<Stmt, Error> {
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
            (11, &[f]) => StmtKind::Function(self.function(f)?),
            (14, &[p]) if self.tree.nodes[p].alt == 1 => {
                let kids = self.kids(p);
                StmtKind::Push {
                    port: self.word(self.tree.nodes[kids[0]].start).into(),
                    value: self.node(kids[1])?,
                }
            }
            (14 | 15, &[k]) => return Err(self.later(k)),
            _ => return Err(self.later(d)),
        };
        Ok(Stmt {
            kind,
            span: self.span(n),
        })
    }

    /// The function of node `n`, a `Function`.
    fn function(&self, n: usize) -> Result<Function, Error> {
        let kids = self.kids(n);
        let (&body, head) = kids.split_last().expect("Function ends in its body");
        let (mut params, mut ports) = (Vec::new(), None);
        for &k in &head[1..] {
            match self.tree.name(k) {
                "Params" => params = self.params(k)?,
                _ if self.tree.nodes[k].alt == 0 => {
                    let port = |p: &usize| {
                        let pk = self.kids(*p);
                        Ok((
                            self.word(self.tree.nodes[pk[0]].start).into(),
                            self.ty(pk[1])?,
                        ))
                    };
                    ports = Some(
                        self.kids(k)
                            .iter()
                            .map(port)
                            .collect::<Result<_, Error>>()?,
                    );
                }
                _ => return Err(self.later(k)),
            }
        }
        let equation = self.word(self.tree.nodes[body].start) == "=";
        let (&first, trailers) = self.kids(body).split_first().expect("a Body has its body");
        let body = if equation {
            self.node(first)?
        } else {
            self.block(first, false)?
        };
        let mut tests = Vec::new();
        for &t in trailers {
            if self.tree.nodes[t].alt != 0 {
                return Err(self.later(t));
            }
            for &c in self.kids(t) {
                let ck = self.kids(c);
                tests.push((self.node(ck[0])?, self.node(ck[1])?));
            }
        }
        Ok(Function {
            name: self.word(self.tree.nodes[kids[0]].start).into(),
            params,
            ports,
            equation,
            body,
            tests,
        })
    }
}

/// `(= (a b) e)`, `(= (_) e)`, `(return a b)`, `(<- p e)`, and a function
/// `(def f (x (y: int)) (-> (stdout: Lines)) = e (test (a b) …))`, the `=` for an equation.
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
            StmtKind::Push { port, value } => write!(f, "(<- {port} {value})"),
            StmtKind::Function(func) => {
                let ps: Vec<String> = func.params.iter().map(|p| p.to_string()).collect();
                write!(f, "(def {} ({})", func.name, ps.join(" "))?;
                if let Some(ports) = &func.ports {
                    let ps: Vec<String> =
                        ports.iter().map(|(n, t)| format!("({n}: {t})")).collect();
                    write!(f, " (-> {})", ps.join(" "))?;
                }
                write!(f, " {}{}", if func.equation { "= " } else { "" }, func.body)?;
                if !func.tests.is_empty() {
                    f.write_str(" (test")?;
                    for (a, b) in &func.tests {
                        write!(f, " ({a} {b})")?;
                    }
                    f.write_str(")")?;
                }
                f.write_str(")")
            }
        }
    }
}
