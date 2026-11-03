//! Statements and blocks (step L1.11): bindings with their targets, and `return`; and
//! declarations (step L1.12): functions with their `test` tables, and the push `p <- e`; and
//! from step L2.1, the declarations of structs, of types, and of methods `T.m`.

use std::collections::HashMap;

use super::{Builder, Built, Error, Expr, ExprKind, Note, Param, Type};
use crate::lex::Span;

/// A statement and its span.
#[derive(Debug)]
pub struct Stmt {
    /// What it is.
    pub kind: StmtKind,
    /// Its text, its `;` included.
    pub span: Span,
}

/// The kinds of statement.
#[derive(Debug)]
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
    /// A struct declaration.
    Struct(Struct),
    /// A type declaration.
    Type(TypeDecl),
    /// A method declaration.
    Method(Method),
}

/// `struct Point { x: f64, y: f64 = 0.0, import geometry.Named }`.
#[derive(Debug)]
pub struct Struct {
    /// Its name.
    pub name: String,
    /// Its fields, in written order.
    pub fields: Vec<Field>,
}

/// A field of a struct.
#[derive(Debug)]
pub enum Field {
    /// `x: T`, or `x: T = e` with a default.
    Typed {
        /// Its name.
        name: String,
        /// Its type.
        ty: Type,
        /// Its default, if written.
        default: Option<Expr>,
        /// Its text.
        span: Span,
    },
    /// `import geometry.Named`: the fields of the struct or interface of that path.
    Import {
        /// The path, joined by `.`.
        path: String,
        /// Its text.
        span: Span,
    },
}

/// `type Shape = Circle | Square;` or `type Tree(T) = #leaf | #node(l: Tree(T), r: Tree(T));`:
/// a name for a type, which may name itself, with its type parameters.
#[derive(Debug)]
pub struct TypeDecl {
    /// Its name.
    pub name: String,
    /// Its type parameters, in written order.
    pub params: Vec<String>,
    /// The type it names.
    pub ty: Type,
}

/// A method `T.m(params) = e;`, the function `T.m` whose receiver `this: T` is its first,
/// positional parameter; or `T.m = e;` with no parentheses, a constant member of `T`.
#[derive(Debug)]
pub struct Method {
    /// The receiver's type, `T`.
    pub receiver: String,
    /// Whether its parameters are written in parentheses, `T.m()` rather than `T.m`.
    pub called: bool,
    /// The method: its name `m`, its written parameters, which do not include the receiver,
    /// and its body.
    pub function: Function,
}

/// A function: `f(params) = e;` or `f(params) { … }`, either followed by `test` tables.
#[derive(Debug)]
pub struct Function {
    /// Its name.
    pub name: String,
    /// Its parameters.
    pub params: Vec<Param>,
    /// Its output ports, `-> (stdout: Lines)`, if declared.
    pub ports: Option<Vec<Port>>,
    /// Whether its body is an equation `= e`; otherwise it is a block, which may export
    /// nothing, as a `main` that only pushes does.
    pub equation: bool,
    /// Its body.
    pub body: Expr,
    /// The cases of its `test` tables, `input -> expected`, in written order.
    pub tests: Vec<(Expr, Expr)>,
}

/// An output port of a function's header: `stdout: Lines`.
#[derive(Debug)]
pub struct Port {
    /// Its name.
    pub name: String,
    /// Its type.
    pub ty: Type,
    /// Its text.
    pub span: Span,
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
    /// The block of node `n`, a `Block`: its statements, of which at most one is a `return`.
    /// The export is stored last, where the formatter writes it (step L1.13); the order of the
    /// others is kept. Whether it must export is for what takes it (`Builder::node`).
    pub(super) fn block(&mut self, n: usize) -> Result<Expr, Error> {
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
                        message: "a block exports once".into(),
                        notes: vec![Note {
                            span: first,
                            text: "the block's first export".into(),
                        }],
                    });
                }
                export = Some(s.span);
            }
            stmts.push(s);
        }
        if let Some(i) = stmts
            .iter()
            .position(|s| matches!(s.kind, StmtKind::Return(_)))
        {
            let export = stmts.remove(i);
            stmts.push(export);
        }
        Ok(Expr {
            kind: ExprKind::Block(stmts),
            span: self.span(n),
        })
    }

    /// The statement node `n`, an `Item`, built to.
    pub(super) fn item(&mut self, n: usize) -> Result<Stmt, Error> {
        match self.take(n) {
            Some(Ok(Built::Stmt(s))) => Ok(*s),
            Some(Err(e)) => Err(e),
            Some(Ok(Built::Expr(_) | Built::Type(_) | Built::Pattern(_))) | None => {
                Err(self.later(n))
            }
        }
    }

    pub(super) fn make_item(&mut self, n: usize) -> Result<Stmt, Error> {
        let d = self.kids(n)[0];
        let kids = self.kids(d);
        let kind = match self.tree.name(d) {
            "Return" => StmtKind::Return(
                kids.iter()
                    .map(|&k| self.node(k))
                    .collect::<Result<_, _>>()?,
            ),
            "PlainBinding" => {
                let (&value, targets) = kids.split_last().expect("PlainBinding ends in a value");
                StmtKind::Bind {
                    targets: targets.iter().map(|&t| self.target(t)).collect(),
                    value: self.node(value)?,
                }
            }
            "Function" => StmtKind::Function(self.function(d, 0)?),
            "Method" => StmtKind::Method(Method {
                receiver: self.word(self.tree.nodes[kids[0]].start).into(),
                called: self.word(self.tree.nodes[kids[1]].end) == "(",
                function: self.function(d, 1)?,
            }),
            "Struct" if self.tree.layer(d) == 2 => StmtKind::Struct(self.structure(d)?),
            "TypeDecl" => {
                let (&ty, head) = kids.split_last().expect("TypeDecl ends in its type");
                let mut params = Vec::new();
                if let Some(&ps) = head.get(1) {
                    let mut seen = HashMap::new();
                    for &p in self.kids(ps) {
                        let name = self.word(self.tree.nodes[p].start);
                        self.once(&mut seen, name, p, "type parameter", "declared")?;
                        params.push(name.to_string());
                    }
                }
                StmtKind::Type(TypeDecl {
                    name: self.word(self.tree.nodes[kids[0]].start).into(),
                    params,
                    ty: self.ty(ty)?,
                })
            }
            "WholePush" => StmtKind::Push {
                port: self.word(self.tree.nodes[kids[0]].start).into(),
                value: self.node(kids[1])?,
            },
            _ => return Err(self.later(d)),
        };
        Ok(Stmt {
            kind,
            span: self.span(n),
        })
    }

    /// The target of node `n`, a `Target`: a name or `_`.
    pub(super) fn target(&self, n: usize) -> Target {
        match self.kids(n) {
            [_] => Target::Name(self.word(self.tree.nodes[n].start).into()),
            _ => Target::Wild,
        }
    }

    /// The struct of node `n`, a `Struct`; a field declared twice, or a path imported twice,
    /// is an error.
    fn structure(&mut self, n: usize) -> Result<Struct, Error> {
        let (&name, kids) = self
            .kids(n)
            .split_first()
            .expect("Struct = 'struct' Name …");
        let mut fields = Vec::with_capacity(kids.len());
        let (mut names, mut paths) = (HashMap::new(), HashMap::new());
        for &k in kids {
            // A `StructField` is a field with a default, or holds a `Field`.
            let (f, default) = match self.kids(k) {
                [f] => (*f, None),
                [_, _, d] => (k, Some(*d)),
                _ => unreachable!("StructField = Name ':' Type '=' Expr | Field"),
            };
            let fk = self.kids(f);
            let span = self.span(k);
            if self.tree.name(fk[0]) == "Path" {
                let p = &self.tree.nodes[fk[0]];
                let path =
                    &self.text[self.tokens[p.start].span.start..self.tokens[p.end - 1].span.end];
                self.once(&mut paths, path, fk[0], "import", "written")?;
                let path = (p.start..p.end).step_by(2).map(|i| self.word(i));
                fields.push(Field::Import {
                    path: path.collect::<Vec<_>>().join("."),
                    span,
                });
            } else {
                let name = self.word(self.tree.nodes[fk[0]].start);
                self.once(&mut names, name, fk[0], "field", "declared")?;
                fields.push(Field::Typed {
                    name: name.into(),
                    ty: self.ty(fk[1])?,
                    default: default.map(|d| self.node(d)).transpose()?,
                    span,
                });
            }
        }
        Ok(Struct {
            name: self.word(self.tree.nodes[name].start).into(),
            fields,
        })
    }

    /// The function of node `n`, a `Function`, or a `Method` when `skip` is 1: its name is
    /// its kid `skip`, after the receiver's.
    fn function(&mut self, n: usize, skip: usize) -> Result<Function, Error> {
        let kids = self.kids(n);
        let (&body, head) = kids.split_last().expect("Function ends in its body");
        let (mut params, mut ports) = (Vec::new(), None);
        for &k in &head[skip + 1..] {
            match self.tree.name(k) {
                "Params" => params = self.params(k)?,
                "Ports" => {
                    let mut list = Vec::new();
                    for &p in self.kids(k) {
                        let pk = self.kids(p);
                        list.push(Port {
                            name: self.word(self.tree.nodes[pk[0]].start).into(),
                            ty: self.ty(pk[1])?,
                            span: self.span(p),
                        });
                    }
                    ports = Some(list);
                }
                _ => return Err(self.later(k)),
            }
        }
        let equation = self.word(self.tree.nodes[body].start) == "=";
        let (&first, trailers) = self.kids(body).split_first().expect("a Body has its body");
        let body = if equation {
            self.node(first)?
        } else {
            self.body(first)?
        };
        let mut tests = Vec::new();
        for &t in trailers {
            if self.tree.name(t) != "TestTable" {
                return Err(self.later(t));
            }
            for &c in self.kids(t) {
                let ck = self.kids(c);
                tests.push((self.node(ck[0])?, self.node(ck[1])?));
            }
        }
        Ok(Function {
            name: self.word(self.tree.nodes[kids[skip]].start).into(),
            params,
            ports,
            equation,
            body,
            tests,
        })
    }
}
