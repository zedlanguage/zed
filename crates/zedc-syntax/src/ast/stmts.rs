//! Statements and blocks (step L1.11): bindings with their targets, and `return`; and
//! declarations (step L1.12): functions with their `test` tables, and the push `p <- e`; and
//! from step L2.1, the declarations of structs, of types, and of methods `T.m`; and from step
//! L2.2, imports with their `@hash` pins, and the annotations `@name` written before a
//! declaration; and from step L6.1, the guards `while c;` and `until c;`, `mutable x = e;`,
//! indexed definitions `x[i in s] = e;`, boundary values `with x = e0` after a binding or an
//! indexed definition, and expression statements `e;`; and from step L7.3, the unit items
//! `@name;` and `@name(args);`, as `@log(#off);`.

use std::collections::HashMap;

use super::builder::{Builder, Built};
use super::{
    Annot, BoundaryItem, Error, Expr, ExprKind, Field, Function, Import, ImportKind, IndexKey,
    IndexedDef, Method, Note, Port, Stmt, StmtKind, Struct, TypeDecl,
};
use crate::lex::{Part, Span, Tok};
use zedc_base::address::ContentAddress;

impl Builder<'_, '_> {
    /// The block of node `n`, a `Block`: its statements, of which at most one is a `return`.
    /// The statements are stored in the order the formatter writes them (`StmtKind::place`):
    /// the `while` guards first, then the `until` guards and the export last; the order of the
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
                        row: None,
                        span: s.span,
                        message: "this block exports a second time, and a block exports one value, once. \
                                  Remove one of the two exports."
                            .into(),
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
        stmts.sort_by_key(|s| s.kind.place());
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
        let kind = match self.tree.name(d) {
            "Annotated" => self.annotated(d)?,
            "UnitAnnot" => StmtKind::UnitAnnot(self.annot(self.kids(d)[0])?),
            _ => self.decl(d)?,
        };
        Ok(Stmt {
            kind,
            span: self.span(n),
        })
    }

    /// The annotations and declaration of node `n`, an `Annotated`. An annotation with
    /// parentheses is an `Annot` node; a bare one is an `ANNOT` token of `n` itself.
    fn annotated(&mut self, n: usize) -> Result<StmtKind, Error> {
        let (&d, nodes) = self.kids(n).split_last().expect("Annotated ends in a Decl");
        let mut annots = Vec::new();
        let mut nodes = nodes.iter().peekable();
        let mut i = self.tree.nodes[n].start;
        while i < self.tree.nodes[d].start {
            if let Some(&a) = nodes.next_if(|&&a| self.tree.nodes[a].start == i) {
                annots.push(self.annot(a)?);
                i = self.tree.nodes[a].end;
                continue;
            }
            let Tok::Annot(name) = &self.tokens[i].tok else {
                unreachable!("Annotated = (Annot | ANNOT)+ Decl")
            };
            annots.push(Annot {
                name: name.clone(),
                called: false,
                positional: Vec::new(),
                named: Vec::new(),
                span: self.tokens[i].span,
            });
            i += 1;
        }
        let decl = Stmt {
            kind: self.decl(d)?,
            span: self.span(d),
        };
        Ok(StmtKind::Annotated {
            annots,
            decl: Box::new(decl),
        })
    }

    /// The annotation of node `n`, an `Annot`: `@name`, or `@name(args)`, whose arguments do
    /// not end in `...`, since an annotation is not a call that can be curried.
    fn annot(&mut self, n: usize) -> Result<Annot, Error> {
        let node = &self.tree.nodes[n];
        let Tok::Annot(name) = &self.tokens[node.start].tok else {
            unreachable!("Annot = ANNOT …")
        };
        let (positional, named) = match node.kids[..] {
            [] => (Vec::new(), Vec::new()),
            [args] => match self.args(args, self.span(n))? {
                (_, _, true) => {
                    return Err(Error {
                        row: None,
                        span: self.span(n),
                        message: format!(
                            "the arguments of `@{name}` end in `...`, and only a call takes `...`, to \
                             leave its other arguments open; an annotation is given all of its \
                             arguments. Remove the `...`."
                        ),
                        notes: Vec::new(),
                    });
                }
                (positional, named, false) => (positional, named),
            },
            _ => unreachable!("Annot = ANNOT ('(' Args? ')')?"),
        };
        Ok(Annot {
            name: name.clone(),
            called: node.end - node.start > 1,
            positional,
            named,
            span: self.span(n),
        })
    }

    /// The import of node `n`, an `Import`: its path, what it binds, and its pin.
    fn import(&mut self, n: usize) -> Result<Import, Error> {
        let kids = self.kids(n);
        let (pin, kids) = match kids.split_last() {
            Some((&p, rest)) if self.tree.name(p) == "Pin" => (Some(self.pin(p)?), rest),
            _ => (None, kids),
        };
        let p = &self.tree.nodes[kids[0]];
        let path = (p.start..p.end).step_by(2).map(|i| self.word(i));
        let path = path.collect::<Vec<_>>().join(".");
        let kind = match &kids[1..] {
            // `import u.{a, b}`: the path is followed by `.`.
            names if self.word(p.end) == "." => {
                let mut seen = HashMap::new();
                let mut out = Vec::with_capacity(names.len());
                for &k in names {
                    let name = self.word(self.tree.nodes[k].start);
                    self.once(&mut seen, name, k, "name", "imported")?;
                    out.push(name.to_string());
                }
                ImportKind::Selective(out)
            }
            [alias] => ImportKind::Alias(self.word(self.tree.nodes[*alias].start).into()),
            _ => ImportKind::Qualified,
        };
        Ok(Import { path, kind, pin })
    }

    /// The content address of node `n`, a `Pin`: `@hash("…")` with 64 lowercase hexadecimal
    /// digits written out in the string.
    fn pin(&self, n: usize) -> Result<ContentAddress, Error> {
        let node = &self.tree.nodes[n];
        let fail = |span: Span, message: String| {
            Err(Error {
                row: None,
                span,
                message,
                notes: Vec::new(),
            })
        };
        let Tok::Annot(name) = &self.tokens[node.start].tok else {
            unreachable!("Pin = ANNOT '(' STRING ','? ')'")
        };
        if name != "hash" {
            return fail(
                self.tokens[node.start].span,
                format!("an import is pinned with `@hash`, not `@{name}`"),
            );
        }
        let string = &self.tokens[node.start + 2];
        let Tok::Str(parts) = &string.tok else {
            unreachable!("Pin = ANNOT '(' STRING ','? ')'")
        };
        let mut hex = String::new();
        for p in parts {
            match p {
                Part::Text(t) => hex.push_str(t),
                Part::Hole { .. } => {
                    return fail(
                        string.span,
                        "the hash of a pin is written out; it has no `${…}` hole".into(),
                    );
                }
            }
        }
        if let Some(c) = hex.chars().find(|c| !matches!(c, '0'..='9' | 'a'..='f')) {
            return fail(
                string.span,
                format!("a hash is written in lowercase hexadecimal digits, and {c:?} is not one"),
            );
        }
        match ContentAddress::parse(&hex) {
            Some(a) => Ok(a),
            None => fail(
                string.span,
                format!(
                    "a hash has 64 hexadecimal digits, and this one has {}",
                    hex.len()
                ),
            ),
        }
    }

    /// The statement kind of node `d`, a declaration.
    fn decl(&mut self, d: usize) -> Result<StmtKind, Error> {
        let kids = self.kids(d);
        Ok(match self.tree.name(d) {
            "Return" => StmtKind::Return(
                kids.iter()
                    .map(|&k| self.node(k))
                    .collect::<Result<_, _>>()?,
            ),
            "PlainBinding" => {
                let (kids, boundary) = self.boundary(kids)?;
                let (&value, targets) = kids.split_last().expect("PlainBinding ends in a value");
                StmtKind::Bind {
                    targets: targets.iter().map(|&t| self.target(t)).collect(),
                    value: self.node(value)?,
                    boundary,
                }
            }
            "Mutable" => StmtKind::Mutable(Box::new(Stmt {
                kind: self.decl(kids[0])?,
                span: self.span(kids[0]),
            })),
            // `local local d` parses; the chain is walked in a loop, the declaration at its end
            // built, and the chain wrapped around it from the inside out.
            "Local" => {
                let mut chain = vec![d];
                let mut inner = kids[0];
                while self.tree.name(inner) == "Local" {
                    chain.push(inner);
                    inner = self.kids(inner)[0];
                }
                let mut kind = self.decl(inner)?;
                let mut span = self.span(inner);
                for &l in chain.iter().rev() {
                    kind = StmtKind::Local(Box::new(Stmt { kind, span }));
                    span = self.span(l);
                }
                return Ok(kind);
            }
            "IndexedDef" => {
                let (kids, boundary) = self.boundary(kids)?;
                let [name, keys @ .., value] = kids else {
                    unreachable!("IndexedDef = Name ('[' IndexKey ']')+ '=' Expr Boundary? ';'")
                };
                StmtKind::IndexedDef(IndexedDef {
                    name: self.word(self.tree.nodes[*name].start).into(),
                    keys: self.keys(keys)?,
                    value: self.node(*value)?,
                    boundary,
                })
            }
            "While" => StmtKind::While(self.node(kids[0])?),
            "Until" => StmtKind::Until(self.node(kids[0])?),
            "ExprStmt" => StmtKind::Expr(self.node(kids[0])?),
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
            "Import" => StmtKind::Import(self.import(d)?),
            _ => return Err(self.later(d)),
        })
    }

    /// The kids of a declaration that may end in a `Boundary`, without it, and the boundary
    /// values it holds.
    fn boundary<'k>(
        &mut self,
        kids: &'k [usize],
    ) -> Result<(&'k [usize], Vec<BoundaryItem>), Error> {
        let Some((&b, rest)) = kids
            .split_last()
            .filter(|&(&b, _)| self.tree.name(b) == "Boundary")
        else {
            return Ok((kids, Vec::new()));
        };
        let mut items = Vec::new();
        for &item in self.kids(b) {
            let [name, keys @ .., value] = self.kids(item) else {
                unreachable!("BoundaryItem = Name ('[' IndexKey ']')* '=' Expr")
            };
            items.push(BoundaryItem {
                name: self.word(self.tree.nodes[*name].start).into(),
                keys: self.keys(keys)?,
                value: self.node(*value)?,
                span: self.span(item),
            });
        }
        Ok((rest, items))
    }

    /// The keys of `IndexKey` nodes: `i in s`, or a key expression.
    fn keys(&mut self, keys: &[usize]) -> Result<Vec<IndexKey>, Error> {
        keys.iter()
            .map(|&k| {
                Ok(match *self.kids(k) {
                    [name, set] => IndexKey::In {
                        name: self.word(self.tree.nodes[name].start).into(),
                        set: self.node(set)?,
                    },
                    [e] => IndexKey::At(self.node(e)?),
                    _ => unreachable!("IndexKey = Name 'in' Expr | Expr"),
                })
            })
            .collect()
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
                "Params" => params = self.params(k, self.span(n))?,
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
