//! Statements and blocks (step L1.11): bindings with their targets, and `return`; and
//! declarations (step L1.12): functions with their `test` tables, and the push `p <- e`; and
//! from step L2.1, the declarations of structs, of types, and of methods `T.m`; and from step
//! L2.2, imports with their `@hash` pins, and the annotations `@name` written before a
//! declaration; and from step L6.1, the guards `while c;` and `until c;`,
//! indexed definitions `x[i in s] = e;` with their boundary entries
//! `with x[k] = e0`, the start values `initial x = e;` with their `with carryForward`, and expression statements `e;`; and from step L7.3, the unit items
//! `@name;` and `@name(args);`, as `@log(#off);`.

use std::collections::{HashMap, HashSet};

use super::builder::{Builder, Built, MAIN_INPUTS, MAIN_OUTPUTS};
use super::{
    Annot, BoundaryItem, Error, Expr, ExprKind, Field, Function, Import, ImportKind, IndexKey,
    IndexedDef, Initial, MainHeader, Method, Note, Param, Port, PortName, PortValue, Stmt,
    StmtKind, Struct, TestPorts, Type, TypeDecl, TypeKind, TypeParam,
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
                        menu: String::new(),
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
        self.initials_placed(Some(n), &stmts)?;
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
                        menu: String::new(),
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
                menu: String::new(),
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
                let (&value, targets) = kids.split_last().expect("PlainBinding ends in a value");
                StmtKind::Bind {
                    targets: targets.iter().map(|&t| self.target(t)).collect(),
                    value: self.node(value)?,
                }
            }
            "Initial" => {
                // `Carry`, when written, is the third kid; the word is read from the grammar's rule,
                // not from the text.
                let (target, value, carry) = match *kids {
                    [target, value] => (target, value, false),
                    [target, value, _] => (target, value, true),
                    _ => unreachable!("Initial = 'initial' InitTarget '=' Expr Carry? ';'"),
                };
                let kids = self.kids(target);
                let (mut names, mut ty, mut keys) = (Vec::new(), None, Vec::new());
                match self.tree.name(kids[kids.len() - 1]) {
                    "Type" => {
                        names.push(self.name_of(kids[0]));
                        ty = Some(self.ty(kids[1])?);
                    }
                    "IndexKey" => {
                        names.push(self.name_of(kids[0]));
                        keys = self.keys(&kids[1..])?;
                    }
                    _ => names.extend(kids.iter().map(|&k| self.name_of(k))),
                }
                StmtKind::Initial(Box::new(Initial {
                    names,
                    ty,
                    keys,
                    value: self.node(value)?,
                    carry,
                }))
            }
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
                port: self.push_target(kids[0])?,
                value: self.node(kids[1])?,
            },
            "Import" => StmtKind::Import(self.import(d)?),
            _ => return Err(self.later(d)),
        })
    }

    /// The name of node `n`, a `Name`, and its text.
    fn name_of(&self, n: usize) -> (String, Span) {
        (self.word(self.tree.nodes[n].start).into(), self.span(n))
    }

    /// The kids of an indexed definition, which may end in a `Boundary`, without it, and the
    /// boundary entries it holds.
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
                unreachable!("BoundaryItem = Name ('[' IndexKey ']')+ '=' Expr")
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

    /// The struct of node `n`, a `Struct`; a field declared twice is an error. A path imported
    /// again is kept once, at its first import: it brings in the same fields, and a field
    /// brought in twice with equal forms is one field at its first place (DESIGN.md
    /// sec:introspection).
    fn structure(&mut self, n: usize) -> Result<Struct, Error> {
        let (&name, kids) = self
            .kids(n)
            .split_first()
            .expect("Struct = 'struct' Name …");
        let mut fields = Vec::with_capacity(kids.len());
        let (mut names, mut paths) = (HashMap::new(), HashSet::new());
        for &k in kids {
            // Type parameters (`struct S(A) {…}`) and an import with type arguments
            // (`import P(A)`) are read by the parser and built at step L2.5.
            if self.tree.name(k) == "TypeParams" {
                return Err(self.later(k));
            }
            // A law member (`law ordered() = lo <= hi`) is read by the parser and built at
            // step L12.0; `law` is a keyword, so no field begins with it.
            if self.word(self.tree.nodes[k].start) == "law" {
                return Err(self.later_as(k, "the struct law member"));
            }
            // Any other `StructField` is a field with a default, an import with type arguments,
            // or holds a `Field`.
            let (f, default) = match self.kids(k) {
                [f] if self.tree.name(*f) == "TypeApply" => return Err(self.later(k)),
                [f] => (*f, None),
                [_, _, d] => (k, Some(*d)),
                _ => unreachable!("StructField = Name ':' Type '=' Expr | Field"),
            };
            let fk = self.kids(f);
            let span = self.span(k);
            if self.tree.name(fk[0]) == "Path" {
                // A path is its words, so `a.B`, `a .B` and `a . B` are one path, and a repeat
                // of a path is dropped. O(1) per import: one hash lookup keyed by its words,
                // in time linear in their length.
                let p = &self.tree.nodes[fk[0]];
                let words: Vec<&str> = (p.start..p.end).step_by(2).map(|i| self.word(i)).collect();
                let path = words.join(".");
                if paths.insert(words) {
                    fields.push(Field::Import { path, span });
                }
            } else {
                let field = self.word(self.tree.nodes[fk[0]].start);
                if let Err(mut e) = self.once(&mut names, field, fk[0], "field", "declared") {
                    e.message = format!(
                        "the struct `{}` has the field `{field}` twice, and a struct has each \
                         field once. Remove one of the two.",
                        self.word(self.tree.nodes[name].start)
                    );
                    return Err(e);
                }
                fields.push(Field::Typed {
                    name: field.into(),
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
        let name: String = self.word(self.tree.nodes[kids[skip]].start).into();
        let is_main = skip == 0 && name == "main";
        let (mut params, mut result) = (Vec::new(), None);
        for &k in &head[skip + 1..] {
            match self.tree.name(k) {
                "Params" => params = self.params(k, self.span(n))?,
                // Any result type but `int` is rejected naming `int`, a form this zedc does not
                // compile yet as well, as the old `-> (stdout: Lines)`, after the parameter,
                // whose message says where each old input is read now ([`Self::main_header`]).
                "Result" if is_main => {
                    let t = self.kids(k)[0];
                    result = Some(match self.ty(t) {
                        Ok(r) if matches!(&r.kind, TypeKind::Name(n) if n == "int") => Ok(r),
                        _ => Err(self.span(t)),
                    });
                }
                "Result" => return Err(self.later_as(k, "the declared result type")),
                _ => return Err(self.later(k)),
            }
        }
        let (params, main) = match is_main {
            true => {
                let (params, header) = self.main_header(params, result, self.span(body))?;
                (params, Some(Box::new(header)))
            }
            false => (params, None),
        };
        let equation = self.word(self.tree.nodes[body].start) == "=";
        let (&first, trailers) = self.kids(body).split_first().expect("a Body has its body");
        let body = if equation {
            self.node(first)?
        } else {
            self.body(first)?
        };
        let mut tests = Vec::new();
        let mut given = Vec::new();
        for &t in trailers {
            if self.tree.name(t) != "TestTable" {
                return Err(self.later(t));
            }
            let (ports, rows) = match self.kids(t).split_first() {
                Some((&p, rows)) if self.tree.name(p) == "TestPorts" => (Some(p), rows),
                _ => (None, self.kids(t)),
            };
            let first = tests.len();
            for &c in rows {
                let ck = self.kids(c);
                tests.push((self.node(ck[0])?, self.node(ck[1])?));
            }
            if let Some(p) = ports {
                given.push(TestPorts {
                    rows: first..tests.len(),
                    ports: self.test_ports(p, is_main)?,
                });
            }
        }
        Ok(Function {
            name,
            params,
            main,
            equation,
            body,
            tests,
            given,
        })
    }

    /// The ports of the `TestPorts` node `p`, `with p = e, …`, on a table of `main` when
    /// `is_main` (DESIGN.md sec:ports, "A test table gives a port its values"). A field of
    /// `main` is checked here: on `main`'s table, `main::stdin`, `main::args`, `main::env` and
    /// `main::files` are the inputs a row's key gives, and any other field is rejected. Every
    /// function reads `main::files` (QUESTIONS A68), so any table may give it; the outputs, and
    /// the other inputs on another function's table, are not compiled yet, since this zedc
    /// compares the outputs by a row's value and a function other than `main` reads the other
    /// inputs by `main::args`, of layer L3. A name is left to the resolver, which knows what the unit
    /// defines. A port given twice in one clause is rejected.
    fn test_ports(&mut self, p: usize, is_main: bool) -> Result<Vec<PortValue>, Error> {
        let mut out: Vec<PortValue> = Vec::new();
        // Complexity tradeoff: a search of the ports before each one costs O(ports²) per
        // clause; a map from each port given to its text costs O(1) per port.
        let mut seen: HashMap<String, Span> = HashMap::new();
        for &pv in self.kids(p) {
            let (name, value) = (self.kids(pv)[0], self.kids(pv)[1]);
            let node = &self.tree.nodes[name];
            let span = self.span(name);
            let port = match node.end - node.start {
                1 => PortName::Name(self.word(node.start).to_string(), span),
                _ => {
                    let field = self.word(node.end - 1).to_string();
                    match field.as_str() {
                        // Every function reads the file port as `main::files` (A68).
                        "files" => PortName::Main(field, span),
                        _ if !is_main => {
                            return Err(self.later_as(
                                name,
                                "in the table of a function other than `main`, a test clause \
                                 giving",
                            ));
                        }
                        "stdin" | "args" | "env" => PortName::Main(field, span),
                        "stdout" | "stderr" => {
                            return Err(self.later_as(name, "a test clause giving"));
                        }
                        _ => {
                            let repair = |f: &str| Note {
                                span,
                                text: format!("repair: `main::{f} = …`"),
                            };
                            return Err(Error {
                                row: None,
                                menu: String::new(),
                                span,
                                message: format!(
                                    "`main::{field}` in `test with` is not a port of `main`"
                                ),
                                notes: ["stdin", "args", "env", "files"].map(repair).to_vec(),
                            });
                        }
                    }
                }
            };
            if let Some(&twice) = seen.get(&port.to_string()) {
                return Err(Error {
                    row: None,
                    menu: String::new(),
                    span,
                    message: format!("`{port}` is given twice in this `test with`"),
                    notes: vec![Note {
                        span: twice,
                        text: format!(
                            "`{port}` is first given here; repair: remove one of the two"
                        ),
                    }],
                });
            }
            seen.insert(port.to_string(), span);
            out.push(PortValue {
                port,
                value: self.node(value)?,
            });
        }
        Ok(out)
    }

    /// The parameters and ports the rest of the compiler runs `main` with, from its written
    /// header `main(m: MainArgs) -> int` (DESIGN.md sec:ports, step L1.19), whose body is the
    /// text `body`: an input parameter for each field of `m` the body reads and for
    /// `main::files` when any function of the text reads it, named as written (`m.stdin`), and an output port for each field it pushes
    /// to (`m.stdout`), in the order of `MainArgs`; and the header as written. Or why the
    /// header is not one `main` may have: a second parameter, a parameter of another type,
    /// or a default value; then a result other than `int`, written at the span `result` holds
    /// ([`main_result_error`]).
    fn main_header(
        &self,
        params: Vec<Param>,
        result: Option<Result<Type, Span>>,
        body: Span,
    ) -> Result<(Vec<Param>, MainHeader), Error> {
        // A short headline that shows the piece written and the header `main` takes, the rule
        // in the notes, each at `span` (DESIGN.md sec:diagnostics, "A short headline").
        let error = |span: Span, message: String, notes: &[String]| Error {
            row: None,
            menu: String::new(),
            span,
            message,
            notes: (notes.iter())
                .map(|text| Note {
                    span,
                    text: text.clone(),
                })
                .collect(),
        };
        let written = |s: Span| &self.text[s.start..s.end];
        let mut params = params.into_iter();
        let param = params.next();
        if let Some(second) = params.next() {
            let first = param.as_ref().expect("a first parameter");
            let m = &first.name;
            return Err(error(
                second.span,
                format!(
                    "Second parameter of `main`: `{}`. Try `main({m}: MainArgs)` instead.",
                    written(second.span)
                ),
                &[
                    format!(
                        "`main` takes one argument, of type `MainArgs`, which holds every input \
                         and output of the program: `{m}.args` (the words after `--`), \
                         `{m}.stdin` (standard input), `{m}.env` (the environment), \
                         `{m}.stdout` and `{m}.stderr`"
                    ),
                    format!(
                        "what `{}` read is read through `{m}`: `{m}.args`, `{m}.stdin` or \
                         `{m}.env`; files are read with `main::files`, and the clock with \
                         `clock(period: …)`",
                        second.name
                    ),
                ],
            ));
        }
        if let Some(p) = &param {
            let main_args = match &p.ty {
                None => true,
                Some(t) => matches!(&t.kind, TypeKind::Name(n) if n == "MainArgs"),
            };
            if !main_args {
                return Err(error(
                    p.span,
                    format!(
                        "Parameter of `main` that is not a `MainArgs`: `{}`. Try \
                         `main(m: MainArgs)` instead.",
                        written(p.span)
                    ),
                    &main_param_notes(self.text, p),
                ));
            }
            if p.default.is_some() {
                let kept = match &p.ty {
                    Some(t) => format!("{}: {}", p.name, written(t.span)),
                    None => p.name.clone(),
                };
                return Err(error(
                    p.span,
                    format!(
                        "Default value on the parameter of `main`: `{}`. Try `main({kept})` \
                         instead.",
                        written(p.span)
                    ),
                    &[
                        "`main` is called once, when the program starts, with the program's \
                       inputs and outputs: its argument is never left out"
                            .to_string(),
                    ],
                ));
            }
        }
        let result = (result.transpose()).map_err(|span| main_result_error(self.text, span))?;
        let main = self.mains.of(body).expect("a main's body is in the table");
        let (mut inputs, outputs) = *main.uses.borrow();
        // A read of `main::files` in another function opens the port as a read in the body does;
        // the parameter stands at the body's read when there is one.
        let files = MAIN_INPUTS.len() - 1;
        inputs[files] = inputs[files].or(self.mains.outside(body));
        let m = param.as_ref().map(|p| p.name.as_str());
        let named = |field: &str| match (field, m) {
            ("main::files", _) | (_, None) => field.to_string(),
            (_, Some(m)) => format!("{m}.{field}"),
        };
        // `MainArgs` declares each field's type, so the type sits at the parameter's type as
        // written (or at the parameter, when it has none), where a derivation shows it; in
        // `main()`, with no parameter, at the empty span where the body first uses the field.
        let declared = (param.as_ref()).map(|p| p.ty.as_ref().map_or(p.span, |t| t.span));
        let at = |span: Span| {
            declared.unwrap_or(Span {
                start: span.start,
                end: span.start,
            })
        };
        let name = |n: &str, span: Span| Type {
            kind: TypeKind::Name(n.into()),
            span,
        };
        let mut synth = Vec::new();
        for (field, used) in MAIN_INPUTS.iter().zip(&inputs) {
            let Some(span) = *used else { continue };
            let ty = match *field {
                "args" => name("CommandLine", at(span)),
                "stdin" => name("Lines", at(span)),
                "main::files" => name("Files", at(span)),
                _ => Type {
                    kind: TypeKind::Arrow {
                        params: vec![TypeParam {
                            name: None,
                            positional: false,
                            ty: name("String", at(span)),
                        }],
                        partial: true,
                        result: Box::new(name("String", at(span))),
                    },
                    span: at(span),
                },
            };
            synth.push(Param {
                name: named(field),
                tuple: None,
                positional: false,
                ty: Some(ty),
                default: None,
                span,
                name_at: span,
            });
        }
        let mut ports = Vec::new();
        for (field, used) in MAIN_OUTPUTS.iter().zip(&outputs) {
            let Some(span) = *used else { continue };
            ports.push(Port {
                name: named(field),
                ty: name("Lines", at(span)),
                span,
            });
        }
        let header = MainHeader {
            param: param.map(|p| (p.name, p.span, p.ty)),
            result,
            ports,
        };
        Ok((synth, header))
    }
}

/// The error for a result type other than `int` declared on `main`, written at `span`: a
/// short headline with the type written and `int`, the rule in the notes.
fn main_result_error(text: &str, span: Span) -> Error {
    let written = &text[span.start..span.end];
    let note = |text: &str| Note {
        span,
        text: text.into(),
    };
    Error {
        row: None,
        menu: String::new(),
        span,
        notes: vec![
            note(
                "`main` gives an `int`, the program's exit status, 0 for success; a body that \
                 exports nothing gives 0, so the result may be left out",
            ),
            note(
                "the program writes lines with a push to `m.stdout`, as `m.stdout <- lines;`, \
                 with `main(m: MainArgs)`",
            ),
        ],
        message: format!("Result of `main` that is not an `int`: `{written}`. Try `int` instead."),
    }
}

/// The notes for the parameter `p` of `main` in `text`, whose type is not `MainArgs`: what
/// `main` takes, and where each input an old header named a parameter for is read now.
fn main_param_notes(text: &str, p: &Param) -> Vec<String> {
    let name = &p.name;
    let ty =
        p.ty.as_ref()
            .expect("a parameter with a type other than MainArgs");
    let written = &text[ty.span.start..ty.span.end];
    let takes = "`main` takes one argument, of type `MainArgs`, which holds every input and \
                 output of the program; the program's output is pushed to `m.stdout`"
        .to_string();
    let read = match &ty.kind {
        TypeKind::Name(n) if n == "Lines" => "`m.stdin`, the lines of standard input",
        TypeKind::Name(n) if n == "CommandLine" => {
            "`m.args`, the words after `--` on the command line"
        }
        TypeKind::Name(n) if n == "Files" => "`main::files`, which reads files by path",
        TypeKind::Arrow { partial: true, .. } => "`m.env`, the environment variables by name",
        _ => {
            return vec![
                takes,
                format!(
                    "the `{written}` that `{name}` held is computed in the body, from `m.args` \
                     (the words after `--`), `m.stdin` (standard input) or `m.env` (the \
                     environment)"
                ),
            ];
        }
    };
    vec![
        takes,
        format!("what `{name}` read is read from {read}, where `{name}` is written now"),
    ]
}
