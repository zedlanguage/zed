//! Name resolution (step L1.14): every name a unit uses, tied to the binder it names.
//!
//! A bare name resolves in the order of DESIGN.md sec:units, stopping at the first hit: the
//! block scopes, innermost outward; the unit's top level; the prelude. Imports and qualified
//! names arrive at L2. Statement order has no meaning, so a name bound anywhere in a scope is
//! in scope throughout it. A scope is a block, or a function's or lambda's parameters, which
//! share one scope with the statements of a body block (so `f(x) { x = 1; }` rebinds `x`), or
//! the names an `else` pattern binds, in scope in its default. A parameter's type and default
//! see the parameters (`hi: int where lo <= hi`) but not the body's bindings; a function's
//! `test` cases are read in the scope around the function.
//!
//! Binding a name twice in one scope is an error, except that functions of one name whose
//! written parameter types differ are the arrows of one overload set; a name in a nested scope
//! shadows the outer one. A name that resolves to a prelude word of a later layer is an error
//! naming the layer. A member `x.f` whose `f` is in scope may be a uniform call `f(x)`; its
//! resolution is recorded, and elaboration (step L1.16) tells a field from a function.

use std::collections::{BTreeMap, HashMap, HashSet};
use std::ops::Range;

use imbl::Vector;

use crate::ast::{
    Annot, Error, Expr, ExprKind, Param, Pattern, Port, Stmt, StmtKind, StrPart, Target,
};
use crate::ast::{Note, Type, TypeBound, TypeKind};
use crate::lex::Span;

/// What binds a name.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    /// A binding `x = e;` or a target of `a, b = e;`.
    Binding,
    /// A function declaration.
    Function,
    /// A parameter of a function or a lambda.
    Param,
    /// An output port of a function's header, `-> (stdout: Lines)`.
    Port,
    /// A name an `else` pattern binds, `#a(f:)`.
    Pattern,
}

/// A binder: a name, where it is bound, and what binds it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Binder {
    /// The name.
    pub name: String,
    /// The text that binds it: the statement, the parameter, the port or the pattern.
    pub span: Span,
    /// What binds it.
    pub kind: Kind,
}

/// What a use of a name names.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ref {
    /// Binders of the unit, by index: one, or the arrows of an overload set. The list is
    /// persistent, so every use of a set of `K` arrows shares it: `U` uses cost `O(U)`, not
    /// `O(U·K)`.
    Bound(Vector<usize>),
    /// A prelude word of layer L1.
    Prelude(String),
}

/// The resolution of a unit.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Resolution {
    /// The unit's binders, in the order they are met.
    pub binders: Vec<Binder>,
    /// Each use, by its text: a name, a type name, a push's statement (whose port it names),
    /// or a member whose name is in scope.
    pub uses: BTreeMap<Span, Ref>,
    /// The binders of each `else` pattern, by the `else`'s text: a range of `binders`.
    pub patterns: BTreeMap<Span, Range<usize>>,
    /// Where each declaration statement starts, in every scope: a binding, a function, a
    /// struct, a type, a method, an import, a `mutable`, a piece of an indexed definition, or an
    /// annotated one. A doc comment attaches to the declaration that follows it (DESIGN.md
    /// sec:grammar, comments).
    pub decls: HashSet<usize>,
    /// The unit item `@log(#off);`, if the unit has one: it drops the log lines that every
    /// body of the unit writes (DESIGN.md sec:ports). Step L7.3, which writes the lines, reads it.
    pub log_off: Option<Span>,
}

/// The value words of the prelude, each with the layer it belongs to (DESIGN.md, "Defined
/// words by layer"): at L1 the numeric casts, the `String` cast that interpolation calls, and
/// the `String` functions the documentation uses.
const WORDS: &[(&str, u32)] = &[
    ("String", 1),
    ("int", 1),
    ("rat", 1),
    ("f64", 1),
    ("abs", 1),
    ("len", 1),
    ("lower", 1),
    ("upper", 1),
    ("trim", 1),
    ("sum", 1),
    ("bitAnd", 1),
    ("bitOr", 1),
    ("bitXor", 1),
    ("bitNot", 1),
    ("shl", 1),
    ("shr", 1),
    ("popCount", 1),
    ("leadingZeros", 1),
    ("trailingZeros", 1),
    ("rotl", 1),
    ("rotr", 1),
    ("f64Bits", 1),
    ("count", 3),
    ("map", 3),
    ("where", 3),
    ("foldl", 3),
    ("foldr", 3),
    ("reduce", 3),
    ("allOk", 3),
    ("split", 3),
    ("lines", 3),
    ("concat", 3),
    ("fam", 3),
    ("discard", 3),
    ("fold", 3),
    ("reindex", 3),
    ("gen", 3),
    ("rekey", 4),
    ("group", 4),
    ("flatMap", 4),
    ("tag", 4),
    ("sort", 5),
    ("rank", 5),
    ("scan", 5),
    ("zip", 5),
    ("patch", 5),
    ("join", 5),
    ("diff", 5),
    ("first", 5),
    ("last", 5),
    ("minBy", 5),
    ("maxBy", 5),
    ("slice", 5),
    ("take", 5),
    ("drop", 5),
    ("takeWhile", 5),
    ("chunkBy", 5),
    ("fix", 6),
];

/// The layer of the prelude value word `name`, if it is one.
pub fn prelude_layer(name: &str) -> Option<u32> {
    WORDS
        .iter()
        .find(|(w, _)| *w == name)
        .map(|&(_, layer)| layer)
}

/// Whether `name` is a prelude value word of any layer or a prelude type name.
pub fn is_prelude_name(name: &str) -> bool {
    prelude_layer(name).is_some() || TYPES.contains(&name)
}

/// The annotations, each with the layer it belongs to (DESIGN.md, "Defined words by layer").
/// `@hash`, of layer L2, pins an import and annotates no declaration.
const ANNOTATIONS: &[(&str, u32)] = &[
    ("hash", 2),
    ("foreign", 7),
    ("export", 7),
    ("borrowed", 7),
    ("stateless", 7),
    ("log", 7),
    ("after", 7),
    ("checked", 10),
    ("invariant", 15),
    ("ensure", 15),
    ("proved", 15),
    ("exhaustive", 15),
    ("exact", 15),
    ("strict", 15),
    ("associative", 16),
    ("commutative", 16),
    ("idempotent", 16),
    ("injective", 16),
    ("assume", 16),
    ("measure", 17),
    ("cost", 18),
    ("fused", 18),
    ("memoized", 18),
    ("noalloc", 18),
    ("preallocated", 18),
    ("decides", 22),
    ("require", 24),
];

/// The layer of the annotation `@name`, if it is one.
pub fn annotation_layer(name: &str) -> Option<u32> {
    ANNOTATIONS
        .iter()
        .find(|(w, _)| *w == name)
        .map(|&(_, layer)| layer)
}

/// Whether `a` is written `@name(#off)`, with the one argument `#off`.
fn is_off(a: &Annot) -> bool {
    a.named.is_empty()
        && matches!(&a.positional[..], [Expr { kind: ExprKind::Atom(x), .. }] if x == "off")
}

/// The type names of the prelude at L1; a unit declares no type before L2.
const TYPES: &[&str] = &["int", "rat", "f64", "bool", "String", "Lines", "Files"];

/// The carriers, which a bounded type variable ranges over, in the order the checker prints
/// them.
const CARRIERS: &[&str] = &["int", "f64", "rat", "String", "bool"];

/// The resolution of `unit`, or every error in it, in text order.
pub fn resolve(unit: &[Stmt]) -> Result<Resolution, Vec<Error>> {
    let mut r = Resolver::default();
    r.scopes.push(Vec::new());
    r.walk(Task::Stmts(unit));
    if r.errors.is_empty() {
        Ok(r.out)
    } else {
        r.errors.sort_by_key(|e| e.span);
        Err(r.errors)
    }
}

/// What a name is found to be: binders of the unit, or a prelude word of a layer.
enum Found {
    Bound(Vector<usize>),
    Word(u32),
}

#[derive(Default)]
struct Resolver {
    out: Resolution,
    errors: Vec<Error>,
    /// The scopes, outermost first: the names each binds.
    scopes: Vec<Vec<String>>,
    /// The bindings of each name in the open scopes, innermost last, so a name is found in
    /// `O(1)` however deep the scopes nest.
    visible: HashMap<String, Vec<Bound>>,
    /// The type variables a bounds clause around the type being walked binds, by name.
    tvars: HashMap<String, TypeVar>,
    /// The function types around the type being walked, outermost first, by their text.
    arrows: Vec<Span>,
    /// The bounds clauses around the type being walked, outermost first, by their text.
    clauses: Vec<Span>,
}

/// A type variable of a bounds clause, while its type is walked.
struct TypeVar {
    /// Its text in the clause.
    span: Span,
    /// How many function types were open around the clause.
    depth: usize,
    /// Its first use, and the outermost function type inside the clause that holds the use,
    /// if one does.
    first: Option<(Span, Option<Span>)>,
}

/// A name's binders in one scope.
struct Bound {
    /// How many scopes are open around the scope, itself included.
    level: usize,
    ids: Vector<usize>,
    /// The written parameter types of each, which tell an overload's arrows apart: a set, so
    /// declaring `K` overloads costs `O(K)`, not `O(K²)`.
    signatures: HashSet<Option<Vec<Option<String>>>>,
}

impl Resolver {
    /// Binds `name` in the innermost scope; `signature` is a function's parameter types.
    fn bind(&mut self, name: &str, span: Span, kind: Kind, signature: Option<Vec<Option<String>>>) {
        if name.ends_with('\'') {
            return self.primed(name, span);
        }
        let id = self.out.binders.len();
        let level = self.scopes.len();
        let here = (self.visible.get(name))
            .and_then(|v| v.last())
            .filter(|b| b.level == level);
        if let Some(b) = here {
            let first = &self.out.binders[b.ids[0]];
            let overload = kind == Kind::Function
                && first.kind == Kind::Function
                && !b.signatures.contains(&signature);
            if !overload {
                let (message, note) = match &signature {
                    Some(_) if first.kind == Kind::Function => (
                        format!(
                            "`{name}` is already declared in this scope with these parameter \
                             types"
                        ),
                        format!("the first `{name}` with these parameter types"),
                    ),
                    _ => (
                        format!("`{name}` is already bound in this scope"),
                        format!("the first binding of `{name}`"),
                    ),
                };
                let notes = vec![Note {
                    span: first.span,
                    text: note,
                }];
                self.errors.push(Error {
                    row: None,
                    span,
                    message,
                    notes,
                });
                return;
            }
        }
        let v = self.visible.entry(name.into()).or_default();
        if v.last().is_none_or(|b| b.level != level) {
            v.push(Bound {
                level,
                ids: Vector::new(),
                signatures: HashSet::new(),
            });
            self.scopes.last_mut().expect("a scope").push(name.into());
        }
        let b = v.last_mut().expect("pushed above");
        b.ids.push_back(id);
        b.signatures.insert(signature);
        self.out.binders.push(Binder {
            name: name.into(),
            span,
            kind,
        });
    }

    fn open(&mut self) {
        self.scopes.push(Vec::new());
    }

    /// Closes the innermost scope, so its names name what they named outside it.
    fn close(&mut self) {
        for name in self.scopes.pop().expect("an open scope") {
            let v = self.visible.get_mut(&name).expect("bound in the scope");
            v.pop();
            if v.is_empty() {
                self.visible.remove(&name);
            }
        }
    }

    /// What `name` names here, or `None`.
    fn find(&self, name: &str) -> Option<Found> {
        if let Some(b) = self.visible.get(name).and_then(|v| v.last()) {
            return Some(Found::Bound(b.ids.clone()));
        }
        prelude_layer(name).map(Found::Word)
    }

    /// Records the use of `name` at `span`, or the error that it names nothing at L1.
    fn name(&mut self, name: &str, span: Span) {
        if name.ends_with('\'') {
            return self.primed(name, span);
        }
        let message = match self.find(name) {
            Some(Found::Bound(ids)) => {
                self.out.uses.insert(span, Ref::Bound(ids));
                return;
            }
            Some(Found::Word(1)) => {
                self.out.uses.insert(span, Ref::Prelude(name.into()));
                return;
            }
            Some(Found::Word(layer)) => format!("`{name}` is a prelude word of layer L{layer}"),
            None => format!("`{name}` is not defined"),
        };
        self.errors.push(Error {
            row: None,
            span,
            message,
            notes: Vec::new(),
        });
    }

    /// Does `root` and every task it leads to, in written order. The tasks wait on a stack on
    /// the heap, so a unit of any nesting depth is resolved on a small thread stack; a task
    /// pushes the pieces it leads to in reverse, so they are done, and their binders numbered,
    /// in the order the text gives.
    fn walk<'a>(&mut self, root: Task<'a>) {
        let mut todo = vec![root];
        while let Some(task) = todo.pop() {
            match task {
                Task::Stmts(stmts) => self.stmts(stmts, &mut todo),
                Task::Stmt(s) => self.stmt(s, &mut todo),
                Task::Function {
                    params,
                    ports,
                    body,
                } => self.function(params, ports, body, &mut todo),
                Task::Expr(e) => self.expr(e, &mut todo),
                Task::Ty(t) => self.ty(t, &mut todo),
                Task::Pattern(p) => self.pattern(p, &mut todo),
                Task::BindField(name, span) => self.bind(name, span, Kind::Pattern, None),
                Task::Else {
                    span,
                    pattern,
                    default,
                } => {
                    self.open();
                    todo.push(Task::Close);
                    todo.push(Task::Expr(default));
                    if let Some(p) = pattern {
                        let start = self.out.binders.len();
                        todo.push(Task::PatternEnd(span, start));
                        todo.push(Task::Pattern(p));
                    }
                }
                Task::PatternEnd(span, start) => {
                    let end = self.out.binders.len();
                    self.out.patterns.insert(span, start..end);
                }
                Task::Member(span, name) => {
                    if name.ends_with('\'') {
                        self.later(span, &format!("the primed field `{name}`"), "L6.3");
                    } else if let Some(Found::Bound(ids)) = self.find(name) {
                        self.out.uses.insert(span, Ref::Bound(ids));
                    }
                }
                Task::Close => self.close(),
                Task::ArrowEnd => {
                    self.arrows.pop();
                }
                Task::ForEnd(ty, fresh) => self.for_end(ty, fresh),
            }
        }
    }

    /// The statements of the innermost scope: their binders first, since order has no meaning.
    fn stmts<'a>(&mut self, stmts: &'a [Stmt], todo: &mut Vec<Task<'a>>) {
        let mut families = HashSet::new();
        for s in stmts {
            if !matches!(
                s.kind,
                StmtKind::Return(_)
                    | StmtKind::Push { .. }
                    | StmtKind::While(_)
                    | StmtKind::Until(_)
                    | StmtKind::Expr(_)
                    | StmtKind::UnitAnnot(_)
            ) {
                self.out.decls.insert(s.span.start);
            }
            self.declare(s, false, &mut families);
        }
        todo.extend(stmts.iter().rev().map(Task::Stmt));
    }

    /// Binds the names the statement `s` declares. Resolution refuses the forms of layer L6
    /// whole, but binds their names, so that a use of one is not reported as well; in such a
    /// statement (`whole`) a primed name, a loop step's output, is not bound. The pieces of one
    /// indexed family bind its name once: `families` holds the families bound in this scope.
    fn declare<'s>(&mut self, s: &'s Stmt, whole: bool, families: &mut HashSet<&'s str>) {
        match &s.kind {
            StmtKind::Bind {
                targets, boundary, ..
            } => {
                let whole = whole || !boundary.is_empty();
                for t in targets {
                    match t {
                        Target::Name(n) if whole && n.ends_with('\'') => {}
                        Target::Name(n) => self.bind(n, s.span, Kind::Binding, None),
                        Target::Wild => {}
                    }
                }
            }
            StmtKind::Function(f) => {
                let signature = f
                    .params
                    .iter()
                    .map(|p| p.ty.as_ref().map(|t| t.to_string()));
                self.bind(&f.name, s.span, Kind::Function, Some(signature.collect()));
            }
            // The declaration is not annotated again, and a `mutable` holds a binding, so this
            // recursion is one level deep.
            StmtKind::Annotated { decl, .. } => self.declare(decl, whole, families),
            StmtKind::Mutable(decl) => self.declare(decl, true, families),
            StmtKind::IndexedDef(d) => {
                if !d.name.ends_with('\'') && families.insert(d.name.as_str()) {
                    self.bind(&d.name, s.span, Kind::Binding, None);
                }
            }
            StmtKind::Return(_)
            | StmtKind::Push { .. }
            | StmtKind::Struct(_)
            | StmtKind::Type(_)
            | StmtKind::Method(_)
            | StmtKind::Import(_)
            | StmtKind::While(_)
            | StmtKind::Until(_)
            | StmtKind::Expr(_)
            | StmtKind::UnitAnnot(_) => {}
        }
    }

    /// The statement `s`, whose binders its scope has.
    fn stmt<'a>(&mut self, s: &'a Stmt, todo: &mut Vec<Task<'a>>) {
        match &s.kind {
            StmtKind::Bind { boundary, .. } if !boundary.is_empty() => {
                self.later(s.span, "a boundary `with`", "L6.2")
            }
            StmtKind::Bind { value, .. } => todo.push(Task::Expr(value)),
            StmtKind::Return(es) => todo.extend(es.iter().rev().map(Task::Expr)),
            StmtKind::Push { port, .. } if port.ends_with('\'') => {
                self.later(s.span, "a generation push `x' <- e`", "L6.3")
            }
            StmtKind::Push { port, value } => {
                self.name(port, s.span);
                todo.push(Task::Expr(value));
            }
            StmtKind::Function(f) => {
                let ports: &[Port] = f.ports.as_deref().unwrap_or_default();
                todo.push(Task::Function {
                    params: &f.params,
                    ports,
                    body: &f.body,
                });
                for (a, b) in f.tests.iter().rev() {
                    todo.push(Task::Expr(b));
                    todo.push(Task::Expr(a));
                }
                todo.extend(ports.iter().rev().map(|p| Task::Ty(&p.ty)));
            }
            StmtKind::Struct(_) => self.later(s.span, "a struct declaration", "L2.4"),
            // A primed name is of layer L6 wherever it stands (DESIGN.md sec:grammar).
            StmtKind::Method(m) if m.receiver.ends_with('\'') => self.primed(&m.receiver, s.span),
            StmtKind::Method(m) if m.function.name.ends_with('\'') => {
                self.primed(&m.function.name, s.span)
            }
            StmtKind::Method(_) => self.later(s.span, "a method", "L2.4"),
            StmtKind::Type(_) => self.later(s.span, "a type declaration", "L2.5"),
            StmtKind::Import(_) => self.later(s.span, "an import", "L2.3"),
            StmtKind::Mutable(_) => self.later(s.span, "a `mutable` binding", "L6.3"),
            StmtKind::IndexedDef(_) => self.later(s.span, "an indexed definition", "L6.2"),
            StmtKind::While(_) => self.later(s.span, "a `while` guard", "L6.3"),
            StmtKind::Until(_) => self.later(s.span, "an `until` guard", "L6.3"),
            StmtKind::Expr(_) => self.later(s.span, "an expression statement", "L6.3"),
            StmtKind::Annotated { annots, decl } => {
                annots.iter().for_each(|a| self.annotation(a));
                todo.push(Task::Stmt(decl));
            }
            StmtKind::UnitAnnot(a) => self.unit_annotation(a, s.span),
        }
    }

    /// The annotation `a`. None has a meaning before layer L7, so each is refused with its
    /// reason: it is no annotation, it is `@hash`, which annotates no declaration, or it is of
    /// a later layer.
    fn annotation(&mut self, a: &Annot) {
        let name = &a.name;
        let message = match annotation_layer(name) {
            None => format!("`@{name}` is not an annotation"),
            Some(2) => "`@hash` pins an import and follows its unit path, as in \
                 `import geometry.shapes @hash(\"…\");`; it annotates no declaration"
                .into(),
            Some(layer) => format!("`@{name}` is an annotation of layer L{layer}"),
        };
        self.errors.push(Error {
            row: None,
            span: a.span,
            message,
            notes: Vec::new(),
        });
    }

    /// The unit item `a;`, written as the statement at `span`. Two annotations are unit items:
    /// `@log(#off);`, which this layer accepts, and `@strict;`, of layer L15. Each other way to
    /// write one is refused with its reason.
    fn unit_annotation(&mut self, a: &Annot, span: Span) {
        let name = &a.name;
        let fail = |message: String| Error {
            row: None,
            span,
            message,
            notes: Vec::new(),
        };
        let error = match annotation_layer(name) {
            Some(_) if name == "strict" => return self.annotation(a),
            None | Some(2) => return self.annotation(a),
            Some(_) if name != "log" => fail(format!(
                "`@{name}` annotates a declaration and is not a unit item; write it before \
                 the declaration it annotates"
            )),
            Some(_) if !a.called => fail(
                "`@log;` is not a unit item: `@log` writes a line at each evaluation of the \
                 definition or statement it annotates, and the unit item `@log(#off);` drops \
                 the lines of every body in the unit"
                    .into(),
            ),
            Some(_) if !is_off(a) => fail(
                "the unit item `@log` takes the one argument `#off`, as in `@log(#off);`, \
                 which drops the lines of every body in the unit"
                    .into(),
            ),
            Some(_) if self.scopes.len() > 1 => fail(
                "`@log(#off);` is an item of a unit and stands at its top level, not in a \
                 block; write `@log(#off)` before a function's declaration to drop the lines \
                 of its body"
                    .into(),
            ),
            Some(_) => match self.out.log_off {
                None => return self.out.log_off = Some(span),
                Some(first) => Error {
                    notes: vec![Note {
                        span: first,
                        text: "the first `@log(#off);`".into(),
                    }],
                    ..fail("the unit has `@log(#off);` twice".into())
                },
            },
        };
        self.errors.push(error);
    }

    /// The primed name `name`, which names a loop step's output.
    fn primed(&mut self, name: &str, span: Span) {
        self.later(span, &format!("the primed name `{name}`"), "L6.3");
    }

    /// The form `what`, which the parser builds, has its meaning from step `step`.
    fn later(&mut self, span: Span, what: &str, step: &str) {
        self.errors.push(Error {
            row: None,
            span,
            message: format!("{what} is compiled from step {step}"),
            notes: Vec::new(),
        });
    }

    /// A function's or lambda's parameters, ports and body: one scope, which a body block's
    /// statements share.
    fn function<'a>(
        &mut self,
        params: &'a [Param],
        ports: &'a [Port],
        body: &'a Expr,
        todo: &mut Vec<Task<'a>>,
    ) {
        if let Some(p) = params.iter().find(|p| p.tuple.is_some()) {
            return self.later(p.span, "a tuple-destructuring parameter", "L2.4");
        }
        self.open();
        for p in params {
            self.bind(&p.name, p.span, Kind::Param, None);
        }
        for p in ports {
            self.bind(&p.name, p.span, Kind::Port, None);
        }
        todo.push(Task::Close);
        todo.push(match &body.kind {
            ExprKind::Block(stmts) => Task::Stmts(stmts),
            _ => Task::Expr(body),
        });
        for p in params.iter().rev() {
            todo.extend(p.default.as_ref().map(Task::Expr));
            todo.extend(p.ty.as_ref().map(Task::Ty));
        }
    }

    fn expr<'a>(&mut self, e: &'a Expr, todo: &mut Vec<Task<'a>>) {
        match &e.kind {
            ExprKind::Int { .. }
            | ExprKind::Float(_)
            | ExprKind::Rat(_)
            | ExprKind::Bool(_)
            | ExprKind::Atom(_) => {}
            ExprKind::Str(parts) => todo.extend(parts.iter().rev().filter_map(|p| match p {
                StrPart::Hole(h) => Some(Task::Expr(h)),
                StrPart::Text(_) => None,
            })),
            ExprKind::Name(n) => self.name(n, e.span),
            ExprKind::Unary(_, a) => todo.push(Task::Expr(a)),
            ExprKind::Binary(_, a, b) | ExprKind::Index(a, b) => {
                todo.push(Task::Expr(b));
                todo.push(Task::Expr(a));
            }
            ExprKind::Call {
                callee,
                positional,
                named,
                ..
            } => {
                todo.extend(named.iter().rev().map(|(_, a)| Task::Expr(a)));
                todo.extend(positional.iter().rev().map(Task::Expr));
                todo.push(Task::Expr(callee));
            }
            ExprKind::Tuple(items) => todo.extend(items.iter().rev().map(Task::Expr)),
            ExprKind::Lambda { params, body } => todo.push(Task::Function {
                params,
                ports: &[],
                body,
            }),
            ExprKind::Is { of, ty, .. } => {
                todo.push(Task::Ty(ty));
                todo.push(Task::Expr(of));
            }
            ExprKind::Else {
                of,
                pattern,
                default,
            } => {
                todo.push(Task::Else {
                    span: e.span,
                    pattern: pattern.as_ref(),
                    default,
                });
                todo.push(Task::Expr(of));
            }
            ExprKind::Block(stmts) => {
                self.open();
                todo.push(Task::Close);
                todo.push(Task::Stmts(stmts));
            }
            ExprKind::If {
                cond,
                then,
                otherwise,
            } => {
                todo.push(Task::Expr(otherwise));
                todo.push(Task::Expr(then));
                todo.push(Task::Expr(cond));
            }
            ExprKind::Member { of, name, .. } => {
                todo.push(Task::Member(e.span, name));
                todo.push(Task::Expr(of));
            }
            ExprKind::Record(_) => self.later(e.span, "a record display", "L2.4"),
            ExprKind::With { .. } => self.later(e.span, "a `with` clause", "L2.4"),
            ExprKind::This => self.later(e.span, "`this`", "L2.4"),
            ExprKind::Match { .. } => self.later(e.span, "a `match`", "L2.4"),
            ExprKind::Range(..) => self.later(e.span, "a range", "L3.2"),
            ExprKind::In { .. } => self.later(e.span, "an `in` test", "L3.2"),
            ExprKind::Reduce { .. } => self.later(e.span, "a reduction `><`", "L3.2"),
            ExprKind::Read { .. } => self.later(e.span, "a metadata read `::`", "L3.2"),
            ExprKind::Section(_) => self.later(e.span, "an operator section", "L3.2"),
            ExprKind::Array(_) => self.later(e.span, "an array display", "L3.2"),
            ExprKind::Set(_) => self.later(e.span, "a set display", "L3.2"),
            ExprKind::Map(_) => self.later(e.span, "a map display", "L3.2"),
            ExprKind::For { .. } => self.later(e.span, "a `for`", "L3.2"),
            ExprKind::Loop { .. } => self.later(e.span, "a `loop`", "L6.3"),
            ExprKind::Break(_) => self.later(e.span, "a `break`", "L6.3"),
            ExprKind::Spread { .. } => {
                self.later(e.span, "a call `*.` that writes its receiver", "L6.3")
            }
            ExprKind::SortKey { .. } => self.later(e.span, "a sort key `asc` or `desc`", "L5.1"),
        }
    }

    /// The names the pattern `p` binds: each field written `f:` binds `f`.
    fn pattern<'a>(&mut self, p: &'a Pattern, todo: &mut Vec<Task<'a>>) {
        let Pattern::Atom {
            fields,
            items,
            span,
            ..
        } = p
        else {
            let what = match p {
                Pattern::Is { .. } => "a type pattern `n is T`",
                Pattern::Lit(_) => "a literal pattern",
                Pattern::Range { .. } => return self.later(p.span(), "a range pattern", "L3.2"),
                _ => "a struct, name, `_` or tuple pattern",
            };
            return self.later(p.span(), what, "L2.4");
        };
        todo.extend(items.iter().rev().map(Task::Pattern));
        todo.extend(fields.iter().rev().map(|(f, sub)| match sub {
            Some(sub) => Task::Pattern(sub),
            None => Task::BindField(f, *span),
        }));
    }

    fn ty<'a>(&mut self, t: &'a Type, todo: &mut Vec<Task<'a>>) {
        match &t.kind {
            TypeKind::Name(n) if TYPES.contains(&n.as_str()) => {
                self.out.uses.insert(t.span, Ref::Prelude(n.clone()));
            }
            TypeKind::Name(n) if self.tvars.contains_key(n) => self.type_var(n, t.span),
            TypeKind::Name(n) => self.errors.push(Error {
                row: None,
                span: t.span,
                message: format!("the type `{n}` is not defined"),
                // Inside a clause, the name reads as a type variable its clause forgot.
                notes: self
                    .clauses
                    .last()
                    .map(|&span| Note {
                        span,
                        text: format!(
                            "a type variable is bounded by the clause after its type, as \
                             `for {n} in int | f64`; this clause does not bound `{n}`"
                        ),
                    })
                    .into_iter()
                    .collect(),
            }),
            TypeKind::For { ty, bounds } => {
                // Each bound is read outside the clause, so `for T in U` with `U` bounded
                // around it is no carrier either.
                for b in bounds {
                    self.carriers(&b.name, &b.carriers);
                }
                let mut fresh = Vec::with_capacity(bounds.len());
                for b in bounds {
                    if let Some(outer) = self.tvars.get(&b.name) {
                        self.errors.push(Error {
                            row: None,
                            span: b.span,
                            message: format!("the type variable `{}` is bounded twice", b.name),
                            notes: vec![Note {
                                span: outer.span,
                                text: format!("the first bound of `{}`", b.name),
                            }],
                        });
                        continue;
                    }
                    let var = TypeVar {
                        span: b.span,
                        depth: self.arrows.len(),
                        first: None,
                    };
                    self.tvars.insert(b.name.clone(), var);
                    fresh.push(b);
                }
                self.clauses.push(t.span);
                todo.push(Task::ForEnd(ty, fresh));
                todo.push(Task::Ty(ty));
            }
            TypeKind::Atom(_) => {}
            TypeKind::Tuple(ts) | TypeKind::Union(ts) | TypeKind::And(ts) => {
                todo.extend(ts.iter().rev().map(Task::Ty));
            }
            TypeKind::Diff(a, b) => {
                todo.push(Task::Ty(b));
                todo.push(Task::Ty(a));
            }
            TypeKind::Arrow { params, result, .. } => {
                self.arrows.push(t.span);
                todo.push(Task::ArrowEnd);
                todo.push(Task::Ty(result));
                todo.extend(params.iter().rev().map(|p| Task::Ty(&p.ty)));
            }
            TypeKind::Bounded {
                lower,
                upper,
                result,
            } => {
                self.arrows.push(t.span);
                todo.push(Task::ArrowEnd);
                todo.extend([result, upper, lower].map(|t| Task::Ty(t)));
            }
            TypeKind::Apply(..) => self.later(t.span, "an applied type", "L2.5"),
            TypeKind::AtomApply(..) => self.later(t.span, "an atom type with a payload", "L2.5"),
            TypeKind::Record(_) => self.later(t.span, "a record type", "L2.5"),
            TypeKind::Array(_) => self.later(t.span, "a family type `[T]`", "L3.2"),
        }
    }

    /// A use of the bounded type variable `n` at `span`. Its bound is a bound of the outermost
    /// function type inside its clause that holds it, where a call binds it (DESIGN.md
    /// sec:type_language), so every use stands in that one function type.
    fn type_var(&mut self, n: &str, span: Span) {
        let var = self.tvars.get_mut(n).expect("a bounded variable");
        let home = self.arrows.get(var.depth).copied();
        let first = var.first;
        if first.is_none() {
            var.first = Some((span, home));
        }
        let message = match (home, first) {
            (None, _) => format!(
                "the bounded variable `{n}` stands outside a function type: its bound is a \
                 function type's, which a call binds"
            ),
            // The first use was outside one, and is reported.
            (Some(_), Some((_, None))) => return,
            (Some(h), Some((_, Some(f)))) if h != f => format!(
                "the bounded variable `{n}` stands in two function types: its bound is the bound \
                 of one function type, which a call binds"
            ),
            _ => return,
        };
        let mut notes: Vec<Note> = first
            .map(|(s, _)| Note {
                span: s,
                text: format!("the first use of `{n}`"),
            })
            .into_iter()
            .collect();
        notes.extend(home.or(first.and_then(|(_, h)| h)).map(|f| Note {
            span: f,
            text: "the function type that holds a use".into(),
        }));
        self.errors.push(Error {
            row: None,
            span,
            message,
            notes,
        });
    }

    /// The end of the type `ty` of a bounds clause: the clause closes, each variable of `fresh`
    /// leaves scope, and one the type does not hold is an error.
    fn for_end(&mut self, ty: &Type, fresh: Vec<&TypeBound>) {
        self.clauses.pop();
        for b in fresh {
            let var = self.tvars.remove(&b.name).expect("bound above");
            if var.first.is_none() {
                self.errors.push(Error {
                    row: None,
                    span: b.span,
                    message: format!(
                        "the bound names `{}`, which the type before `for` does not hold",
                        b.name
                    ),
                    notes: vec![Note {
                        span: ty.span,
                        text: "the type".into(),
                    }],
                });
            }
        }
    }

    /// The bound `t` of the type variable `v`: a union of carriers. Unions nest as deep as the
    /// text, so the parts still to read wait on a stack, in written order.
    fn carriers(&mut self, v: &str, t: &Type) {
        let mut todo = vec![t];
        while let Some(t) = todo.pop() {
            self.carrier(v, t, &mut todo);
        }
    }

    /// One part `t` of the bound of `v`; the parts of a union go to `todo`.
    fn carrier<'t>(&mut self, v: &str, t: &'t Type, todo: &mut Vec<&'t Type>) {
        match &t.kind {
            TypeKind::Name(n) if CARRIERS.contains(&n.as_str()) => {
                self.out.uses.insert(t.span, Ref::Prelude(n.clone()));
            }
            TypeKind::Union(ts) => todo.extend(ts.iter().rev()),
            kind => {
                let what = match kind {
                    TypeKind::Name(n) if self.tvars.contains_key(n) => {
                        format!("`{n}` is a type variable")
                    }
                    TypeKind::Name(n) => format!("`{n}` is no carrier"),
                    TypeKind::Atom(a) => format!("`#{a}` is an atom, no carrier"),
                    _ => "this type is no carrier".into(),
                };
                self.errors.push(Error {
                    row: None,
                    span: t.span,
                    message: format!(
                        "the bound of `{v}` is not a union of carriers: {what}; the carriers are \
                         {}",
                        CARRIERS.join(", ")
                    ),
                    notes: Vec::new(),
                });
            }
        }
    }
}

/// A piece of the walk still to do, kept on the walk's stack.
#[derive(Clone, Copy)]
enum Task<'a> {
    Stmts(&'a [Stmt]),
    Stmt(&'a Stmt),
    /// A function's or lambda's parameters, ports and body.
    Function {
        params: &'a [Param],
        ports: &'a [Port],
        body: &'a Expr,
    },
    Expr(&'a Expr),
    Ty(&'a Type),
    Pattern(&'a Pattern),
    /// A pattern field written `f:`, which binds `f` at the pattern's text.
    BindField(&'a str, Span),
    /// An `else` whose `of` is done: its pattern and default, in a scope of their own.
    Else {
        span: Span,
        pattern: Option<&'a Pattern>,
        default: &'a Expr,
    },
    /// The end of the pattern of the `else` at the span: its binders are those from the index.
    PatternEnd(Span, usize),
    /// A member `of.name` whose `of` is done: what `name` names, if anything.
    Member(Span, &'a str),
    /// The end of the innermost scope.
    Close,
    /// The end of a function type, which is no longer open around the place.
    ArrowEnd,
    /// The end of the type of a bounds clause, whose variables are the bounds listed.
    ForEnd(&'a Type, Vec<&'a TypeBound>),
}
