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
use crate::ast::{Note, Type, TypeKind};
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

/// The type names of the prelude at L1; a unit declares no type before L2.
const TYPES: &[&str] = &["int", "rat", "f64", "bool", "String", "Lines", "Files"];

/// The resolution of `unit`, or every error in it, in text order.
pub fn resolve(unit: &[Stmt]) -> Result<Resolution, Vec<Error>> {
    let mut r = Resolver::default();
    r.scopes.push(Vec::new());
    r.stmts(unit);
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

    /// The statements of the innermost scope: their binders first, since order has no meaning.
    fn stmts(&mut self, stmts: &[Stmt]) {
        let mut families = HashSet::new();
        for s in stmts {
            if !matches!(
                s.kind,
                StmtKind::Return(_)
                    | StmtKind::Push { .. }
                    | StmtKind::While(_)
                    | StmtKind::Until(_)
                    | StmtKind::Expr(_)
            ) {
                self.out.decls.insert(s.span.start);
            }
            self.declare(s, false, &mut families);
        }
        stmts.iter().for_each(|s| self.stmt(s));
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
            | StmtKind::Expr(_) => {}
        }
    }

    /// The statement `s`, whose binders its scope has.
    fn stmt(&mut self, s: &Stmt) {
        match &s.kind {
            StmtKind::Bind { boundary, .. } if !boundary.is_empty() => {
                self.later(s.span, "a boundary `with`", "L6.2")
            }
            StmtKind::Bind { value, .. } => self.expr(value),
            StmtKind::Return(es) => es.iter().for_each(|e| self.expr(e)),
            StmtKind::Push { port, .. } if port.ends_with('\'') => {
                self.later(s.span, "a generation push `x' <- e`", "L6.3")
            }
            StmtKind::Push { port, value } => {
                self.name(port, s.span);
                self.expr(value);
            }
            StmtKind::Function(f) => {
                let ports: &[Port] = f.ports.as_deref().unwrap_or_default();
                for p in ports {
                    self.ty(&p.ty);
                }
                for (a, b) in &f.tests {
                    self.expr(a);
                    self.expr(b);
                }
                self.function(&f.params, ports, &f.body);
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
                self.stmt(decl);
            }
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
    fn function(&mut self, params: &[Param], ports: &[Port], body: &Expr) {
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
        for p in params {
            if let Some(t) = &p.ty {
                self.ty(t);
            }
            if let Some(d) = &p.default {
                self.expr(d);
            }
        }
        match &body.kind {
            ExprKind::Block(stmts) => self.stmts(stmts),
            _ => self.expr(body),
        }
        self.close();
    }

    fn expr(&mut self, e: &Expr) {
        match &e.kind {
            ExprKind::Int { .. }
            | ExprKind::Float(_)
            | ExprKind::Rat(_)
            | ExprKind::Bool(_)
            | ExprKind::Atom(_) => {}
            ExprKind::Str(parts) => {
                for p in parts {
                    if let StrPart::Hole(h) = p {
                        self.expr(h);
                    }
                }
            }
            ExprKind::Name(n) => self.name(n, e.span),
            ExprKind::Unary(_, a) => self.expr(a),
            ExprKind::Binary(_, a, b) | ExprKind::Index(a, b) => {
                self.expr(a);
                self.expr(b);
            }
            ExprKind::Call {
                callee,
                positional,
                named,
                ..
            } => {
                self.expr(callee);
                positional.iter().for_each(|a| self.expr(a));
                named.iter().for_each(|(_, a)| self.expr(a));
            }
            ExprKind::Tuple(items) => items.iter().for_each(|i| self.expr(i)),
            ExprKind::Lambda { params, body } => self.function(params, &[], body),
            ExprKind::Is { of, ty, .. } => {
                self.expr(of);
                self.ty(ty);
            }
            ExprKind::Else {
                of,
                pattern,
                default,
            } => {
                self.expr(of);
                self.open();
                if let Some(p) = pattern {
                    let start = self.out.binders.len();
                    self.pattern(p);
                    let end = self.out.binders.len();
                    self.out.patterns.insert(e.span, start..end);
                }
                self.expr(default);
                self.close();
            }
            ExprKind::Block(stmts) => {
                self.open();
                self.stmts(stmts);
                self.close();
            }
            ExprKind::If {
                cond,
                then,
                otherwise,
            } => {
                self.expr(cond);
                self.expr(then);
                self.expr(otherwise);
            }
            ExprKind::Member { of, name, .. } => {
                self.expr(of);
                if name.ends_with('\'') {
                    return self.later(e.span, &format!("the primed field `{name}`"), "L6.3");
                }
                if let Some(Found::Bound(ids)) = self.find(name) {
                    self.out.uses.insert(e.span, Ref::Bound(ids));
                }
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
    fn pattern(&mut self, p: &Pattern) {
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
        for (f, sub) in fields {
            match sub {
                Some(sub) => self.pattern(sub),
                None => self.bind(f, *span, Kind::Pattern, None),
            }
        }
        items.iter().for_each(|i| self.pattern(i));
    }

    fn ty(&mut self, t: &Type) {
        match &t.kind {
            TypeKind::Name(n) if TYPES.contains(&n.as_str()) => {
                self.out.uses.insert(t.span, Ref::Prelude(n.clone()));
            }
            TypeKind::Name(n) => self.errors.push(Error {
                row: None,
                span: t.span,
                message: format!("the type `{n}` is not defined"),
                notes: Vec::new(),
            }),
            TypeKind::Atom(_) => {}
            TypeKind::Tuple(ts) | TypeKind::Union(ts) | TypeKind::And(ts) => {
                ts.iter().for_each(|t| self.ty(t));
            }
            TypeKind::Diff(a, b) => {
                self.ty(a);
                self.ty(b);
            }
            TypeKind::Arrow { params, result, .. } => {
                params.iter().for_each(|p| self.ty(&p.ty));
                self.ty(result);
            }
            TypeKind::Bounded {
                lower,
                upper,
                result,
            } => [lower, upper, result].into_iter().for_each(|t| self.ty(t)),
            TypeKind::Apply(..) => self.later(t.span, "an applied type", "L2.5"),
            TypeKind::AtomApply(..) => self.later(t.span, "an atom type with a payload", "L2.5"),
            TypeKind::Record(_) => self.later(t.span, "a record type", "L2.5"),
            TypeKind::Array(_) => self.later(t.span, "a family type `[T]`", "L3.2"),
        }
    }
}
