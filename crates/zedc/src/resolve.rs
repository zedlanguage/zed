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

use std::collections::{BTreeMap, HashMap};

use crate::ast::{Error, Expr, ExprKind, Param, Pattern, Port, Stmt, StmtKind, StrPart, Target};
use crate::ast::{Type, TypeKind};
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
    /// Binders of the unit, by index: one, or the arrows of an overload set.
    Bound(Vec<usize>),
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
}

/// The value words of the prelude, each with the layer it belongs to (DESIGN.md, "Defined
/// words by layer"): at L1 the numeric casts and the `String` functions the documentation
/// uses.
const WORDS: &[(&str, u32)] = &[
    ("int", 1),
    ("rat", 1),
    ("f64", 1),
    ("abs", 1),
    ("len", 1),
    ("lower", 1),
    ("upper", 1),
    ("trim", 1),
    ("sum", 1),
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

/// The type names of the prelude at L1; a unit declares no type before L2.
const TYPES: &[&str] = &["int", "rat", "f64", "bool", "String", "Lines", "Files"];

/// The resolution of `unit`, or every error in it, in text order.
pub fn resolve(unit: &[Stmt]) -> Result<Resolution, Vec<Error>> {
    let mut r = Resolver::default();
    r.scopes.push(HashMap::new());
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
    Bound(Vec<usize>),
    Word(u32),
}

#[derive(Default)]
struct Resolver {
    out: Resolution,
    errors: Vec<Error>,
    /// The scopes, outermost first: each name's binders.
    scopes: Vec<HashMap<String, Vec<usize>>>,
    /// Each function binder's written parameter types, which tell an overload's arrows apart.
    signatures: HashMap<usize, Vec<Option<String>>>,
}

impl Resolver {
    /// Binds `name` in the innermost scope; `signature` is a function's parameter types.
    fn bind(&mut self, name: &str, span: Span, kind: Kind, signature: Option<Vec<Option<String>>>) {
        let id = self.out.binders.len();
        let scope = self.scopes.last_mut().expect("a scope");
        if let Some(ids) = scope.get(name) {
            let first = &self.out.binders[ids[0]];
            let overload = kind == Kind::Function
                && first.kind == Kind::Function
                && ids
                    .iter()
                    .all(|i| self.signatures.get(i) != signature.as_ref());
            if !overload {
                let message = match &signature {
                    Some(_) if first.kind == Kind::Function => format!(
                        "`{name}` is already declared in this scope with these parameter \
                         types, at byte {}",
                        first.span.start
                    ),
                    _ => format!(
                        "`{name}` is already bound in this scope, at byte {}",
                        first.span.start
                    ),
                };
                self.errors.push(Error { span, message });
                return;
            }
        }
        scope.entry(name.into()).or_default().push(id);
        if let Some(s) = signature {
            self.signatures.insert(id, s);
        }
        self.out.binders.push(Binder {
            name: name.into(),
            span,
            kind,
        });
    }

    /// What `name` names here, or `None`.
    fn find(&self, name: &str) -> Option<Found> {
        if let Some(ids) = self.scopes.iter().rev().find_map(|s| s.get(name)) {
            return Some(Found::Bound(ids.clone()));
        }
        WORDS
            .iter()
            .find(|(w, _)| *w == name)
            .map(|&(_, layer)| Found::Word(layer))
    }

    /// Records the use of `name` at `span`, or the error that it names nothing at L1.
    fn name(&mut self, name: &str, span: Span) {
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
        self.errors.push(Error { span, message });
    }

    /// The statements of the innermost scope: their binders first, since order has no meaning.
    fn stmts(&mut self, stmts: &[Stmt]) {
        for s in stmts {
            match &s.kind {
                StmtKind::Bind { targets, .. } => {
                    for t in targets {
                        if let Target::Name(n) = t {
                            self.bind(n, s.span, Kind::Binding, None);
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
                StmtKind::Return(_) | StmtKind::Push { .. } => {}
            }
        }
        for s in stmts {
            match &s.kind {
                StmtKind::Bind { value, .. } => self.expr(value),
                StmtKind::Return(es) => es.iter().for_each(|e| self.expr(e)),
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
            }
        }
    }

    /// A function's or lambda's parameters, ports and body: one scope, which a body block's
    /// statements share.
    fn function(&mut self, params: &[Param], ports: &[Port], body: &Expr) {
        self.scopes.push(HashMap::new());
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
        self.scopes.pop();
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
                self.scopes.push(HashMap::new());
                if let Some(p) = pattern {
                    self.pattern(p);
                }
                self.expr(default);
                self.scopes.pop();
            }
            ExprKind::Block(stmts) => {
                self.scopes.push(HashMap::new());
                self.stmts(stmts);
                self.scopes.pop();
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
                if let Some(Found::Bound(ids)) = self.find(name) {
                    self.out.uses.insert(e.span, Ref::Bound(ids));
                }
            }
        }
    }

    /// The names the pattern `p` binds: each field written `f:` binds `f`.
    fn pattern(&mut self, p: &Pattern) {
        let Pattern::Atom {
            fields,
            items,
            span,
            ..
        } = p;
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
                span: t.span,
                message: format!("the type `{n}` is not defined"),
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
        }
    }
}
