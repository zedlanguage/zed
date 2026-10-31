//! The checker (step L1.26): resolution rules 1, 3 and 4 of DESIGN.md "Resolution". Each
//! node is typed bottom up; an `is` test narrows the name it tests in each branch it guards;
//! each declared function gets a signature from its body. A numeric literal adopts the
//! carrier an operator or a parameter expects, exactly or not at all (sec:domains). A lambda
//! in a slot of function type takes its parameter types and kinds from that type, and a
//! declared function passed there must have its parameter kinds.
//!
//! A function's parameter with neither a type nor a closed default is inferred, with the body
//! checked once (docs/thresholds.md, replacement 1). The parameter's values form a class, a
//! node of a union-find forest, holding the carriers it may still take. A use that needs two
//! values to share a carrier, as the operands of `+` do, merges their classes; a use that
//! accepts some carriers removes the rest; a literal joins the class it meets. Each step only
//! merges classes or removes carriers, so the solution is reached by propagation with no
//! search. When the function ends, each class of its parameters takes its type: the first of
//! int, f64 and rat if it holds a literal, which then adopts it; a type variable if it may
//! take any value; its one carrier; a type variable bounded by its carriers if several; and an
//! error if none, listing every use that removed one.
//!
//! Where DESIGN.md does not say: a type variable used as a tuple or a function gives the
//! unknown, so `first(p) = p[0]` is generic, and a non-tuple argument fails at run time; an
//! atom passes through the operators and the prelude words, as the kernel's primitives pass
//! it, but not through a declared function, which binds it; a call matching several arrows
//! takes the first one's result.
//!
//! Step L1.27: an atom of a named family is data (sec:failure). `else` strips only the loose
//! atoms, and a family atom that selects no arrow is an error, where a loose one flows on.

pub mod ty;

use std::collections::{BTreeMap, HashMap};
use std::sync::Arc;

use zed_kernel::types::Type as KType;
use zed_kernel::{Prim, Rat, Term, Value, eval};

use crate::ast::{
    Error, Expr, ExprKind, Function, Note, Param, Pattern, Stmt, StmtKind, StrPart, Target, Type,
    TypeKind,
};
use crate::elab::Tables;
use crate::lex::Span;
use crate::resolve::{Kind, Ref, Resolution};

use ty::{Arrow, Binds, Carrier, EVERY, OTHER, Piece, SParam, Sig, Ty, atoms, errs, mask_text};

/// How a function argument fits the function type its slot expects.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Fit {
    /// A lambda: for each parameter of the expected type, the lambda's parameter that takes
    /// it, if any; and the lambda's parameters the type does not pass, each filled by its
    /// default.
    Lambda {
        /// The lambda parameter for each parameter of the type.
        order: Vec<Option<usize>>,
        /// The lambda parameters filled by their defaults.
        extra: Vec<usize>,
    },
    /// A declared function whose named parameters are in another order: for each of its
    /// parameters, the index of the type's parameter that fills it.
    Adapter {
        /// The type's parameter for each of the function's.
        from: Vec<usize>,
    },
}

/// What the checker finds.
#[derive(Clone, Debug, Default)]
pub struct Info {
    /// The value each adopted literal takes, by its span, before any `-`.
    pub adopt: HashMap<Span, Value>,
    /// The signature of the function called through a value, by the call's span.
    pub calls: HashMap<Span, Arc<Sig>>,
    /// The fit of each function argument that needs one, by its span.
    pub fits: HashMap<Span, Fit>,
    /// Each declared function's signature, by its binder.
    pub sigs: BTreeMap<usize, Arc<Sig>>,
    /// The type of each top-level name bound by `=` (step L1.37).
    pub tops: HashMap<String, Ty>,
    /// The type errors.
    pub errors: Vec<Error>,
}

/// Checks a resolved unit.
pub fn check(unit: &[Stmt], res: &Resolution) -> Info {
    check_with(&Tables::new(unit, res), unit)
}

pub(crate) fn check_with<'a>(t: &Tables<'a>, unit: &'a [Stmt]) -> Info {
    let mut ck = Ck::new(t);
    ck.scope(unit, true);
    ck.finish();
    ck.info
        .errors
        .sort_by(|a, b| (a.span, &a.message).cmp(&(b.span, &b.message)));
    ck.info.errors.dedup();
    ck.info
}

/// The type of the binary operator `op` applied to arguments of the types `args`, with the
/// errors the application reports: how an operator treats loose and family atoms.
pub fn operator(op: &str, args: &[Ty]) -> (Ty, Vec<String>) {
    let res = crate::resolve::resolve(&[]).expect("the empty unit resolves");
    let t = Tables::new(&[], &res);
    let mut ck = Ck::new(&t);
    let args = args.iter().map(|a| Some(Arg::of(a.clone()))).collect();
    let (out, _) = ck.apply(
        &format!("`{op}`"),
        &op_sig(op),
        args,
        true,
        Span { start: 0, end: 0 },
    );
    (out, ck.info.errors.into_iter().map(|e| e.message).collect())
}

/// A numeric literal: its span, its value, whether a `-` is applied to it, and its text.
#[derive(Clone)]
struct Lit {
    span: Span,
    value: Value,
    neg: bool,
    text: String,
}

/// An argument: its type, the literal it is, if it is one, and the expression it is, if any.
#[derive(Clone)]
struct Arg {
    ty: Ty,
    lit: Option<Lit>,
    at: Option<Span>,
}

impl Arg {
    fn of(ty: Ty) -> Arg {
        Arg {
            ty,
            lit: None,
            at: None,
        }
    }
}

/// Facts an `is` test makes: binders narrowed to a type, and the test.
type Facts = Vec<(usize, Ty, Span)>;

/// Where an expression's type comes from, for a derivation (DESIGN.md "Diagnostics").
#[derive(Clone)]
enum Src<'a> {
    /// A name, by its binder.
    Name(usize),
    /// A call of a declared function, by its binder.
    Call(usize),
    /// Anything else: its parts' derivations continue it.
    Other(&'a Expr),
}

/// An expression's type as the checker last found it, and where it comes from.
type Seen<'a> = (Ty, Src<'a>);

/// Where a binder's type comes from: the text, what it says, the expression whose derivation
/// continues it, and the origin it narrows.
#[derive(Clone)]
struct Origin {
    span: Span,
    text: String,
    from: Option<Span>,
    then: Option<Box<Origin>>,
}

/// The most steps one derivation follows through definitions.
const DEPTH: usize = 16;

/// A class of values that must share one carrier: a node of the union-find forest of
/// docs/thresholds.md, replacement 1. Only a root's fields other than `parent` and `rank`
/// are read.
#[derive(Clone)]
struct Class {
    parent: usize,
    rank: u8,
    /// The carriers it may still take, and [`OTHER`] if it may take other values.
    mask: u8,
    /// The depth of the function whose parameter made it; of a merged class, the least.
    level: usize,
    /// The literals that joined it, each with whether it follows: a follower adopts the
    /// class's carrier but does not restrict it.
    lits: Vec<(Lit, bool)>,
    /// The uses that removed carriers from it.
    reasons: Vec<Note>,
    /// Its type, once the function of its level ends.
    resolved: Option<Ty>,
}

struct Ck<'t, 'a> {
    t: &'t Tables<'a>,
    env: HashMap<usize, Ty>,
    info: Info,
    /// Each write to `info`'s maps, and to a class while a repair is tried, with the value
    /// it replaced, so that a repair is undone by what it wrote.
    log: Vec<Undo>,
    /// Each expression's type, by its span, as last found.
    seen: HashMap<Span, Seen<'a>>,
    /// Where each binder's type comes from.
    whence: HashMap<usize, Origin>,
    /// Whether a repair is being tried, so its errors offer none.
    trying: bool,
    /// The classes; class `k` is the type variable `$k`.
    classes: Vec<Class>,
    /// How many declared functions are being checked, one inside another.
    level: usize,
    /// The classes each of those functions resolves when it ends, by its level.
    pending: Vec<Vec<usize>>,
}

impl<'t, 'a> Ck<'t, 'a> {
    fn new(t: &'t Tables<'a>) -> Self {
        Ck {
            t,
            env: HashMap::new(),
            info: Info::default(),
            log: Vec::new(),
            seen: HashMap::new(),
            whence: HashMap::new(),
            trying: false,
            classes: Vec::new(),
            level: 0,
            pending: vec![Vec::new()],
        }
    }

    /// An error at `span`, with the derivation of the expression there.
    fn error(&mut self, span: Span, message: impl Into<String>) {
        let notes = self.derive(&[span]);
        self.error_with(span, message, notes);
    }

    fn error_with(&mut self, span: Span, message: impl Into<String>, notes: Vec<Note>) {
        self.info.errors.push(Error {
            span,
            message: message.into(),
            notes,
        });
    }

    /// The derivation of the expressions at `spans`: for each, its type, and for a name or a
    /// call, where the binder's type comes from, followed through each definition.
    fn derive(&self, spans: &[Span]) -> Vec<Note> {
        let mut out = Vec::new();
        for &s in spans {
            self.derive_into(s, &mut out, 0);
        }
        out
    }

    fn derive_into(&self, span: Span, out: &mut Vec<Note>, depth: usize) {
        let Some((ty, src)) = self.seen.get(&span) else {
            return;
        };
        let ty = self.show(ty);
        let push = |out: &mut Vec<Note>, span: Span, text: String| {
            let n = Note { span, text };
            if !out.contains(&n) {
                out.push(n);
            }
        };
        if depth > DEPTH {
            let text = format!("this is {ty}; its derivation goes back further than {DEPTH} steps");
            push(out, span, text);
            return;
        }
        let id = match src {
            Src::Name(id) => {
                let name = &self.t.res.binders[*id].name;
                push(out, span, format!("`{name}` is {ty} here"));
                *id
            }
            Src::Call(id) => {
                let name = &self.t.res.binders[*id].name;
                push(out, span, format!("this call of `{name}` gives {ty}"));
                *id
            }
            Src::Other(e) => {
                let parts: Vec<&Expr> = match &e.kind {
                    ExprKind::Unary(_, a) => vec![a],
                    ExprKind::Binary(_, a, b) => vec![a, b],
                    ExprKind::Else { of, default, .. } => vec![of, default],
                    ExprKind::If {
                        cond,
                        then,
                        otherwise,
                    } => vec![cond, then, otherwise],
                    ExprKind::Call {
                        positional, named, ..
                    } => positional
                        .iter()
                        .chain(named.iter().map(|(_, a)| a))
                        .collect(),
                    ExprKind::Tuple(items) => items.iter().collect(),
                    ExprKind::Index(of, _) => vec![of],
                    _ => Vec::new(),
                };
                let what = match &e.kind {
                    ExprKind::Unary(op, _) | ExprKind::Binary(op, _, _) => format!("this `{op}`"),
                    ExprKind::Else { .. } => "this `else`".into(),
                    ExprKind::If { .. } => "this `if`".into(),
                    ExprKind::Call { callee, .. } => match &callee.kind {
                        ExprKind::Name(n) => format!("this call of `{n}`"),
                        _ => "this call".into(),
                    },
                    _ => "this expression".into(),
                };
                let verb = if parts.is_empty() { "is" } else { "gives" };
                push(out, span, format!("{what} {verb} {ty}"));
                for p in parts {
                    match literal(p) {
                        Some(l) => push(
                            out,
                            p.span,
                            format!("this literal, {}, is {}", l.text, {
                                lit_ty(&l.value, l.neg)
                            }),
                        ),
                        None => self.derive_into(p.span, out, depth + 1),
                    }
                }
                return;
            }
        };
        let mut o = self.whence.get(&id);
        if o.is_none() {
            let b = &self.t.res.binders[id];
            push(out, b.span, format!("`{}` is bound here", b.name));
        }
        while let Some(origin) = o {
            push(out, origin.span, origin.text.clone());
            if let Some(f) = origin.from {
                self.derive_into(f, out, depth + 1);
            }
            o = origin.then.as_deref();
        }
    }

    /// Records where binder `id` gets its type.
    fn origin(&mut self, id: usize, span: Span, text: String, from: Option<Span>) {
        self.whence.insert(
            id,
            Origin {
                span,
                text,
                from,
                then: None,
            },
        );
    }

    fn id(&self, span: Span, name: &str) -> usize {
        self.t.id(span, name)
    }

    /// The statements of one scope, in the order elaboration binds them; the export's type.
    fn scope(&mut self, stmts: &'a [Stmt], top: bool) -> Ty {
        let mut export = None;
        let mut items: Vec<&'a Stmt> = Vec::new();
        for s in stmts {
            match &s.kind {
                StmtKind::Return(es) => export = Some(es),
                _ => items.push(s),
            }
        }
        let Ok(order) = self.t.order(&items) else {
            return Ty::dynamic();
        };
        for i in order {
            self.stmt(items[i]);
        }
        if top {
            for s in &items {
                if let StmtKind::Bind { targets, .. } = &s.kind
                    && let [Target::Name(n)] = &targets[..]
                    && let Some(ty) = self.env.get(&self.id(s.span, n))
                {
                    self.put(Undo::Top(n.clone(), Some(ty.clone())));
                }
            }
            for s in &items {
                if let StmtKind::Function(f) = &s.kind {
                    self.tests(f, self.id(s.span, &f.name));
                }
            }
        }
        match export {
            None => Ty::tuple(Vec::new()),
            Some(es) if es.len() == 1 => self.expr(&es[0]),
            Some(es) => Ty::tuple(es.iter().map(|e| self.expr(e)).collect()),
        }
    }

    fn stmt(&mut self, s: &'a Stmt) {
        match &s.kind {
            StmtKind::Bind { targets, value } => {
                let v = self.expr(value);
                match &targets[..] {
                    [Target::Name(n)] => {
                        let id = self.id(s.span, n);
                        let text = format!("`{n}` is defined as this expression, {v}");
                        self.origin(id, value.span, text, Some(value.span));
                        self.env.insert(id, v);
                    }
                    [Target::Wild] => {}
                    _ => {
                        for (i, target) in targets.iter().enumerate() {
                            let c = self.component(&v, i, targets.len(), value.span);
                            if let Target::Name(n) = target {
                                let id = self.id(s.span, n);
                                let text = format!("`{n}` is component {i} of this, {c}");
                                self.origin(id, value.span, text, Some(value.span));
                                self.env.insert(id, c);
                            }
                        }
                    }
                }
            }
            StmtKind::Function(f) => {
                let id = self.id(s.span, &f.name);
                let sig = self.infer(f, s.span);
                let text = format!("`{}` is declared here, `{sig}`", f.name);
                self.origin(id, s.span, text, None);
                self.env.insert(id, Ty::func(sig.clone()));
                self.put(Undo::Sig(id, Some(sig)));
            }
            StmtKind::Push { value, .. } => {
                self.expr(value);
            }
            StmtKind::Return(_) => unreachable!("an export is not a binding"),
        }
    }

    /// Component `i` of `v`, destructured into `n` names: of each tuple shape, with `v`'s
    /// atoms, which `TupleGet` passes.
    fn component(&mut self, v: &Ty, i: usize, n: usize, span: Span) -> Ty {
        let mut out = self.passing(v, "a tuple", span);
        for p in v.pieces() {
            match p {
                Piece::Tuple(cs) if cs.len() == n => out = out.union(&cs[i]),
                Piece::Dyn | Piece::Var(_) => out = out.union(&Ty::dynamic()),
                p if p.is_atoms() => {}
                p => {
                    if i == 0 {
                        self.error(
                            span,
                            format!("this value is {}, not a tuple of {n}", p.ty()),
                        );
                    }
                    out = out.union(&Ty::dynamic());
                }
            }
        }
        out
    }

    /// The signature of a declared function. A parameter with neither a type nor a closed
    /// default gets a class, which its uses narrow, the body checked once. When the function
    /// ends, each class of its level takes its type; a class merged with one of a function
    /// around it waits for that function.
    fn infer(&mut self, f: &'a Function, span: Span) -> Arc<Sig> {
        let params: Vec<SParam> = f
            .params
            .iter()
            .enumerate()
            .map(|(i, p)| SParam {
                name: p.name.as_str().into(),
                positional: p.positional,
                default: p.default.as_ref().map(|d| {
                    let closed = self.t.uses_in(d.span, &[]).is_empty();
                    (self.id(span, &f.name), i, closed)
                }),
            })
            .collect();
        let ids: Vec<usize> = f.params.iter().map(|p| self.id(p.span, &p.name)).collect();
        let mut given: Vec<Option<Ty>> = Vec::new();
        for p in &f.params {
            let t = self.param_type(p);
            given.push(t);
        }
        if let Some(ports) = &f.ports {
            for p in ports {
                let id = self.id(p.span, &p.name);
                let text = format!("`{}` is an output port", p.name);
                self.origin(id, p.span, text, None);
                self.env.insert(id, Ty::dynamic());
            }
        }
        self.level += 1;
        let level = self.level;
        if self.pending.len() <= level {
            self.pending.push(Vec::new());
        }
        let mut tys = Vec::new();
        for ((id, p), g) in ids.iter().zip(&f.params).zip(given) {
            let (t, text) = match (&p.ty, g) {
                (Some(a), Some(t)) if t == Ty::dynamic() => {
                    let text = format!(
                        "`{}` is declared `{a}`, whose values the checker does not track: \
                         it takes `{}` as unknown, _",
                        p.name, p.name
                    );
                    (t, text)
                }
                (Some(a), Some(t)) => (t, format!("`{}` is declared `{a}`", p.name)),
                (None, Some(t)) => {
                    let text = format!("`{}` is {t}, the carrier of its default", p.name);
                    (t, text)
                }
                (_, None) => {
                    let k = self.class();
                    let text = format!("`{}` has no declared type; its uses give it ${k}", p.name);
                    (Ty::var(format!("${k}").into()), text)
                }
            };
            self.origin(*id, p.span, text, None);
            self.env.insert(*id, t.clone());
            tys.push(t);
        }
        // A default that reads the other parameters, at its parameter's type.
        for (p, t) in f.params.iter().zip(&tys) {
            let Some(d) = &p.default else {
                continue;
            };
            if self.t.uses_in(d.span, &[]).is_empty() {
                continue;
            }
            let what = format!("the default of `{}`", p.name);
            match self.class_of_ty(t) {
                Some(k) => {
                    let dt = self.expr(d);
                    if !self.flow(k, &dt, &what, d.span) {
                        let shown = self.show(t);
                        let mut notes = self.derive(&[d.span]);
                        notes.extend(self.reasons(t));
                        self.error_with(d.span, format!("{what} is {dt}, not {shown}"), notes);
                    }
                }
                None => {
                    let dt = self.expr_at(d, Some(t));
                    if !dt.subtype(t) {
                        self.error(d.span, format!("{what} is {dt}, not {t}"));
                    }
                }
            }
        }
        let result = match &f.body.kind {
            ExprKind::Block(stmts) if !f.equation => self.scope(stmts, false),
            _ => self.expr(&f.body),
        };
        let mut own = Vec::new();
        for k in std::mem::take(&mut self.pending[level]) {
            let r = self.find(k);
            if self.classes[r].resolved.is_some() {
                continue;
            }
            let at = self.classes[r].level;
            if at < level {
                self.pending[at].push(r);
                continue;
            }
            self.resolve(r);
            own.push(r);
        }
        // The classes of this level that are type variables, named in order of appearance.
        let sig = self.solved_sig(&Sig::one(params, tys, result));
        let mut seen = Vec::new();
        for a in &sig.arrows {
            a.params.iter().for_each(|p| p.vars_in(&mut seen));
            a.result.vars_in(&mut seen);
        }
        let taken: Vec<Arc<str>> = seen
            .iter()
            .filter(|v| class_id(v).is_none())
            .cloned()
            .collect();
        let mut names = Binds::new();
        let mut bounds = BTreeMap::new();
        let mut n = 0;
        for v in &seen {
            let Some(r) = class_id(v).filter(|r| own.contains(r)) else {
                continue;
            };
            let name = loop {
                let name = var_name(n);
                n += 1;
                if !taken.contains(&name) {
                    break name;
                }
            };
            if self.classes[r].mask != EVERY {
                bounds.insert(name.clone(), self.classes[r].mask);
            }
            self.classes[r].resolved = Some(Ty::var(name.clone()));
            names.insert(v.clone(), Ty::var(name));
        }
        // A type variable that does not reach the signature means nothing outside it.
        for &r in &own {
            if let Some(t) = &self.classes[r].resolved
                && t.vars.iter().any(|v| class_id(v).is_some())
            {
                self.classes[r].resolved = Some(Ty::dynamic());
            }
        }
        let mut sig = sig.replace(&names);
        sig.bounds.extend(bounds);
        self.level -= 1;
        Arc::new(sig)
    }

    /// A new class, of every value, at the current level.
    fn class(&mut self) -> usize {
        let id = self.classes.len();
        self.classes.push(Class {
            parent: id,
            rank: 0,
            mask: EVERY,
            level: self.level,
            lits: Vec::new(),
            reasons: Vec::new(),
            resolved: None,
        });
        self.pending[self.level].push(id);
        id
    }

    /// The root of class `k`'s tree.
    fn find(&self, mut k: usize) -> usize {
        while self.classes[k].parent != k {
            k = self.classes[k].parent;
        }
        k
    }

    /// Logs class `r` before a change, while a repair is tried.
    fn touch(&mut self, r: usize) {
        if self.trying {
            self.log
                .push(Undo::Class(r, Box::new(self.classes[r].clone())));
        }
    }

    /// Removes from class `k` the carriers `mask` lacks, as `what` at `span` requires;
    /// false, changing nothing, if none would be left.
    fn restrict(&mut self, k: usize, mask: u8, what: &str, span: Span) -> bool {
        let r = self.find(k);
        let m = self.classes[r].mask & mask;
        if m == self.classes[r].mask {
            return true;
        }
        if m == 0 {
            return false;
        }
        self.touch(r);
        let c = &mut self.classes[r];
        c.mask = m;
        c.reasons.push(Note {
            span,
            text: format!("{what} takes {}", mask_text(mask)),
        });
        true
    }

    /// Merges classes `a` and `b`, as `what` at `span` requires; false, changing nothing, if
    /// they share no carrier. The shorter lists move into the longer, so that each item
    /// moves `O(log n)` times.
    fn merge(&mut self, a: usize, b: usize, what: &str, span: Span) -> bool {
        let (a, b) = (self.find(a), self.find(b));
        if a == b {
            return true;
        }
        let m = self.classes[a].mask & self.classes[b].mask;
        if m == 0 {
            return false;
        }
        self.touch(a);
        self.touch(b);
        let (root, child) = match self.classes[a].rank < self.classes[b].rank {
            true => (b, a),
            false => (a, b),
        };
        if self.classes[a].rank == self.classes[b].rank {
            self.classes[root].rank += 1;
        }
        let mut lits = std::mem::take(&mut self.classes[child].lits);
        let mut reasons = std::mem::take(&mut self.classes[child].reasons);
        let level = self.classes[child].level;
        self.classes[child].parent = root;
        let c = &mut self.classes[root];
        if c.lits.len() < lits.len() {
            std::mem::swap(&mut c.lits, &mut lits);
        }
        c.lits.extend(lits);
        if c.reasons.len() < reasons.len() {
            std::mem::swap(&mut c.reasons, &mut reasons);
        }
        c.reasons.extend(reasons);
        c.reasons.push(Note {
            span,
            text: format!("{what} gives these values one carrier"),
        });
        c.mask = m;
        c.level = c.level.min(level);
        true
    }

    /// The literal `l` joins class `k`; unless it follows, the class keeps only the carriers
    /// it may adopt, and false if none would be left.
    fn join(&mut self, k: usize, l: &Lit, follower: bool) -> bool {
        if !follower {
            let m = Carrier::ALL
                .into_iter()
                .filter(|&c| adoptable(l, c))
                .fold(0, |m, c| m | c.bit());
            if !self.restrict(k, m, &format!("the literal {}", l.text), l.span) {
                return false;
            }
        }
        let r = self.find(k);
        self.touch(r);
        self.classes[r].lits.push((l.clone(), follower));
        true
    }

    /// The values of `t` flow into class `k`: a class merges with it, a carrier restricts it
    /// to that carrier, and a tuple or a function to other values; atoms and the unknown
    /// change nothing.
    fn flow(&mut self, k: usize, t: &Ty, what: &str, span: Span) -> bool {
        for p in t.pieces() {
            let ok = match (self.class_of(&p), p.carrier()) {
                (Some(j), _) => self.merge(k, j, what, span),
                _ if matches!(p, Piece::Dyn | Piece::Var(_)) || p.is_atoms() => true,
                (None, Some(c)) => self.restrict(k, c.bit(), what, span),
                (None, None) => self.restrict(k, OTHER, what, span),
            };
            if !ok {
                return false;
            }
        }
        true
    }

    /// Gives class `r` its type: the first of int, f64 and rat it may take if a literal that
    /// does not follow joined it, every literal adopting it; a type variable if it may take
    /// any value; its carrier if one; a type variable bounded by its carriers if several;
    /// else the unknown.
    fn resolve(&mut self, r: usize) {
        let (mask, lits) = (self.classes[r].mask, self.classes[r].lits.clone());
        let numeric = [Carrier::Int, Carrier::F64, Carrier::Rat]
            .into_iter()
            .find(|c| mask & c.bit() != 0)
            .filter(|_| lits.iter().any(|(_, follows)| !follows));
        let ty = match numeric {
            Some(c) => Ty::carrier(c),
            None if mask == EVERY => Ty::var(format!("${r}").into()),
            None if mask & OTHER == 0 && mask.count_ones() == 1 => {
                Ty::carrier(Carrier::of_mask(mask).next().expect("one carrier"))
            }
            None if mask & OTHER == 0 => Ty::var(format!("${r}").into()),
            None => Ty::dynamic(),
        };
        if let Some(c) = ty.numeric_carrier() {
            for (l, _) in &lits {
                self.adopt_to(l, c);
            }
        }
        self.classes[r].resolved = Some(ty);
    }

    /// The class `p` is, if it is a class not yet resolved: its root.
    fn class_of(&self, p: &Piece) -> Option<usize> {
        let Piece::Var(v) = p else {
            return None;
        };
        let r = self.find(class_id(v)?);
        self.classes[r].resolved.is_none().then_some(r)
    }

    /// The class `t` is, if it is one and nothing else.
    fn class_of_ty(&self, t: &Ty) -> Option<usize> {
        match t.pieces().as_slice() {
            [p] => self.class_of(p),
            _ => None,
        }
    }

    /// `t` shown with each class narrowed to some carriers shown as their union.
    fn show(&self, t: &Ty) -> String {
        let mut rest = t.clone();
        let mut parts = Vec::new();
        for v in &t.vars {
            if let Some(r) = self.class_of(&Piece::Var(v.clone())) {
                let m = self.classes[r].mask;
                if m != EVERY && m & OTHER == 0 {
                    parts.push(mask_text(m));
                    rest.vars.remove(v);
                }
            }
        }
        if parts.is_empty() {
            return t.to_string();
        }
        if !rest.is_empty() {
            parts.push(rest.to_string());
        }
        parts.join(" | ")
    }

    /// The uses that narrowed the classes in `t`.
    fn reasons(&self, t: &Ty) -> Vec<Note> {
        let mut out: Vec<Note> = Vec::new();
        for p in t.pieces() {
            if let Some(k) = self.class_of(&p) {
                for n in &self.classes[k].reasons {
                    if !out.contains(n) {
                        out.push(n.clone());
                    }
                }
            }
        }
        out
    }

    /// For each class variable in `vars`, its root's type: the one it was given, else the
    /// root's variable.
    fn solving(&self, vars: &[Arc<str>]) -> Binds {
        let mut b = Binds::new();
        for v in vars {
            let Some(k) = class_id(v).filter(|&k| k < self.classes.len()) else {
                continue;
            };
            let r = self.find(k);
            let t = match &self.classes[r].resolved {
                Some(t) => t.clone(),
                None => Ty::var(format!("${r}").into()),
            };
            if t != Ty::var(v.clone()) {
                b.insert(v.clone(), t);
            }
        }
        b
    }

    /// `t` with each class variable replaced by its root's type.
    fn solved(&self, t: &Ty) -> Ty {
        let mut vars = Vec::new();
        t.vars_in(&mut vars);
        t.replace(&self.solving(&vars))
    }

    /// `s` with each class variable replaced by its root's type.
    fn solved_sig(&self, s: &Sig) -> Sig {
        s.replace(&self.solving(&sig_vars(s)))
    }

    /// `s` with each class variable replaced by its type, as [`Self::finish`] puts it: a
    /// type variable of the function around named as one of `s`'s own takes the next name
    /// `s` does not use.
    fn finished(&self, s: &Sig) -> Sig {
        let vars = sig_vars(s);
        let mut b = self.solving(&vars);
        let own: Vec<Arc<str>> = vars
            .iter()
            .filter(|v| class_id(v).is_none())
            .cloned()
            .collect();
        let mut used = own.clone();
        for t in b.values() {
            used.extend(t.vars.iter().cloned());
        }
        let mut renamed: BTreeMap<Arc<str>, Arc<str>> = BTreeMap::new();
        let mut n = 0;
        for t in b.values_mut() {
            let Some(v) = t.vars.iter().find(|v| own.contains(v)).cloned() else {
                continue;
            };
            let to = renamed
                .entry(v.clone())
                .or_insert_with(|| {
                    loop {
                        let name = var_name(n);
                        n += 1;
                        if !used.contains(&name) {
                            used.push(name.clone());
                            break name;
                        }
                    }
                })
                .clone();
            *t = t.subst(&[(v, Ty::var(to))].into());
        }
        s.replace(&b)
    }

    /// Puts each class's type in place of its variable in what the checker found.
    fn finish(&mut self) {
        let sigs = std::mem::take(&mut self.info.sigs);
        self.info.sigs = sigs
            .into_iter()
            .map(|(k, s)| (k, Arc::new(self.finished(&s))))
            .collect();
        let calls = std::mem::take(&mut self.info.calls);
        self.info.calls = calls
            .into_iter()
            .map(|(k, s)| (k, Arc::new(self.finished(&s))))
            .collect();
        let tops = std::mem::take(&mut self.info.tops);
        self.info.tops = tops
            .into_iter()
            .map(|(k, t)| (k, self.solved(&t)))
            .collect();
        let mut errors = std::mem::take(&mut self.info.errors);
        for e in &mut errors {
            e.message = self.named(&e.message);
            for n in &mut e.notes {
                n.text = self.named(&n.text);
            }
        }
        self.info.errors = errors;
    }

    /// `text` with each class variable `$k` replaced by its type.
    fn named(&self, text: &str) -> String {
        let mut out = String::new();
        let mut rest = text;
        while let Some(i) = rest.find('$') {
            out.push_str(&rest[..i]);
            let tail = &rest[i + 1..];
            let n = tail.bytes().take_while(u8::is_ascii_digit).count();
            match tail[..n]
                .parse::<usize>()
                .ok()
                .filter(|&k| k < self.classes.len())
            {
                Some(k) => out.push_str(&self.solved(&Ty::var(format!("${k}").into())).to_string()),
                None => {
                    out.push('$');
                    out.push_str(&tail[..n]);
                }
            }
            rest = &tail[n..];
        }
        out.push_str(rest);
        out
    }

    /// A parameter's declared type: its annotation, or its closed default's type with each
    /// carrier widened to the whole carrier.
    fn param_type(&mut self, p: &'a Param) -> Option<Ty> {
        if let Some(t) = &p.ty {
            return Some(self.ty_of(t));
        }
        let d = p.default.as_ref()?;
        if !self.t.uses_in(d.span, &[]).is_empty() {
            return None;
        }
        let t = self.expr(d);
        let mut out = Ty::empty();
        for piece in t.pieces() {
            out = out.union(&match piece.carrier() {
                Some(c) => Ty::carrier(c),
                None => piece.ty(),
            });
        }
        Some(out)
    }

    /// The cases of `f`'s `test` tables, each checked as a call, its expected value adopting
    /// as the right side of `==` does.
    fn tests(&mut self, f: &'a Function, id: usize) {
        let Some(sig) = self.info.sigs.get(&id).cloned() else {
            return;
        };
        for (input, expected) in &f.tests {
            let args: Vec<&'a Expr> = match (&input.kind, f.params.len()) {
                (_, 1) => vec![input],
                (ExprKind::Tuple(items), n) if items.len() == n => items.iter().collect(),
                _ => continue,
            };
            let args: Vec<Option<Arg>> =
                args.into_iter().map(|a| Some(self.arg(a, None))).collect();
            let (result, _) = self.apply(&format!("`{}`", f.name), &sig, args, false, input.span);
            let want = self.arg(expected, None);
            self.equal(&Arg::of(result), &want);
        }
    }

    /// An argument: a numeric literal kept unadopted, a function in a slot of function type
    /// fitted to it, else the expression's type.
    fn arg(&mut self, e: &'a Expr, expected: Option<&Ty>) -> Arg {
        if let Some(l) = literal(e) {
            return Arg {
                ty: lit_ty(&l.value, l.neg),
                lit: Some(l),
                at: Some(e.span),
            };
        }
        Arg {
            at: Some(e.span),
            ..Arg::of(self.expr_at(e, expected))
        }
    }

    /// `e`'s type where `expected` is wanted: a lambda or a declared function in a slot of
    /// one function type is fitted to it, and a numeric literal adopts its one carrier.
    fn expr_at(&mut self, e: &'a Expr, expected: Option<&Ty>) -> Ty {
        let Some(want) = expected else {
            return self.expr(e);
        };
        if let Some(sig) = only_fn(want) {
            if let ExprKind::Lambda { params, body } = &e.kind {
                return self.fit_lambda(params, body, &sig, e.span);
            }
            if let Some(id) = self.declared(e) {
                return self.fit_declared(id, &sig, e.span);
            }
        }
        if let (Some(l), Some(c)) = (literal(e), want.numeric_carrier()) {
            return self.adopt_to(&l, c);
        }
        self.expr(e)
    }

    /// The literal `l` adopting `c`, recorded; an error when it is not exactly a `c`.
    fn adopt_to(&mut self, l: &Lit, c: Carrier) -> Ty {
        match adopt(l, c) {
            Ok(None) => lit_ty(&l.value, l.neg),
            Ok(Some(v)) => {
                let t = lit_ty(&v, l.neg);
                self.put(Undo::Adopt(l.span, Some(v)));
                t
            }
            Err(m) => {
                self.error(l.span, m);
                lit_ty(&l.value, l.neg)
            }
        }
    }

    /// `e`'s type, recorded for derivations.
    fn expr(&mut self, e: &'a Expr) -> Ty {
        let t = self.expr_of(e);
        let src = match &e.kind {
            ExprKind::Name(_) => match self.t.res.uses.get(&e.span) {
                Some(Ref::Bound(ids)) if ids.len() == 1 => Src::Name(ids[0]),
                _ => Src::Other(e),
            },
            ExprKind::Call { callee, .. } => match self.declared(callee) {
                Some(id) => Src::Call(id),
                None => Src::Other(e),
            },
            _ => Src::Other(e),
        };
        self.seen.insert(e.span, (t.clone(), src));
        t
    }

    fn expr_of(&mut self, e: &'a Expr) -> Ty {
        if let Some(l) = literal(e) {
            return match self.info.adopt.get(&l.span) {
                Some(v) => lit_ty(v, l.neg),
                None => lit_ty(&l.value, l.neg),
            };
        }
        match &e.kind {
            // A `rat` literal is decorated and keeps its carrier; a literal past the size
            // limit is elaboration's error.
            ExprKind::Rat(s) => match Rat::decimal(s) {
                Some(r) => Ty::lit(&Value::rat(r)),
                None => Ty::dynamic(),
            },
            ExprKind::Int { .. } | ExprKind::Float(_) => Ty::dynamic(),
            ExprKind::Bool(b) => Ty::lit(&Value::Bool(*b)),
            ExprKind::Atom(a) => Ty::set(KType::atom(a)),
            ExprKind::Str(parts) => {
                let mut holes = Vec::new();
                let mut text = String::new();
                for p in parts {
                    match p {
                        StrPart::Text(t) => text.push_str(t),
                        StrPart::Hole(h) => holes.push(self.expr(h)),
                    }
                }
                if holes.is_empty() {
                    return Ty::lit(&Value::str(&text));
                }
                let mut out = Ty::carrier(Carrier::Str);
                passed(&mut out, holes.iter());
                out
            }
            ExprKind::Name(_) => self.name(e.span),
            ExprKind::Unary(op, a) => {
                let x = self.arg(a, None);
                let sig = op_sig(op);
                self.apply(&format!("`{op}`"), &sig, vec![Some(x)], true, e.span)
                    .0
            }
            ExprKind::Binary(op, a, b) => self.binary(op, a, b, e.span),
            ExprKind::Call {
                callee,
                positional,
                named,
                curry,
            } => self.call(callee, positional, named, *curry, e.span),
            ExprKind::Index(of, k) => self.index(of, k, e.span),
            ExprKind::Tuple(items) => Ty::tuple(items.iter().map(|i| self.expr(i)).collect()),
            ExprKind::Lambda { params, body } => self.lambda(params, body),
            ExprKind::Is { of, ty, .. } => {
                self.expr(of);
                self.ty_of(ty);
                Ty::carrier(Carrier::Bool)
            }
            ExprKind::Else {
                of,
                pattern,
                default,
            } => {
                let v = self.expr(of);
                if pattern.is_some() {
                    for (i, b) in self.t.res.binders.iter().enumerate() {
                        if b.kind == Kind::Pattern && default.span.start >= b.span.start {
                            self.env.entry(i).or_insert_with(Ty::dynamic);
                        }
                    }
                }
                let d = self.expr(default);
                match pattern {
                    None => v.without_loose().union(&d),
                    Some(Pattern::Atom {
                        name,
                        fields,
                        items,
                        ..
                    }) if fields.is_empty() && items.is_empty() => {
                        v.diff(&Ty::set(KType::atom(name))).union(&d)
                    }
                    Some(_) => v.union(&d),
                }
            }
            ExprKind::Block(stmts) => self.scope(stmts, false),
            ExprKind::If {
                cond,
                then,
                otherwise,
            } => {
                let (c, yes, no) = self.cond(cond);
                let mut out = self.passing(&c, "the condition of `if`", cond.span);
                let what = "the condition of `if`";
                for p in c.pieces() {
                    let ok = match self.class_of(&p) {
                        Some(k) => self.restrict(k, Carrier::Bool.bit(), what, cond.span),
                        None => {
                            matches!(p, Piece::Dyn)
                                || p.is_atoms()
                                || p.carrier() == Some(Carrier::Bool)
                        }
                    };
                    if !ok {
                        let shown = self.show(&c);
                        let mut notes = self.derive(&[cond.span]);
                        notes.extend(self.reasons(&c));
                        self.error_with(cond.span, format!("{what} is {shown}, not bool"), notes);
                        break;
                    }
                }
                let a = self.under(&yes, then);
                let b = self.under(&no, otherwise);
                out = out.union(&a).union(&b);
                out
            }
            ExprKind::Member { of, name, safe } => {
                self.member(of, name, *safe, e.span, &[], &[], false, e.span)
            }
        }
    }

    /// The loose atoms of `t`, which flow through `what` unchanged: an atom of a named family
    /// is data, and data that selects no arrow is an error (sec:failure).
    fn passing(&mut self, t: &Ty, what: &str, span: Span) -> Ty {
        if !t.family.is_empty() {
            self.error(
                span,
                format!("{what} does not take {}", Ty::set(t.family.clone())),
            );
        }
        Ty::set(t.loose())
    }

    /// `e` checked with the binders of `facts` narrowed.
    fn under(&mut self, facts: &Facts, e: &'a Expr) -> Ty {
        let saved = self.narrow(facts);
        let out = self.expr(e);
        self.widen(saved);
        out
    }

    /// Narrows the binders of `facts`, each origin now the test; gives what to restore.
    fn narrow(&mut self, facts: &Facts) -> Vec<(usize, Option<Ty>, Option<Origin>)> {
        facts
            .iter()
            .map(|(b, t, test)| {
                let name = &self.t.res.binders[*b].name;
                let old = self.whence.get(b).cloned();
                let o = Origin {
                    span: *test,
                    text: format!("`{name}` is narrowed to {t} where this test decides"),
                    from: None,
                    then: old.clone().map(Box::new),
                };
                self.whence.insert(*b, o);
                (*b, self.env.insert(*b, t.clone()), old)
            })
            .collect()
    }

    /// Restores what [`Self::narrow`] changed.
    fn widen(&mut self, saved: Vec<(usize, Option<Ty>, Option<Origin>)>) {
        for (b, old, o) in saved.into_iter().rev() {
            match old {
                Some(t) => self.env.insert(b, t),
                None => self.env.remove(&b),
            };
            match o {
                Some(o) => self.whence.insert(b, o),
                None => self.whence.remove(&b),
            };
        }
    }

    /// A condition's type and the facts it makes when it holds and when it does not.
    fn cond(&mut self, e: &'a Expr) -> (Ty, Facts, Facts) {
        match &e.kind {
            ExprKind::Is { of, ty, negated } => {
                let v = self.expr(of);
                let t = self.ty_of(ty);
                let b = match (&of.kind, self.t.res.uses.get(&of.span)) {
                    (ExprKind::Name(_), Some(Ref::Bound(ids))) if ids.len() == 1 => ids[0],
                    _ => return (Ty::carrier(Carrier::Bool), Vec::new(), Vec::new()),
                };
                let (yes, no) = (vec![(b, v.meet(&t), e.span)], vec![(b, v.diff(&t), e.span)]);
                let bool_ = Ty::carrier(Carrier::Bool);
                match negated {
                    false => (bool_, yes, no),
                    true => (bool_, no, yes),
                }
            }
            ExprKind::Unary("!", a) => {
                let (t, yes, no) = self.cond(a);
                let sig = op_sig("!");
                let t = self
                    .apply("`!`", &sig, vec![Some(Arg::of(t))], true, e.span)
                    .0;
                (t, no, yes)
            }
            ExprKind::Binary(op @ ("&&" | "||"), a, b) => {
                let (ta, ya, na) = self.cond(a);
                let first = if *op == "&&" { &ya } else { &na };
                let saved = self.narrow(first);
                let (tb, yb, nb) = self.cond(b);
                self.widen(saved);
                let sig = op_sig("&&");
                let t = self
                    .apply(
                        &format!("`{op}`"),
                        &sig,
                        vec![Some(Arg::of(ta)), Some(Arg::of(tb))],
                        true,
                        e.span,
                    )
                    .0;
                if *op == "&&" {
                    (t, [ya, yb].concat(), Vec::new())
                } else {
                    (t, Vec::new(), [na, nb].concat())
                }
            }
            _ => (self.expr(e), Vec::new(), Vec::new()),
        }
    }

    fn binary(&mut self, op: &'static str, a: &'a Expr, b: &'a Expr, span: Span) -> Ty {
        match op {
            "&&" | "||" => {
                let (ta, ya, na) = self.cond(a);
                let first = if op == "&&" { ya } else { na };
                let tb = self.under(&first, b);
                let sig = op_sig("&&");
                self.apply(
                    &format!("`{op}`"),
                    &sig,
                    vec![Some(Arg::of(ta)), Some(Arg::of(tb))],
                    true,
                    span,
                )
                .0
            }
            "==" | "!=" => {
                let (x, y) = (self.arg(a, None), self.arg(b, None));
                self.equal(&x, &y);
                Ty::carrier(Carrier::Bool)
            }
            "<" | "<=" | ">" | ">=" => {
                let (x, y) = (self.arg(a, None), self.arg(b, None));
                self.compare(op, x, y, span)
            }
            _ => {
                let (x, y) = (self.arg(a, None), self.arg(b, None));
                // A divisor whose type holds no zero cannot fail with `#divByZero`.
                let nonzero = matches!(op, "/" | "div" | "mod")
                    && !y.ty.contains(&Value::Int(0))
                    && !y.ty.contains(&Value::rat(Rat::int(0.into())));
                let carried = [&x.ty, &y.ty]
                    .iter()
                    .any(|t| t.atoms().contains(&Value::atom("divByZero")));
                let sig = op_sig(op);
                let r = self.apply(&format!("`{op}`"), &sig, vec![Some(x), Some(y)], true, span);
                match nonzero && !carried {
                    true => r.0.diff(&Ty::set(KType::atom("divByZero"))),
                    false => r.0,
                }
            }
        }
    }

    /// `==` and `!=`: any two values; a literal adopts the other side's one numeric carrier,
    /// and of two literals the integer adopts the other's.
    fn equal(&mut self, x: &Arg, y: &Arg) {
        match (&x.lit, &y.lit) {
            (Some(l), Some(m)) => {
                let (lc, mc) = (lit_carrier(&l.value), lit_carrier(&m.value));
                if rank(lc) < rank(mc) {
                    self.adopt_to(l, mc);
                } else if rank(mc) < rank(lc) {
                    self.adopt_to(m, lc);
                }
            }
            (Some(l), None) => self.follow(l, &y.ty),
            (None, Some(m)) => self.follow(m, &x.ty),
            (None, None) => {}
        }
    }

    /// The literal `l` compared with a value of `t`: it adopts `t`'s one numeric carrier, or
    /// follows its class.
    fn follow(&mut self, l: &Lit, t: &Ty) {
        if let Some(k) = self.class_of_ty(t) {
            self.join(k, l, true);
        } else if let Some(c) = t.numeric_carrier() {
            self.adopt_to(l, c);
        }
    }

    /// An ordering: two values of one carrier, or two tuples of one length; atoms pass.
    fn compare(&mut self, op: &str, x: Arg, y: Arg, span: Span) -> Ty {
        let mut sig = op_sig("<");
        let tuples = |t: &Ty| t.tuples.iter().map(|cs| cs.len()).collect::<Vec<usize>>();
        let mut lens = tuples(&x.ty);
        lens.extend(tuples(&y.ty));
        lens.sort_unstable();
        lens.dedup();
        for n in lens {
            let any = Ty::tuple(vec![Ty::dynamic(); n]);
            sig.arrows.push(Arrow {
                params: vec![any.clone(), any],
                result: Ty::carrier(Carrier::Bool),
            });
        }
        self.apply(&format!("`{op}`"), &sig, vec![Some(x), Some(y)], true, span)
            .0
    }

    fn name(&mut self, span: Span) -> Ty {
        match self.t.res.uses.get(&span) {
            Some(Ref::Bound(ids)) if ids.len() == 1 => {
                self.env.get(&ids[0]).cloned().unwrap_or_else(Ty::dynamic)
            }
            Some(Ref::Prelude(w)) if w != "sum" => Ty::func(word_sig(w)),
            _ => Ty::dynamic(),
        }
    }

    /// The declared function that `e` names, if it names exactly one.
    fn declared(&self, e: &Expr) -> Option<usize> {
        match (&e.kind, self.t.res.uses.get(&e.span)) {
            (ExprKind::Name(_), Some(Ref::Bound(ids))) if ids.len() == 1 => {
                self.t.funcs.contains_key(&ids[0]).then_some(ids[0])
            }
            _ => None,
        }
    }

    fn call(
        &mut self,
        callee: &'a Expr,
        positional: &'a [Expr],
        named: &'a [(String, Expr)],
        curry: bool,
        span: Span,
    ) -> Ty {
        if let ExprKind::Member { of, name, safe } = &callee.kind {
            return self.member(of, name, *safe, callee.span, positional, named, curry, span);
        }
        if let ExprKind::Atom(name) = &callee.kind {
            for a in positional.iter().chain(named.iter().map(|(_, a)| a)) {
                self.expr(a);
            }
            return Ty::set(KType::atom_with(name, &KType::top()));
        }
        if let Some(id) = self.declared(callee) {
            let sig = match self.env.get(&id) {
                Some(t) => only_fn(t),
                None => None,
            };
            let from = self.info.errors.len();
            let out = match &sig {
                Some(sig) => self.call_sig(
                    sig,
                    true,
                    None,
                    positional,
                    named,
                    curry,
                    span,
                    &self.t.funcs[&id].name.clone(),
                ),
                None => Ty::dynamic(),
            };
            if let (Some(o), Some(sig)) = (self.whence.get(&id).cloned(), sig) {
                let text = format!("`{}` is declared here, `{sig}`", self.t.funcs[&id].name);
                self.also(from, Note { span: o.span, text });
            }
            return out;
        }
        let f = self.expr(callee);
        let what = match &callee.kind {
            ExprKind::Name(n) => n.clone(),
            _ => "this value".into(),
        };
        if let (ExprKind::Name(w), Some(Ref::Prelude(_))) =
            (&callee.kind, self.t.res.uses.get(&callee.span))
        {
            if named.is_empty() && !curry && positional.len() == 1 {
                return self.word(w, positional, None, span);
            }
            return Ty::dynamic();
        }
        self.call_value(&f, &what, None, positional, named, curry, span)
    }

    /// A prelude word applied to one argument, the receiver or the only positional one.
    fn word(&mut self, w: &str, positional: &'a [Expr], receiver: Option<Arg>, span: Span) -> Ty {
        let x = match receiver {
            Some(r) => r,
            None => self.arg(&positional[0], None),
        };
        if w == "sum" {
            return self.sum(x.ty, span);
        }
        let sig = word_sig(w);
        self.apply(&format!("`{w}`"), &sig, vec![Some(x)], true, span)
            .0
    }

    /// `sum` of a tuple: its components added in turn, `0` for the empty tuple; atoms pass.
    fn sum(&mut self, t: Ty, span: Span) -> Ty {
        let mut out = self.passing(&t, "`sum`", span);
        let add = op_sig("+");
        for p in t.pieces() {
            match p {
                Piece::Tuple(cs) => {
                    let Some((first, rest)) = cs.split_first() else {
                        out = out.union(&Ty::lit(&Value::Int(0)));
                        continue;
                    };
                    let mut acc = first.clone();
                    for c in rest {
                        acc = self
                            .apply(
                                "`sum`",
                                &add,
                                vec![Some(Arg::of(acc)), Some(Arg::of(c.clone()))],
                                true,
                                span,
                            )
                            .0;
                    }
                    if let Some(c) = acc.pieces().iter().find(|p| {
                        !matches!(p, Piece::Dyn | Piece::Var(_))
                            && !p.is_atoms()
                            && !p.carrier().is_some_and(Carrier::numeric)
                    }) {
                        self.error(span, format!("`sum` does not take ({})", c.ty()));
                    }
                    out = out.union(&acc);
                }
                Piece::Dyn | Piece::Var(_) => out = out.union(&Ty::dynamic()),
                p if p.is_atoms() => {}
                p => self.error(span, format!("`sum` does not take ({})", p.ty())),
            }
        }
        out
    }

    /// A call through a value: each function its type holds, applied; an atom passes.
    #[allow(clippy::too_many_arguments)]
    fn call_value(
        &mut self,
        f: &Ty,
        what: &str,
        receiver: Option<Arg>,
        positional: &'a [Expr],
        named: &'a [(String, Expr)],
        curry: bool,
        span: Span,
    ) -> Ty {
        let mut out = self.passing(f, "a call", span);
        let mut checked = false;
        if let Some(s) = f.fns.first()
            && f.fns.iter().all(|g| g.same_kinds(s))
        {
            self.put(Undo::Call(span, Some(s.clone())));
        }
        for p in f.pieces() {
            match p {
                Piece::Fn(sig) => {
                    checked = true;
                    let r = self.call_sig(
                        &sig,
                        false,
                        receiver.clone(),
                        positional,
                        named,
                        curry,
                        span,
                        what,
                    );
                    out = out.union(&r);
                }
                Piece::Dyn | Piece::Var(_) => out = out.union(&Ty::dynamic()),
                p if p.is_atoms() => {}
                p => {
                    self.error(span, format!("`{what}` is {}, not a function", p.ty()));
                    out = out.union(&Ty::dynamic());
                }
            }
        }
        if !checked {
            for a in positional.iter().chain(named.iter().map(|(_, a)| a)) {
                self.expr(a);
            }
        }
        out
    }

    /// A call of a function of signature `sig`; `declared` when it is the declared function
    /// itself, whose defaults every call can fill, and not a value of its type, which fills
    /// only closed ones. A call elaboration rejects gives the unknown, unchecked.
    #[allow(clippy::too_many_arguments)]
    fn call_sig(
        &mut self,
        sig: &Sig,
        declared: bool,
        receiver: Option<Arg>,
        positional: &'a [Expr],
        named: &'a [(String, Expr)],
        curry: bool,
        span: Span,
        what: &str,
    ) -> Ty {
        let n = sig.params.len();
        let mut slots: Vec<Option<&'a Expr>> = vec![None; n];
        let mut next = 0;
        let has_receiver = receiver.is_some();
        if has_receiver {
            if n == 0 {
                return Ty::dynamic();
            }
            next = 1;
        }
        for a in positional {
            match sig.params.get(next) {
                Some(p) if p.positional || !declared && sig.params.iter().all(|p| p.positional) => {
                    slots[next] = Some(a);
                    next += 1;
                }
                _ => return Ty::dynamic(),
            }
        }
        for (name, a) in named {
            match sig.params.iter().position(|p| *p.name == **name) {
                Some(j)
                    if !sig.params[j].positional
                        && slots[j].is_none()
                        && !(has_receiver && j == 0) =>
                {
                    slots[j] = Some(a)
                }
                _ => return Ty::dynamic(),
            }
        }
        let missing: Vec<usize> = (0..n)
            .filter(|&j| slots[j].is_none() && !(has_receiver && j == 0))
            .collect();
        if curry {
            if missing.is_empty() || missing.iter().any(|&j| sig.params[j].positional) {
                return Ty::dynamic();
            }
        } else if missing
            .iter()
            .any(|&j| !matches!(sig.params[j].default, Some((_, _, closed)) if declared || closed))
        {
            return Ty::dynamic();
        }
        let mut args: Vec<Option<Arg>> = Vec::new();
        for (j, s) in slots.iter().enumerate() {
            args.push(match s {
                _ if has_receiver && j == 0 => receiver.clone(),
                Some(a) => {
                    let want = Ty::union_all(sig.arrows.iter().map(|ar| &ar.params[j]));
                    Some(self.arg(a, Some(&want)))
                }
                None => None,
            });
        }
        let label = format!("`{what}`");
        let (result, kept) = self.apply(&label, sig, args, false, span);
        if !curry {
            return result;
        }
        let params: Vec<SParam> = missing.iter().map(|&j| sig.params[j].clone()).collect();
        let arrows = kept
            .iter()
            .map(|&k| Arrow {
                params: missing
                    .iter()
                    .map(|&j| sig.arrows[k].params[j].clone())
                    .collect(),
                result: sig.arrows[k].result.clone(),
            })
            .collect();
        Ty::func(Arc::new(Sig {
            params,
            arrows,
            bounds: sig.bounds.clone(),
        }))
    }

    /// `x.f(args)` and `x?.f(args)`: the call `f(x, args)`; `?.` passes `x`'s atoms around it.
    #[allow(clippy::too_many_arguments)]
    fn member(
        &mut self,
        of: &'a Expr,
        name: &str,
        safe: bool,
        member: Span,
        positional: &'a [Expr],
        named: &'a [(String, Expr)],
        curry: bool,
        span: Span,
    ) -> Ty {
        let mut x = self.arg(of, None);
        let atoms = x.ty.loose();
        if safe {
            x = Arg::of(x.ty.without_loose());
        }
        let out = match self.t.res.uses.get(&member) {
            Some(Ref::Bound(ids)) if ids.len() == 1 => {
                let id = ids[0];
                let f = self.env.get(&id).cloned().unwrap_or_else(Ty::dynamic);
                if self.t.funcs.contains_key(&id) {
                    match only_fn(&f) {
                        Some(sig) => {
                            self.call_sig(&sig, true, Some(x), positional, named, curry, span, name)
                        }
                        None => Ty::dynamic(),
                    }
                } else {
                    self.call_value(&f, name, Some(x), positional, named, curry, span)
                }
            }
            Some(Ref::Bound(_)) => Ty::dynamic(),
            _ => match crate::resolve::prelude_layer(name) {
                Some(1) if positional.is_empty() && named.is_empty() && !curry => {
                    self.word(name, &[], Some(x), span)
                }
                _ => Ty::dynamic(),
            },
        };
        match safe {
            true => out.union(&Ty::set(atoms)),
            false => out,
        }
    }

    /// `f[k]` on a declared function is a section; `t[i]` with a literal `i` the tuple's
    /// component; else an application.
    fn index(&mut self, of: &'a Expr, k: &'a Expr, span: Span) -> Ty {
        if self.declared(of).is_some() {
            self.expr(k);
            return Ty::dynamic();
        }
        let v = self.expr(of);
        let ExprKind::Int { .. } = &k.kind else {
            let x = self.arg(k, None);
            let mut out = self.passing(&v, "a call", span);
            for p in v.pieces() {
                match p {
                    Piece::Fn(sig) => {
                        let r = self
                            .apply("this function", &sig, vec![Some(x.clone())], false, span)
                            .0;
                        out = out.union(&r);
                    }
                    Piece::Dyn | Piece::Var(_) => out = out.union(&Ty::dynamic()),
                    p if p.is_atoms() => {}
                    p => {
                        self.error(span, format!("this value is {}, not a function", p.ty()));
                        out = out.union(&Ty::dynamic());
                    }
                }
            }
            return out;
        };
        let i = match literal(k).map(|l| l.value) {
            Some(Value::Int(i)) => i,
            _ => return Ty::dynamic(),
        };
        let mut out = self.passing(&v, "an index", span);
        for p in v.pieces() {
            match p {
                Piece::Tuple(cs) => match usize::try_from(i).ok().and_then(|i| cs.get(i)) {
                    Some(c) => out = out.union(c),
                    None => self.error(
                        span,
                        format!("{} has no component {i}", Ty::tuple(cs.clone())),
                    ),
                },
                Piece::Dyn | Piece::Var(_) => out = out.union(&Ty::dynamic()),
                p if p.is_atoms() => {}
                p => self.error(span, format!("`[{i}]` takes a tuple, not {}", p.ty())),
            }
        }
        out
    }

    /// A lambda with no expected type: its parameters positional, typed by their annotations.
    fn lambda(&mut self, params: &'a [Param], body: &'a Expr) -> Ty {
        let mut tys = Vec::new();
        for p in params {
            let t = match &p.ty {
                Some(t) => self.ty_of(t),
                None => Ty::dynamic(),
            };
            let id = self.id(p.span, &p.name);
            self.env.insert(id, t.clone());
            tys.push(t);
        }
        let result = self.body(body, None);
        let names = params
            .iter()
            .map(|p| SParam {
                name: p.name.as_str().into(),
                positional: true,
                default: None,
            })
            .collect();
        Ty::func(Arc::new(Sig::one(names, tys, result)))
    }

    fn body(&mut self, body: &'a Expr, want: Option<&Ty>) -> Ty {
        match &body.kind {
            ExprKind::Block(stmts) => self.scope(stmts, false),
            _ => self.expr_at(body, want),
        }
    }

    /// A lambda in a slot of the function type `e`: its first parameters take `e`'s
    /// positional ones, in order, and the rest `e`'s named ones by name; a parameter `e`
    /// does not pass needs a default.
    fn fit_lambda(&mut self, params: &'a [Param], body: &'a Expr, e: &Arc<Sig>, span: Span) -> Ty {
        let pos: Vec<usize> = (0..e.params.len())
            .filter(|&j| e.params[j].positional)
            .collect();
        let mut order: Vec<Option<usize>> = vec![None; e.params.len()];
        let mut extra = Vec::new();
        if params.len() < pos.len() {
            self.error(
                span,
                format!(
                    "the lambda takes {} parameter{}, and `{e}` passes {} by position",
                    params.len(),
                    if params.len() == 1 { "" } else { "s" },
                    pos.len()
                ),
            );
            return Ty::func(e.clone());
        }
        for (i, p) in params.iter().enumerate() {
            if i < pos.len() {
                order[pos[i]] = Some(i);
                continue;
            }
            match e
                .params
                .iter()
                .position(|q| !q.positional && *q.name == *p.name)
            {
                Some(j) if order[j].is_none() => order[j] = Some(i),
                _ if p.default.is_some() => extra.push(i),
                _ => {
                    let free: Vec<String> = (0..e.params.len())
                        .filter(|&j| !e.params[j].positional && order[j].is_none())
                        .map(|j| format!("`{}`", e.params[j].name))
                        .collect();
                    let fix = match free.first() {
                        Some(f) => format!(": rename it {f}"),
                        None => String::new(),
                    };
                    self.error(
                        p.span,
                        format!(
                            "the lambda's parameter `{}` is not a parameter of `{e}`{fix}",
                            p.name
                        ),
                    );
                    return Ty::func(e.clone());
                }
            }
        }
        for arrow in &e.arrows {
            for (j, o) in order.iter().enumerate() {
                if let Some(i) = o {
                    let p = &params[*i];
                    let mut t = arrow.params[j].clone();
                    if let Some(a) = &p.ty {
                        let a = self.ty_of(a);
                        if !t.subtype(&a) {
                            self.error(
                                p.span,
                                format!(
                                    "the lambda's parameter `{}` is {a}, and `{e}` passes {t}",
                                    p.name
                                ),
                            );
                        }
                        t = a;
                    }
                    let id = self.id(p.span, &p.name);
                    self.env.insert(id, t);
                }
            }
            for &i in &extra {
                let p = &params[i];
                let t = self.expr(p.default.as_ref().expect("a default"));
                let id = self.id(p.span, &p.name);
                self.env.insert(id, t);
            }
            let r = self.body(body, Some(&arrow.result));
            if !r.subtype(&arrow.result) {
                self.error(
                    body.span,
                    format!("the lambda returns {r}, and `{e}` returns {}", arrow.result),
                );
            }
        }
        let identity = extra.is_empty() && order.iter().enumerate().all(|(j, o)| *o == Some(j));
        if !identity {
            self.put(Undo::Fit(span, Some(Fit::Lambda { order, extra })));
        }
        Ty::func(e.clone())
    }

    /// A declared function in a slot of the function type `e`: the same number of positional
    /// parameters and the same named ones, in any order, and types that fit.
    fn fit_declared(&mut self, id: usize, e: &Arc<Sig>, span: Span) -> Ty {
        let f = self.t.funcs[&id];
        let own = self.env.get(&id).cloned().unwrap_or_else(Ty::dynamic);
        let Some(s) = only_fn(&own) else {
            return own;
        };
        let pos = |s: &Sig| s.params.iter().filter(|p| p.positional).count();
        let mut from = Vec::new();
        let mut k = 0;
        let mut ok = pos(&s) == pos(e) && s.params.len() == e.params.len();
        let epos: Vec<usize> = (0..e.params.len())
            .filter(|&j| e.params[j].positional)
            .collect();
        for p in &s.params {
            if !ok {
                break;
            }
            if p.positional {
                from.push(epos[k]);
                k += 1;
            } else {
                match e
                    .params
                    .iter()
                    .position(|q| !q.positional && q.name == p.name)
                {
                    Some(j) => from.push(j),
                    None => ok = false,
                }
            }
        }
        if !ok {
            let names: Vec<&str> = f.params.iter().map(|p| p.name.as_str()).collect();
            let call: Vec<String> = names.iter().map(|n| format!("{n}: {n}")).collect();
            self.error(
                span,
                format!(
                    "the parameters of `{}` ({}) do not fit `{e}`: declare them as it passes them, \
                     with `positional` where it passes by position, or pass a lambda, ({}) -> {}({})",
                    f.name,
                    s.params
                        .iter()
                        .map(|p| match p.positional {
                            true => format!("positional {}", p.name),
                            false => p.name.to_string(),
                        })
                        .collect::<Vec<_>>()
                        .join(", "),
                    names.join(", "),
                    f.name,
                    call.join(", ")
                ),
            );
            return Ty::func(e.clone());
        }
        // `s` with its parameters in `e`'s order.
        let mut inv = vec![0; from.len()];
        for (i, &j) in from.iter().enumerate() {
            inv[j] = i;
        }
        let permuted = Sig {
            bounds: s.bounds.clone(),
            params: e.params.clone(),
            arrows: s
                .arrows
                .iter()
                .map(|a| Arrow {
                    params: inv.iter().map(|&i| a.params[i].clone()).collect(),
                    result: a.result.clone(),
                })
                .collect(),
        };
        if !ty::fits_sig(&permuted, e) {
            self.error(span, format!("`{}` is `{s}`, not `{e}`", f.name));
        }
        if from.iter().enumerate().any(|(i, &j)| i != j) {
            self.put(Undo::Fit(span, Some(Fit::Adapter { from })));
        }
        Ty::func(e.clone())
    }

    /// The type a type expression denotes; a port's type is unknown here, and elaboration
    /// reports it.
    fn ty_of(&mut self, t: &Type) -> Ty {
        match &t.kind {
            TypeKind::Name(n) => match n.as_str() {
                "int" => Ty::carrier(Carrier::Int),
                "rat" => Ty::carrier(Carrier::Rat),
                "f64" => Ty::carrier(Carrier::F64),
                "bool" => Ty::carrier(Carrier::Bool),
                "String" => Ty::carrier(Carrier::Str),
                _ => Ty::dynamic(),
            },
            TypeKind::Atom(a) => Ty::set(KType::atom(a)),
            TypeKind::Tuple(ts) => Ty::tuple(ts.iter().map(|t| self.ty_of(t)).collect()),
            TypeKind::Union(ts) => {
                let ts: Vec<Ty> = ts.iter().map(|t| self.ty_of(t)).collect();
                Ty::union_all(&ts)
            }
            TypeKind::And(ts) => {
                let mut ts = ts
                    .iter()
                    .map(|t| self.ty_of(t))
                    .collect::<Vec<_>>()
                    .into_iter();
                let first = ts.next().unwrap_or_else(Ty::dynamic);
                ts.fold(first, |a, b| a.meet(&b))
            }
            TypeKind::Diff(a, b) => {
                let (a, b) = (self.ty_of(a), self.ty_of(b));
                a.diff(&b)
            }
            TypeKind::Arrow { params, result, .. } => {
                let tys = params.iter().map(|p| self.ty_of(&p.ty)).collect();
                let result = self.ty_of(result);
                let names = params
                    .iter()
                    .map(|p| SParam {
                        name: p.name.clone().unwrap_or_default().into(),
                        positional: p.positional || p.name.is_none(),
                        default: None,
                    })
                    .collect();
                Ty::func(Arc::new(Sig::one(names, tys, result)))
            }
        }
    }

    /// The derivation of an application `apply` rejects: each argument's, in order, then each
    /// arrow of `sig`, the constraints it failed.
    fn applied(&self, what: &str, sig: &Sig, args: &[Option<Arg>], span: Span) -> Vec<Note> {
        let mut out = Vec::new();
        for a in args.iter().flatten() {
            match (&a.lit, a.at) {
                (Some(l), Some(at)) => out.push(Note {
                    span: at,
                    text: format!("this literal, {}, is {}", l.text, a.ty),
                }),
                (None, Some(at)) => self.derive_into(at, &mut out, 0),
                _ => {}
            }
        }
        for arrow in &sig.arrows {
            let one = Sig {
                params: sig.params.clone(),
                arrows: vec![arrow.clone()],
                bounds: sig.bounds.clone(),
            };
            out.push(Note {
                span,
                text: format!("{what} takes {one}"),
            });
        }
        out
    }

    /// The repairs of a rejected application the checker discharges: each argument wrapped
    /// in a prelude word, when the application then checks, tried with the checker's state
    /// restored after.
    fn repairs(
        &mut self,
        what: &str,
        sig: &Sig,
        args: &[Option<Arg>],
        pass: bool,
        span: Span,
    ) -> Vec<Note> {
        let mut out = Vec::new();
        if self.trying {
            return out;
        }
        for (i, a) in args.iter().enumerate() {
            let Some(Arg {
                lit: None,
                at: Some(at),
                ty,
            }) = a
            else {
                continue;
            };
            for w in ["String", "int", "rat", "f64"] {
                let Some(r) = converted(&word_sig(w), ty) else {
                    continue;
                };
                let mut with = args.to_vec();
                with[i] = Some(Arg::of(r));
                let saved = self.mark();
                self.trying = true;
                self.apply(what, sig, with, pass, span);
                let ok = self.info.errors.len() == saved.errors;
                self.trying = false;
                self.undo(&saved);
                if ok {
                    out.push(Note {
                        span: *at,
                        text: format!("repair: wrap this in `{w}(…)`; the checker accepts that"),
                    });
                }
            }
        }
        out
    }

    /// Adds `note` to each error from the `from`th on that lacks it.
    fn also(&mut self, from: usize, note: Note) {
        for e in &mut self.info.errors[from..] {
            if !e.notes.contains(&note) {
                e.notes.push(note.clone());
            }
        }
    }

    /// Applies `sig` to `args`, a missing one filled by its default. When `pass` holds, as
    /// for an operator or a prelude word, an argument's atoms pass through, two arguments'
    /// merged into `#errs`. Gives the result and the arrows kept.
    fn apply(
        &mut self,
        what: &str,
        sig: &Sig,
        mut args: Vec<Option<Arg>>,
        pass: bool,
        span: Span,
    ) -> (Ty, Vec<usize>) {
        let mut out = Ty::empty();
        if pass {
            let atoms: Vec<Ty> = args
                .iter()
                .flatten()
                .filter(|a| a.lit.is_none())
                .map(|a| Ty::set(a.ty.loose()))
                .collect();
            passed(&mut out, atoms.iter());
            for a in args.iter_mut().flatten() {
                a.ty = a.ty.without_loose();
            }
        }
        let r = match sig.arrows.len() {
            1 => self.apply_one(what, sig, &args, span),
            _ => self.apply_many(what, sig, &mut args, span),
        };
        match r {
            Ok((t, kept)) => (out.union(&t), kept),
            Err(message) => {
                let mut notes = self.applied(what, sig, &args, span);
                for a in args.iter().flatten() {
                    for n in self.reasons(&a.ty) {
                        if !notes.contains(&n) {
                            notes.push(n);
                        }
                    }
                }
                notes.extend(self.repairs(what, sig, &args, pass, span));
                self.error_with(span, message, notes);
                (out.union(&Ty::dynamic()), Vec::new())
            }
        }
    }

    /// The message of an application that does not check: the arguments, each class shown
    /// as the carriers left to it.
    fn rejected(&self, what: &str, args: &[Option<Arg>]) -> String {
        self.rejected_at(what, args, None)
    }

    /// [`Self::rejected`], with argument `i` shown as the piece `p` of it that failed.
    fn rejected_at(&self, what: &str, args: &[Option<Arg>], at: Option<(usize, &Piece)>) -> String {
        let shown: Vec<String> = args
            .iter()
            .enumerate()
            .map(|(i, a)| match (a, at) {
                (_, Some((j, p))) if i == j => self.show(&p.ty()),
                (Some(a), _) => self.show(&a.ty),
                (None, _) => "_".into(),
            })
            .collect();
        format!("{what} does not take ({})", shown.join(", "))
    }

    /// [`Self::apply`] of a signature of one arrow. The arguments at the parameters that are
    /// one bounded variable share a carrier: their classes merge, and their literals adopt
    /// it. Every other argument is checked piece by piece, a class taking the carriers its
    /// parameter allows.
    fn apply_one(
        &mut self,
        what: &str,
        sig: &Sig,
        args: &[Option<Arg>],
        span: Span,
    ) -> Result<(Ty, Vec<usize>), String> {
        let arrow = &sig.arrows[0];
        let fail = |ck: &Self| Err(ck.rejected(what, args));
        let mut binds = Binds::new();
        let mut grouped = vec![false; args.len()];
        for (v, &m) in &sig.bounds {
            let at: Vec<usize> = (0..args.len())
                .filter(|&i| args[i].is_some() && arrow.params[i] == Ty::var(v.clone()))
                .collect();
            let lit_at = at
                .iter()
                .any(|&i| args[i].as_ref().is_some_and(|a| a.lit.is_some()));
            if at.len() < 2 && !lit_at {
                continue;
            }
            let (mut carriers, mut classes, mut lits) = (0u8, Vec::new(), Vec::new());
            for &i in &at {
                grouped[i] = true;
                let a = args[i].as_ref().expect("an argument");
                if let Some(l) = &a.lit {
                    lits.push(l.clone());
                    continue;
                }
                for p in a.ty.pieces() {
                    match (self.class_of(&p), p.carrier()) {
                        (Some(k), _) => classes.push(k),
                        _ if matches!(p, Piece::Dyn | Piece::Var(_)) => {}
                        (None, Some(c)) => carriers |= c.bit(),
                        (None, None) => return fail(self),
                    }
                }
            }
            let bound = match (carriers.count_ones(), classes.first()) {
                (n, _) if n > 1 => return fail(self),
                (1, _) => {
                    let c = Carrier::of_mask(carriers).next().expect("one carrier");
                    if m & carriers == 0 {
                        return fail(self);
                    }
                    for &k in &classes {
                        if !self.restrict(k, c.bit(), what, span) {
                            return fail(self);
                        }
                    }
                    for l in &lits {
                        self.adopt_to(l, c);
                    }
                    Ty::carrier(c)
                }
                (_, Some(&k)) => {
                    for &j in &classes[1..] {
                        if !self.merge(k, j, what, span) {
                            return fail(self);
                        }
                    }
                    if !self.restrict(k, m, what, span) {
                        return fail(self);
                    }
                    for l in &lits {
                        if !self.join(k, l, false) {
                            return fail(self);
                        }
                    }
                    Ty::var(format!("${}", self.find(k)).into())
                }
                _ if !lits.is_empty() => {
                    // The carrier of the bound its literals adopt fewest times to.
                    let adoptions = |c: Carrier| {
                        lits.iter()
                            .all(|l| adoptable(l, c))
                            .then(|| lits.iter().filter(|l| lit_carrier(&l.value) != c).count())
                    };
                    let Some(c) = Carrier::of_mask(m)
                        .filter_map(|c| adoptions(c).map(|n| (n, c)))
                        .min_by_key(|&(n, _)| n)
                        .map(|(_, c)| c)
                    else {
                        return fail(self);
                    };
                    for l in &lits {
                        self.adopt_to(l, c);
                    }
                    Ty::carrier(c)
                }
                _ => Ty::dynamic(),
            };
            binds.insert(v.clone(), bound);
        }
        for (i, a) in args.iter().enumerate() {
            let Some(a) = a else {
                continue;
            };
            if grouped[i] {
                continue;
            }
            let p = &arrow.params[i];
            // A parameter that is a class of the function around: the argument flows into it.
            if let Some(k) = self.class_of_ty(p) {
                let ok = match &a.lit {
                    Some(l) => self.join(k, l, false),
                    None => self.flow(k, &a.ty, what, span),
                };
                if !ok {
                    return fail(self);
                }
                continue;
            }
            if let Some(l) = &a.lit {
                let t = match p.numeric_carrier() {
                    // A literal that cannot adopt is its own error, and the application's none.
                    Some(c) if adopt(l, c).is_err() => {
                        self.adopt_to(l, c);
                        continue;
                    }
                    Some(c) => self.adopt_to(l, c),
                    None => a.ty.clone(),
                };
                if !t.sub(p, &mut binds) {
                    return fail(self);
                }
                continue;
            }
            for piece in a.ty.pieces() {
                let ok = match self.class_of(&piece) {
                    _ if piece == Piece::Dyn => true,
                    Some(_) if p.dynamic => true,
                    Some(_) if !p.vars.is_empty() => piece.ty().sub(p, &mut binds),
                    Some(k) => self.restrict(k, mask_of(p), what, span),
                    None => piece.ty().sub(p, &mut binds),
                };
                if !ok {
                    return Err(self.rejected_at(what, args, Some((i, &piece))));
                }
            }
        }
        // Each bounded variable's binding is within its bound.
        for (v, &m) in &sig.bounds {
            let Some(t) = binds.get(v).cloned() else {
                continue;
            };
            for piece in t.pieces() {
                let ok = match (self.class_of(&piece), piece.carrier()) {
                    (Some(k), _) => self.restrict(k, m, what, span),
                    _ if matches!(piece, Piece::Dyn | Piece::Var(_)) => true,
                    (None, Some(c)) => m & c.bit() != 0,
                    (None, None) => false,
                };
                if !ok {
                    return fail(self);
                }
            }
        }
        binds.retain(|v, _| class_id(v).is_none());
        let mut out = Ty::empty();
        let given: Vec<&Arg> = args.iter().flatten().collect();
        if given.iter().any(|a| a.ty.dynamic) {
            out = out.union(&Ty::dynamic());
        }
        if given
            .iter()
            .all(|a| a.lit.is_some() || a.ty.pieces().iter().any(|p| *p != Piece::Dyn))
        {
            out = out.union(&close(&arrow.result.replace(&binds), sig));
        }
        Ok((out, vec![0]))
    }

    /// [`Self::apply`] of a signature of several arrows, each over one carrier or a tuple:
    /// an operator, a prelude word, or a section of one. The classes of the arguments merge,
    /// since every arrow takes one carrier for all its parameters, and its literals join
    /// them; without a class, each literal adopts the carrier of its parameter on the
    /// arrows that adopt fewest. Then the arguments' pieces are taken in turn, each state
    /// the arrows still alive: a state per set of arrows, not per combination of pieces.
    fn apply_many(
        &mut self,
        what: &str,
        sig: &Sig,
        args: &mut [Option<Arg>],
        span: Span,
    ) -> Result<(Ty, Vec<usize>), String> {
        let mut class = None;
        for a in args.iter().flatten() {
            for p in a.ty.pieces() {
                if let Some(k) = self.class_of(&p) {
                    match class {
                        None => class = Some(k),
                        Some(c) => {
                            if !self.merge(c, k, what, span) {
                                return Err(self.rejected(what, args));
                            }
                        }
                    }
                }
            }
        }
        let kept: Vec<usize> = match class {
            Some(k) => {
                for a in args.iter().flatten() {
                    if let Some(l) = &a.lit
                        && !self.join(k, l, false)
                    {
                        return Err(self.rejected(what, args));
                    }
                }
                (0..sig.arrows.len()).collect()
            }
            None => match self.fewest(what, sig, args)? {
                Some(kept) => kept,
                None => return Ok((Ty::dynamic(), Vec::new())),
            },
        };
        // The states: the arrows alive, whether a piece was unknown, and the first pieces
        // that reached it, by argument.
        let n = args.len();
        let mut states: Vec<(Vec<usize>, bool, Vec<Option<Piece>>)> =
            vec![(kept.clone(), false, Vec::new())];
        for (i, a) in args.iter().enumerate() {
            let pieces: Vec<Option<Piece>> = match a {
                None => vec![None],
                Some(a) if a.lit.is_some() && class.is_some() => {
                    vec![Some(Piece::Var(format!("${}", class.unwrap()).into()))]
                }
                Some(a) => a.ty.pieces().into_iter().map(Some).collect(),
            };
            let mut next: Vec<(Vec<usize>, bool, Vec<Option<Piece>>)> = Vec::new();
            for (alive, dyn_, path) in &states {
                for p in &pieces {
                    let (alive, dyn_) = match p {
                        None => (alive.clone(), *dyn_),
                        // A class may still take any value its mask allows, so it keeps
                        // every arrow; the restriction after the arguments narrows it.
                        Some(p) if self.class_of(p).is_some() => (alive.clone(), *dyn_),
                        Some(Piece::Dyn | Piece::Var(_)) => (alive.clone(), true),
                        Some(p) => {
                            let alive = alive
                                .iter()
                                .copied()
                                .filter(|&k| {
                                    p.ty().sub(&sig.arrows[k].params[i], &mut Binds::new())
                                })
                                .collect();
                            (alive, *dyn_)
                        }
                    };
                    if !next.iter().any(|s| s.0 == alive && s.1 == dyn_) {
                        let mut path = path.clone();
                        path.push(p.clone());
                        next.push((alive, dyn_, path));
                    }
                }
            }
            states = next;
        }
        let mut out = Ty::empty();
        for (alive, dyn_, path) in &states {
            let shown = |ck: &Self| {
                let shown: Vec<String> = path
                    .iter()
                    .map(|p| p.as_ref().map(|p| ck.show(&p.ty())).unwrap_or("_".into()))
                    .collect();
                format!("{what} does not take ({})", shown.join(", "))
            };
            let at: Vec<usize> = (0..n)
                .filter(|&i| path[i].as_ref().is_some_and(|p| self.class_of(p).is_some()))
                .collect();
            match class {
                Some(k) if !at.is_empty() => {
                    let mask_at =
                        |a: &Arrow| at.iter().fold(EVERY, |m, &i| m & mask_of(&a.params[i]));
                    let m = alive.iter().fold(0, |m, &j| m | mask_at(&sig.arrows[j]));
                    if alive.is_empty() || !self.restrict(k, m, what, span) {
                        return Err(shown(self));
                    }
                    if *dyn_ {
                        out = out.union(&Ty::dynamic());
                        continue;
                    }
                    let r = self.find(k);
                    let km = self.classes[r].mask;
                    let rel: Vec<&Arrow> = alive
                        .iter()
                        .map(|&j| &sig.arrows[j])
                        .filter(|a| mask_at(a) & km != 0)
                        .collect();
                    let follows = rel.iter().all(|a| {
                        let m = mask_at(a);
                        m.count_ones() == 1
                            && Carrier::of_mask(m)
                                .next()
                                .is_some_and(|c| Ty::carrier(c).subtype(&a.result))
                    });
                    if follows {
                        out = out.union(&Ty::var(format!("${r}").into()));
                        for a in &rel {
                            out = out.union(&Ty::set(a.result.atoms()));
                        }
                    } else {
                        for a in &rel {
                            out = out.union(&close(&a.result, sig));
                        }
                    }
                }
                _ if *dyn_ => out = out.union(&Ty::dynamic()),
                _ => {
                    let Some(&j) = alive.first() else {
                        return Err(shown(self));
                    };
                    let a = &sig.arrows[j];
                    let mut binds = Binds::new();
                    for (p, t) in path.iter().zip(&a.params) {
                        if let Some(p) = p {
                            p.ty().sub(t, &mut binds);
                        }
                    }
                    out = out.union(&close(&a.result.subst(&binds), sig));
                }
            }
        }
        Ok((out, kept))
    }

    /// The arrows of `sig` whose adoptions of the literal arguments are fewest, all the
    /// same, with those adoptions made and the arguments retyped.
    /// `None` when a literal adopts no arrow's carrier exactly, which is reported.
    fn fewest(
        &mut self,
        what: &str,
        sig: &Sig,
        args: &mut [Option<Arg>],
    ) -> Result<Option<Vec<usize>>, String> {
        let mut best: Option<(usize, Vec<(Span, Value)>)> = None;
        let mut kept = Vec::new();
        let mut adopt_error = None;
        for (k, arrow) in sig.arrows.iter().enumerate() {
            let mut need = Vec::new();
            let mut ok = true;
            for (a, p) in args.iter().zip(&arrow.params) {
                // An arrow no other argument can fit is no candidate.
                if let Some(Arg { lit: None, ty, .. }) = a {
                    ok &= ty.is_empty() || ty.meets(p);
                }
                let Some(Arg {
                    lit: Some(l), ty, ..
                }) = a
                else {
                    continue;
                };
                if ty.subtype(p) || p.dynamic {
                    continue;
                }
                match p.numeric_carrier().map(|c| adopt(l, c)) {
                    Some(Ok(Some(v))) if lit_ty(&v, l.neg).subtype(p) => need.push((l.span, v)),
                    Some(Err(m)) => {
                        adopt_error.get_or_insert((l.span, m));
                        ok = false;
                    }
                    // Kept as it is, the literal is checked as any argument is.
                    _ => ok &= ty.meets(p),
                }
            }
            if !ok {
                continue;
            }
            match &best {
                Some((n, _)) if *n < need.len() => {}
                Some((n, b)) if *n == need.len() && *b == need => kept.push(k),
                Some((n, _)) if *n == need.len() => {}
                _ => {
                    best = Some((need.len(), need));
                    kept = vec![k];
                }
            }
        }
        let Some((_, need)) = best else {
            if let Some((s, m)) = adopt_error {
                self.error(s, m);
                return Ok(None);
            }
            return Err(self.rejected(what, args));
        };
        for (s, v) in need {
            let neg = args
                .iter()
                .flatten()
                .any(|a| a.lit.as_ref().is_some_and(|l| l.span == s && l.neg));
            for a in args.iter_mut().flatten() {
                if a.lit.as_ref().is_some_and(|l| l.span == s) {
                    a.ty = lit_ty(&v, neg);
                }
            }
            self.put(Undo::Adopt(s, Some(v)));
        }
        Ok(Some(kept))
    }
}

/// The type of the one-parameter word `sig` applied to `t`, its atoms passing through; none
/// when a piece of `t` fits no arrow, an unknown one fitting only an arrow that takes any.
fn converted(sig: &Sig, t: &Ty) -> Option<Ty> {
    let mut out = Ty::set(t.loose());
    for p in t.without_loose().pieces() {
        let arrow = sig.arrows.iter().find(|a| match p {
            Piece::Dyn | Piece::Var(_) => a.params[0].dynamic,
            _ => p.ty().sub(&a.params[0], &mut Binds::new()),
        })?;
        out = out.union(&arrow.result);
    }
    Some(out)
}

/// `out` with the atoms of `ts` added: when two of them hold atoms, also `#errs`, which two
/// distinct failures merge into.
fn passed<'t>(out: &mut Ty, ts: impl Iterator<Item = &'t Ty>) {
    let mut n = 0;
    for t in ts {
        let a = t.atoms();
        if !a.is_empty() {
            n += 1;
            *out = out.union(&Ty::set(a));
        }
    }
    if n > 1 {
        *out = out.union(&Ty::set(errs()));
    }
}

/// `t` with the type variables of `sig`'s parameters that no argument bound made unknown.
fn close(t: &Ty, sig: &Sig) -> Ty {
    let mut own = Vec::new();
    for a in &sig.arrows {
        a.params.iter().for_each(|p| p.vars_in(&mut own));
    }
    let binds: Binds = own
        .into_iter()
        .filter(|v| !v.starts_with('$'))
        .map(|v| (v, Ty::dynamic()))
        .collect();
    t.subst(&binds)
}

/// The one function `t` is, when it is nothing else.
fn only_fn(t: &Ty) -> Option<Arc<Sig>> {
    match (
        &t.fns[..],
        t.set.is_empty() && t.tuples.is_empty() && t.vars.is_empty() && !t.dynamic,
    ) {
        ([s], true) => Some(s.clone()),
        _ => None,
    }
}

/// A write to one of [`Info`]'s maps: the key and the value, `None` for no entry. In the log,
/// the value is the one the write replaced.
#[derive(Clone)]
enum Undo {
    Adopt(Span, Option<Value>),
    Call(Span, Option<Arc<Sig>>),
    Fit(Span, Option<Fit>),
    Sig(usize, Option<Arc<Sig>>),
    Top(String, Option<Ty>),
    /// A class, while a repair is tried.
    Class(usize, Box<Class>),
}

/// How long the log and the errors were at a point.
struct Mark {
    log: usize,
    errors: usize,
}

/// Sets `$map[$key]` to `$value`, removing it for `None`, and gives the value it replaces.
macro_rules! set {
    ($map:expr, $key:expr, $value:expr) => {
        match $value {
            Some(v) => $map.insert($key.clone(), v),
            None => $map.remove(&$key),
        }
    };
}

impl Ck<'_, '_> {
    /// Makes the write `w`, logging the value it replaces.
    fn put(&mut self, w: Undo) {
        let undo = self.set(w);
        self.log.push(undo);
    }

    /// Makes the write `w` and gives the write that undoes it.
    fn set(&mut self, w: Undo) -> Undo {
        if let Undo::Class(k, c) = w {
            return Undo::Class(k, Box::new(std::mem::replace(&mut self.classes[k], *c)));
        }
        let i = &mut self.info;
        match w {
            Undo::Adopt(k, v) => Undo::Adopt(k, set!(i.adopt, k, v)),
            Undo::Call(k, v) => Undo::Call(k, set!(i.calls, k, v)),
            Undo::Fit(k, v) => Undo::Fit(k, set!(i.fits, k, v)),
            Undo::Sig(k, v) => Undo::Sig(k, set!(i.sigs, k, v)),
            Undo::Top(k, v) => {
                let old = set!(i.tops, k, v);
                Undo::Top(k, old)
            }
            Undo::Class(..) => unreachable!("a class is set above"),
        }
    }

    /// The point the checker is at.
    fn mark(&self) -> Mark {
        Mark {
            log: self.log.len(),
            errors: self.info.errors.len(),
        }
    }

    /// Undoes every write and error since `m`, the latest first.
    fn undo(&mut self, m: &Mark) {
        while self.log.len() > m.log {
            let w = self.log.pop().expect("longer than the mark");
            self.set(w);
        }
        self.info.errors.truncate(m.errors);
    }
}

/// `e` as a numeric literal, perhaps under one `-`.
fn literal(e: &Expr) -> Option<Lit> {
    let (inner, neg) = match &e.kind {
        ExprKind::Unary("-", a) => (&**a, true),
        _ => (e, false),
    };
    let text = |s: &str| s.chars().filter(|&c| c != '_').collect::<String>();
    let value = match &inner.kind {
        ExprKind::Int { radix, digits } => Value::int_text(&text(digits), *radix)?,
        ExprKind::Float(s) => Value::float(text(s).parse().ok()?),
        _ => return None,
    };
    Some(Lit {
        span: inner.span,
        value,
        neg,
        text: inner.to_string(),
    })
}

fn run(p: Prim, v: &Value) -> Option<Value> {
    eval(&Term::Prim(p, vec![Term::Lit(v.clone())])).ok()
}

/// The type of the literal `v`, under `-` when `neg`.
fn lit_ty(v: &Value, neg: bool) -> Ty {
    match neg {
        true => Ty::lit(&run(Prim::Neg, v).unwrap_or_else(|| v.clone())),
        false => Ty::lit(v),
    }
}

fn lit_carrier(v: &Value) -> Carrier {
    match v {
        Value::Float(_) => Carrier::F64,
        Value::Rat(_) => Carrier::Rat,
        _ => Carrier::Int,
    }
}

/// The order two literals adopt in: an integer the other's carrier.
fn rank(c: Carrier) -> u8 {
    match c {
        Carrier::Int => 0,
        _ => 1,
    }
}

/// The literal `l` as a `c`: `None` when it is one already, an error when it is not exactly
/// one.
fn adopt(l: &Lit, c: Carrier) -> Result<Option<Value>, String> {
    if lit_carrier(&l.value) == c || !adoptable(l, c) {
        return Ok(None);
    }
    let exact = match &l.value {
        Value::Float(_) => Rat::decimal(&l.text).map(Value::rat),
        v => run(Prim::CastRat, v),
    };
    let not = || Err(format!("`{}` is not {} {}", l.text, article(c), c.name()));
    let Some(exact) = exact else {
        return not();
    };
    let v = match c {
        Carrier::Int => run(Prim::CastInt, &exact),
        Carrier::Rat => Some(exact),
        Carrier::F64 => run(Prim::CastF64, &exact),
        _ => None,
    };
    match v {
        Some(v) if !matches!(v, Value::Atom(_)) => Ok(Some(v)),
        _ => not(),
    }
}

/// Whether `l` may adopt `c`: an integer literal any numeric carrier, a decimal one `f64`
/// and `rat`, which it denotes exactly, and not `int`.
fn adoptable(l: &Lit, c: Carrier) -> bool {
    c.numeric() && !(matches!(l.value, Value::Float(_)) && c == Carrier::Int)
}

fn article(c: Carrier) -> &'static str {
    match c {
        Carrier::Int | Carrier::F64 => "an",
        _ => "a",
    }
}

/// One arrow per carrier in `cs`, of `n` parameters of that carrier, returning `result` or
/// the carrier itself.
fn arrows(cs: &[Carrier], n: usize, result: impl Fn(Carrier) -> Ty) -> Vec<Arrow> {
    cs.iter()
        .map(|&c| Arrow {
            params: vec![Ty::carrier(c); n],
            result: result(c),
        })
        .collect()
}

fn positional(n: usize) -> Vec<SParam> {
    (0..n)
        .map(|i| SParam {
            name: format!("x{i}").into(),
            positional: true,
            default: None,
        })
        .collect()
}

/// An operator's arrows.
fn op_sig(op: &str) -> Sig {
    use Carrier::*;
    let same = |c: Carrier| Ty::carrier(c);
    let bool_ = |_| Ty::carrier(Bool);
    let div0 = |c: Carrier| Ty::carrier(c).union(&Ty::set(KType::atom("divByZero")));
    let (n, arrows) = match op {
        "+" | "-" | "*" => (2, arrows(&[Int, F64, Rat], 2, same)),
        "/" => (
            2,
            [arrows(&[F64], 2, same), arrows(&[Rat], 2, div0)].concat(),
        ),
        "div" | "mod" => (2, arrows(&[Int], 2, div0)),
        "**" => (2, arrows(&[Int, F64], 2, same)),
        "++" => (2, arrows(&[Str], 2, same)),
        "<" => (2, arrows(&[Int, F64, Rat, Str, Bool], 2, bool_)),
        "&&" => (2, arrows(&[Bool], 2, bool_)),
        "!" => (1, arrows(&[Bool], 1, bool_)),
        "neg" => (1, arrows(&[Int, F64, Rat], 1, same)),
        _ => return op_sig("neg"),
    };
    Sig {
        params: positional(n),
        arrows,
        bounds: BTreeMap::new(),
    }
}

/// A prelude word's arrows.
fn word_sig(w: &str) -> Arc<Sig> {
    use Carrier::*;
    let a = |names: &[&str]| {
        names
            .iter()
            .fold(Ty::empty(), |t, n| t.union(&Ty::set(KType::atom(n))))
    };
    let arrow = |from: Carrier, to: Carrier, fails: &[&str]| Arrow {
        params: vec![Ty::carrier(from)],
        result: Ty::carrier(to).union(&a(fails)),
    };
    let arrows = match w {
        "String" => vec![Arrow {
            params: vec![Ty::dynamic()],
            result: Ty::carrier(Str),
        }],
        "int" => vec![
            arrow(Int, Int, &[]),
            arrow(F64, Int, &["inexact", "invalid"]),
            arrow(Rat, Int, &["inexact"]),
            arrow(Str, Int, &["invalid"]),
        ],
        "rat" => vec![
            arrow(Int, Rat, &[]),
            arrow(F64, Rat, &["invalid"]),
            arrow(Rat, Rat, &[]),
            arrow(Str, Rat, &["invalid"]),
        ],
        "f64" => vec![
            arrow(Int, F64, &["inexact"]),
            arrow(F64, F64, &[]),
            arrow(Rat, F64, &["inexact"]),
            arrow(Str, F64, &["inexact", "invalid"]),
        ],
        "abs" => arrows(&[Int, F64, Rat], 1, Ty::carrier),
        "len" => vec![arrow(Str, Int, &[])],
        _ => vec![arrow(Str, Str, &[])],
    };
    Arc::new(Sig {
        params: positional(1),
        arrows,
        bounds: BTreeMap::new(),
    })
}

/// The class a type variable names: `$k` is class `k`.
fn class_id(v: &str) -> Option<usize> {
    v.strip_prefix('$')?.parse().ok()
}

/// The `n`th name of a signature's own type variables: `T`, `U`, `V`, `W`, `T5`, ….
fn var_name(n: usize) -> Arc<str> {
    match n {
        0..4 => ["T", "U", "V", "W"][n].into(),
        _ => format!("T{}", n + 1).into(),
    }
}

/// The variables of `s`, in order of first appearance.
fn sig_vars(s: &Sig) -> Vec<Arc<str>> {
    let mut out = Vec::new();
    for a in &s.arrows {
        a.params.iter().for_each(|p| p.vars_in(&mut out));
        a.result.vars_in(&mut out);
    }
    out
}

/// The carriers a value of `t` may be of, and [`OTHER`] if it may be a tuple, a function or
/// another value that is no atom: every value if `t` is unknown or has a variable.
fn mask_of(t: &Ty) -> u8 {
    if t.dynamic || !t.vars.is_empty() {
        return EVERY;
    }
    let mut m = 0;
    for c in Carrier::ALL {
        if !(&t.set & &c.ty()).is_empty() {
            m |= c.bit();
        }
    }
    let carriers = Carrier::ALL.into_iter().fold(atoms(), |s, c| &s | &c.ty());
    if !t.tuples.is_empty() || !t.fns.is_empty() || !(&t.set - &carriers).is_empty() {
        m |= OTHER;
    }
    m
}
