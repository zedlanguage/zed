//! The checker (step L1.26): resolution rules 1, 3 and 4 of DESIGN.md "Resolution". Each
//! node is typed bottom up; an `is` test narrows the name it tests in each branch it guards;
//! each declared function gets a signature from its body. A numeric literal adopts the
//! carrier an operator or a parameter expects, exactly or not at all (sec:domains). A lambda
//! in a slot of function type takes its parameter types and kinds from that type, and a
//! declared function passed there must have its parameter kinds.
//!
//! A function's parameter with neither a type nor a closed default is inferred. The body is
//! first checked with the parameter unknown, `_`: an error there does not depend on the
//! parameter and is reported. Then with a type variable: when the body checks, the function
//! is generic. Else each carrier is tried, every combination for several parameters, and
//! the function gets one arrow per combination that checks, the arrows with the fewest
//! literal adoptions (a literal has one value, so the arrows kept must adopt alike).
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

use ty::{Arrow, Binds, Carrier, Piece, SParam, Sig, Ty, errs};

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

/// How many checks of a function's whole body a signature search that is not inside another
/// may make. A check costs the function's size less the functions declared in it, the
/// searches of those counted at their own sizes, so the searches inside one function cost at
/// most `RUNS` times its size, however they nest.
const RUNS: usize = 20_000;

/// How many contexts, the types of the binders it reads from outside, one function declared
/// inside another is searched in, inside a search not inside another; in any further context
/// its signature gives `_` for its undeclared parameters and its result. A search in a new
/// context checks the functions declared inside it in new contexts, so without this the
/// contexts, and the searches, multiply with the depth of the nesting.
const CONTEXTS: usize = 64;

/// The most piece combinations one application checks before it gives the unknown.
const COMBOS: usize = 256;

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

/// An expression's type as the checker last found it, and where it comes from. A signature
/// search runs the body once per combination, and each run records every subexpression
/// before any error in it is derived, so a derivation reads only its own run's records.
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

/// The most failed combinations a signature search lists.
const SHOWN: usize = 12;

struct Ck<'t, 'a> {
    t: &'t Tables<'a>,
    env: HashMap<usize, Ty>,
    info: Info,
    /// Each write to `info`'s maps, with the value it replaced, so that a run of a search
    /// is undone by what it wrote rather than by a copy of all of `info`.
    log: Vec<Undo>,
    fresh: usize,
    /// What the outermost search under way has spent, in bytes of bodies checked.
    runs: usize,
    /// What it may spend: `RUNS` times the size of its function.
    budget: usize,
    /// Each expression's type, by its span, as last found.
    seen: HashMap<Span, Seen<'a>>,
    /// Where each binder's type comes from.
    whence: HashMap<usize, Origin>,
    /// Whether a repair is being tried, so its errors offer none.
    trying: bool,
    /// Whether a signature search is checking a combination whose errors it discards, so
    /// that they carry no notes.
    quiet: bool,
    /// How many signature searches are under way, one inside another.
    searching: usize,
    /// The signatures found inside the outermost search, by the function's statement and
    /// what its search reads from outside it.
    memo: HashMap<Span, HashMap<Key, Arc<Searched>>>,
    /// The context of each search under way, the outermost first.
    contexts: Vec<usize>,
    /// The number of each context: by the function's statement, the context of the search
    /// around it and the types of the binders it reads from the function around it.
    numbers: HashMap<Span, HashMap<Context, (usize, usize)>>,
    /// How many contexts are numbered.
    numbered: usize,
    /// The adoptions of the nested searches found inside the outermost search, each with
    /// its number: those differing from before the search, and the numbers of the nested
    /// searches inside it with any.
    summaries: BTreeMap<Adoptions, usize>,
}

impl<'t, 'a> Ck<'t, 'a> {
    fn new(t: &'t Tables<'a>) -> Self {
        Ck {
            t,
            env: HashMap::new(),
            info: Info::default(),
            log: Vec::new(),
            fresh: 0,
            runs: 0,
            budget: 0,
            seen: HashMap::new(),
            whence: HashMap::new(),
            trying: false,
            quiet: false,
            searching: 0,
            memo: HashMap::new(),
            contexts: Vec::new(),
            numbers: HashMap::new(),
            numbered: 0,
            summaries: BTreeMap::new(),
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
        if self.quiet {
            return out;
        }
        for &s in spans {
            self.derive_into(s, &mut out, 0);
        }
        out
    }

    fn derive_into(&self, span: Span, out: &mut Vec<Note>, depth: usize) {
        let Some((ty, src)) = self.seen.get(&span) else {
            return;
        };
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
                let sig = self.signature(f, s.span);
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

    /// The signature of a declared function. Each run of a search checks the functions
    /// declared in its body again, so inside the outermost search a function's signature is
    /// found once for each set of types of the binders it reads from outside: the searches
    /// of nested functions cost the sum of their runs, not the product. Those types are
    /// numbered as a context, from the context of the search around it and the types of the
    /// binders it reads from the function around it, so the key costs no more than those. A search inside
    /// another leaves its writes in the log as one entry, which the maps do not hold, so
    /// that finding it again costs `O(1)`, not the size of the function; the outermost
    /// search makes them once, when it ends.
    fn signature(&mut self, f: &'a Function, span: Span) -> Arc<Sig> {
        let key = Key {
            around: self.contexts.last().copied(),
            quiet: self.quiet,
            trying: self.trying,
            outer: self
                .t
                .outer(span)
                .iter()
                .map(|b| self.env.get(b).cloned())
                .collect(),
        };
        let found = self.memo.get(&span).and_then(|m| m.get(&key)).cloned();
        if let Some(s) = found {
            self.info.errors.extend(s.errors.iter().cloned());
            let sig = s.sig.clone();
            self.log.push(Undo::Nested(s));
            return sig;
        }
        let start = self.mark();
        if self.searching == 0 {
            self.runs = 0;
            self.budget = RUNS * (span.end - span.start).max(1);
        }
        self.searching += 1;
        let context = (key.around, key.outer.clone());
        let numbers = self.numbers.entry(span).or_default();
        let count = numbers.len();
        let (number, nth) = *numbers.entry(context).or_insert((self.numbered, count));
        if number == self.numbered {
            self.numbered += 1;
        }
        self.contexts.push(number);
        let sig = self.infer(f, span, nth >= CONTEXTS);
        self.contexts.pop();
        self.searching -= 1;
        if self.searching == 0 {
            self.memo.clear();
            self.summaries.clear();
            self.numbers.clear();
            self.numbered = 0;
            let mut todo: Vec<Arc<Searched>> = self.log[start.log..]
                .iter()
                .filter_map(|w| match w {
                    Undo::Nested(s) => Some(s.clone()),
                    _ => None,
                })
                .collect();
            while let Some(s) = todo.pop() {
                for w in &s.wrote {
                    match w {
                        Undo::Nested(c) => todo.push(c.clone()),
                        w => self.put(w.clone()),
                    }
                }
            }
            return sig;
        }
        let wrote = self.wrote(&start);
        let errors = self.info.errors[start.errors..].to_vec();
        while self.log.len() > start.log {
            let w = self.log.pop().expect("longer than the mark");
            self.set(w);
        }
        let adopted = self.adopted(&wrote, span);
        let summary = match adopted.count {
            0 => None,
            count => {
                let n = self.summaries.len();
                let id = *self.summaries.entry(adopted.of).or_insert(n);
                Some((id, count))
            }
        };
        let s = Arc::new(Searched {
            span,
            sig: sig.clone(),
            wrote,
            errors,
            summary,
        });
        self.memo
            .entry(span)
            .or_default()
            .entry(key)
            .or_insert(s.clone());
        self.log.push(Undo::Nested(s));
        sig
    }

    /// The adoptions of the writes `wrote` inside `span` that differ from those the maps
    /// hold, and of the nested searches among them.
    fn adopted(&self, wrote: &[Undo], span: Span) -> Adopted {
        let own: Vec<(Span, Value)> = adoptions_in(wrote, span)
            .into_iter()
            .filter(|(s, v)| self.info.adopt.get(s) != Some(v))
            .collect();
        let mut nested = BTreeMap::new();
        for w in wrote {
            if let Undo::Nested(c) = w {
                match c.summary {
                    Some(n) => nested.insert(c.span, n),
                    None => nested.remove(&c.span),
                };
            }
        }
        let count = own.len() + nested.values().map(|&(_, n)| n).sum::<usize>();
        Adopted {
            of: (
                own,
                nested.into_iter().map(|(s, (id, _))| (s, id)).collect(),
            ),
            count,
        }
    }

    /// The signature of a declared function, inferred where a parameter has no type, or with
    /// `_` for those parameters and the result if `unknown`.
    fn infer(&mut self, f: &'a Function, span: Span, unknown: bool) -> Arc<Sig> {
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
        let open: Vec<usize> = (0..f.params.len())
            .filter(|&i| given[i].is_none())
            .collect();
        let own = self.t.own(span).max(1);
        let run = |ck: &mut Self, tys: &[Ty]| -> Ty {
            ck.runs += own;
            for ((id, t), (p, g)) in ids.iter().zip(tys).zip(f.params.iter().zip(&given)) {
                let text = match (&p.ty, g) {
                    (Some(a), _) if *t == Ty::dynamic() => format!(
                        "`{}` is declared `{a}`, whose values the checker does not track: \
                         it takes `{}` as unknown, _",
                        p.name, p.name
                    ),
                    (Some(a), _) => format!("`{}` is declared `{a}`", p.name),
                    (None, Some(_)) => {
                        format!("`{}` is {t}, the carrier of its default", p.name)
                    }
                    (None, None) if *t == Ty::dynamic() => format!(
                        "`{}` has no declared type; the signature search checks the body \
                         first with `{}` unknown, _, so what fails there fails at every type",
                        p.name, p.name
                    ),
                    (None, None) => format!(
                        "`{}` has no declared type; the signature search takes it as {t}",
                        p.name
                    ),
                };
                ck.origin(*id, p.span, text, None);
                ck.env.insert(*id, t.clone());
            }
            // A default that reads the other parameters, at its parameter's type.
            for (p, t) in f.params.iter().zip(tys) {
                if let Some(d) = &p.default
                    && !ck.t.uses_in(d.span, &[]).is_empty()
                {
                    let dt = ck.expr_at(d, Some(t));
                    if !dt.subtype(t) {
                        ck.error(
                            d.span,
                            format!("the default of `{}` is {dt}, not {t}", p.name),
                        );
                    }
                }
            }
            match &f.body.kind {
                ExprKind::Block(stmts) if !f.equation => ck.scope(stmts, false),
                _ => ck.expr(&f.body),
            }
        };
        let with = |fill: &dyn Fn(usize) -> Ty| -> Vec<Ty> {
            (0..given.len())
                .map(|i| given[i].clone().unwrap_or_else(|| fill(i)))
                .collect()
        };
        let sig = |arrows: Vec<Arrow>| {
            Arc::new(Sig {
                params: params.clone(),
                arrows,
            })
        };
        if unknown && !open.is_empty() {
            return sig(vec![Arrow {
                params: with(&|_| Ty::dynamic()),
                result: Ty::dynamic(),
            }]);
        }
        if open.is_empty() {
            let tys = with(&|_| unreachable!());
            let result = run(self, &tys);
            return sig(vec![Arrow {
                params: tys,
                result,
            }]);
        }
        let start = self.mark();
        // With the open parameters unknown: an error here does not depend on them.
        let tys = with(&|_| Ty::dynamic());
        let result = run(self, &tys);
        if self.info.errors.len() > start.errors || self.runs > self.budget || open.len() > 5 {
            return sig(vec![Arrow {
                params: tys,
                result,
            }]);
        }
        self.undo(&start);
        // With a type variable for each.
        let vars: Vec<Arc<str>> = open
            .iter()
            .map(|_| {
                self.fresh += 1;
                format!("${}", self.fresh).into()
            })
            .collect();
        let tys = with(&|i| Ty::var(vars[open.iter().position(|&j| j == i).unwrap()].clone()));
        let quiet = std::mem::replace(&mut self.quiet, true);
        let result = run(self, &tys);
        self.quiet = quiet;
        if self.info.errors.len() == start.errors {
            return Arc::new(rename(
                &sig(vec![Arrow {
                    params: tys,
                    result,
                }]),
                &vars,
            ));
        }
        // With carriers for one parameter, then for two, …, type variables for the rest: the
        // first count at which some combination checks gives the arrows.
        let n = open.len();
        let width = Carrier::ALL.len();
        let mut found: Vec<Found> = Vec::new();
        let mut first_error = None;
        let mut failures: Vec<Note> = Vec::new();
        let mut unshown = 0;
        for level in 1..=n {
            for mask in (0..1usize << n).filter(|m| m.count_ones() as usize == level) {
                for k in 0..width.pow(level as u32) {
                    if self.runs > self.budget {
                        self.undo(&start);
                        return sig(vec![Arrow {
                            params: with(&|_| Ty::dynamic()),
                            result: Ty::dynamic(),
                        }]);
                    }
                    self.undo(&start);
                    // The carrier of open parameter `j`, if the mask fixes it.
                    let pick = |j: usize| {
                        (mask >> j & 1 == 1).then(|| {
                            let rank = (mask & ((1 << j) - 1)).count_ones();
                            Carrier::ALL[(k / width.pow(rank)) % width]
                        })
                    };
                    let tys = with(&|i| {
                        let j = open.iter().position(|&o| o == i).unwrap();
                        match pick(j) {
                            Some(c) => Ty::carrier(c),
                            None => Ty::var(vars[j].clone()),
                        }
                    });
                    let quiet = std::mem::replace(&mut self.quiet, true);
                    let before = (self.runs, self.fresh);
                    let result = run(self, &tys);
                    self.quiet = quiet;
                    if self.info.errors.len() > start.errors {
                        let shown = failures
                            .iter()
                            .filter(|n| n.text.starts_with("with "))
                            .count()
                            < SHOWN;
                        let quiet_error =
                            (level == n).then(|| self.info.errors[start.errors].clone());
                        if level == n && shown {
                            // Again with notes, from the counters the run without them
                            // started at, so that it checks as that run did; then with the
                            // counters that run left, so that the combinations after it run
                            // as they would have.
                            let (runs, fresh) = (self.runs, self.fresh);
                            self.undo(&start);
                            (self.runs, self.fresh) = before;
                            run(self, &tys);
                            (self.runs, self.fresh) = (runs, fresh);
                        }
                        if level == n {
                            let names: Vec<String> = (0..n)
                                .map(|j| {
                                    let c = pick(j).expect("every parameter fixed");
                                    format!("`{}`: {}", f.params[open[j]].name, c.name())
                                })
                                .collect();
                            // The run with notes can find a nested search's signature anew
                            // where the run without them found it again, and so reach the
                            // budget where that run did not.
                            let e = match self.info.errors.get(start.errors) {
                                Some(e) => e,
                                None => quiet_error.as_ref().expect("a failed run"),
                            };
                            let with = format!("with {}, {}", names.join(", "), e.message);
                            first_error.get_or_insert(with.clone());
                            if failures
                                .iter()
                                .filter(|n| n.text.starts_with("with "))
                                .count()
                                < SHOWN
                            {
                                failures.push(Note {
                                    span: e.span,
                                    text: with,
                                });
                                for note in &e.notes {
                                    if !failures.contains(note) {
                                        failures.push(note.clone());
                                    }
                                }
                            } else {
                                unshown += 1;
                            }
                        }
                        continue;
                    }
                    let wrote = self.wrote(&start);
                    self.undo(&start);
                    let mine = adoptions_in(&wrote, span);
                    let adopted = self.adopted(&wrote, span);
                    let nested = adopted.of.1;
                    found.push((tys, result, wrote, (mine, nested), adopted.count));
                }
            }
            if !found.is_empty() {
                break;
            }
        }
        self.undo(&start);
        let Some(fewest) = found.iter().map(|f| f.4).min() else {
            let names: Vec<String> = open
                .iter()
                .map(|&i| format!("`{}`", f.params[i].name))
                .collect();
            if unshown > 0 {
                failures.push(Note {
                    span,
                    text: format!("{unshown} more combinations fail; the first {SHOWN} are shown"),
                });
            }
            self.error_with(
                span,
                format!(
                    "`{}` checks at no type of {}: {}",
                    f.name,
                    names.join(", "),
                    first_error.expect("a failed combination")
                ),
                failures,
            );
            let tys = with(&|_| Ty::dynamic());
            return sig(vec![Arrow {
                params: tys,
                result: Ty::dynamic(),
            }]);
        };
        let keep: Vec<_> = found.into_iter().filter(|f| f.4 == fewest).collect();
        // A combination whose adoptions inside the body are the first's: each adoption as
        // written, or as before the search where the run did not write it.
        let (first, first_nested) = &keep[0].3;
        let before = |s: &Span| self.info.adopt.get(s);
        let same = |(mine, nested): &(BTreeMap<Span, Value>, Vec<(Span, usize)>)| {
            nested == first_nested
                && mine
                    .keys()
                    .chain(first.keys())
                    .all(|s| mine.get(s).or(before(s)) == first.get(s).or(before(s)))
        };
        let arrows = keep
            .iter()
            .filter(|f| same(&f.3))
            .map(|(tys, result, ..)| Arrow {
                params: tys.clone(),
                result: result.clone(),
            })
            .collect();
        let wrote = keep.into_iter().next().expect("a kept combination").2;
        for w in wrote {
            self.put(w);
        }
        Arc::new(rename(&sig(arrows), &vars))
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
                for p in c.pieces() {
                    let ok = matches!(p, Piece::Dyn)
                        || p.is_atoms()
                        || p.carrier() == Some(Carrier::Bool);
                    if !ok {
                        self.error(cond.span, format!("the condition of `if` is {c}, not bool"));
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
            (Some(l), None) => {
                if let Some(c) = y.ty.numeric_carrier() {
                    self.adopt_to(l, c);
                }
            }
            (None, Some(m)) => {
                if let Some(c) = x.ty.numeric_carrier() {
                    self.adopt_to(m, c);
                }
            }
            (None, None) => {}
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
        Ty::func(Arc::new(Sig { params, arrows }))
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
        Ty::func(Arc::new(Sig {
            params: params
                .iter()
                .map(|p| SParam {
                    name: p.name.as_str().into(),
                    positional: true,
                    default: None,
                })
                .collect(),
            arrows: vec![Arrow {
                params: tys,
                result,
            }],
        }))
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
                Ty::func(Arc::new(Sig {
                    params: params
                        .iter()
                        .map(|p| SParam {
                            name: p.name.clone().unwrap_or_default().into(),
                            positional: p.positional || p.name.is_none(),
                            default: None,
                        })
                        .collect(),
                    arrows: vec![Arrow {
                        params: tys,
                        result,
                    }],
                }))
            }
        }
    }

    /// The derivation of an application `apply` rejects: each argument's, in order, then each
    /// arrow of `sig`, the constraints it failed.
    fn applied(&self, what: &str, sig: &Sig, args: &[Option<Arg>], span: Span) -> Vec<Note> {
        let mut out = Vec::new();
        if self.quiet {
            return out;
        }
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
        if self.trying || self.quiet {
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

    /// Applies `sig` to `args`, a missing one filled by its default. Each literal argument
    /// adopts the carrier of its parameter on the arrows that adopt fewest; then each
    /// combination of the arguments' pieces takes the first of those arrows that holds it.
    /// When `pass` holds, as for an operator or a prelude word, an argument's atoms pass
    /// through, two arguments' merged into `#errs`. Gives the result and the arrows kept.
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
        // The adoptions each arrow needs.
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
            } else {
                let shown: Vec<String> = args
                    .iter()
                    .map(|a| a.as_ref().map(|a| a.ty.to_string()).unwrap_or("_".into()))
                    .collect();
                let mut notes = self.applied(what, sig, &args, span);
                notes.extend(self.repairs(what, sig, &args, pass, span));
                self.error_with(
                    span,
                    format!("{what} does not take ({})", shown.join(", ")),
                    notes,
                );
            }
            return (out.union(&Ty::dynamic()), Vec::new());
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
        // Each combination of pieces.
        let pieces: Vec<Vec<Option<Piece>>> = args
            .iter()
            .map(|a| match a {
                Some(a) => a.ty.pieces().into_iter().map(Some).collect(),
                None => vec![None],
            })
            .collect();
        let total = pieces.iter().map(|p| p.len()).product::<usize>();
        if total > COMBOS {
            return (out.union(&Ty::dynamic()), kept);
        }
        for c in 0..total {
            let mut rest = c;
            let combo: Vec<&Option<Piece>> = pieces
                .iter()
                .map(|ps| {
                    let p = &ps[rest % ps.len()];
                    rest /= ps.len();
                    p
                })
                .collect();
            if combo.iter().any(|p| matches!(p, Some(Piece::Dyn))) {
                out = out.union(&Ty::dynamic());
                continue;
            }
            let mut hit = None;
            for &k in &kept {
                let arrow = &sig.arrows[k];
                let mut binds = Binds::new();
                let fits = combo.iter().zip(&arrow.params).all(|(p, t)| match p {
                    Some(p) => p.ty().sub(t, &mut binds),
                    None => true,
                });
                if fits {
                    hit = Some(close(&arrow.result.subst(&binds), sig));
                    break;
                }
            }
            match hit {
                Some(r) => out = out.union(&r),
                None => {
                    let shown: Vec<String> = combo
                        .iter()
                        .map(|p| p.as_ref().map(|p| p.ty().to_string()).unwrap_or("_".into()))
                        .collect();
                    let mut notes = self.applied(what, sig, &args, span);
                    notes.extend(self.repairs(what, sig, &args, pass, span));
                    self.error_with(
                        span,
                        format!("{what} does not take ({})", shown.join(", ")),
                        notes,
                    );
                    return (out.union(&Ty::dynamic()), kept);
                }
            }
        }
        (out, kept)
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

/// `sig` with the variables `vars` renamed `T`, `U`, `V`, `W`, `T5`, … in order of first
/// appearance.
fn rename(sig: &Sig, vars: &[Arc<str>]) -> Sig {
    let mut seen = Vec::new();
    for a in &sig.arrows {
        a.params.iter().for_each(|p| p.vars_in(&mut seen));
        a.result.vars_in(&mut seen);
    }
    let names: BTreeMap<Arc<str>, Arc<str>> = seen
        .into_iter()
        .filter(|v| vars.contains(v))
        .enumerate()
        .map(|(i, v)| {
            let n: Arc<str> = match i {
                0..4 => ["T", "U", "V", "W"][i].into(),
                _ => format!("T{}", i + 1).into(),
            };
            (v, n)
        })
        .collect();
    Sig {
        params: sig.params.clone(),
        arrows: sig
            .arrows
            .iter()
            .map(|a| Arrow {
                params: a.params.iter().map(|p| p.rename(&names)).collect(),
                result: a.result.rename(&names),
            })
            .collect(),
    }
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

/// The adoptions among the writes `wrote` inside `span`, each as last written.
fn adoptions_in(wrote: &[Undo], span: Span) -> BTreeMap<Span, Value> {
    wrote
        .iter()
        .filter_map(|w| match w {
            Undo::Adopt(s, Some(v)) if span.start <= s.start && s.end <= span.end => {
                Some((*s, v.clone()))
            }
            _ => None,
        })
        .collect()
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
    /// A nested search's writes, which the maps do not hold until the outermost search ends.
    Nested(Arc<Searched>),
}

/// A combination of a signature's search that checks: its types, its result, what its run
/// wrote, its adoptions inside the body and the numbers of the nested searches' adoptions,
/// and how many differ from those before the search.
type Found = (
    Vec<Ty>,
    Ty,
    Vec<Undo>,
    (BTreeMap<Span, Value>, Vec<(Span, usize)>),
    usize,
);

/// Adoptions differing from before a search: those of its own writes, and the number of
/// each nested search's, by the nested function's statement.
type Adoptions = (Vec<(Span, Value)>, Vec<(Span, usize)>);

/// The adoptions of a search's writes that differ from before it, and how many there are,
/// the nested searches' counted.
struct Adopted {
    of: Adoptions,
    count: usize,
}

/// The context of a search: the number of the context of the search around it and the type
/// of each binder it reads from the function around it.
type Context = (Option<usize>, Vec<Option<Ty>>);

/// What a function's signature search reads from outside the function: the context of the
/// search around it, whether its errors carry notes or offer repairs, and the type of each binder it reads
/// from the function around it, in the order of [`Tables::outer`].
#[derive(PartialEq, Eq, Hash)]
struct Key {
    around: Option<usize>,
    quiet: bool,
    trying: bool,
    outer: Vec<Option<Ty>>,
}

/// A function's signature search: the function's statement, the signature, the writes it
/// left, each with the value it wrote, its errors, and the number and count of its
/// adoptions differing from before the search, if any differ.
struct Searched {
    span: Span,
    sig: Arc<Sig>,
    wrote: Vec<Undo>,
    errors: Vec<Error>,
    summary: Option<(usize, usize)>,
}

/// How long the log and the errors were at a point of a search.
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
            Undo::Nested(s) => Undo::Nested(s),
        }
    }

    /// The point the search is at.
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

    /// The writes since `m`, each with the value its key now has, in the order made.
    fn wrote(&self, m: &Mark) -> Vec<Undo> {
        let i = &self.info;
        self.log[m.log..]
            .iter()
            .map(|w| match w {
                Undo::Adopt(k, _) => Undo::Adopt(*k, i.adopt.get(k).cloned()),
                Undo::Call(k, _) => Undo::Call(*k, i.calls.get(k).cloned()),
                Undo::Fit(k, _) => Undo::Fit(*k, i.fits.get(k).cloned()),
                Undo::Sig(k, _) => Undo::Sig(*k, i.sigs.get(k).cloned()),
                Undo::Top(k, _) => Undo::Top(k.clone(), i.tops.get(k).cloned()),
                Undo::Nested(s) => Undo::Nested(s.clone()),
            })
            .collect()
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
    })
}
