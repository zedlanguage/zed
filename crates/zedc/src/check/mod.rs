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

pub mod ty;

use std::collections::{BTreeMap, HashMap};
use std::sync::Arc;

use zed_kernel::types::Type as KType;
use zed_kernel::{Prim, Rat, Term, Value, eval};

use crate::ast::{
    Error, Expr, ExprKind, Function, Param, Stmt, StmtKind, StrPart, Target, Type, TypeKind,
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
    /// The type errors.
    pub errors: Vec<Error>,
}

/// Checks a resolved unit.
pub fn check(unit: &[Stmt], res: &Resolution) -> Info {
    check_with(&Tables::new(unit, res), unit)
}

pub(crate) fn check_with<'a>(t: &Tables<'a>, unit: &'a [Stmt]) -> Info {
    let mut ck = Ck {
        t,
        env: HashMap::new(),
        info: Info::default(),
        fresh: 0,
        runs: 0,
    };
    ck.scope(unit, true);
    ck.info
        .errors
        .sort_by(|a, b| (a.span, &a.message).cmp(&(b.span, &b.message)));
    ck.info.errors.dedup();
    ck.info
}

/// The most bodies one unit's signature searches check.
const RUNS: usize = 20_000;

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

/// An argument: its type, and the literal it is, if it is one.
#[derive(Clone)]
struct Arg {
    ty: Ty,
    lit: Option<Lit>,
}

impl Arg {
    fn of(ty: Ty) -> Arg {
        Arg { ty, lit: None }
    }
}

/// Facts an `is` test makes: binders narrowed to a type.
type Facts = Vec<(usize, Ty)>;

struct Ck<'t, 'a> {
    t: &'t Tables<'a>,
    env: HashMap<usize, Ty>,
    info: Info,
    fresh: usize,
    runs: usize,
}

impl<'t, 'a> Ck<'t, 'a> {
    fn error(&mut self, span: Span, message: impl Into<String>) {
        self.info.errors.push(Error {
            span,
            message: message.into(),
        });
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
                        self.env.insert(id, v);
                    }
                    [Target::Wild] => {}
                    _ => {
                        for (i, target) in targets.iter().enumerate() {
                            let c = self.component(&v, i, targets.len(), value.span);
                            if let Target::Name(n) = target {
                                let id = self.id(s.span, n);
                                self.env.insert(id, c);
                            }
                        }
                    }
                }
            }
            StmtKind::Function(f) => {
                let id = self.id(s.span, &f.name);
                let sig = self.infer(f, s.span);
                self.env.insert(id, Ty::func(sig.clone()));
                self.info.sigs.insert(id, sig);
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
        let mut out = Ty::set(v.atoms());
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

    /// The signature of a declared function, inferred where a parameter has no type.
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
                self.env.insert(id, Ty::dynamic());
            }
        }
        let open: Vec<usize> = (0..f.params.len())
            .filter(|&i| given[i].is_none())
            .collect();
        let run = |ck: &mut Self, tys: &[Ty]| -> Ty {
            ck.runs += 1;
            for (id, t) in ids.iter().zip(tys) {
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
        if open.is_empty() {
            let tys = with(&|_| unreachable!());
            let result = run(self, &tys);
            return sig(vec![Arrow {
                params: tys,
                result,
            }]);
        }
        let start = self.info.clone();
        // With the open parameters unknown: an error here does not depend on them.
        let tys = with(&|_| Ty::dynamic());
        let result = run(self, &tys);
        if self.info.errors.len() > start.errors.len() || self.runs > RUNS || open.len() > 5 {
            return sig(vec![Arrow {
                params: tys,
                result,
            }]);
        }
        self.info = start.clone();
        // With a type variable for each.
        let vars: Vec<Arc<str>> = open
            .iter()
            .map(|_| {
                self.fresh += 1;
                format!("${}", self.fresh).into()
            })
            .collect();
        let tys = with(&|i| Ty::var(vars[open.iter().position(|&j| j == i).unwrap()].clone()));
        let result = run(self, &tys);
        if self.info.errors.len() == start.errors.len() {
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
        let mut found: Vec<(Vec<Ty>, Ty, Info, usize)> = Vec::new();
        let mut first_error = None;
        for level in 1..=n {
            for mask in (0..1usize << n).filter(|m| m.count_ones() as usize == level) {
                for k in 0..width.pow(level as u32) {
                    if self.runs > RUNS {
                        self.info = start;
                        return sig(vec![Arrow {
                            params: with(&|_| Ty::dynamic()),
                            result: Ty::dynamic(),
                        }]);
                    }
                    self.info = start.clone();
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
                    let result = run(self, &tys);
                    if self.info.errors.len() > start.errors.len() {
                        if level == n && first_error.is_none() {
                            let names: Vec<String> = (0..n)
                                .map(|j| {
                                    let c = pick(j).expect("every parameter fixed");
                                    format!("`{}`: {}", f.params[open[j]].name, c.name())
                                })
                                .collect();
                            first_error = Some(format!(
                                "with {}, {}",
                                names.join(", "),
                                self.info.errors[start.errors.len()].message
                            ));
                        }
                        continue;
                    }
                    let adopted = adoptions(&self.info, &start, span);
                    found.push((tys, result, self.info.clone(), adopted));
                }
            }
            if !found.is_empty() {
                break;
            }
        }
        let Some(fewest) = found.iter().map(|f| f.3).min() else {
            self.info = start;
            let names: Vec<String> = open
                .iter()
                .map(|&i| format!("`{}`", f.params[i].name))
                .collect();
            self.error(
                span,
                format!(
                    "`{}` checks at no type of {}: {}",
                    f.name,
                    names.join(", "),
                    first_error.expect("a failed combination")
                ),
            );
            let tys = with(&|_| Ty::dynamic());
            return sig(vec![Arrow {
                params: tys,
                result: Ty::dynamic(),
            }]);
        };
        let keep: Vec<&(Vec<Ty>, Ty, Info, usize)> =
            found.iter().filter(|f| f.3 == fewest).collect();
        let first = keep[0].2.clone();
        let same = |i: &Info| within(&i.adopt, span) == within(&first.adopt, span);
        let arrows = keep
            .iter()
            .filter(|f| same(&f.2))
            .map(|(tys, result, _, _)| Arrow {
                params: tys.clone(),
                result: result.clone(),
            })
            .collect();
        self.info = first;
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
            };
        }
        Arg::of(self.expr_at(e, expected))
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
                self.info.adopt.insert(l.span, v);
                t
            }
            Err(m) => {
                self.error(l.span, m);
                lit_ty(&l.value, l.neg)
            }
        }
    }

    fn expr(&mut self, e: &'a Expr) -> Ty {
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
                    None => v.without_atoms().union(&d),
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
                let mut out = Ty::set(c.atoms());
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

    /// `e` checked with the binders of `facts` narrowed.
    fn under(&mut self, facts: &Facts, e: &'a Expr) -> Ty {
        let saved: Vec<(usize, Option<Ty>)> = facts
            .iter()
            .map(|(b, t)| (*b, self.env.insert(*b, t.clone())))
            .collect();
        let out = self.expr(e);
        for (b, old) in saved.into_iter().rev() {
            match old {
                Some(t) => self.env.insert(b, t),
                None => self.env.remove(&b),
            };
        }
        out
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
                let (yes, no) = (vec![(b, v.meet(&t))], vec![(b, v.diff(&t))]);
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
                let saved: Vec<(usize, Option<Ty>)> = first
                    .iter()
                    .map(|(k, t)| (*k, self.env.insert(*k, t.clone())))
                    .collect();
                let (tb, yb, nb) = self.cond(b);
                for (k, old) in saved.into_iter().rev() {
                    match old {
                        Some(t) => self.env.insert(k, t),
                        None => self.env.remove(&k),
                    };
                }
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
            return match sig {
                Some(sig) => self.call_sig(
                    &sig,
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
        let mut out = Ty::set(t.atoms());
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
        let mut out = Ty::set(f.atoms());
        let mut checked = false;
        if let Some(s) = f.fns.first()
            && f.fns.iter().all(|g| g.same_kinds(s))
        {
            self.info.calls.insert(span, s.clone());
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
        let atoms = x.ty.atoms();
        if safe {
            x = Arg::of(x.ty.without_atoms());
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
            let mut out = Ty::set(v.atoms());
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
        let mut out = Ty::set(v.atoms());
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
            self.info.fits.insert(span, Fit::Lambda { order, extra });
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
            self.info.fits.insert(span, Fit::Adapter { from });
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
                .map(|a| Ty::set(a.ty.atoms()))
                .collect();
            passed(&mut out, atoms.iter());
            for a in args.iter_mut().flatten() {
                a.ty = a.ty.without_atoms();
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
                if let Some(Arg { lit: None, ty }) = a {
                    ok &= ty.is_empty() || ty.meets(p);
                }
                let Some(Arg { lit: Some(l), ty }) = a else {
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
                self.error(span, format!("{what} does not take ({})", shown.join(", ")));
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
            self.info.adopt.insert(s, v);
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
                    self.error(span, format!("{what} does not take ({})", shown.join(", ")));
                    return (out.union(&Ty::dynamic()), kept);
                }
            }
        }
        (out, kept)
    }
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

/// The adoptions in `info` that `start` does not have, inside `span`.
fn adoptions(info: &Info, start: &Info, span: Span) -> usize {
    within(&info.adopt, span)
        .into_iter()
        .filter(|(s, v)| start.adopt.get(s) != Some(v))
        .count()
}

fn within(adopt: &HashMap<Span, Value>, span: Span) -> BTreeMap<Span, Value> {
    adopt
        .iter()
        .filter(|(s, _)| span.start <= s.start && s.end <= span.end)
        .map(|(s, v)| (*s, v.clone()))
        .collect()
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
