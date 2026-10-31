//! Elaboration (step L1.16): a resolved L1 unit to kernel terms, by the rules of DESIGN.md
//! "Kernel desugaring".
//!
//! A unit is its definitions, not a term: each top-level binding and function is a [`Def`], in
//! dependency order, and [`Unit::close`] wraps a term in them as nested lets so it can be
//! evaluated. A block is the lets of its statements in dependency order over its export; a
//! cycle among them is recursion, which arrives at L6. Every binder gets a kernel name unique
//! in the unit: its own name when no other binder shares it and it is not a prelude word, else
//! `name@k` for the `k`-th binder of that name. Temporaries are `$1`, `$2`, …. Because the
//! names are unique, a default is filled by let-binding the call's arguments under the
//! parameters' own names, with no capture.
//!
//! Where DESIGN.md does not say: `++` is its own primitive `Concat`, never `Add`; `e else d`
//! matches any atom (`#_`), which is exact while every atom is loose (before L2's named atom
//! families); a call through a value other than a declared function takes named arguments,
//! closed defaults and `...` from the signature the checker gives the value (L1.26); a prelude
//! word is the free variable of its name, bound by the interpreter (L1.18); a `test` table
//! belongs to a function at the unit's top level.

use std::cmp::Reverse;
use std::collections::{BTreeMap, BTreeSet, BinaryHeap, HashMap, HashSet};
use std::sync::Arc;

use zed_kernel::types::Type as KType;
use zed_kernel::{Pattern as KPattern, Prim, Rat, Term, Value};

use crate::ast::{
    Error, Expr, ExprKind, Function, Param, Pattern, Stmt, StmtKind, StrPart, Target, Type,
    TypeKind,
};
use crate::check::{self, Fit, Info};
use crate::lex::Span;
use crate::resolve::{Kind, Ref, Resolution, prelude_layer};

/// A top-level definition.
#[derive(Clone, Debug, PartialEq)]
pub struct Def {
    /// Its source name, or the temporary's name for the tuple of `a, b = e;`.
    pub name: String,
    /// Its kernel name.
    pub kernel: Arc<str>,
    /// Its value.
    pub term: Term,
    /// Whether it is bound by `=` to a value whose type, as the checker gives it, has no
    /// function component (step L1.37).
    pub first_order: bool,
}

/// A case of a `test` table: `f(input) == expected`.
#[derive(Clone, Debug, PartialEq)]
pub struct Test {
    /// The function's source name.
    pub function: String,
    /// The bool term that checks the case, over the unit's definitions.
    pub check: Term,
    /// The arguments the key gives, in declaration order.
    pub args: Vec<Term>,
    /// The expected value.
    pub want: Term,
    /// The case's text.
    pub span: Span,
}

/// An elaborated unit.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct Unit {
    /// The definitions, each after those it uses.
    pub defs: Vec<Def>,
    /// The test cases, in written order.
    pub tests: Vec<Test>,
}

impl Unit {
    /// `body` under the definitions it reaches, each a let, in the unit's order. For many
    /// terms of one unit, make its [`Cones`] once.
    pub fn close(&self, body: Term) -> Term {
        Cones::new(self).close(body)
    }

    /// The definition of source name `name`, closed over the others.
    pub fn get(&self, name: &str) -> Option<Term> {
        let d = self.defs.iter().find(|d| d.name == name)?;
        Some(self.close(Term::Var(d.kernel.clone())))
    }
}

/// The definitions each term of a unit reaches, from an index of the unit made once: each
/// kernel name's definition, and the names each definition reads, found when first needed. A
/// term's cone then costs the definitions in it, not a pass over the unit.
pub struct Cones<'u> {
    unit: &'u Unit,
    by_kernel: BTreeMap<&'u str, usize>,
    free: Vec<std::cell::OnceCell<BTreeSet<Arc<str>>>>,
}

impl<'u> Cones<'u> {
    /// The index of `unit`.
    pub fn new(unit: &'u Unit) -> Self {
        Cones {
            unit,
            by_kernel: unit
                .defs
                .iter()
                .enumerate()
                .map(|(i, d)| (&*d.kernel, i))
                .collect(),
            free: unit
                .defs
                .iter()
                .map(|_| std::cell::OnceCell::new())
                .collect(),
        }
    }

    /// The definitions `roots` read, and those they read in turn: their positions in the
    /// unit, in its order.
    pub fn reach(&self, roots: &[&Term]) -> Vec<usize> {
        let mut seen = BTreeSet::new();
        let mut todo: Vec<Arc<str>> = roots.iter().flat_map(|t| crate::stage::free(t)).collect();
        while let Some(x) = todo.pop() {
            if let Some(&i) = self.by_kernel.get(&*x)
                && seen.insert(i)
            {
                let free = self.free[i].get_or_init(|| crate::stage::free(&self.unit.defs[i].term));
                todo.extend(free.iter().cloned());
            }
        }
        seen.into_iter().collect()
    }

    /// The definitions `roots` reach, in the unit's order.
    pub fn defs(&self, roots: &[&Term]) -> impl Iterator<Item = &'u Def> + use<'u> {
        let unit = self.unit;
        self.reach(roots).into_iter().map(move |i| &unit.defs[i])
    }

    /// `body` under the definitions it reaches, each a let, in the unit's order: each after
    /// those it uses, as in the unit.
    pub fn close(&self, body: Term) -> Term {
        let defs: Vec<&Def> = self.defs(&[&body]).collect();
        defs.into_iter().rev().fold(body, |body, d| {
            Term::Let(d.kernel.clone(), Arc::new(d.term.clone()), Arc::new(body))
        })
    }
}

/// The elaboration of `unit` under its resolution, or every error in it, in text order.
pub fn elaborate(unit: &[Stmt], res: &Resolution) -> Result<Unit, Vec<Error>> {
    let t = Tables::new(unit, res);
    let mut info = check::check_with(&t, unit);
    let checked = std::mem::take(&mut info.errors);
    let mut e = Elab::new(t, info);
    let mut out = Unit::default();
    if let Some((binds, _)) = e.scope(unit, true) {
        out.defs = binds
            .into_iter()
            .map(|(name, kernel, term)| Def {
                first_order: e.info.tops.get(&name).is_some_and(|t| t.first_order()),
                name,
                kernel,
                term,
            })
            .collect();
    }
    out.tests = std::mem::take(&mut e.tests);
    e.errors.extend(checked);
    if e.errors.is_empty() {
        Ok(out)
    } else {
        e.errors
            .sort_by(|a, b| (a.span, &a.message).cmp(&(b.span, &b.message)));
        e.errors.dedup();
        Err(e.errors)
    }
}

/// A binding of a scope: source name, kernel name, value.
type Bind = (String, Arc<str>, Term);

/// The binders of a unit, shared by the checker and elaboration.
pub(crate) struct Tables<'a> {
    pub(crate) res: &'a Resolution,
    /// Each binder's index, by its span and name.
    pub(crate) ids: HashMap<(Span, &'a str), usize>,
    /// Each function binder's declaration.
    pub(crate) funcs: HashMap<usize, &'a Function>,
    /// The uses of each binder, in the order of the text.
    uses_of: Vec<Vec<Span>>,
}

struct Elab<'a> {
    t: Tables<'a>,
    /// Each binder's kernel name.
    names: Vec<Arc<str>>,
    /// The checker's findings.
    info: Info,
    fresh: usize,
    tests: Vec<Test>,
    errors: Vec<Error>,
    /// The term a call leaving a parameter out binds it to, by the function's binder and the
    /// parameter's index.
    defaults: HashMap<(usize, usize), Term>,
}

impl<'a> Tables<'a> {
    pub(crate) fn new(unit: &'a [Stmt], res: &'a Resolution) -> Self {
        let ids = res
            .binders
            .iter()
            .enumerate()
            .map(|(i, b)| ((b.span, b.name.as_str()), i))
            .collect();
        let mut uses_of = vec![Vec::new(); res.binders.len()];
        for (u, r) in &res.uses {
            if let Ref::Bound(ids) = r {
                for &b in ids {
                    uses_of[b].push(*u);
                }
            }
        }
        let mut t = Tables {
            res,
            ids,
            funcs: HashMap::new(),
            uses_of,
        };
        t.collect_functions(unit);
        t
    }

    /// Records every function declaration of `stmts` and of the blocks inside them.
    fn collect_functions(&mut self, stmts: &'a [Stmt]) {
        for s in stmts {
            match &s.kind {
                StmtKind::Function(f) => {
                    if let Some(&id) = self.ids.get(&(s.span, f.name.as_str())) {
                        self.funcs.insert(id, f);
                    }
                    for p in &f.params {
                        if let Some(d) = &p.default {
                            self.collect_in(d);
                        }
                    }
                    self.collect_in(&f.body);
                }
                StmtKind::Bind { value, .. } | StmtKind::Push { value, .. } => {
                    self.collect_in(value)
                }
                StmtKind::Return(es) => es.iter().for_each(|e| self.collect_in(e)),
            }
        }
    }

    fn collect_in(&mut self, e: &'a Expr) {
        match &e.kind {
            ExprKind::Block(stmts) => self.collect_functions(stmts),
            ExprKind::Str(parts) => parts.iter().for_each(|p| {
                if let StrPart::Hole(h) = p {
                    self.collect_in(h)
                }
            }),
            ExprKind::Unary(_, a) | ExprKind::Member { of: a, .. } | ExprKind::Is { of: a, .. } => {
                self.collect_in(a)
            }
            ExprKind::Binary(_, a, b) | ExprKind::Index(a, b) => {
                self.collect_in(a);
                self.collect_in(b);
            }
            ExprKind::Call {
                callee,
                positional,
                named,
                ..
            } => {
                self.collect_in(callee);
                positional.iter().for_each(|a| self.collect_in(a));
                named.iter().for_each(|(_, a)| self.collect_in(a));
            }
            ExprKind::Tuple(items) => items.iter().for_each(|i| self.collect_in(i)),
            ExprKind::Lambda { body, .. } => self.collect_in(body),
            ExprKind::Else { of, default, .. } => {
                self.collect_in(of);
                self.collect_in(default);
            }
            ExprKind::If {
                cond,
                then,
                otherwise,
            } => {
                self.collect_in(cond);
                self.collect_in(then);
                self.collect_in(otherwise);
            }
            _ => {}
        }
    }

    pub(crate) fn id(&self, span: Span, name: &str) -> usize {
        self.ids[&(span, name)]
    }

    /// The binders used in `span`, outside the spans in `skip`.
    pub(crate) fn uses_in(&self, span: Span, skip: &[Span]) -> Vec<usize> {
        let from = Span {
            start: span.start,
            end: 0,
        };
        let to = Span {
            start: span.end,
            end: 0,
        };
        self.res
            .uses
            .range(from..to)
            .filter(|(u, _)| u.end <= span.end)
            .filter(|(u, _)| !skip.iter().any(|s| s.start <= u.start && u.end <= s.end))
            .flat_map(|(_, r)| match r {
                Ref::Bound(ids) => ids.clone(),
                Ref::Prelude(_) => Vec::new(),
            })
            .collect()
    }

    pub(crate) fn binders_of(&self, s: &'a Stmt) -> Vec<usize> {
        match &s.kind {
            StmtKind::Bind { targets, .. } => targets
                .iter()
                .filter_map(|t| match t {
                    Target::Name(n) => Some(self.id(s.span, n)),
                    Target::Wild => None,
                })
                .collect(),
            StmtKind::Function(f) => vec![self.id(s.span, &f.name)],
            StmtKind::Push { .. } | StmtKind::Return(_) => Vec::new(),
        }
    }

    /// The order the statements of one scope are bound in, each after those it uses, a
    /// function's `test` tables aside; else the statements of one cycle. Each use of a
    /// binder of the scope is placed in its statement by a binary search, so the order
    /// reads the uses of the scope's own binders only, not those of the scopes inside it.
    pub(crate) fn order(&self, items: &[&'a Stmt]) -> Result<Vec<usize>, Vec<usize>> {
        let mut deps: Vec<Vec<usize>> = vec![Vec::new(); items.len()];
        for (i, s) in items.iter().enumerate() {
            for b in self.binders_of(s) {
                for u in &self.uses_of[b] {
                    let k = items.partition_point(|s| s.span.start <= u.start);
                    let Some(user) = k.checked_sub(1) else {
                        continue;
                    };
                    let at = items[user];
                    if u.end > at.span.end || in_tests(at, *u) {
                        continue;
                    }
                    deps[user].push(i);
                }
            }
        }
        for d in &mut deps {
            d.sort_unstable();
            d.dedup();
        }
        topo(&deps)
    }
}

/// Whether `u` lies in one of the `test` tables of the function `s` declares.
fn in_tests(s: &Stmt, u: Span) -> bool {
    let StmtKind::Function(f) = &s.kind else {
        return false;
    };
    let k = f.tests.partition_point(|(a, _)| a.span.start <= u.start);
    k.checked_sub(1)
        .is_some_and(|k| u.end <= f.tests[k].1.span.end)
}

impl<'a> Elab<'a> {
    fn new(t: Tables<'a>, info: Info) -> Self {
        let res = t.res;
        let mut count: HashMap<&str, usize> = HashMap::new();
        for b in &res.binders {
            *count.entry(&b.name).or_default() += 1;
        }
        let mut seen: HashMap<&str, usize> = HashMap::new();
        let names = res
            .binders
            .iter()
            .map(|b| {
                let k = seen.entry(&b.name).or_default();
                *k += 1;
                if count[b.name.as_str()] == 1 && prelude_layer(&b.name).is_none() {
                    b.name.as_str().into()
                } else {
                    format!("{}@{k}", b.name).into()
                }
            })
            .collect();
        Elab {
            t,
            names,
            info,
            fresh: 0,
            tests: Vec::new(),
            errors: Vec::new(),
            defaults: HashMap::new(),
        }
    }

    fn error<T>(&mut self, span: Span, message: impl Into<String>) -> Option<T> {
        self.errors.push(Error {
            span,
            message: message.into(),
            notes: Vec::new(),
        });
        None
    }

    fn temp(&mut self) -> Arc<str> {
        self.fresh += 1;
        format!("${}", self.fresh).into()
    }

    fn id(&self, span: Span, name: &str) -> usize {
        self.t.id(span, name)
    }

    /// The statements of one scope: its bindings in dependency order, and its export. `top`
    /// is the unit's top level, where a function's `test` table is elaborated.
    fn scope(&mut self, stmts: &'a [Stmt], top: bool) -> Option<(Vec<Bind>, Option<Term>)> {
        let mut export = None;
        let mut items: Vec<&'a Stmt> = Vec::new();
        for s in stmts {
            match &s.kind {
                StmtKind::Return(es) => export = Some(es),
                _ => items.push(s),
            }
        }
        let order = match self.t.order(&items) {
            Ok(order) => order,
            Err(cycle) => {
                let names: Vec<String> = cycle.iter().map(|&i| what(items[i])).collect();
                let message = match &names[..] {
                    [one] => format!("{one} is defined in terms of itself"),
                    _ => format!("{} are defined in terms of each other", names.join(", ")),
                };
                return self.error(
                    items[cycle[0]].span,
                    format!("{message}: recursion arrives at layer L6"),
                );
            }
        };
        let mut binds = Vec::new();
        let mut ok = true;
        for i in order {
            ok &= self.stmt(items[i], top, &mut binds).is_some();
        }
        let export = match export {
            None => None,
            Some(es) => {
                let mut ts = Vec::new();
                for e in es {
                    ts.push(self.expr(e));
                }
                let ts: Option<Vec<Term>> = ts.into_iter().collect();
                let mut ts = ts?;
                Some(if ts.len() == 1 {
                    ts.pop().expect("one")
                } else {
                    Term::Prim(Prim::Tuple, ts)
                })
            }
        };
        ok.then_some((binds, export))
    }

    /// A block's term: the lets of its statements over its export, or `()` without one.
    fn block(&mut self, stmts: &'a [Stmt]) -> Option<Term> {
        let (binds, export) = self.scope(stmts, false)?;
        let body = export.unwrap_or(Term::Prim(Prim::Tuple, Vec::new()));
        Some(binds.into_iter().rev().fold(body, |body, (_, k, t)| {
            Term::Let(k, Arc::new(t), Arc::new(body))
        }))
    }

    fn stmt(&mut self, s: &'a Stmt, top: bool, out: &mut Vec<Bind>) -> Option<()> {
        match &s.kind {
            StmtKind::Bind { targets, value } => {
                let v = self.expr(value)?;
                match &targets[..] {
                    [Target::Name(n)] => {
                        let k = self.names[self.id(s.span, n)].clone();
                        out.push((n.clone(), k, v));
                    }
                    [Target::Wild] => {
                        let t = self.temp();
                        out.push((t.to_string(), t, v));
                    }
                    _ => {
                        let t = self.temp();
                        out.push((t.to_string(), t.clone(), v));
                        for (i, target) in targets.iter().enumerate() {
                            if let Target::Name(n) = target {
                                let k = self.names[self.id(s.span, n)].clone();
                                let get = Term::Prim(
                                    Prim::TupleGet,
                                    vec![Term::Var(t.clone()), Term::Lit(Value::Int(i as i64))],
                                );
                                out.push((n.clone(), k, get));
                            }
                        }
                    }
                }
            }
            StmtKind::Function(f) => {
                let id = self.id(s.span, &f.name);
                let mut params = Vec::new();
                for p in &f.params {
                    params.push(self.names[self.id(p.span, &p.name)].clone());
                }
                // A default other than a literal or a name is a definition of its own, `f$x`, a
                // function of the parameters it reads, so a call leaving it out calls it rather
                // than holding a copy of it, and defaults that call functions with defaults stay
                // linear in size. A literal or a name is copied: no copy is captured, the kernel
                // names being unique in the unit.
                let ids: Vec<usize> = f.params.iter().map(|p| self.id(p.span, &p.name)).collect();
                let mut thunks = Vec::new();
                let mut ok = true;
                for (j, p) in f.params.iter().enumerate() {
                    let Some(d) = &p.default else { continue };
                    let read: HashSet<usize> = self.t.uses_in(d.span, &[]).into_iter().collect();
                    let reads: Vec<Arc<str>> = (0..ids.len())
                        .filter(|i| read.contains(&ids[*i]))
                        .map(|i| params[i].clone())
                        .collect();
                    let Some(t) = self.expr(d) else {
                        ok = false;
                        continue;
                    };
                    let at_call = if matches!(t, Term::Lit(_) | Term::Var(_)) {
                        t
                    } else {
                        let k: Arc<str> = format!("{}${}", self.names[id], params[j]).into();
                        let args = reads.iter().map(|r| Term::Var(r.clone())).collect();
                        thunks.push((k.to_string(), k.clone(), Term::Lam(reads, Arc::new(t))));
                        Term::App(Arc::new(Term::Var(k)), args)
                    };
                    self.defaults.insert((id, j), at_call);
                }
                let body = match &f.body.kind {
                    ExprKind::Block(stmts) if !f.equation => self.block(stmts),
                    _ => self.expr(&f.body),
                };
                let tests = self.tests(f, id, s.span, top);
                let body = body?;
                tests?;
                ok.then_some(())?;
                out.push((
                    f.name.clone(),
                    self.names[id].clone(),
                    Term::Lam(params, Arc::new(body)),
                ));
                out.extend(thunks);
            }
            StmtKind::Push { port, value } => {
                let v = self.expr(value)?;
                let t = self.temp();
                out.push((
                    t.to_string(),
                    t,
                    Term::Push(port.as_str().into(), Arc::new(v)),
                ));
            }
            StmtKind::Return(_) => unreachable!("an export is not a binding"),
        }
        Some(())
    }

    /// The cases of `f`'s `test` tables: a key is the argument, or for a function of several
    /// parameters the tuple of its arguments in declaration order.
    fn tests(&mut self, f: &'a Function, id: usize, span: Span, top: bool) -> Option<()> {
        if f.tests.is_empty() {
            return Some(());
        }
        if !top {
            return self.error(
                span,
                format!(
                    "`{}` has a test table, which belongs to a function at the unit's top level",
                    f.name
                ),
            );
        }
        let mut ok = true;
        for (input, expected) in &f.tests {
            let case = Span {
                start: input.span.start,
                end: expected.span.end,
            };
            let args = match (&input.kind, f.params.len()) {
                (_, 1) => vec![input],
                (ExprKind::Tuple(items), n) if items.len() == n => items.iter().collect(),
                (_, n) => {
                    ok = false;
                    self.error::<()>(
                        input.span,
                        format!(
                            "a test key of `{}` is the tuple of its {n} arguments",
                            f.name
                        ),
                    );
                    continue;
                }
            };
            let args: Option<Vec<Term>> = args.into_iter().map(|a| self.expr(a)).collect();
            let want = self.expr(expected);
            let (Some(args), Some(want)) = (args, want) else {
                ok = false;
                continue;
            };
            let call = Term::App(Arc::new(Term::Var(self.names[id].clone())), args.clone());
            self.tests.push(Test {
                function: f.name.clone(),
                check: Term::Prim(Prim::Eq, vec![call, want.clone()]),
                args,
                want,
                span: case,
            });
        }
        ok.then_some(())
    }

    fn expr(&mut self, e: &'a Expr) -> Option<Term> {
        if let Some(fit) = self.info.fits.get(&e.span).cloned() {
            return self.fit(e, fit);
        }
        if let Some(v) = self.info.adopt.get(&e.span) {
            return Some(Term::Lit(v.clone()));
        }
        let lit = |v: Value| Some(Term::Lit(v));
        match &e.kind {
            ExprKind::Int { radix, digits } => {
                let digits: String = digits.chars().filter(|&c| c != '_').collect();
                lit(Value::int_text(&digits, *radix).expect("the lexer's digits"))
            }
            ExprKind::Float(s) => {
                let s: String = s.chars().filter(|&c| c != '_').collect();
                lit(Value::float(s.parse().expect("the lexer's float text")))
            }
            ExprKind::Rat(s) => match Rat::decimal(s) {
                Some(r) => lit(Value::rat(r)),
                None => self.error(e.span, "this rational is beyond the evaluator's size limit"),
            },
            ExprKind::Bool(b) => lit(Value::Bool(*b)),
            ExprKind::Atom(a) => lit(Value::atom(a)),
            ExprKind::Str(parts) => self.string(parts),
            ExprKind::Name(n) => self.name(n, e.span),
            ExprKind::Unary(op, a) => {
                let p = if *op == "-" { Prim::Neg } else { Prim::Not };
                Some(Term::Prim(p, vec![self.expr(a)?]))
            }
            ExprKind::Binary(op, a, b) => {
                let (a, b) = (self.expr(a), self.expr(b));
                let (a, b) = (a?, b?);
                let t = |v: bool| Term::Lit(Value::Bool(v));
                let p = match *op {
                    "||" => return Some(if_(a, t(true), b)),
                    "&&" => return Some(if_(a, b, t(false))),
                    "==" => Prim::Eq,
                    "!=" => Prim::Ne,
                    "<" => Prim::Lt,
                    "<=" => Prim::Le,
                    ">" => Prim::Gt,
                    ">=" => Prim::Ge,
                    "+" => Prim::Add,
                    "-" => Prim::Sub,
                    "*" => Prim::Mul,
                    "/" => Prim::Div,
                    "div" => Prim::IntDiv,
                    "mod" => Prim::Mod,
                    "**" => Prim::Pow,
                    "++" => Prim::Concat,
                    _ => return self.error(e.span, format!("`{op}` is not an L1 operator")),
                };
                Some(Term::Prim(p, vec![a, b]))
            }
            ExprKind::Call {
                callee,
                positional,
                named,
                curry,
            } => self.call(callee, positional, named, *curry, e.span),
            ExprKind::Index(of, k) => self.index(of, k),
            ExprKind::Tuple(items) => {
                let ts: Vec<Option<Term>> = items.iter().map(|i| self.expr(i)).collect();
                Some(Term::Prim(
                    Prim::Tuple,
                    ts.into_iter().collect::<Option<_>>()?,
                ))
            }
            ExprKind::Lambda { params, body } => self.lambda(params, body),
            ExprKind::Is { of, ty, negated } => {
                let (v, t) = (self.expr(of), self.ty(ty));
                let (v, t) = (v?, t?);
                if !t.decidable() {
                    return self.error(
                        ty.span,
                        "`is` cannot test a value against a function type at run time",
                    );
                }
                let arms = [(KPattern::Is(t), true), (KPattern::Wild, false)];
                Some(Term::Match(
                    Arc::new(v),
                    arms.map(|(p, b)| (p, Term::Lit(Value::Bool(b != *negated))))
                        .to_vec(),
                ))
            }
            ExprKind::Else {
                of,
                pattern,
                default,
            } => {
                let (v, d) = (self.expr(of), self.expr(default));
                let pat = match pattern {
                    Some(p) => self.pattern(p).map(Some),
                    None => Some(None),
                };
                let (v, d, pat) = (v?, d?, pat?);
                let t = self.temp();
                let arm = pat.unwrap_or(KPattern::AnyAtom);
                Some(Term::Match(
                    Arc::new(v),
                    vec![(arm, d), (KPattern::Bind(t.clone()), Term::Var(t))],
                ))
            }
            ExprKind::Block(stmts) => self.block(stmts),
            ExprKind::If {
                cond,
                then,
                otherwise,
            } => {
                let (c, a, b) = (self.expr(cond), self.expr(then), self.expr(otherwise));
                Some(if_(c?, a?, b?))
            }
            ExprKind::Member { of, name, safe } => {
                self.member(of, name, *safe, e.span, &[], &[], false, e.span)
            }
        }
    }

    /// Interpolation: the nonempty parts joined by `++`, each hole `String(hole)`.
    fn string(&mut self, parts: &'a [StrPart]) -> Option<Term> {
        let mut terms = Vec::new();
        for p in parts {
            match p {
                StrPart::Text(t) if t.is_empty() => {}
                StrPart::Text(t) => terms.push(Term::Lit(Value::str(t))),
                StrPart::Hole(h) => {
                    let h = self.expr(h)?;
                    terms.push(Term::App(Arc::new(Term::Var("String".into())), vec![h]));
                }
            }
        }
        let mut terms = terms.into_iter();
        let first = terms.next().unwrap_or(Term::Lit(Value::str("")));
        Some(terms.fold(first, |a, b| Term::Prim(Prim::Concat, vec![a, b])))
    }

    fn name(&mut self, n: &str, span: Span) -> Option<Term> {
        match self.t.res.uses.get(&span) {
            Some(Ref::Bound(ids)) if ids.len() > 1 => self.error(
                span,
                format!(
                    "`{n}` names {} overloads; choosing among them arrives at L2",
                    ids.len()
                ),
            ),
            Some(Ref::Bound(ids)) if self.t.res.binders[ids[0]].kind == Kind::Port => self.error(
                span,
                format!("`{n}` is an output port, written with `{n} <- e`, not a value"),
            ),
            Some(Ref::Bound(ids)) => Some(Term::Var(self.names[ids[0]].clone())),
            Some(Ref::Prelude(w)) => Some(Term::Var(w.as_str().into())),
            None => unreachable!("a resolved unit records every name"),
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
    ) -> Option<Term> {
        if let ExprKind::Member { of, name, safe } = &callee.kind {
            return self.member(of, name, *safe, callee.span, positional, named, curry, span);
        }
        if let ExprKind::Atom(name) = &callee.kind {
            return self.atom(name, positional, named, curry, span);
        }
        if let Some(id) = self.declared(callee) {
            return self.call_declared(id, None, positional, named, curry, span);
        }
        let f = self.expr(callee)?;
        self.call_value(f, None, positional, named, curry, span)
    }

    /// An atom with a payload, `#name(a, b)` by position or `#name(f: a)` by name.
    fn atom(
        &mut self,
        name: &str,
        positional: &'a [Expr],
        named: &'a [(String, Expr)],
        curry: bool,
        span: Span,
    ) -> Option<Term> {
        if curry {
            return self.error(
                span,
                "`...` curries a function's named parameters; an atom has none",
            );
        }
        if !positional.is_empty() && !named.is_empty() {
            return self.error(span, "an atom's payload is all by position or all by name");
        }
        let fields = named.iter().map(|(f, _)| Value::str(f)).collect();
        let mut args = vec![Term::Lit(Value::str(name)), Term::Lit(Value::Tuple(fields))];
        let mut ok = true;
        for a in positional.iter().chain(named.iter().map(|(_, a)| a)) {
            match self.expr(a) {
                Some(t) => args.push(t),
                None => ok = false,
            }
        }
        ok.then_some(Term::Prim(Prim::Atom, args))
    }

    /// A call through a value other than a declared function. With the signature the
    /// checker gives the value, named arguments, closed defaults and `...` work as for a
    /// declared function; without one, the arguments are positional.
    fn call_value(
        &mut self,
        f: Term,
        receiver: Option<Term>,
        positional: &'a [Expr],
        named: &'a [(String, Expr)],
        curry: bool,
        span: Span,
    ) -> Option<Term> {
        let Some(sig) = self.info.calls.get(&span).cloned() else {
            if !named.is_empty() || curry {
                return self.error(
                    span,
                    "named arguments and `...` need the parameter names of the function \
                     called, which a prelude word and a value of unknown type do not give",
                );
            }
            let mut args: Vec<Term> = receiver.into_iter().collect();
            let mut ok = true;
            for a in positional {
                match self.expr(a) {
                    Some(t) => args.push(t),
                    None => ok = false,
                }
            }
            return ok.then(|| Term::App(Arc::new(f), args));
        };
        let n = sig.params.len();
        let mut slots: Vec<Option<Term>> = vec![None; n];
        let mut next = 0;
        if let Some(r) = receiver {
            if n == 0 {
                return self.error(span, format!("`{sig}` has no parameter for a receiver"));
            }
            slots[0] = Some(r);
            next = 1;
        }
        let mut ok = true;
        for a in positional {
            match sig.params.get(next) {
                None => {
                    return self.error(a.span, format!("too many arguments: `{sig}` takes {n}"));
                }
                Some(p) if !p.positional => {
                    return self.error(
                        a.span,
                        format!(
                            "`{}` of `{sig}` is named: pass it as `{}: …`",
                            p.name, p.name
                        ),
                    );
                }
                Some(_) => {
                    slots[next] = self.expr(a);
                    ok &= slots[next].is_some();
                    next += 1;
                }
            }
        }
        for (name, a) in named {
            match sig.params.iter().position(|p| *p.name == **name) {
                None => return self.error(a.span, format!("`{sig}` has no parameter `{name}`")),
                Some(j) if sig.params[j].positional => {
                    return self.error(
                        a.span,
                        format!("`{name}` of `{sig}` is positional: pass it by position"),
                    );
                }
                Some(j) if slots[j].is_some() => {
                    return self.error(a.span, format!("`{name}` is already supplied"));
                }
                Some(j) => {
                    slots[j] = self.expr(a);
                    ok &= slots[j].is_some();
                }
            }
        }
        if !ok {
            return None;
        }
        let missing: Vec<usize> = (0..n).filter(|&j| slots[j].is_none()).collect();
        if curry {
            if let Some(&j) = missing.iter().find(|&&j| sig.params[j].positional) {
                return self.error(
                    span,
                    format!(
                        "`...` curries named parameters only; the positional `{}` is left out",
                        sig.params[j].name
                    ),
                );
            }
            if missing.is_empty() {
                return self.error(span, "`...` leaves no named parameter out");
            }
            // The function value is bound once, outside the lambda.
            let fv = self.temp();
            let temps: Vec<Arc<str>> = missing.iter().map(|_| self.temp()).collect();
            let mut k = 0;
            let args = slots
                .into_iter()
                .map(|s| {
                    s.unwrap_or_else(|| {
                        k += 1;
                        Term::Var(temps[k - 1].clone())
                    })
                })
                .collect();
            let call = Term::App(Arc::new(Term::Var(fv.clone())), args);
            return Some(Term::Let(
                fv,
                Arc::new(f),
                Arc::new(Term::Lam(temps, Arc::new(call))),
            ));
        }
        for &j in &missing {
            let p = &sig.params[j];
            let filled = match p.default {
                Some((fid, idx, true)) => {
                    let d = self.t.funcs[&fid].params[idx]
                        .default
                        .as_ref()
                        .expect("a default");
                    self.expr(d)
                }
                Some((_, _, false)) => {
                    return self.error(
                        span,
                        format!(
                            "the default of `{}` reads the function's other parameters, so only \
                             a call of the declared function fills it: pass `{}`",
                            p.name, p.name
                        ),
                    );
                }
                None => {
                    return self.error(span, format!("missing argument `{}` of `{sig}`", p.name));
                }
            };
            slots[j] = Some(filled?);
        }
        let args = slots.into_iter().map(|s| s.expect("filled")).collect();
        Some(Term::App(Arc::new(f), args))
    }

    /// A function argument fitted to the function type its slot expects: a lambda whose
    /// parameters are in another order or carry defaults, or a declared function whose
    /// named parameters are in another order.
    fn fit(&mut self, e: &'a Expr, fit: Fit) -> Option<Term> {
        match (fit, &e.kind) {
            (Fit::Lambda { order, extra }, ExprKind::Lambda { params, body }) => {
                let mut names = Vec::new();
                for o in &order {
                    names.push(match o {
                        Some(i) => self.names[self.id(params[*i].span, &params[*i].name)].clone(),
                        None => self.temp(),
                    });
                }
                let mut body = match &body.kind {
                    ExprKind::Block(stmts) => self.block(stmts)?,
                    _ => self.expr(body)?,
                };
                for &i in extra.iter().rev() {
                    let p = &params[i];
                    let d = self.expr(p.default.as_ref().expect("an extra has a default"))?;
                    let k = self.names[self.id(p.span, &p.name)].clone();
                    body = Term::Let(k, Arc::new(d), Arc::new(body));
                }
                Some(Term::Lam(names, Arc::new(body)))
            }
            (Fit::Adapter { from }, _) => {
                let ExprKind::Name(n) = &e.kind else {
                    unreachable!("an adapter is recorded on a name")
                };
                let f = self.name(n, e.span)?;
                let temps: Vec<Arc<str>> = from.iter().map(|_| self.temp()).collect();
                let args = from.iter().map(|&j| Term::Var(temps[j].clone())).collect();
                Some(Term::Lam(temps, Arc::new(Term::App(Arc::new(f), args))))
            }
            _ => unreachable!("a lambda fit is recorded on a lambda"),
        }
    }

    /// A saturated or curried call of the declared function `id`; `receiver` fills its first
    /// parameter, of either kind.
    fn call_declared(
        &mut self,
        id: usize,
        receiver: Option<Term>,
        positional: &'a [Expr],
        named: &'a [(String, Expr)],
        curry: bool,
        span: Span,
    ) -> Option<Term> {
        let f = self.t.funcs[&id];
        let fname = &f.name;
        let n = f.params.len();
        let mut slots: Vec<Option<Term>> = vec![None; n];
        let mut next = 0;
        if let Some(r) = receiver {
            if n == 0 {
                return self.error(span, format!("`{fname}` has no parameter for a receiver"));
            }
            slots[0] = Some(r);
            next = 1;
        }
        let mut ok = true;
        for a in positional {
            match f.params.get(next) {
                None => {
                    return self.error(a.span, format!("too many arguments: `{fname}` takes {n}"));
                }
                Some(p) if !p.positional => {
                    return self.error(
                        a.span,
                        format!(
                            "`{}` of `{fname}` is named: pass it as `{}: …`",
                            p.name, p.name
                        ),
                    );
                }
                Some(_) => {
                    slots[next] = self.expr(a);
                    ok &= slots[next].is_some();
                    next += 1;
                }
            }
        }
        for (name, a) in named {
            match f.params.iter().position(|p| p.name == *name) {
                None => {
                    return self.error(a.span, format!("`{fname}` has no parameter `{name}`"));
                }
                Some(j) if f.params[j].positional => {
                    return self.error(
                        a.span,
                        format!("`{name}` of `{fname}` is positional: pass it by position"),
                    );
                }
                Some(j) if slots[j].is_some() => {
                    return self.error(a.span, format!("`{name}` is already supplied"));
                }
                Some(j) => {
                    slots[j] = self.expr(a);
                    ok &= slots[j].is_some();
                }
            }
        }
        if !ok {
            return None;
        }
        let kname = |e: &Self, p: &Param| e.names[e.id(p.span, &p.name)].clone();
        let fv = Arc::new(Term::Var(self.names[id].clone()));
        let missing: Vec<usize> = (0..n).filter(|&j| slots[j].is_none()).collect();
        let all: Vec<Term> = f.params.iter().map(|p| Term::Var(kname(self, p))).collect();
        let supplied = |e: &Self, slots: Vec<Option<Term>>, body: Term| {
            slots
                .into_iter()
                .zip(&f.params)
                .rev()
                .fold(body, |body, (s, p)| match s {
                    Some(t) => Term::Let(kname(e, p), Arc::new(t), Arc::new(body)),
                    None => body,
                })
        };
        if curry {
            if let Some(&j) = missing.iter().find(|&&j| f.params[j].positional) {
                return self.error(
                    span,
                    format!(
                        "`...` curries named parameters only; the positional `{}` is left out",
                        f.params[j].name
                    ),
                );
            }
            if missing.is_empty() {
                return self.error(span, "`...` leaves no named parameter out");
            }
            let params = missing.iter().map(|&j| kname(self, &f.params[j])).collect();
            let body = supplied(self, slots, Term::App(fv, all));
            return Some(Term::Lam(params, Arc::new(body)));
        }
        if missing.is_empty() {
            let args = slots.into_iter().map(|s| s.expect("supplied")).collect();
            return Some(Term::App(fv, args));
        }
        let mut ok = true;
        for &j in &missing {
            if f.params[j].default.is_none() {
                ok = false;
                self.error::<()>(
                    span,
                    format!("missing argument `{}` of `{fname}`", f.params[j].name),
                );
            }
        }
        if !ok {
            return None;
        }
        // The defaults, each after the defaulted parameters it reads.
        let ids: Vec<usize> = missing
            .iter()
            .map(|&j| self.id(f.params[j].span, &f.params[j].name))
            .collect();
        let deps: Vec<Vec<usize>> = missing
            .iter()
            .map(|&j| {
                let d = f.params[j].default.as_ref().expect("checked");
                let mut deps: Vec<usize> = self
                    .t
                    .uses_in(d.span, &[])
                    .into_iter()
                    .filter_map(|b| ids.iter().position(|&i| i == b))
                    .collect();
                deps.sort_unstable();
                deps.dedup();
                deps
            })
            .collect();
        let order = match topo(&deps) {
            Ok(order) => order,
            Err(cycle) => {
                let names: Vec<String> = cycle
                    .iter()
                    .map(|&i| format!("`{}`", f.params[missing[i]].name))
                    .collect();
                return self.error(
                    span,
                    format!("the defaults of {} read each other", names.join(", ")),
                );
            }
        };
        let mut defaults = Vec::new();
        for i in order {
            let p = &f.params[missing[i]];
            let d = match self.defaults.get(&(id, missing[i])) {
                Some(t) => t.clone(),
                // A call inside the function's own declaration, before its defaults are bound.
                None => self.expr(p.default.as_ref().expect("checked"))?,
            };
            defaults.push((kname(self, p), d));
        }
        let body = defaults
            .into_iter()
            .rev()
            .fold(Term::App(fv, all), |body, (k, d)| {
                Term::Let(k, Arc::new(d), Arc::new(body))
            });
        Some(supplied(self, slots, body))
    }

    /// `x.f(args)` and `x?.f(args)`: the uniform call `f(x, args)`, `?.` passing an atom `x`
    /// through. Without parentheses the arguments are empty.
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
    ) -> Option<Term> {
        let x = self.expr(of)?;
        let (receiver, t) = if safe {
            let t = self.temp();
            (Term::Var(t.clone()), Some(t))
        } else {
            (x.clone(), None)
        };
        let call = match self.t.res.uses.get(&member) {
            Some(Ref::Bound(ids)) if ids.len() > 1 => {
                return self.error(
                    member,
                    format!(
                        "`{name}` names {} overloads; choosing among them arrives at L2",
                        ids.len()
                    ),
                );
            }
            Some(Ref::Bound(ids)) if self.t.funcs.contains_key(&ids[0]) => {
                self.call_declared(ids[0], Some(receiver), positional, named, curry, span)?
            }
            Some(Ref::Bound(ids)) => {
                let f = Term::Var(self.names[ids[0]].clone());
                self.call_value(f, Some(receiver), positional, named, curry, span)?
            }
            _ => match prelude_layer(name) {
                Some(1) => {
                    let f = Term::Var(name.into());
                    self.call_value(f, Some(receiver), positional, named, curry, span)?
                }
                Some(layer) => {
                    return self.error(
                        member,
                        format!("`{name}` is a prelude word of layer L{layer}"),
                    );
                }
                None => {
                    return self.error(
                        member,
                        format!("`{name}` is not a function in scope, and fields arrive at L2"),
                    );
                }
            },
        };
        Some(match t {
            None => call,
            Some(t) => Term::Let(
                t.clone(),
                Arc::new(x),
                Arc::new(Term::Match(
                    Arc::new(Term::Var(t.clone())),
                    vec![(KPattern::AnyAtom, Term::Var(t)), (KPattern::Wild, call)],
                )),
            ),
        })
    }

    /// `f[k]` on a declared function: the section filling its first parameter, no default
    /// filled; `t[i]` with a literal `i`: the tuple component; else an application.
    fn index(&mut self, of: &'a Expr, k: &'a Expr) -> Option<Term> {
        if let Some(id) = self.declared(of) {
            let f = self.t.funcs[&id];
            let k = self.expr(k)?;
            let fv = Arc::new(Term::Var(self.names[id].clone()));
            return match f.params.len() {
                0 => self.error(of.span, format!("`{}` takes no arguments", f.name)),
                1 => Some(Term::App(fv, vec![k])),
                n => {
                    let rest: Vec<Arc<str>> = (1..n).map(|_| self.temp()).collect();
                    let mut args = vec![k];
                    args.extend(rest.iter().map(|r| Term::Var(r.clone())));
                    Some(Term::Lam(rest, Arc::new(Term::App(fv, args))))
                }
            };
        }
        let (v, i) = (self.expr(of), self.expr(k));
        let (v, i) = (v?, i?);
        Some(match (&k.kind, i) {
            (ExprKind::Int { .. }, i) => Term::Prim(Prim::TupleGet, vec![v, i]),
            (_, i) => Term::App(Arc::new(v), vec![i]),
        })
    }

    fn lambda(&mut self, params: &'a [Param], body: &'a Expr) -> Option<Term> {
        let mut names = Vec::new();
        for p in params {
            if let Some(d) = &p.default {
                return self.error(
                    d.span,
                    "a lambda's parameter has a default only where an expected function type \
                     leaves it out",
                );
            }
            names.push(self.names[self.id(p.span, &p.name)].clone());
        }
        let body = match &body.kind {
            ExprKind::Block(stmts) => self.block(stmts)?,
            _ => self.expr(body)?,
        };
        Some(Term::Lam(names, Arc::new(body)))
    }

    /// The type a type expression denotes. A function type is curried, one level per
    /// parameter, and `->?` makes each level partial; `() -> V` has the empty tuple as its
    /// one key.
    fn ty(&mut self, t: &Type) -> Option<KType> {
        let all = |b: &mut Self, ts: &[Type]| -> Option<Vec<KType>> {
            let ts: Vec<Option<KType>> = ts.iter().map(|t| b.ty(t)).collect();
            ts.into_iter().collect()
        };
        Some(match &t.kind {
            TypeKind::Name(n) => match n.as_str() {
                "int" => KType::int(),
                "rat" => KType::rat(),
                "f64" => KType::f64(),
                "bool" => KType::bool(),
                "String" => KType::string(),
                _ => {
                    return self.error(
                        t.span,
                        format!("`{n}` is the type of a port, and no value has it"),
                    );
                }
            },
            TypeKind::Atom(a) => KType::atom(a),
            TypeKind::Tuple(ts) => KType::tuple(all(self, ts)?),
            TypeKind::Union(ts) => all(self, ts)?
                .into_iter()
                .fold(KType::empty(), |a, b| a | b),
            TypeKind::And(ts) => all(self, ts)?.into_iter().fold(KType::top(), |a, b| a & b),
            TypeKind::Diff(a, b) => {
                let (a, b) = (self.ty(a), self.ty(b));
                a? - &b?
            }
            TypeKind::Arrow {
                params,
                partial,
                result,
            } => {
                let keys: Vec<Option<KType>> = params.iter().map(|p| self.ty(&p.ty)).collect();
                let result = self.ty(result);
                let mut keys: Vec<KType> = keys.into_iter().collect::<Option<_>>()?;
                if keys.is_empty() {
                    keys.push(KType::tuple(Vec::new()));
                }
                let level = if *partial {
                    KType::partial
                } else {
                    KType::exact
                };
                keys.into_iter().rev().fold(result?, |v, k| level(k, v))
            }
        })
    }

    /// An `else` pattern: an atom, its payload matched by position or by name; a field
    /// written `f:` binds `f`.
    fn pattern(&mut self, p: &Pattern) -> Option<KPattern> {
        let Pattern::Atom {
            name,
            fields,
            items,
            span,
        } = p;
        if fields.is_empty() {
            let items: Option<Vec<KPattern>> = items.iter().map(|i| self.pattern(i)).collect();
            return Some(KPattern::Atom(name.as_str().into(), items?));
        }
        if !items.is_empty() {
            return self.error(*span, "an atom's payload is all by position or all by name");
        }
        if let Some(f) = repeated(fields.iter().map(|(f, _)| f.as_str())) {
            return self.error(*span, format!("the pattern names `{f}` twice"));
        }
        let mut out = Vec::new();
        for (f, sub) in fields {
            let sub = match sub {
                Some(sub) => self.pattern(sub)?,
                None => KPattern::Bind(self.names[self.id(*span, f)].clone()),
            };
            out.push((f.as_str().into(), sub));
        }
        Some(KPattern::Fields(name.as_str().into(), out))
    }
}

/// A name that occurs twice in `names`.
fn repeated<'n>(names: impl Iterator<Item = &'n str>) -> Option<&'n str> {
    let mut seen = HashSet::new();
    names.into_iter().find(|n| !seen.insert(*n))
}

fn if_(c: Term, a: Term, b: Term) -> Term {
    Term::If(Arc::new(c), Arc::new(a), Arc::new(b))
}

/// How a statement is named in a cycle's error.
fn what(s: &Stmt) -> String {
    match &s.kind {
        StmtKind::Bind { targets, .. } => {
            let names: Vec<String> = targets
                .iter()
                .filter_map(|t| match t {
                    Target::Name(n) => Some(format!("`{n}`")),
                    Target::Wild => None,
                })
                .collect();
            names.join(" and ")
        }
        StmtKind::Function(f) => format!("`{}`", f.name),
        StmtKind::Push { port, .. } => format!("the push to `{port}`"),
        StmtKind::Return(_) => "the export".into(),
    }
}

/// An order of `0..deps.len()` with each item after its dependencies, ties by index; else the
/// items of one cycle, in order along it. The ready items wait in a heap, smallest first, each
/// counting the dependencies it still waits on, so the order takes `O((n + e) log n)`.
#[doc(hidden)]
pub fn topo(deps: &[Vec<usize>]) -> Result<Vec<usize>, Vec<usize>> {
    let n = deps.len();
    let mut waits: Vec<usize> = deps.iter().map(Vec::len).collect();
    let mut users: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (i, ds) in deps.iter().enumerate() {
        for &d in ds {
            users[d].push(i);
        }
    }
    let mut ready: BinaryHeap<Reverse<usize>> =
        (0..n).filter(|&i| waits[i] == 0).map(Reverse).collect();
    let mut done = vec![false; n];
    let mut order = Vec::with_capacity(n);
    while let Some(Reverse(i)) = ready.pop() {
        done[i] = true;
        order.push(i);
        for &u in &users[i] {
            waits[u] -= 1;
            if waits[u] == 0 {
                ready.push(Reverse(u));
            }
        }
    }
    if order.len() < n {
        // Every item left waits on another left; walk until one repeats.
        let mut seen: BTreeMap<usize, usize> = BTreeMap::new();
        let mut path = Vec::new();
        let mut i = (0..n).find(|&i| !done[i]).expect("an item left");
        while !seen.contains_key(&i) {
            seen.insert(i, path.len());
            path.push(i);
            i = *deps[i]
                .iter()
                .find(|&&d| !done[d])
                .expect("a dependency left");
        }
        return Err(path.split_off(seen[&i]));
    }
    Ok(order)
}
