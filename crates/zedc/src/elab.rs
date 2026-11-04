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

use std::cell::OnceCell;
use std::cmp::Reverse;
use std::collections::{BTreeMap, BTreeSet, BinaryHeap, HashMap, HashSet};
use std::hash::{Hash, Hasher};
use std::sync::Arc;

use imbl::Vector;

use zed_kernel::num::{LiteralRounding, literal_f64, show_f64};
use zed_kernel::types::Type as KType;
use zed_kernel::{Pattern as KPattern, Prim, Rat, Term, Universe, Value};

use crate::ast::{
    Error, Every, Expr, ExprKind, Function, Param, Pattern, Stmt, StmtKind, StrPart, Target, Type,
    TypeKind,
};
use crate::check::{self, Fit, Info, Misfit};
use crate::lex::Span;
use crate::rejection::Row;
use crate::resolve::{Kind, Ref, Resolution, prelude_layer};

mod walk;

/// A top-level definition.
#[derive(Clone, Debug, PartialEq)]
pub struct Def {
    /// Its source name, or the temporary's name for the tuple of `a, b = e;`.
    pub name: String,
    /// Its kernel name.
    pub kernel: Arc<str>,
    /// Its value, shared with the lets that close a term over it.
    pub term: Arc<Term>,
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
    /// The test cases, in written order, shared with the unit once staged.
    pub tests: Arc<[Test]>,
    /// The warnings, which do not stop the build: each operation that widens a value past a
    /// machine word (DESIGN.md sec:domains). `run::compile` moves them out, placed in the
    /// source, and leaves this empty.
    pub warnings: Vec<Error>,
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
/// kernel name's definition, and the definitions each definition reads, found when first
/// needed. A term's cone then costs the definitions in it, not a pass over the unit, and
/// closing a term over its cone shares each definition's term rather than copying it.
pub struct Cones<'u> {
    unit: &'u Unit,
    by_kernel: HashMap<&'u str, usize>,
    /// The positions of the definitions each definition reads.
    reads: Vec<OnceCell<Vec<usize>>>,
    /// Each definition's digest, for a query key.
    digests: Vec<OnceCell<[u8; 32]>>,
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
            reads: unit.defs.iter().map(|_| OnceCell::new()).collect(),
            digests: unit.defs.iter().map(|_| OnceCell::new()).collect(),
        }
    }

    /// The positions of the definitions of the names `t` reads.
    fn positions(&self, t: &Term) -> impl Iterator<Item = usize> {
        crate::stage::free(t)
            .into_iter()
            .filter_map(|x| self.by_kernel.get(&*x).copied())
    }

    /// The definitions `roots` read, and those they read in turn: their positions in the
    /// unit, in its order.
    pub fn reach(&self, roots: &[&Term]) -> Vec<usize> {
        let mut seen = BTreeSet::new();
        let mut todo: Vec<usize> = roots.iter().flat_map(|t| self.positions(t)).collect();
        while let Some(i) = todo.pop() {
            if seen.insert(i) {
                let reads =
                    self.reads[i].get_or_init(|| self.positions(&self.unit.defs[i].term).collect());
                todo.extend(reads);
            }
        }
        seen.into_iter().collect()
    }

    /// The definitions `roots` reach, in the unit's order.
    pub fn defs(&self, roots: &[&Term]) -> impl Iterator<Item = &'u Def> + use<'u> {
        let unit = self.unit;
        self.reach(roots).into_iter().map(move |i| &unit.defs[i])
    }

    /// The BLAKE3 digest of the definition at position `i`: of its kernel name and its term
    /// as `Debug` prints them, made once.
    pub fn digest(&self, i: usize) -> &[u8; 32] {
        self.digests[i].get_or_init(|| {
            let d = &self.unit.defs[i];
            *blake3::hash(format!("{}={:?}", d.kernel, d.term).as_bytes()).as_bytes()
        })
    }

    /// `body` under the definitions it reaches, each a let, in the unit's order: each after
    /// those it uses, as in the unit. Each let shares its definition's term.
    pub fn close(&self, body: Term) -> Term {
        self.close_with(body, None)
    }

    /// `body` closed as [`Cones::close`] closes it, with the definition at position `i` bound
    /// to `term` when `swap` is `Some((i, term))` (step L25.8, a mutant). `term` must read
    /// the names the definition reads, as a mutant's term does, so the cone is the same.
    pub fn close_with(&self, body: Term, swap: Option<(usize, &Arc<Term>)>) -> Term {
        let reach = self.reach(&[&body]);
        reach.into_iter().rev().fold(body, |body, i| {
            let d = &self.unit.defs[i];
            let term = match swap {
                Some((j, term)) if j == i => term.clone(),
                _ => d.term.clone(),
            };
            Term::Let(d.kernel.clone(), term, Arc::new(body))
        })
    }
}

/// The elaboration of `unit` under its resolution, or every error in it, in text order.
pub fn elaborate(unit: &[Stmt], res: &Resolution) -> Result<Unit, Vec<Error>> {
    elaborate_in(unit, res, None).map(|(unit, _)| unit)
}

/// A written operator or integer constant that a mutant may replace (step L25.8), found by
/// [`elaborate_marked`].
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Mark {
    /// For an operator, the text between its operands, which holds it; for a constant, the
    /// constant.
    pub span: Span,
    /// For `*`, whether `/` is defined there (the product holds no `int`).
    pub quotient: bool,
}

/// The operators a mutant may replace: `==`, `!=`, `<`, `<=`, `>`, `>=`, `+`, `-`, `*`, `/`.
pub fn mutable(p: Prim) -> bool {
    use Prim::*;
    matches!(p, Eq | Ne | Lt | Le | Gt | Ge | Add | Sub | Mul | Div)
}

/// The elaboration of `unit` as [`elaborate`] gives it, with each written operator and integer
/// constant a mutant may replace marked, and the marks (step L25.8). A marked operator
/// `Prim(p, [a, b])` is `Prim(p, [a, b, m])` and a marked constant `n` is `Prim(Neg, [n, m])`,
/// `m` the literal index of its [`Mark`]: neither shape is elaborated otherwise, an operator
/// having two arguments and `Neg` one. A mark adds a last child or wraps a leaf, so every
/// node of the unmarked elaboration has the same position in the marked one. The marked unit
/// is for finding positions only; it is never run.
pub fn elaborate_marked(unit: &[Stmt], res: &Resolution) -> Result<(Unit, Vec<Mark>), Vec<Error>> {
    elaborate_in(unit, res, Some(Vec::new()))
        .map(|(unit, marks)| (unit, marks.expect("marks were asked for")))
}

/// The index of the mark on `t`, when `t` is a marked operator or constant of
/// [`elaborate_marked`].
pub fn mark_of(t: &Term) -> Option<usize> {
    match t {
        Term::Prim(p, args) if mutable(*p) => match &args[..] {
            [_, _, Term::Lit(Value::Int(m))] => usize::try_from(*m).ok(),
            _ => None,
        },
        Term::Prim(Prim::Neg, args) => match &args[..] {
            [Term::Lit(_), Term::Lit(Value::Int(m))] => usize::try_from(*m).ok(),
            _ => None,
        },
        _ => None,
    }
}

fn elaborate_in(
    unit: &[Stmt],
    res: &Resolution,
    marks: Option<Vec<Mark>>,
) -> Result<(Unit, Option<Vec<Mark>>), Vec<Error>> {
    let t = Tables::new(unit, res);
    let mut info = check::check_with(&t, unit);
    let warnings = check::widen::warnings(&t, unit, &info.adopt);
    let checked = std::mem::take(&mut info.errors);
    let mut e = Elab::new(t, &info);
    e.marks = marks;
    let mut out = Unit::default();
    if let Some((binds, _)) = e.scope(unit, true) {
        out.defs = binds
            .into_iter()
            .map(|(name, kernel, term)| Def {
                first_order: e.info.tops.get(&name).is_some_and(|t| t.first_order()),
                name,
                kernel,
                term: Arc::new(term),
            })
            .collect();
    }
    out.tests = std::mem::take(&mut e.tests).into();
    out.warnings = warnings;
    // The checker's errors first, so that where both report one error, as for an argument
    // that fills no parameter, the checker's, which carries its notes, is the one kept: the
    // sort is stable.
    let mut errors = checked;
    errors.append(&mut e.errors);
    if errors.is_empty() {
        Ok((out, e.marks.take()))
    } else {
        errors.sort_by(|a, b| (a.span, &a.message).cmp(&(b.span, &b.message)));
        errors.dedup_by(|a, b| (a.span, &a.message, a.row) == (b.span, &b.message, b.row));
        Err(errors)
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
    /// The uses of the unit's binders, grouped by the list of binders each may name (one
    /// binder, or the arrows of an overload set), each use once, in the order of the text: `U`
    /// uses of a set of `K` arrows are `U + K` entries, not `U·K`.
    uses: Vec<Uses>,
    /// The groups of `uses` naming each binder.
    groups_of: Vec<Vec<usize>>,
    /// Every written type of the unit, each once, in the order of the text: a parameter's, a
    /// lambda parameter's and an `is` test's. The checker checks their bounds.
    pub(crate) written: Vec<&'a Type>,
}

/// The uses of one list of binders.
struct Uses {
    binders: Vector<usize>,
    at: Vec<Span>,
}

/// A list of binders as a key: hashed by its first binder and length, compared by sharing
/// first and by content only when not shared. Each use of an overload set shares the set's
/// list (`Ref::Bound`), so finding a use's group costs `O(1)`.
struct ListKey<'a>(&'a Vector<usize>);

impl Hash for ListKey<'_> {
    fn hash<H: Hasher>(&self, h: &mut H) {
        (self.0.front(), self.0.len()).hash(h)
    }
}

impl PartialEq for ListKey<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.0.ptr_eq(other.0) || self.0 == other.0
    }
}

impl Eq for ListKey<'_> {}

struct Elab<'a> {
    t: Tables<'a>,
    /// Each binder's kernel name.
    names: Vec<Arc<str>>,
    /// The checker's findings, which elaboration only reads.
    info: &'a Info,
    /// The temporary each argument of a call that passes atoms is bound to, while the call is
    /// elaborated.
    passing: HashMap<Span, Arc<str>>,
    /// The calls being guarded.
    guarding: HashSet<Span>,
    fresh: usize,
    tests: Vec<Test>,
    errors: Vec<Error>,
    /// The term a call leaving a parameter out binds it to, by the function's binder and the
    /// parameter's index.
    defaults: HashMap<(usize, usize), Term>,
    /// The marks of a marked elaboration ([`elaborate_marked`]), `None` for an ordinary one.
    marks: Option<Vec<Mark>>,
}

/// A part of the unit still to visit while [`Tables`] collects the declarations and written
/// types.
enum Collect<'a> {
    Stmt(&'a Stmt),
    Expr(&'a Expr),
    Type(&'a Type),
}

/// Puts each parameter's written type and default on `todo`, in the order of the text.
fn collect_params<'a>(params: &'a [Param], todo: &mut Vec<Collect<'a>>) {
    for p in params {
        todo.extend(p.ty.as_ref().map(Collect::Type));
        todo.extend(p.default.as_ref().map(Collect::Expr));
    }
}

/// Puts the parts `e` holds on `todo`, in the order of the text.
fn collect_expr<'a>(e: &'a Expr, todo: &mut Vec<Collect<'a>>) {
    let expr = |e: &'a Expr| Collect::Expr(e);
    match &e.kind {
        ExprKind::Block(stmts) => todo.extend(stmts.iter().map(Collect::Stmt)),
        ExprKind::Str(parts) => todo.extend(parts.iter().filter_map(|p| match p {
            StrPart::Hole(h) => Some(expr(h)),
            _ => None,
        })),
        ExprKind::Unary(_, a) | ExprKind::Member { of: a, .. } => todo.push(expr(a)),
        ExprKind::Is { of, ty, .. } => todo.extend([expr(of), Collect::Type(ty)]),
        ExprKind::Binary(_, a, b)
        | ExprKind::Index(a, b)
        | ExprKind::Else {
            of: a, default: b, ..
        } => todo.extend([expr(a), expr(b)]),
        ExprKind::Call {
            callee,
            positional,
            named,
            ..
        } => {
            todo.push(expr(callee));
            todo.extend(positional.iter().map(expr));
            todo.extend(named.iter().map(|(_, a)| expr(a)));
        }
        ExprKind::Tuple(items) => todo.extend(items.iter().map(expr)),
        ExprKind::Lambda { params, body } => {
            collect_params(params, todo);
            todo.push(expr(body));
        }
        ExprKind::If {
            cond,
            then,
            otherwise,
        } => todo.extend([expr(cond), expr(then), expr(otherwise)]),
        _ => {}
    }
}

impl<'a> Tables<'a> {
    pub(crate) fn new(unit: &'a [Stmt], res: &'a Resolution) -> Self {
        let ids = res
            .binders
            .iter()
            .enumerate()
            .map(|(i, b)| ((b.span, b.name.as_str()), i))
            .collect();
        let mut uses: Vec<Uses> = Vec::new();
        let mut groups_of = vec![Vec::new(); res.binders.len()];
        let mut group: HashMap<ListKey, usize> = HashMap::new();
        for (u, r) in &res.uses {
            let Ref::Bound(ids) = r else { continue };
            let g = *group.entry(ListKey(ids)).or_insert_with(|| {
                for &b in ids {
                    groups_of[b].push(uses.len());
                }
                uses.push(Uses {
                    binders: ids.clone(),
                    at: Vec::new(),
                });
                uses.len() - 1
            });
            uses[g].at.push(*u);
        }
        let mut t = Tables {
            res,
            ids,
            funcs: HashMap::new(),
            uses,
            groups_of,
            written: Vec::new(),
        };
        t.collect_functions(unit);
        t
    }

    /// Records every function declaration and written type of `stmts` and of the blocks
    /// inside them. The walk keeps the parts still to visit on a heap stack, so a deeply nested
    /// expression does not grow the thread's stack. Each part's children go on the stack in
    /// reverse, so the parts are met in the order of the text, the order of `written`.
    fn collect_functions(&mut self, stmts: &'a [Stmt]) {
        let mut todo: Vec<Collect<'a>> = stmts.iter().rev().map(Collect::Stmt).collect();
        while let Some(c) = todo.pop() {
            let at = todo.len();
            match c {
                Collect::Type(t) => self.written.push(t),
                Collect::Stmt(s) => self.collect_stmt(s, &mut todo),
                Collect::Expr(e) => collect_expr(e, &mut todo),
            }
            todo[at..].reverse();
        }
    }

    /// Records the function declaration `s` if it is one and puts the parts it holds on
    /// `todo`, in the order of the text.
    fn collect_stmt(&mut self, s: &'a Stmt, todo: &mut Vec<Collect<'a>>) {
        match &s.kind {
            StmtKind::Function(f) => {
                if let Some(&id) = self.ids.get(&(s.span, f.name.as_str())) {
                    self.funcs.insert(id, f);
                }
                collect_params(&f.params, todo);
                todo.push(Collect::Expr(&f.body));
                for (a, b) in &f.tests {
                    todo.extend([Collect::Expr(a), Collect::Expr(b)]);
                }
            }
            StmtKind::Bind { value, .. } | StmtKind::Push { value, .. } => {
                todo.push(Collect::Expr(value))
            }
            StmtKind::Return(es) => todo.extend(es.iter().map(Collect::Expr)),
            StmtKind::Struct(_)
            | StmtKind::Type(_)
            | StmtKind::Method(_)
            | StmtKind::Import(_)
            | StmtKind::Annotated { .. }
            | StmtKind::Mutable(_)
            | StmtKind::IndexedDef(_)
            | StmtKind::While(_)
            | StmtKind::Until(_)
            | StmtKind::Expr(_)
            | StmtKind::UnitAnnot(_) => {}
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
            .filter_map(|(_, r)| match r {
                Ref::Bound(ids) => Some(ids),
                Ref::Prelude(_) => None,
            })
            .flatten()
            .copied()
            .collect()
    }

    pub(crate) fn binders_of(&self, s: &'a Stmt) -> Vec<usize> {
        match &s.kind {
            StmtKind::Bind { targets, .. } => targets
                .iter()
                .filter_map(|t| match t {
                    Target::Name(n, _) => Some(self.id(s.span, n)),
                    Target::Wild => None,
                })
                .collect(),
            StmtKind::Function(f) => vec![self.id(s.span, &f.name)],
            StmtKind::Push { .. } | StmtKind::Return(_) | StmtKind::UnitAnnot(_) => Vec::new(),
            StmtKind::Struct(_)
            | StmtKind::Type(_)
            | StmtKind::Method(_)
            | StmtKind::Import(_)
            | StmtKind::Annotated { .. } => {
                unreachable!("resolve rejects the forms of layer L2")
            }
            StmtKind::Mutable(_)
            | StmtKind::IndexedDef(_)
            | StmtKind::While(_)
            | StmtKind::Until(_)
            | StmtKind::Expr(_) => unreachable!("resolve rejects the forms of layer L6"),
        }
    }

    /// The order the statements of one scope are bound in, each after those it uses, a
    /// function's `test` tables aside; else the statements of one cycle. Each use of a
    /// binder of the scope is placed in its statement by a binary search, so the order
    /// reads the uses of the scope's own binders only, not those of the scopes inside it.
    /// A use of an overload set waits on one join node, which waits on the set's statements,
    /// so `U` uses of `K` overloads make `U + K` dependencies, not `U·K`.
    pub(crate) fn order(&self, items: &[&'a Stmt]) -> Result<Vec<usize>, Vec<usize>> {
        let bound: Vec<(usize, usize)> = (items.iter().enumerate())
            .flat_map(|(i, s)| self.binders_of(s).into_iter().map(move |b| (b, i)))
            .collect();
        let item_of: HashMap<usize, usize> = bound.iter().copied().collect();
        let mut deps: Vec<Vec<usize>> = vec![Vec::new(); items.len()];
        let mut seen: HashSet<usize> = HashSet::new();
        for &(b, _) in &bound {
            for &g in &self.groups_of[b] {
                if !seen.insert(g) {
                    continue;
                }
                let group = &self.uses[g];
                let mut named: Vec<usize> = (group.binders.iter())
                    .filter_map(|b| item_of.get(b).copied())
                    .collect();
                named.sort_unstable();
                named.dedup();
                let on = match named[..] {
                    [one] => one,
                    _ => {
                        deps.push(named);
                        deps.len() - 1
                    }
                };
                for u in &group.at {
                    let k = items.partition_point(|s| s.span.start <= u.start);
                    let Some(user) = k.checked_sub(1) else {
                        continue;
                    };
                    let at = items[user];
                    if u.end > at.span.end || in_tests(at, *u) {
                        continue;
                    }
                    deps[user].push(on);
                }
            }
        }
        for d in &mut deps {
            d.sort_unstable();
            d.dedup();
        }
        topo_joined(&deps, items.len())
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
    fn new(t: Tables<'a>, info: &'a Info) -> Self {
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
            passing: HashMap::new(),
            guarding: HashSet::new(),
            fresh: 0,
            tests: Vec::new(),
            errors: Vec::new(),
            defaults: HashMap::new(),
            marks: None,
        }
    }

    /// The literal `v` of the constant `e`; marked when the elaboration is marked and `e` is
    /// an integer literal, whatever carrier it adopted.
    fn constant(&mut self, e: &Expr, v: Value) -> Term {
        match &mut self.marks {
            Some(marks) if matches!(e.kind, ExprKind::Int { .. }) => {
                let m = Term::Lit(Value::Int(marks.len() as i64));
                marks.push(Mark {
                    span: e.span,
                    quotient: false,
                });
                Term::Prim(Prim::Neg, vec![Term::Lit(v), m])
            }
            _ => Term::Lit(v),
        }
    }

    fn error<T>(&mut self, span: Span, message: impl Into<String>) -> Option<T> {
        self.error_in(None, span, message)
    }

    /// The error of a call's argument that does not fill a parameter of `who`, as the checker
    /// reports it too.
    fn misfit<T>(&mut self, span: Span, misfit: Misfit, who: &str) -> Option<T> {
        self.error_in(misfit.row(), span, misfit.message(who))
    }

    fn error_in<T>(
        &mut self,
        row: Option<Row>,
        span: Span,
        message: impl Into<String>,
    ) -> Option<T> {
        self.errors.push(Error {
            row,
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

    /// The type a type expression denotes ([`kernel_type`]); each name of a port in it is an
    /// error. Its bounds were checked by the checker, which reads every written type.
    fn ty(&mut self, t: &Type) -> Option<KType> {
        let mut ports = Vec::new();
        let k = kernel_type(t, &mut ports, None);
        for (span, message) in ports {
            self.error::<()>(span, message);
        }
        k
    }

    /// An `else` pattern: an atom, its payload matched by position or by name; a field
    /// written `f:` binds `f`.
    ///
    /// Patterns nest as deep as the source, so the atoms still open wait on a stack. The
    /// parts are elaborated in written order, and the first refused part ends the atom and
    /// each atom around it, as the recursion did (step T2-mid).
    fn pattern(&mut self, p: &Pattern) -> Option<KPattern> {
        let mut stack = Vec::new();
        let mut finished = self.pattern_open(p, &mut stack);
        loop {
            let Some(top) = stack.last_mut() else {
                return finished.expect("the pattern's result");
            };
            let step = match (top, finished.take()) {
                (_, Some(None)) => Err(None),
                (OpenPattern::Items { name, items, done }, k) => {
                    let items: &[Pattern] = items;
                    done.extend(k.flatten());
                    match items.get(done.len()) {
                        Some(item) => Ok(item),
                        None => Err(Some(KPattern::Atom((*name).into(), std::mem::take(done)))),
                    }
                }
                (
                    OpenPattern::Fields {
                        name,
                        fields,
                        span,
                        done,
                    },
                    k,
                ) => {
                    let fields: &[(String, Option<Pattern>)] = fields;
                    if let Some(Some(k)) = k {
                        done.push((fields[done.len()].0.as_str().into(), k));
                    }
                    loop {
                        match fields.get(done.len()) {
                            None => {
                                let fs = std::mem::take(done);
                                break Err(Some(KPattern::Fields((*name).into(), fs)));
                            }
                            Some((_, Some(sub))) => break Ok(sub),
                            Some((f, None)) => {
                                let b = self.names[self.id(*span, f)].clone();
                                done.push((f.as_str().into(), KPattern::Bind(b)));
                            }
                        }
                    }
                }
            };
            match step {
                Ok(part) => finished = self.pattern_open(part, &mut stack),
                Err(k) => {
                    stack.pop();
                    finished = Some(k);
                }
            }
        }
    }

    /// Opens the atom pattern `p` on `stack`; or, when its shape is refused, its result.
    fn pattern_open<'p>(
        &mut self,
        p: &'p Pattern,
        stack: &mut Vec<OpenPattern<'p>>,
    ) -> Option<Option<KPattern>> {
        let Pattern::Atom {
            name,
            fields,
            items,
            span,
        } = p
        else {
            unreachable!("resolve rejects the forms of layer L2")
        };
        if fields.is_empty() {
            stack.push(OpenPattern::Items {
                name,
                items,
                done: Vec::new(),
            });
            return None;
        }
        if !items.is_empty() {
            return Some(self.error(*span, "an atom's payload is all by position or all by name"));
        }
        if let Some(f) = repeated(fields.iter().map(|(f, _)| f.as_str())) {
            return Some(self.error(*span, format!("the pattern names `{f}` twice")));
        }
        stack.push(OpenPattern::Fields {
            name,
            fields,
            span: *span,
            done: Vec::new(),
        });
        None
    }
}

/// The kernel type a written type denotes. A function type is curried, one level per
/// parameter, and `->?` makes each level partial; `() -> V` has the empty tuple as its one key.
/// A name of a port denotes no type: it is an error in `ports`, and the type is `None`. With
/// `bounds`, each `L .. U -> V` whose guarantee `L` is not within its permission `U` is an
/// error there, with the cause when that check was refused; the checker passes it once for
/// each written type of a program (the list `Tables::written`, walked by `Ck::bounds`), so
/// every way a program is checked runs this check, and runs it once. One pass over the type.
///
/// Types nest as deep as the source, so the types still open wait on a stack, each with the
/// types of its parts so far; every part is elaborated, in written order, before the type that
/// holds it, so the errors come in the order a recursion would give (step T2-mid).
pub(crate) fn kernel_type(
    t: &Type,
    ports: &mut Vec<(Span, String)>,
    mut bounds: Option<&mut Vec<(Span, String)>>,
) -> Option<KType> {
    let mut stack = vec![OpenType::of(t)];
    loop {
        let top = stack.last_mut().expect("a type in progress");
        if let Some(&part) = top.parts.get(top.done.len()) {
            stack.push(OpenType::of(part));
            continue;
        }
        let OpenType { t, done, .. } = stack.pop().expect("a type in progress");
        let k = kernel_form(t, done, ports, bounds.as_deref_mut());
        match stack.last_mut() {
            Some(holder) => holder.done.push(k),
            None => return k,
        }
    }
}

/// The type `t` denotes, given the types of its parts in [`type_parts`] order, `None` where a
/// part was refused; the errors of [`kernel_type`] for `t` itself go to `ports` and `bounds`.
fn kernel_form(
    t: &Type,
    parts: Vec<Option<KType>>,
    ports: &mut Vec<(Span, String)>,
    bounds: Option<&mut Vec<(Span, String)>>,
) -> Option<KType> {
    Some(match &t.kind {
        TypeKind::Apply(..) | TypeKind::AtomApply(..) | TypeKind::Record(_) => {
            unreachable!("resolve rejects the forms of layer L2")
        }
        TypeKind::Array(_) => unreachable!("resolve rejects the forms of layer L3"),
        // A bounded variable stands for one carrier that a call of the function chooses; a
        // run-time test has no call to choose it.
        TypeKind::For { bounds, .. } => {
            let vars: Vec<String> = bounds.iter().map(|b| format!("`{}`", b.name)).collect();
            ports.push((
                t.span,
                format!(
                    "an `is` test cannot take a type with bounded variables ({}): a call \
                     chooses each one's carrier, and a test has no call; test each carrier \
                     instead",
                    vars.join(", ")
                ),
            ));
            return None;
        }
        TypeKind::Name(n) => match n.as_str() {
            "int" => KType::int(),
            "rat" => KType::rat(),
            "f64" => KType::f64(),
            "bool" => KType::bool(),
            "String" => KType::string(),
            _ => {
                ports.push((
                    t.span,
                    format!("`{n}` is the type of a port, and no value has it"),
                ));
                return None;
            }
        },
        TypeKind::Every(Every::Atom) => crate::check::ty::atoms(),
        TypeKind::Every(Every::Tuple) => KType::universe(Universe::Tuple),
        TypeKind::Every(Every::Struct) => KType::universe(Universe::Struct),
        TypeKind::AtomAny(a) => KType::atom_with(a, &KType::top()),
        TypeKind::Atom(a) => KType::atom(a),
        TypeKind::Tuple(_) => KType::tuple(parts.into_iter().collect::<Option<_>>()?),
        TypeKind::Union(_) => KType::union_all(parts.into_iter().collect::<Option<Vec<_>>>()?),
        TypeKind::And(_) => KType::meet_all(parts.into_iter().collect::<Option<Vec<_>>>()?),
        TypeKind::Diff(..) => {
            let [a, b] = <[Option<KType>; 2]>::try_from(parts).expect("two parts");
            a? - &b?
        }
        TypeKind::Arrow { partial, .. } => {
            let mut keys: Vec<KType> = parts.into_iter().collect::<Option<_>>()?;
            let result = keys.pop().expect("the result is the last part");
            if keys.is_empty() {
                keys.push(KType::tuple(Vec::new()));
            }
            let level = if *partial {
                KType::partial
            } else {
                KType::exact
            };
            keys.into_iter().rev().fold(result, |v, k| level(k, v))
        }
        TypeKind::Bounded { .. } => {
            let [l, u, v] = <[Option<KType>; 3]>::try_from(parts).expect("three parts");
            let (l, u) = (l?, u?);
            if let Some(bounds) = bounds
                && !l.subtype(&u)
            {
                let why = match l.subtype_verdict(&u) {
                    zed_kernel::types::Verdict::Refused(r) => {
                        format!(" (not decided: {})", r.message())
                    }
                    _ => String::new(),
                };
                bounds.push((
                    t.span,
                    format!(
                        "the guarantee (left of `..`) of this morphism type is not within its \
                         permission (right of `..`){why}"
                    ),
                ));
            }
            KType::morphism(l, u, v?)
        }
    })
}

/// A type expression being elaborated by [`kernel_type`]: its parts and the types of those done.
struct OpenType<'t> {
    t: &'t Type,
    parts: Vec<&'t Type>,
    done: Vec<Option<KType>>,
}

impl<'t> OpenType<'t> {
    fn of(t: &'t Type) -> Self {
        Self {
            t,
            parts: type_parts(t),
            done: Vec::new(),
        }
    }
}

/// The parts of `t` that [`kernel_form`] takes the types of, in the order the source writes
/// them: a function type's parameters, then its result.
fn type_parts(t: &Type) -> Vec<&Type> {
    match &t.kind {
        TypeKind::Tuple(ts) | TypeKind::Union(ts) | TypeKind::And(ts) => ts.iter().collect(),
        TypeKind::Diff(a, b) => vec![a, b],
        TypeKind::Arrow { params, result, .. } => {
            params.iter().map(|p| &p.ty).chain([&**result]).collect()
        }
        TypeKind::Bounded {
            lower,
            upper,
            result,
        } => vec![lower, upper, result],
        TypeKind::Name(_)
        | TypeKind::Atom(_)
        | TypeKind::Every(_)
        | TypeKind::AtomAny(_)
        | TypeKind::Apply(..)
        | TypeKind::AtomApply(..)
        | TypeKind::Record(_)
        | TypeKind::Array(_)
        | TypeKind::For { .. } => Vec::new(),
    }
}

/// An atom pattern being elaborated by [`Elab::pattern`]: by position, the patterns of the
/// items done; by name, the fields done.
enum OpenPattern<'p> {
    Items {
        name: &'p str,
        items: &'p [Pattern],
        done: Vec<KPattern>,
    },
    Fields {
        name: &'p str,
        fields: &'p [(String, Option<Pattern>)],
        span: Span,
        done: Vec<(Arc<str>, KPattern)>,
    },
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
                    Target::Name(n, _) => Some(format!("`{n}`")),
                    Target::Wild => None,
                })
                .collect();
            names.join(" and ")
        }
        StmtKind::Function(f) => format!("`{}`", f.name),
        StmtKind::Push { port, .. } => format!("the push to `{port}`"),
        StmtKind::Return(_) => "the export".into(),
        StmtKind::UnitAnnot(a) => format!("the unit item `@{}`", a.name),
        StmtKind::Struct(_)
        | StmtKind::Type(_)
        | StmtKind::Method(_)
        | StmtKind::Import(_)
        | StmtKind::Annotated { .. } => {
            unreachable!("resolve rejects the forms of layer L2")
        }
        StmtKind::Mutable(_)
        | StmtKind::IndexedDef(_)
        | StmtKind::While(_)
        | StmtKind::Until(_)
        | StmtKind::Expr(_) => unreachable!("resolve rejects the forms of layer L6"),
    }
}

/// The order the top-level statements of `unit` other than its export are bound in, as
/// indices among them; else the statements of one cycle. For tests of the dependency order.
#[doc(hidden)]
pub fn top_order(unit: &[Stmt], res: &Resolution) -> Result<Vec<usize>, Vec<usize>> {
    let items: Vec<&Stmt> = (unit.iter())
        .filter(|s| !matches!(s.kind, StmtKind::Return(_)))
        .collect();
    Tables::new(unit, res).order(&items)
}

/// An order of `0..deps.len()` with each item after its dependencies, ties by index; else the
/// items of one cycle, in order along it. The ready items wait in a heap, smallest first, each
/// counting the dependencies it still waits on, so the order takes `O((n + e) log n)`.
#[doc(hidden)]
pub fn topo(deps: &[Vec<usize>]) -> Result<Vec<usize>, Vec<usize>> {
    let (order, done) = place(deps, deps.len());
    if order.len() < deps.len() {
        // Every item left waits on another left: walk to the first in each list.
        return Err(cycle(&done, |i| {
            *(deps[i].iter())
                .find(|&&d| !done[d])
                .expect("a dependency left")
        }));
    }
    Ok(order)
}

/// [`topo`] of the items `0..items` of a graph whose nodes from `items` on are joins, each
/// waiting on the items of its list: an item waiting on a join waits on each of them. The
/// order is that of the graph with each join's items written into each list naming the join,
/// at the cost of the graph as given; the cycle, of an unfinished order, walks to the least
/// item left of each list, a join's items included.
#[doc(hidden)]
pub fn topo_joined(deps: &[Vec<usize>], items: usize) -> Result<Vec<usize>, Vec<usize>> {
    let (order, done) = place(deps, items);
    if order.len() < items {
        // A join's least item left is found once; the walk reads each list once, since it
        // stops at the first item it meets again.
        let mut least: HashMap<usize, usize> = HashMap::new();
        return Err(cycle(&done, |i| {
            (deps[i].iter())
                .filter(|&&d| !done[d])
                .map(|&d| match d < items {
                    true => d,
                    false => *least.entry(d).or_insert_with(|| {
                        *(deps[d].iter())
                            .filter(|&&e| !done[e])
                            .min()
                            .expect("a join not passed has an item left")
                    }),
                })
                .min()
                .expect("a dependency left")
        }));
    }
    Ok(order)
}

/// The items of `0..items` placed in order, and which nodes are placed or passed. A join is
/// passed once its last item is placed, before the next item is taken, so the items ready at
/// each step are those of the graph without joins.
fn place(deps: &[Vec<usize>], items: usize) -> (Vec<usize>, Vec<bool>) {
    let n = deps.len();
    let mut waits: Vec<usize> = deps.iter().map(Vec::len).collect();
    let mut users: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (i, ds) in deps.iter().enumerate() {
        for &d in ds {
            users[d].push(i);
        }
    }
    let mut ready: BinaryHeap<Reverse<usize>> =
        (0..items).filter(|&i| waits[i] == 0).map(Reverse).collect();
    let mut passed: Vec<usize> = (items..n).filter(|&j| waits[j] == 0).collect();
    let mut done = vec![false; n];
    let mut order = Vec::with_capacity(items);
    loop {
        let i = match passed.pop() {
            Some(j) => j,
            None => match ready.pop() {
                Some(Reverse(i)) => {
                    order.push(i);
                    i
                }
                None => break,
            },
        };
        done[i] = true;
        for &u in &users[i] {
            waits[u] -= 1;
            if waits[u] == 0 {
                match u < items {
                    true => ready.push(Reverse(u)),
                    false => passed.push(u),
                }
            }
        }
    }
    (order, done)
}

/// The cycle reached from the first item left by `next`, which gives the item left that an
/// item left waits on.
fn cycle(done: &[bool], mut next: impl FnMut(usize) -> usize) -> Vec<usize> {
    let mut seen: BTreeMap<usize, usize> = BTreeMap::new();
    let mut path = Vec::new();
    let mut i = (0..done.len()).find(|&i| !done[i]).expect("an item left");
    while !seen.contains_key(&i) {
        seen.insert(i, path.len());
        path.push(i);
        i = next(i);
    }
    path.split_off(seen[&i])
}
