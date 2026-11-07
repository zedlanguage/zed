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

use std::collections::{BTreeSet, HashMap, HashSet};
use std::sync::Arc;

use zed_kernel::num::{LiteralRounding, bytes_of, literal_f64, show_f64};
use zed_kernel::types::Type as KType;
use zed_kernel::{Pattern as KPattern, Prim, Rat, Shared, Term, Value};

use crate::ast::{Error, Expr, ExprKind, Function, Pattern, Stmt, StmtKind, StrPart, Target, Type};
use crate::check::{self, Fit, Info, Misfit};
use crate::lex::{Span, unread_literal};
use crate::rejection::Row;
use crate::resolve::tables::Tables;
use crate::resolve::{Kind, Ref, Resolution, prelude_layer};
use crate::work::{self, Stage};

mod defs;
mod kernel_type;
mod walk;

pub use crate::stage::Cones;
pub use defs::{Def, Test, Unit, written_name};
pub(crate) use kernel_type::kernel_type;
pub use crate::resolve::topo::{topo, topo_joined};

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
    let (mut info, warnings) = work::stage(Stage::Check, None, || {
        let info = check::check_with(&t, unit);
        let warnings = check::widen::warnings(&t, unit, &info);
        (info, warnings)
    });
    // The checker's errors first, so that where both report one error, as for an argument
    // that fills no parameter, the checker's, which carries its notes, is the one kept: the
    // sort is stable.
    let checked = std::mem::take(&mut info.errors);
    let (mut out, marks, errors) = lower(t, &info, unit, marks, checked);
    out.warnings = warnings;
    finish(out, marks, errors)
}

/// The elaboration of `unit` under its resolution from `info`, the checker's [`check::check`]
/// of the same unit and resolution, with no errors, or elaboration's own errors in text
/// order. It does what [`elaborate`] does after checking, and gives no warnings, which the
/// checker's widening pass finds. For tests that measure elaboration alone: parsing and
/// checking cost far more per term than elaboration, so a scaling test that times them too
/// cannot see a quadratic in elaboration (COMPLEXITY.md F85).
#[doc(hidden)]
pub fn elaborate_checked(unit: &[Stmt], res: &Resolution, info: &Info) -> Result<Unit, Vec<Error>> {
    assert!(
        info.errors.is_empty(),
        "elaborate_checked takes the Info of a unit the checker accepts"
    );
    let (out, marks, errors) = lower(Tables::new(unit, res), info, unit, None, Vec::new());
    finish(out, marks, errors).map(|(unit, _)| unit)
}

/// Elaboration proper: the unit's definitions and tests from the binder tables `t` and the
/// checker's `info`, with `errors` followed by elaboration's own.
fn lower<'a>(
    t: Tables<'a>,
    info: &'a Info,
    unit: &'a [Stmt],
    marks: Option<Vec<Mark>>,
    mut errors: Vec<Error>,
) -> (Unit, Option<Vec<Mark>>, Vec<Error>) {
    let mut e = Elab::new(t, info);
    e.marks = marks;
    let mut out = Unit::default();
    if let Some((binds, _)) = e.scope(unit, true) {
        out.defs = binds
            .into_iter()
            .map(|(name, kernel, term)| Def {
                first_order: e.info.tops.get(&name).is_some_and(|t| t.first_order()),
                name,
                kernel,
                term: Shared::new(term),
            })
            .collect();
    }
    out.tests = std::mem::take(&mut e.tests).into();
    errors.append(&mut e.errors);
    (out, e.marks.take(), errors)
}

/// `out` and `marks`, or `errors` sorted by place and message, each once.
fn finish(
    out: Unit,
    marks: Option<Vec<Mark>>,
    mut errors: Vec<Error>,
) -> Result<(Unit, Option<Vec<Mark>>), Vec<Error>> {
    if errors.is_empty() {
        Ok((out, marks))
    } else {
        errors.sort_by(|a, b| (a.span, &a.message).cmp(&(b.span, &b.message)));
        errors.dedup_by(|a, b| (a.span, &a.message, a.row) == (b.span, &b.message, b.row));
        Err(errors)
    }
}

/// A binding of a scope: source name, kernel name, value.
type Bind = (String, Arc<str>, Term);

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
                // A term names a prelude word of L1 by its bare name, so a binder of that name is
                // renamed; a word of a later layer never reaches a term, since its use stops the
                // unit at resolution, so a binder `rate` or `order` keeps its name.
                if count[b.name.as_str()] == 1 && prelude_layer(&b.name) != Some(1) {
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

    /// A fresh binder, `$k`: no written name starts with `$`, and the ZIR text form writes and
    /// reads it as it is (zir/text.rs).
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
            Some(Ref::Unit { .. }) => {
                unreachable!("resolve sends a use of another unit's definition to step L2.4")
            }
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

    /// The type a type expression denotes ([`kernel_type()`]); each name of a port in it is an
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
    Term::If(Shared::new(c), Shared::new(a), Shared::new(b))
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
        | StmtKind::Local(_)
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
/// indices among them; else the statements of each cycle, as [`topo_joined`] gives them. For
/// tests of the dependency order.
#[doc(hidden)]
pub fn top_order(unit: &[Stmt], res: &Resolution) -> Result<Vec<usize>, Vec<Vec<usize>>> {
    let items: Vec<&Stmt> = (unit.iter())
        .filter(|s| !matches!(s.kind, StmtKind::Return(_)))
        .collect();
    Tables::new(unit, res).order(&items)
}
