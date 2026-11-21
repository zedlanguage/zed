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

use std::collections::HashMap;
use std::sync::Arc;

use zed_kernel::Shared;

use zedc_base::rejection;
use zedc_base::work::{self, Stage};
use zedc_check::check::ty::{NameDigests, Sig};
use zedc_check::check::{self, Info};
use zedc_resolve::resolve::Resolution;
use zedc_resolve::resolve::tables::Tables;
use zedc_syntax::ast::{Error, Stmt, StmtKind, Target};

mod bodies;
#[cfg(test)]
mod dropped_tests;
mod identities;
mod instances;
pub mod mark;
mod state;
mod walk;

use mark::Mark;
use state::Elab;

pub use walk::MAIN_KEY;
pub use zedc_resolve::resolve::topo::{topo, topo_joined};
pub use zedc_stage::defs::{CallNames, Def, Test, Unit, written_name};
pub use zedc_stage::stage::Cones;

/// The elaboration of `unit` under its resolution, or every error in it, in text order.
pub fn elaborate(unit: &[Stmt], res: &Resolution) -> Result<Unit, Vec<Error>> {
    elaborate_text(unit, res, None, None)
}

/// [`elaborate`], with the unit's text when it is known, which a message quotes: the line each
/// fix of a rejected literal rewrites; and with the target it is built for, as `build.target`
/// names it, which a message that depends on the target names.
pub fn elaborate_text(
    unit: &[Stmt],
    res: &Resolution,
    text: Option<&str>,
    target: Option<&str>,
) -> Result<Unit, Vec<Error>> {
    elaborate_in(unit, res, text, target, None).map(|(unit, _)| unit)
}

/// The elaboration of `unit` as [`elaborate`] gives it, with each written operator and integer
/// constant a mutant may replace marked, and the marks (step L25.8). A marked operator
/// `Prim(p, [a, b])` is `Prim(p, [a, b, m])` and a marked constant `n` is `Prim(Neg, [n, m])`,
/// `m` the literal index of its [`Mark`]: neither shape is elaborated otherwise, an operator
/// having two arguments and `Neg` one. A mark adds a last child or wraps a leaf, so every
/// node of the unmarked elaboration has the same position in the marked one. The marked unit
/// is for finding positions only; it is never run.
pub fn elaborate_marked(unit: &[Stmt], res: &Resolution) -> Result<(Unit, Vec<Mark>), Vec<Error>> {
    elaborate_in(unit, res, None, None, Some(Vec::new()))
        .map(|(unit, marks)| (unit, marks.expect("marks were asked for")))
}

fn elaborate_in<'a>(
    unit: &'a [Stmt],
    res: &'a Resolution,
    text: Option<&'a str>,
    target: Option<&'a str>,
    marks: Option<Vec<Mark>>,
) -> Result<(Unit, Option<Vec<Mark>>), Vec<Error>> {
    let mut t = Tables::with_text(unit, res, text);
    t.target = target;
    let (mut info, warnings) = work::stage(Stage::Check, None, || {
        let info = check::walk::check_with(&t, unit);
        let warnings = check::widen::warnings(&t, unit, &info);
        (info, warnings)
    });
    // The checker's errors first, so that where both report one error, as for an argument
    // that fills no parameter, the checker's, which carries its notes, is the one kept: the
    // sort is stable.
    let checked = std::mem::take(&mut info.errors);
    let refused = std::mem::take(&mut info.warnings);
    let (mut out, marks, errors) = lower(t, &info, unit, marks, checked);
    // The widening warnings and the checker's refused questions, each list in order of place,
    // merged in order of place: the sort is stable, so of two at one place the widening comes
    // first, then the questions in their own order.
    out.warnings = warnings;
    out.warnings.extend(refused);
    out.warnings.sort_by_key(|w| w.span);
    finish(out, marks, errors)
}

/// The elaboration of `unit` under its resolution from `info`, the checker's [`check::walk::check`]
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
    e.keep_checker_spans(&errors);
    // Which parameters of each declared function take only `int`s, for rung 2, which reads
    // arithmetic as integer arithmetic (`Sig::int_params`, RUNG2-carrier). O(functions ×
    // arrows × parameters).
    let int_params = (e.info.sigs.iter())
        .map(|(&id, sig)| (e.names[id].clone(), sig.int_params()))
        .collect();
    let mut out = Unit {
        int_params,
        limits: e.info.limits,
        ..Unit::default()
    };
    // The functions declared at the top level, whose calls may decide the identities of
    // their folds (REDUCE-generic-identity, `instances`).
    if !e.info.split_needs.is_empty() {
        for s in unit.iter().map(Stmt::bare) {
            if let StmtKind::Function(f) = &s.kind {
                let id = e.id(s.span, &f.name);
                e.inst.fns.insert(id, s);
            }
        }
    }
    let scope = e.scope(unit, true);
    // Folds no call decided outside every top-level statement are the export's, which the
    // unit always runs.
    let export: Vec<_> = std::mem::take(&mut e.inst.undecided);
    match scope {
        Some((binds, _)) => {
            e.make_instances();
            // The parameters a call may name, of each definition that is a function: a declared
            // function's from its signature, by its binder's kernel name; a name bound by `=` to a
            // function, as `inc = x -> x + 1`, from its type when that holds one function, since a
            // call through the name passes arguments as that function's signature says (DESIGN.md
            // sec:values_morphisms). With them, the digest of the names a call may write inside
            // the definition's type: a function it returns, a parameter's function type, a
            // function in a tuple (ADDR-nested-param-names), each signature, row and shape the
            // unit's types share hashed once for the whole unit. O(functions + definitions ×
            // parameters + distinct nodes of the types).
            let declared: HashMap<&str, &Sig> = (e.info.sigs.iter())
                .map(|(&id, sig)| (&*e.names[id], &**sig))
                .collect();
            let mut digests = NameDigests::default();
            for (name, kernel, _) in &binds {
                let names = match (declared.get(&**kernel), e.info.tops.get(name)) {
                    (Some(&sig), _) => CallNames {
                        params: sig.callable_names(),
                        inside: digests.sig(sig),
                    },
                    (None, Some(t)) => CallNames {
                        params: (t.fns.only()).map_or(Vec::new(), |s| s.callable_names()),
                        inside: digests.ty(t),
                    },
                    (None, None) => continue,
                };
                out.param_names.insert(kernel.clone(), names);
            }
            // Each body made for a call goes right after the function's written body: after
            // the definitions it reads, which the written body reads too, or which are bodies
            // made of earlier functions, each right after its own.
            let mut bodies: HashMap<Arc<str>, Vec<Def>> = HashMap::new();
            for (id, d) in std::mem::take(&mut e.inst.bodies) {
                let base = e.names[id].clone();
                if let Some(ps) = out.param_names.get(&base).cloned() {
                    out.param_names.insert(d.kernel.clone(), ps);
                }
                if let Some(ps) = out.int_params.get(&base).cloned() {
                    out.int_params.insert(d.kernel.clone(), ps);
                }
                bodies.entry(base).or_default().push(d);
            }
            for (name, kernel, term) in binds {
                let made = bodies.remove(&kernel);
                out.defs.push(Def {
                    first_order: e.info.tops.get(&name).is_some_and(|t| t.first_order()),
                    name,
                    kernel,
                    term: Shared::new(term),
                });
                out.defs.extend(made.into_iter().flatten());
            }
        }
        // A unit that gives no term with no error of the checker's or of elaboration's would
        // be run or tested as if it declared nothing; it is a bug in zedc, reported at the
        // first definition that gave no term (FAIL-elab-none-without-error).
        None if errors.is_empty() && e.errors.is_empty() => {
            let at = e
                .dropped
                .or_else(|| (unit.iter()).find(|s| matches!(s.kind, StmtKind::Return(_))));
            // A unit's scope gives no term only at a cycle, which pushes its errors, at a
            // statement that gives none, which sets `dropped`, or at its export.
            let at = at.expect("a unit that gives no term has a statement that gives none");
            e.errors.push(Error {
                menu: String::new(),
                row: None,
                span: at.span,
                message: rejection::bug(
                    &format!(
                        "each definition the checker accepts is elaborated or elaboration says \
                         why it is not, and {} was neither",
                        named(at)
                    ),
                    Some((file!(), line!())),
                ),
                notes: Vec::new(),
            });
        }
        None => {}
    }
    out.tests = std::mem::take(&mut e.tests).into();
    // A unit elaboration rejected may have left calls unelaborated, so only an accepted one
    // is checked for folds no body took, and for a dropped written body a kept term names.
    if errors.is_empty() && e.errors.is_empty() {
        e.check_instances(&out.defs, &out.tests, export);
        e.check_dropped(&out.defs, &out.tests);
    }
    errors.append(&mut e.errors);
    (out, e.marks.take(), errors)
}

/// The definition `s` names in a message: `` `f` `` for a function, `` `a`, `b` `` for a
/// binding, and the unit's `return` for its export.
fn named(s: &Stmt) -> String {
    match &s.bare().kind {
        StmtKind::Function(f) => format!("`{}`", f.name),
        StmtKind::Bind { targets, .. } => (targets.iter())
            .map(|t| match t {
                Target::Name(n, _) => format!("`{n}`"),
                Target::Wild => "`_`".to_string(),
            })
            .collect::<Vec<_>>()
            .join(", "),
        StmtKind::Return(_) => "the unit's `return`".to_string(),
        _ => "a statement".to_string(),
    }
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
        errors.iter_mut().for_each(Error::sentence);
        // `dedup_by` drops only a copy next to the one kept, so the sort key holds every field
        // the dedup compares: equal errors are then adjacent and each is kept once. With the
        // row left out of the key, two copies with an error of another row at the same place
        // and words between them were both kept (test
        // `copies_of_an_error_with_another_row_between_them_are_kept_once`). The sort is
        // stable, so of two equal errors the first given, the checker's, is kept.
        errors.sort_by(|a, b| {
            (a.span, &a.message, &a.menu, a.row).cmp(&(b.span, &b.message, &b.menu, b.row))
        });
        errors.dedup_by(|a, b| {
            (a.span, &a.message, &a.menu, a.row) == (b.span, &b.message, &b.menu, b.row)
        });
        Err(errors)
    }
}

/// The order the top-level statements of `unit` other than its export are bound in, as
/// indices among them; else the statements of each cycle, as [`topo_joined`] gives them. For
/// tests of the dependency order.
#[doc(hidden)]
pub fn top_order(unit: &[Stmt], res: &Resolution) -> Result<Vec<usize>, Vec<Vec<usize>>> {
    let items: Vec<&Stmt> = (unit.iter())
        .filter(|s| !matches!(s.kind, StmtKind::Return(_)))
        .map(Stmt::bare)
        .collect();
    Tables::new(unit, res).order(&items)
}

#[cfg(test)]
mod tests {
    use super::*;
    use zedc_syntax::lex::Span;

    /// An error at `0..1` with the message `m` and the row `row`.
    fn error(m: &str, row: Option<rejection::Row>) -> Error {
        Error {
            span: Span { start: 0, end: 1 },
            message: m.into(),
            notes: Vec::new(),
            menu: String::new(),
            row,
        }
    }

    /// Two copies of one error, with one of another row between them, are kept once: the
    /// sort puts the copies next to each other, which the dedup needs.
    #[test]
    fn copies_of_an_error_with_another_row_between_them_are_kept_once() {
        let a = Some(rejection::Row::Collision);
        let b = Some(rejection::Row::LiteralCarrier);
        let errors = vec![error("x.", a), error("x.", b), error("x.", a)];
        let Err(kept) = finish(Unit::default(), None, errors) else {
            panic!("errors were given")
        };
        let rows: Vec<_> = kept.iter().map(|e| e.row).collect();
        assert_eq!(rows.len(), 2, "{rows:?}");
    }
}
