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

use zed_kernel::Shared;

use zedc_base::work::{self, Stage};
use zedc_check::check::{self, Info};
use zedc_resolve::resolve::Resolution;
use zedc_resolve::resolve::tables::Tables;
use zedc_syntax::ast::{Error, Stmt, StmtKind};

pub mod mark;
mod state;
mod walk;

use mark::Mark;
use state::Elab;

pub use walk::MAIN_KEY;
pub use zedc_resolve::resolve::topo::{topo, topo_joined};
pub use zedc_stage::defs::{Def, Test, Unit, written_name};
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
    e.rejected = !errors.is_empty();
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
        errors.iter_mut().for_each(Error::sentence);
        errors.sort_by(|a, b| (a.span, &a.message, &a.menu).cmp(&(b.span, &b.message, &b.menu)));
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
