//! The front end of one unit's text (steps L1.29, L1.38 and L2.3): lexing through elaboration
//! and the linear questions (`compile`), the statements and imports of a unit read alone
//! (`parse_unit`), and the diagnostics they give, placed in the source. The queries
//! (`crate::query`) memoize both, and the package loader (`crate::unit`) and the commands
//! (`crate::run`) read them through the queries, so this file is below all three.

use std::sync::Arc;

use zed_kernel::{Shared, Term};

use crate::address::ContentAddress;
use crate::ast::{self, Error, Stmt, StmtKind};
use crate::elab::{Unit, elaborate};
use crate::lex::{self, Span};
use crate::parse::{TOP, parse};
use crate::resolve::{self, Alone};
use crate::suppress::{self, Severity};
use crate::work::{self, Stage};
use crate::{docs, interp, source};

/// The front end's result: the statements, elaboration and placed warnings, or the first
/// rejecting phase's diagnostics.
pub type Front = Result<(Vec<Stmt>, Unit, Vec<Diagnostic>), Vec<Diagnostic>>;

/// A unit's statements and its imports, each with the unit it names, in text order; or the
/// errors of the first phase that rejects it.
pub type Parsed = Result<(Vec<Stmt>, Vec<(Arc<str>, Span)>), Vec<ast::Error>>;

/// A message of the compiler, at a line and column of the source, both counted from 1, with
/// its derivation (DESIGN.md "Diagnostics").
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Diagnostic {
    /// The line.
    pub line: usize,
    /// The column.
    pub col: usize,
    /// Why.
    pub message: String,
    /// Each constraint and step that led to it, in the order the compiler met them.
    pub steps: Vec<Step>,
    /// The row of the rejection table (DESIGN.md sec:diagnostics) it is a case of, if any.
    pub row: Option<crate::rejection::Row>,
    /// The part of its address that the unit's text decides, the same on every run of the same
    /// text; the address printed and suppressed joins it with the file's part
    /// ([`crate::suppress::InFile::address`]).
    pub address: ContentAddress,
}

/// One step of a derivation, placed in the source.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Step {
    /// The line.
    pub line: usize,
    /// The column.
    pub col: usize,
    /// What holds there.
    pub text: String,
    /// The source line.
    pub source: String,
    /// How many characters of the source line the step covers, at least 1.
    pub width: usize,
}

impl std::fmt::Display for Diagnostic {
    /// The message on one line; then each step numbered, with its source line and the text
    /// it covers underlined, a source line shown once for consecutive steps on one place.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}: {}", self.line, self.col, self.message)?;
        let gutter = self
            .steps
            .iter()
            .map(|s| s.line.to_string().len())
            .max()
            .unwrap_or(0);
        let number = self.steps.len().to_string().len();
        let pad = " ".repeat(number + 4);
        let mut last = None;
        for (i, s) in self.steps.iter().enumerate() {
            let n = format!("[{}]", i + 1);
            write!(
                f,
                "\n  {n:<w$} {}:{}: {}",
                s.line,
                s.col,
                s.text,
                w = number + 2
            )?;
            if last == Some((s.line, s.col, s.width)) {
                continue;
            }
            last = Some((s.line, s.col, s.width));
            write!(f, "\n{pad} {:>gutter$} | {}", s.line, s.source)?;
            write!(
                f,
                "\n{pad} {:>gutter$} | {}{}",
                "",
                " ".repeat(s.col - 1),
                "^".repeat(s.width)
            )?;
        }
        Ok(())
    }
}

/// The statements, elaboration and warnings of the unit `text`, the warnings moved out of the
/// elaboration and placed in the source, or the diagnostics of the first phase that rejects it.
pub(crate) fn compile(text: &str) -> Result<(Vec<Stmt>, Unit, Vec<Diagnostic>), Vec<Diagnostic>> {
    let lines = source::Lines::new(text.as_bytes());
    let at = |span: lex::Span, message: String| {
        let e = ast::Error {
            span,
            message,
            notes: Vec::new(),
            row: None,
        };
        placed(text, &lines, &[], Severity::Rejection, vec![e])
    };
    let (tokens, docs) = work::stage(Stage::Lex, None, || lex::lex_with_docs(text))
        .map_err(|e| at(e.span, e.to_string()))?;
    let tree = work::stage(Stage::Parse, None, || parse(text, &tokens, "Unit", TOP))
        .map_err(|e| at(e.span, e.to_string()))?;
    let stmts = work::stage(Stage::Syntax, None, || {
        ast::unit_all_errors(text, &tokens, &tree)
    })
    .map_err(|es| placed(text, &lines, &[], Severity::Rejection, es))?;
    let all = |errors: Vec<ast::Error>| placed(text, &lines, &stmts, Severity::Rejection, errors);
    let res = work::stage(Stage::Resolve, None, || resolve::resolve(&stmts)).map_err(all)?;
    // Doc comments are checked after parsing; their errors join elaboration's.
    let mut errors = work::stage(Stage::Docs, None, || {
        docs::check(text, &tokens, &docs, &res)
    });
    let elaborated = work::stage(Stage::Elaborate, None, || elaborate(&stmts, &res));
    let mut unit = match elaborated {
        Ok(unit) if errors.is_empty() => unit,
        Ok(_) => return Err(all(errors)),
        Err(es) => {
            errors.extend(es);
            errors.sort_by_key(|e| e.span);
            return Err(all(errors));
        }
    };
    let refused = work::stage(Stage::Linear, None, || linear_questions(&stmts, &unit));
    if !refused.is_empty() {
        return Err(all(refused));
    }
    let warnings = placed(
        text,
        &lines,
        &stmts,
        Severity::Warning,
        std::mem::take(&mut unit.warnings),
    );
    Ok((stmts, unit, warnings))
}

/// The menu of a refused linear question at L1 (DESIGN.md sec:diagnostics, row "Linear question
/// outside the polynomial fragment"): the repairs an L1 program can follow. A written domain on
/// a name and the check moved to a `refine` join it at L10, a `proof { }` at L15. Tests:
/// `l01_38_presburger::checker::following_each_repair_of_the_menu_makes_the_program_check`.
const NON_LINEAR_MENU: [&str; 2] = [
    "repair: state an equality on one of the names, as `x == 4 && …`, so the solver removes \
     that name from the question",
    "repair: split the question into functions of fewer constraints each, and join their \
     results where they are called; a function whose body joins them asks the joined question \
     again",
];

/// The linear questions of the unit (step L1.38): for each function other than `main` whose
/// body the linear-relation domain states over its parameters, whether the body can hold and
/// whether it can fail. A question the solver refuses is a rejection at the function, with
/// its cause and the constraints (DESIGN.md "Diagnostics"); a decided question rejects nothing,
/// since a test that never holds is an unreachable arm (step L1.39).
///
/// Complexity tradeoff: a function whose question the solver refuses is rejected, though the
/// program may be correct; the message is "whether `f` can hold is not decided: <cause>". Why:
/// the solver decides only the fragment it can decide without exponential search (the
/// causes, their costs and their triggers are at `presburger::Refusal`'s raise sites:
/// Growth in `Omega::run`, Shadows in `search`, Disjuncts in `pick`). Tests:
/// `l01_38_presburger::checker::a_satisfiable_question_with_no_elimination_that_keeps_the_rows_is_refused`,
/// `l01_38_presburger::checker::a_question_whose_point_lies_past_one_splinter_is_rejected`,
/// `l01_38_presburger::checker::the_linear_questions_of_a_unit_scale`. COMPLEXITY.md row S18.
/// A complete solution would need a complete Presburger procedure, exponential in the worst
/// case, or would accept the function with a warning in place of the rejection.
///
/// Public for the test that times the questions alone, on a unit loaded before the timing:
/// loading the unit of 64 functions there costs 3.5 times its questions, so a scaling test that
/// times the whole load cannot see a quadratic here (COMPLEXITY.md F85).
#[doc(hidden)]
pub fn linear_questions(stmts: &[Stmt], unit: &Unit) -> Vec<ast::Error> {
    use crate::store::{preimage, presburger};
    // The functions of the unit by name and written parameter names, so each overload of a name
    // finds its own definition; overloads alike in both, which differ in types only, are matched
    // to their definitions in the order of the unit's definitions. A kernel name is the written
    // name or the written name and `@k` (`crate::elab`), and a written name holds no `@`
    // (`crate::lex::name`). O(n) in the size of the parameter lists.
    type Key<'a> = (&'a str, Vec<&'a str>);
    type Lams<'a> = Vec<(&'a [Arc<str>], &'a Shared)>;
    let mut defs: std::collections::HashMap<Key, Lams> = std::collections::HashMap::new();
    for d in unit.defs.iter().rev() {
        if let Term::Lam(ps, body) = &*d.term {
            let written = ps.iter().map(|k| crate::elab::written_name(k));
            (defs
                .entry((d.name.as_str(), written.collect()))
                .or_default())
            .push((ps, body));
        }
    }
    // The prelude and every definition, as one chain of lets, each after those it uses, as
    // `Cones::close` binds a body's cone: numbered once and read once for all the functions,
    // where closing each body over its cone read a chain of n calls n times (LOAD-chain).
    let lets = interp::prelude(
        unit.defs
            .iter()
            .rev()
            .fold(Term::Lit(zed_kernel::Value::Bool(true)), |body, d| {
                Term::Let(d.kernel.clone(), d.term.clone(), Shared::new(body))
            }),
    );
    let mut scoped = preimage::Scoped::new(&lets);
    let mut extending = presburger::extend::Extending::new();
    let mut out = Vec::new();
    for s in stmts {
        let StmtKind::Function(f) = &s.kind else {
            continue;
        };
        if f.name == "main" {
            continue;
        }
        let key = (
            f.name.as_str(),
            f.params.iter().map(|p| p.name.as_str()).collect(),
        );
        let Some((ps, body)) = defs.get_mut(&key).and_then(Vec::pop) else {
            continue;
        };
        work::stage(Stage::Linear, Some(&f.name), || {
            // A caller's relation holds its callee's as one shared part (`preimage::Scoped`), and
            // is decided from the callee's answers and its own new constraints
            // (`presburger::extend`), so a chain of n tests `p{i}(x) = p{i-1}(x: x) && x > i`,
            // over one variable or several, costs O(n) in all. Complexity tradeoff: a chain
            // whose links each exclude the point found for their callee is decided whole at each
            // link, O(n²) (at `Extending::defined`); so is one whose links pass their callee other
            // arguments than their own names (`p{i-1}(x: x + 1)`), whose calls are each
            // translated again. Tests `l01_38_presburger::one_scope::
            // the_questions_of_a_chain_of_tests_scale` and `..._over_two_variables_scale`.
            // COMPLEXITY.md rows LOAD-chain and LOAD-chain-share. A chain whose links define
            // auxiliary variables (`x mod 7`) costs O(n) as well: they are numbered once for the
            // scope, and each question reads the definitions its new parts reach (LOAD-chain-aux).
            // The question is stated over the names the user wrote: elaboration renames a binder
            // `x` to `x@k` when another binder of the unit is named `x` too (`crate::elab`), which
            // the user cannot write, so the question, its refusal and its constraints print `x`,
            // and their names do not change with the other functions of the unit. The auxiliary
            // variables of the constraints are numbered from 0 in the order the scope made them,
            // which an earlier function that made one of them first may change.
            let inputs: Vec<Arc<str>> = f.params.iter().map(|p| p.name.as_str().into()).collect();
            if let Some(r) = scoped.relation(body, ps, &inputs, true) {
                let answers = extending.defined(&r, &|n| scoped.def(n));
                for (can, answer) in [("hold", answers.holds), ("fail", answers.fails)] {
                    if let Err(why) = answer {
                        out.push(ast::Error {
                            row: Some(crate::rejection::Row::NonLinearQuestion),
                            span: s.span,
                            message: format!(
                                "whether `{}` can {can} is not decided: {why}",
                                f.name
                            ),
                            notes: vec![
                                ast::Note {
                                    span: f.body.span,
                                    text: format!("the constraints: {}", scoped.written(&r)),
                                },
                                // O(1): two constant lines per refused question.
                                ast::Note {
                                    span: f.body.span,
                                    text: NON_LINEAR_MENU[0].into(),
                                },
                                ast::Note {
                                    span: f.body.span,
                                    text: NON_LINEAR_MENU[1].into(),
                                },
                            ],
                        });
                    }
                }
            }
        });
    }
    out
}

/// The errors `errors` of `text`, of `severity`, as diagnostics, each placed with its steps and
/// its address; `stmts` are the unit's top-level statements, empty when it was rejected before
/// it had them.
pub(crate) fn placed(
    text: &str,
    lines: &source::Lines,
    stmts: &[Stmt],
    severity: Severity,
    errors: Vec<ast::Error>,
) -> Vec<Diagnostic> {
    let addresses = suppress::addresses(text, stmts, severity, &errors);
    errors
        .into_iter()
        .zip(addresses)
        .map(|(e, address)| {
            let (line, col) = lines.line_col(text.as_bytes(), e.span.start);
            Diagnostic {
                line,
                col,
                steps: e.notes.into_iter().map(|n| step(text, lines, n)).collect(),
                message: e.message,
                row: e.row,
                address,
            }
        })
        .collect()
}

/// The step a note is in `text`: its line and column, the source line, and the characters of
/// the note's span on that line.
fn step(text: &str, lines: &source::Lines, n: ast::Note) -> Step {
    let (line, col) = lines.line_col(text.as_bytes(), n.span.start);
    let begin = lines.line_start(n.span.start).0;
    let end = text[n.span.start..]
        .find(['\n', '\r'])
        .map_or(text.len(), |i| n.span.start + i);
    let width = text[n.span.start..n.span.end.clamp(n.span.start, end)]
        .chars()
        .count();
    Step {
        line,
        col,
        text: n.text,
        source: text[begin..end].to_string(),
        width: width.max(1),
    }
}
/// An error at `span` with no derivation.
pub(crate) fn error(span: Span, message: String) -> Error {
    Error {
        row: None,
        span,
        message,
        notes: Vec::new(),
    }
}

/// The statements of the unit `text` and its imports, each with the unit it names, in text
/// order; or the errors of the first phase that rejects it. What [`Query::Parse`] computes.
///
/// [`Query::Parse`]: crate::query::Query::Parse
pub(crate) fn parse_unit(text: &str) -> Parsed {
    let tokens = lex::lex(text).map_err(|e| vec![error(e.span, e.to_string())])?;
    let tree = parse(text, &tokens, "Unit", TOP).map_err(|e| vec![error(e.span, e.to_string())])?;
    let stmts = ast::unit_all_errors(text, &tokens, &tree)?;
    // The imports are found by the resolver's own walk, which meets every import in every
    // scope; read alone, the unit resolves with no other unit, and only the imports are kept.
    let mut imports = resolve::resolve_in(&stmts, &Alone).res.units;
    imports.sort_by_key(|i| i.1);
    Ok((stmts, imports))
}
