//! The front end of one unit's text (steps L1.29, L1.38 and L2.3): lexing through elaboration
//! and the linear questions (`compile`), the statements and imports of a unit read alone
//! (`parse_unit`), and the diagnostics they give, placed in the source. The queries
//! (`crate::query`) memoize both, and the package loader (`crate::unit`) and the commands
//! (`crate::run`) read them through the queries, so this file is below all three.

use std::cmp::Reverse;
use std::collections::{BinaryHeap, HashMap};
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
/// rejecting phase's diagnostics. The elaboration is shared, so a program made from it
/// (`run::program`) holds the same unit.
pub type Front = Result<(Vec<Stmt>, Arc<Unit>, Vec<Diagnostic>), Vec<Diagnostic>>;

/// A unit's statements and its imports, each with the unit it names, the statement's text and
/// the content address it is pinned to, if written (step L2.8), in text order; or the errors of
/// the first phase that rejects it.
pub type Parsed = Result<(Vec<Stmt>, Vec<Imported>), Vec<ast::Error>>;

/// An import statement of a unit: the unit it names, the statement's text, its `;` included,
/// and the content address it is pinned to, if written.
pub type Imported = (Arc<str>, Span, Option<ContentAddress>);

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
    /// The column, counted in characters.
    pub col: usize,
    /// What holds there.
    pub text: String,
    /// The source line, one copy shared by every step on it.
    pub source: Arc<str>,
    /// How many characters of the source line the step covers, at least 1.
    pub width: usize,
}

impl std::fmt::Display for Diagnostic {
    /// The message on one line; then each step numbered. The first step on a line is followed
    /// by that line, shown once for all the steps of the diagnostic on it (`shown`), with the
    /// text each covers underlined (`underlines`). Each line of the source is shown once and each
    /// row of underlines is at most as long as it and the numbers in the row, so k steps on one
    /// line of L characters print O(k log k + L·r) characters, r the rows of underlines, not
    /// O(k·L).
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
        let margin = format!("\n{pad} {:>gutter$} | ", "");
        // The numbers of the steps on each line, in order.
        let mut on: HashMap<usize, Vec<usize>> = HashMap::new();
        for (i, s) in self.steps.iter().enumerate() {
            on.entry(s.line).or_default().push(i + 1);
        }
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
            if let Some(here) = on.get(&s.line)
                && here[0] == i + 1
            {
                let (text, at) = shown(&s.source);
                write!(f, "\n{pad} {:>gutter$} | {text}", s.line)?;
                underlines(f, &margin, &at, &self.steps, here)?;
            }
        }
        Ok(())
    }
}

/// The line `source` as a diagnostic quotes it, each tab shown as four spaces so that every
/// character has a known column, and the column, counted from 0, at which each character
/// starts, then the column after the line. A character takes as many columns as it does on a
/// terminal: none for a combining mark, two for a wide character. O(L) for L characters.
fn shown(source: &str) -> (String, Vec<usize>) {
    use unicode_width::UnicodeWidthChar;
    let mut text = String::with_capacity(source.len());
    let mut at = Vec::with_capacity(source.len() + 1);
    let mut column = 0;
    for c in source.chars() {
        at.push(column);
        if c == '\t' {
            text.push_str("    ");
            column += 4;
        } else {
            text.push(c);
            column += c.width().unwrap_or(0);
        }
    }
    at.push(column);
    (text, at)
}

/// Writes, each row after `margin`, the underlines of the steps numbered `numbers` (counted
/// from 1 in `steps`), all on one line whose characters start at the columns `at` (`shown`).
/// Steps that cover the same text share one underline. When the steps cover one stretch of the
/// line, it is underlined alone; otherwise each underline is followed by the numbers of its
/// steps, `[2]` or `[2, 5]`. An underline and its numbers go on the first row free from one
/// column before its start, so neither overlaps another (interval partitioning, which uses as
/// few rows as the most underlines and numbers over one column). A step that ends past the line
/// gets a caret for each character it lacks; one that covers only combining marks gets one,
/// under the character they combine with. O(s log s + C) for s steps and C characters written.
fn underlines(
    f: &mut std::fmt::Formatter<'_>,
    margin: &str,
    at: &[usize],
    steps: &[Step],
    numbers: &[usize],
) -> std::fmt::Result {
    let end = at.len() - 1;
    let column = |i: usize| at.get(i).copied().unwrap_or(at[end] + i - end);
    // Each stretch some step covers: its first character, its length in characters, and the
    // numbers of the steps that cover it.
    let mut spans: Vec<(usize, usize, usize)> = numbers
        .iter()
        .map(|&n| {
            let s = &steps[n - 1];
            (s.col - 1, s.width.max(1), n)
        })
        .collect();
    spans.sort_unstable();
    let mut covered: Vec<(usize, usize, Vec<usize>)> = Vec::new();
    for (start, width, n) in spans {
        match covered.last_mut() {
            Some((s, w, ns)) if (*s, *w) == (start, width) => ns.push(n),
            _ => covered.push((start, width, vec![n])),
        }
    }
    let labeled = covered.len() > 1;
    // Each underline: its first column, its columns, and the numbers after it. The columns grow
    // with the characters, so these stay in the order of their starts.
    let marks: Vec<(usize, usize, String)> = covered
        .into_iter()
        .map(|(start, width, ns)| {
            // A step on combining marks alone is marked under the character they combine with.
            let (from, to) = match (column(start), column(start + width)) {
                (from, to) if to > from => (from, to),
                (from, _) => (from.saturating_sub(1), from.max(1)),
            };
            let label = if labeled {
                let ns: Vec<String> = ns.iter().map(usize::to_string).collect();
                format!(" [{}]", ns.join(", "))
            } else {
                String::new()
            };
            (from, to - from, label)
        })
        .collect();
    // Complexity tradeoff: underlines that nest go on rows of their own, so a line with steps
    // nested d deep prints d rows of up to L columns: O(L·d + s log s), which is O(s + L) for
    // steps that are disjoint or nested a bounded depth, but O(s·L) for a chain nested on one line
    // as deep as it is long, such as a sum `a0 + a1 + … + an` whose every partial sum is a step.
    // What is given up: that chain's output stays quadratic in its length, though each nested step
    // prints one row and not the line again (COMPLEXITY.md, MSG-line-quote-cost). Why: a step's
    // underline under each character it covers is what shows its extent, and underlines that
    // overlap cannot share a row, so any layout that draws each nested extent in full prints the
    // sum of their widths. A complete solution would show nested extents by their ends, not in
    // full; whether that reads as clearly is open (MSG-line-quote-nested). Tested by
    // `l01_29_diagnostics::layout`.
    let mut rows: Vec<Vec<usize>> = Vec::new();
    // Each row by the first column after its last underline, its numbers and one space.
    let mut free: BinaryHeap<Reverse<(usize, usize)>> = BinaryHeap::new();
    for (k, (from, width, label)) in marks.iter().enumerate() {
        let row = match free.peek() {
            Some(&Reverse((after, row))) if after <= *from => {
                free.pop();
                row
            }
            _ => {
                rows.push(Vec::new());
                rows.len() - 1
            }
        };
        rows[row].push(k);
        free.push(Reverse((from + width + label.len() + 1, row)));
    }
    for row in &rows {
        f.write_str(margin)?;
        let mut done = 0;
        for &k in row {
            let (from, width, label) = &marks[k];
            write!(f, "{:gap$}{:^<width$}{label}", "", "", gap = from - done)?;
            done = from + width + label.len();
        }
    }
    Ok(())
}

/// The statements, elaboration and warnings of the unit `text`, the warnings moved out of the
/// elaboration and placed in the source, or the diagnostics of the first phase that rejects it.
pub(crate) fn compile(text: &str) -> Front {
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
    let refused = work::stage(Stage::Linear, None, || {
        linear_questions(text, &tokens, &stmts, &unit)
    });
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
    Ok((stmts, Arc::new(unit), warnings))
}

/// The operands of the outermost `&&` of `e`, in written order, each as `text` writes it, a
/// grouped operand with its parentheses: what the menu of a refused linear question rewrites
/// (DESIGN.md sec:diagnostics, row "Linear question outside the polynomial fragment"; the
/// menu is `presburger::Refusal::repairs`, tested by
/// `l01_38_presburger::checker::following_each_repair_of_the_menu_makes_the_program_check`).
/// An operand looser than `&&` (an `||`, an `else`, a lambda, a `for`) not written in
/// parentheses is given them, so a repair that joins it to another condition by `&&` keeps
/// its meaning. A walk with an explicit stack, O(the nodes).
fn conjuncts(text: &str, e: &ast::Expr) -> Vec<String> {
    let mut out = Vec::new();
    let mut stack = vec![e];
    while let Some(e) = stack.pop() {
        match &e.kind {
            ast::ExprKind::Binary("&&", l, r) => {
                stack.push(r);
                stack.push(l);
            }
            kind => {
                let written = &text[e.span.start..e.span.end];
                let loose = matches!(
                    kind,
                    ast::ExprKind::Binary("||", ..)
                        | ast::ExprKind::Else { .. }
                        | ast::ExprKind::Lambda { .. }
                        | ast::ExprKind::For { .. }
                );
                out.push(if loose && !grouped(written) {
                    format!("({written})")
                } else {
                    written.to_string()
                });
            }
        }
    }
    out
}

/// Every name `tokens` write, those in the holes of strings included, borrowed from the
/// tokens: the names a new top-level function must not take, since it would then be a second
/// definition of one of the program's names, and one written inside a function, a parameter
/// or a local, would hide it there. A walk with an explicit stack, O(the tokens).
fn names_written(tokens: &[lex::Token]) -> std::collections::HashSet<&str> {
    let mut out = std::collections::HashSet::new();
    let mut stack = vec![tokens];
    while let Some(tokens) = stack.pop() {
        for t in tokens {
            match &t.tok {
                lex::Tok::Name(n) => {
                    out.insert(n.as_str());
                }
                lex::Tok::Str(parts) => stack.extend(parts.iter().filter_map(|p| match p {
                    lex::Part::Hole { tokens, .. } => Some(tokens.as_slice()),
                    lex::Part::Text(_) => None,
                })),
                _ => {}
            }
        }
    }
    out
}

/// `written` with each run of white space that holds a line break made one space, so that a
/// repair prints on one line.
fn one_line(written: &str) -> String {
    let mut out = String::with_capacity(written.len());
    let mut run = String::new();
    for c in written.chars() {
        if c.is_whitespace() {
            run.push(c);
            continue;
        }
        out.push_str(if run.contains('\n') { " " } else { &run });
        run.clear();
        out.push(c);
    }
    out.push_str(if run.contains('\n') { " " } else { &run });
    out
}

/// Whether `written` is one parenthesized group: it opens with `(` whose match is its last
/// character.
fn grouped(written: &str) -> bool {
    let mut depth = 0usize;
    for (i, c) in written.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => {
                depth = depth.saturating_sub(1);
                if depth == 0 {
                    return i + 1 == written.len();
                }
            }
            _ if depth == 0 => return false,
            _ => {}
        }
    }
    false
}

/// The linear questions of the unit (step L1.38): for each function other than `main` whose
/// body the linear-relation domain states over its parameters, whether the body can hold and
/// whether it can fail. A question the solver refuses is a rejection at the function, with
/// its cause and the constraints (DESIGN.md "Diagnostics") and the menu of repairs that
/// `presburger::Refusal::repairs` builds from the cause and the function as `text` writes it;
/// a decided question rejects nothing, since a test that never holds is an unreachable arm
/// (step L1.39).
///
/// Complexity tradeoff: a function whose question the solver refuses is rejected, though the
/// program may be correct; the message names the function, its condition as written and the
/// cause. Why:
/// the solver decides only the fragment it can decide without exponential search (the
/// causes, their costs and their triggers are at `presburger::Refusal`'s raise sites:
/// Growth in `Omega::run`, Shadows in `splinters`, Disjuncts in `pick`). Tests:
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
pub fn linear_questions(
    text: &str,
    tokens: &[lex::Token],
    stmts: &[Stmt],
    unit: &Unit,
) -> Vec<ast::Error> {
    use crate::store::{preimage, presburger};
    // The names the program writes, which the split repair's new functions must not take
    // (`presburger::free_names`): read from `tokens` at the first refused question, once for
    // the unit, and the split's names once for each function name refused.
    let mut taken: Option<std::collections::HashSet<&str>> = None;
    let mut split_names: std::collections::HashMap<&str, [String; 2]> =
        std::collections::HashMap::new();
    // The functions of the unit by name and written parameter names, so each overload of a name
    // finds its own definition; overloads alike in both, which differ in types only, are matched
    // to their definitions in the order of the unit's definitions. A kernel name is the written
    // name or the written name and `@k` (`crate::elab`), and a written name holds no `@`
    // (`crate::lex::name`). O(n) in the size of the parameter lists.
    type Key<'a> = (&'a str, Vec<&'a str>);
    type Lams<'a> = Vec<(&'a [Arc<str>], &'a Shared, &'a Arc<str>)>;
    let mut defs: std::collections::HashMap<Key, Lams> = std::collections::HashMap::new();
    for d in unit.defs.iter().rev() {
        if let Term::Lam(ps, body) = &*d.term {
            let written = ps.iter().map(|k| crate::elab::written_name(k));
            (defs
                .entry((d.name.as_str(), written.collect()))
                .or_default())
            .push((ps, body, &d.kernel));
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
        let Some((ps, body, kernel)) = defs.get_mut(&key).and_then(Vec::pop) else {
            continue;
        };
        work::stage(Stage::Linear, Some(&f.name), || {
            // A caller's relation holds its callee's as one shared part (`preimage::Scoped`), and
            // is decided from the callee's answers and its own new constraints
            // (`presburger::extend`), so a chain of n tests `p{i}(x) = p{i-1}(x: x) && x > i`,
            // over one variable or several, costs O(n) in all. Complexity tradeoff: a chain
            // whose links each exclude the point found for their callee is decided whole at each
            // link, O(n²) (at `Extending::defined`). Tests `l01_38_presburger::one_scope::
            // the_questions_of_a_chain_of_tests_scale` and `..._over_two_variables_scale`.
            // COMPLEXITY.md rows LOAD-chain and LOAD-chain-share. A chain whose links define
            // auxiliary variables (`x mod 7`) costs O(n) as well: they are numbered once for the
            // scope, and each question reads the definitions its new parts reach (LOAD-chain-aux).
            // So does one whose links pass their callee any affine terms of their parameters
            // (`p{i-1}(x: x + 1)`, `p{i-1}(x: 2*x)`, `p{i-1}(y: x, z: x)`, constants): each body is
            // read once over its parameters' canonical atoms, and a call binds them to its
            // arguments (`preimage::Scoped::relation`, LOAD-chain-affine).
            // A link whose point extends a small callee beside the chain reads the chain
            // through its face, the chain projected onto the atoms its call binds
            // (`preimage::Scoped::interface`, LOAD-call-summary).
            // The question is stated over the names the user wrote: elaboration renames a binder
            // `x` to `x@k` when another binder of the unit is named `x` too (`crate::elab`), which
            // the user cannot write, so the question, its refusal and its constraints print `x`,
            // and their names do not change with the other functions of the unit. The auxiliary
            // variables of the constraints are numbered from 0 in the order the scope made them,
            // which an earlier function that made one of them first may change.
            // Rung 2 reads arithmetic as integer arithmetic, so a question is asked only of a
            // function whose parameters all take only `int`s (RUNG2-carrier): one of `f64`,
            // `rat`, `bool` or a type variable that may be `f64` or `rat` is outside the domain,
            // as a float or rational literal is. `Scoped::relation` reads every parameter as an
            // integer input, so a function with an `int` parameter beside a `f64` one asks
            // nothing, even of a body that reads only the `int`. A function the checker gave no
            // signature asks nothing.
            let all_int = (unit.int_params.get(kernel))
                .is_some_and(|ints| ints.len() == f.params.len() && ints.iter().all(|&i| i));
            if !all_int {
                return;
            }
            let inputs: Vec<Arc<str>> = f.params.iter().map(|p| p.name.as_str().into()).collect();
            if let Some(r) = scoped.relation(body, ps, &inputs, true) {
                let mut answers =
                    extending.defined_with(&r, &|n| scoped.def(n), &|g| scoped.interface(g));
                // A relation is read over canonical atoms (LOAD-chain-affine), so a refusal names
                // them; a refused question is asked again over the inputs, its bindings
                // substituted (`preimage::Scoped::written`), and its refusal, if it stays, names
                // the caller's parameters. Complexity tradeoff: that question is decided whole,
                // O(the relation) and more, where its answer came from its callee's; only a
                // refused question, which is printed whole in its note, pays it. A complete
                // solution would write the refusal's rows back through the bindings.
                if answers.holds.is_err() || answers.fails.is_err() {
                    let w = scoped.written(&r);
                    let with = |f| presburger::Formula::and(vec![w.defined(), f]);
                    answers.holds = presburger::decide(&with(w.body.clone()));
                    answers.fails =
                        presburger::decide(&with(presburger::Formula::negate(w.body.clone())));
                }
                // On one line, as the message is: a condition written over several lines has its
                // line breaks and indentation read as single spaces.
                let condition = text[f.body.span.start..f.body.span.end]
                    .split_whitespace()
                    .collect::<Vec<_>>()
                    .join(" ");
                let params = (f.params.iter())
                    .map(|p| format!("`{}`", p.name))
                    .collect::<Vec<_>>()
                    .join(", ");
                for (can, answer) in [("true", answers.holds), ("false", answers.fails)] {
                    if let Err(why) = answer {
                        let constraints = scoped.written(&r).to_string();
                        // The menu rewrites the function as written, on one line: its
                        // parameters the question reads, in written order, and the conditions
                        // of its value, the body of an equation or the value a block ends
                        // with, with the text before and after them. O(the function's text)
                        // per refused question.
                        let found: std::collections::HashSet<&str> =
                            presburger::names_in(&constraints).into_iter().collect();
                        let names: Vec<&str> = (f.params.iter().map(|p| p.name.as_str()))
                            .filter(|p| found.contains(p))
                            .collect();
                        let value = match &f.body.kind {
                            ast::ExprKind::Block(body) if !f.equation => match body.last() {
                                Some(Stmt {
                                    kind: StmtKind::Return(v),
                                    ..
                                }) if v.len() == 1 => &v[0],
                                _ => &f.body,
                            },
                            _ => &f.body,
                        };
                        let head = one_line(&text[s.span.start..value.span.start]);
                        let tail = one_line(&text[value.span.end..s.span.end]);
                        let parts: Vec<String> = (conjuncts(text, value).iter())
                            .map(|c| one_line(c))
                            .collect();
                        let parts: Vec<&str> = parts.iter().map(String::as_str).collect();
                        let what = format!("`{}`", f.name);
                        let into = split_names.entry(f.name.as_str()).or_insert_with(|| {
                            let taken = taken.get_or_insert_with(|| names_written(tokens));
                            presburger::free_names(&f.name, taken)
                        });
                        // A function's statement begins with its name (`Function = Name '('`
                        // in sec:grammar); were it not to, no split is offered rather than one
                        // that renames another word.
                        let split =
                            head.strip_prefix(f.name.as_str())
                                .map(|rest| presburger::Split {
                                    name: &f.name,
                                    rest,
                                    into: [&into[0], &into[1]],
                                });
                        let written = presburger::Written {
                            what: &what,
                            head: &head,
                            tail: &tail,
                            split,
                            conjuncts: &parts,
                            names: &names,
                        };
                        let repairs = why.repairs(&written).into_iter().map(|text| ast::Note {
                            span: f.body.span,
                            text,
                        });
                        // A cause that ends in a sentence of its own, such as a repair, keeps
                        // its full stop, and the message adds none.
                        let why = why.to_string();
                        let stop = if why.ends_with('.') { "" } else { "." };
                        out.push(ast::Error {
                            row: Some(crate::rejection::Row::NonLinearQuestion),
                            span: s.span,
                            message: format!(
                                "zedc could not decide whether the condition of `{}`, written \
                                 `{condition}`, can be {can} for whole-number values of {params}, \
                                 which it works out for every test function: {why}{stop}",
                                f.name
                            ),
                            notes: std::iter::once(ast::Note {
                                span: f.body.span,
                                text: format!("the constraints: {constraints}"),
                            })
                            .chain(repairs)
                            .collect(),
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
    let mut read = Read {
        text,
        lines,
        seen: HashMap::new(),
    };
    errors
        .into_iter()
        .zip(addresses)
        .map(|(e, address)| {
            let (line, col) = read.place(e.span.start);
            Diagnostic {
                line,
                col,
                steps: e.notes.into_iter().map(|n| read.step(n)).collect(),
                message: e.message,
                row: e.row,
                address,
            }
        })
        .collect()
}

/// The lines of `text` that diagnostics are placed on, each read once, so that placing a step
/// costs a search for its line and O(1) after it, not a decoding of the line up to it, and the
/// steps on one line share one copy of it: k steps on a line of L bytes cost O(L + k log n)
/// for n lines, not O(k·L).
struct Read<'t> {
    /// The text.
    text: &'t str,
    /// Its line starts.
    lines: &'t source::Lines,
    /// Each line read, by the byte it starts at.
    seen: HashMap<usize, Line>,
}

/// A line of the source.
struct Line {
    /// Its 1-based number.
    number: usize,
    /// Its text, without its line break.
    source: Arc<str>,
    /// For each byte of it and the end, the number of characters before it.
    chars: Vec<usize>,
}

impl Read<'_> {
    /// The line holding byte `offset`, read the first time it is asked for, and its first byte.
    fn line(&mut self, offset: usize) -> (&Line, usize) {
        let (begin, number) = self.lines.line_start(offset);
        let text = self.text;
        let line = self.seen.entry(begin).or_insert_with(|| {
            let end = text[begin..]
                .find(['\n', '\r'])
                .map_or(text.len(), |i| begin + i);
            let source = &text[begin..end];
            let mut chars = Vec::with_capacity(source.len() + 1);
            let mut count = 0;
            for b in source.bytes() {
                chars.push(count);
                // A byte that is not a continuation byte starts a character.
                count += usize::from(b & 0xC0 != 0x80);
            }
            chars.push(count);
            Line {
                number,
                source: source.into(),
                chars,
            }
        });
        (line, begin)
    }

    /// The 1-based line and column of byte `offset`, the column counted in characters.
    fn place(&mut self, offset: usize) -> (usize, usize) {
        let (line, begin) = self.line(offset);
        (line.number, line.chars[offset - begin] + 1)
    }

    /// The step a note is: its line and column, the source line, and the characters of the
    /// note's span on that line.
    fn step(&mut self, n: ast::Note) -> Step {
        let (line, begin) = self.line(n.span.start);
        let end = begin + line.source.len();
        let first = line.chars[n.span.start - begin];
        let width = line.chars[n.span.end.clamp(n.span.start, end) - begin] - first;
        Step {
            line: line.number,
            col: first + 1,
            text: n.text,
            source: Arc::clone(&line.source),
            width: width.max(1),
        }
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

/// The statements of the unit `text` and its imports ([`Imported`]), in text order; or the
/// errors of the first phase that rejects it. What [`Query::Parse`] computes.
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
