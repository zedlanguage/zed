//! Mutation testing (step L25.8): `zedc test --mutate` replaces one operator or integer
//! constant of a definition at a time, and runs the `test { }` tables (step L1.21) against
//! each such mutant.
//!
//! The replacements: a comparison by its neighbor (`<=` and `<`, `>=` and `>`, `==` and
//! `!=`, each way), `+` and `-` each way, `*` by `/` where `/` is defined on its operands (both
//! hold no `int`) and `/` by `*`, and an integer constant `n` by `n - 1` and by `n + 1`. A
//! mutant is named by its definition's source name, the position of the node in the
//! definition's kernel term, and the replacement, so the name does not change when other
//! declarations move; mutants are taken in that order (definitions by name, nodes in
//! preorder), never in the order of a hash.
//!
//! A mutant is skipped when the optimizer of today, the build stage (`stage::mix`, step
//! L1.28), gives its definition the same term as the original's: the two programs are then
//! the same program. Otherwise it is detected when a row of a table that reaches the
//! definition fails on it, and undetected when every such row passes.
//!
//! Mutants work on the original's elaborated unit: a mutant is the unit with one
//! definition's term replaced, so it costs that definition and the tables that reach it, not
//! a new parse, check or elaboration.

use std::sync::Arc;

use zed_kernel::provenance::{Position, child, with_child};
use zed_kernel::{Prim, Term, Value};

use crate::ast::{Stmt, StmtKind};
use crate::elab::{self, Cones, Mark, Unit};
use crate::lex::Span;
use crate::run::{self, Through};
use crate::source;
use crate::stage::{self, Remix};
use crate::testing;

/// What a mutant puts in place of a node, or what the node was.
#[derive(Clone, PartialEq, Debug)]
pub enum Change {
    /// A binary operator.
    Op(Prim),
    /// An integer constant.
    Int(Value),
}

impl std::fmt::Display for Change {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Change::Op(p) => f.write_str(op_text(*p)),
            Change::Int(v) => write!(f, "{v}"),
        }
    }
}

/// One mutant: the node of a definition it replaces, and the replacement.
#[derive(Clone, Debug)]
pub struct Mutant {
    /// The definition's position in the unit.
    pub def: usize,
    /// The node's position in the definition's term.
    pub at: Position,
    /// The node as written.
    pub was: Change,
    /// What replaces it.
    pub to: Change,
    /// Where the operator or constant is in the source.
    pub offset: usize,
}

/// What running the tables against a mutant found.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Verdict {
    /// A row of a table that reaches the definition fails.
    Detected,
    /// Every row that reaches the definition passes, or none reaches it: the reason.
    Undetected(&'static str),
    /// The build stage gives the mutant's definition the original's term.
    Skipped,
    /// No row that ran fails, and a row that reaches the definition was not run because the
    /// form of the mutant's row does not show that it ends.
    NotRun,
}

/// The source text of operator `p`.
fn op_text(p: Prim) -> &'static str {
    match p {
        Prim::Eq => "==",
        Prim::Ne => "!=",
        Prim::Lt => "<",
        Prim::Le => "<=",
        Prim::Gt => ">",
        Prim::Ge => ">=",
        Prim::Add => "+",
        Prim::Sub => "-",
        Prim::Mul => "*",
        Prim::Div => "/",
        _ => unreachable!("only the operators `elab::mutable` admits are marked"),
    }
}

/// The operators that replace `p`; `quotient` says whether `/` is defined where `p` is `*`.
fn neighbors(p: Prim, quotient: bool) -> &'static [Prim] {
    match p {
        Prim::Lt => &[Prim::Le],
        Prim::Le => &[Prim::Lt],
        Prim::Gt => &[Prim::Ge],
        Prim::Ge => &[Prim::Gt],
        Prim::Eq => &[Prim::Ne],
        Prim::Ne => &[Prim::Eq],
        Prim::Add => &[Prim::Sub],
        Prim::Sub => &[Prim::Add],
        Prim::Mul if quotient => &[Prim::Div],
        Prim::Mul => &[],
        Prim::Div => &[Prim::Mul],
        _ => unreachable!("only the operators `elab::mutable` admits are marked"),
    }
}

/// The offset of the operator in the text between its operands, `gap`: the first byte that
/// is not white space, a `//` comment or a parenthesis.
fn operator_at(text: &str, gap: Span) -> usize {
    let bytes = text.as_bytes();
    let mut i = gap.start;
    while i < gap.end {
        match bytes[i] {
            b' ' | b'\t' | b'\r' | b'\n' | b'(' | b')' => i += 1,
            b'/' if bytes.get(i + 1) == Some(&b'/') => {
                while i < gap.end && bytes[i] != b'\n' {
                    i += 1;
                }
            }
            _ => return i,
        }
    }
    gap.start
}

/// The mutants of `unit`, the elaboration of `stmts`, whose text is `text`: definitions by
/// source name, then nodes in preorder, then replacements in the order [`neighbors`] gives
/// (`n - 1` before `n + 1`). Finding them elaborates `stmts` once more, with marks
/// ([`elab::elaborate_marked`]), and reads each node of each definition once; no mutant's
/// term is built.
pub fn mutants(text: &str, stmts: &[Stmt], unit: &Unit) -> Result<Vec<Mutant>, String> {
    let res = crate::resolve::resolve(stmts)
        .map_err(|_| "the unit, which compiled, does not resolve again".to_string())?;
    let (marked, marks) = elab::elaborate_marked(stmts, &res)
        .map_err(|_| "the unit, which compiled, does not elaborate again with marks".to_string())?;
    if marked.defs.len() != unit.defs.len() {
        return Err(format!(
            "the marked elaboration has {} definitions and the unit {}",
            marked.defs.len(),
            unit.defs.len()
        ));
    }
    let mut order: Vec<usize> = (0..unit.defs.len()).collect();
    order.sort_by(|&a, &b| unit.defs[a].name.cmp(&unit.defs[b].name).then(a.cmp(&b)));
    let mut out = Vec::new();
    for def in order {
        let (m, u) = (&marked.defs[def], &unit.defs[def]);
        if m.name != u.name {
            return Err(format!(
                "definition {def} is `{}` in the marked elaboration and `{}` in the unit",
                m.name, u.name
            ));
        }
        sites(text, def, &m.term, &u.term, &marks, &mut out)?;
    }
    Ok(out)
}

/// Adds the mutants of definition `def` to `out`, walking its marked term `m` and its term `u`
/// together in preorder, with an explicit stack.
fn sites(
    text: &str,
    def: usize,
    m: &Term,
    u: &Term,
    marks: &[Mark],
    out: &mut Vec<Mutant>,
) -> Result<(), String> {
    let mut stack = vec![(m, u, Position::root())];
    while let Some((m, u, at)) = stack.pop() {
        let differs = |what: &str| {
            Err(format!(
                "definition {def}'s marked elaboration differs from its elaboration at {at}: {what}"
            ))
        };
        if let Some(k) = elab::mark_of(m) {
            let Some(mark) = marks.get(k) else {
                return differs("a mark has no entry");
            };
            match (m, u) {
                (Term::Prim(p, ms), Term::Prim(q, us)) if p == q && us.len() == 2 => {
                    let offset = operator_at(text, mark.span);
                    for &to in neighbors(*p, mark.quotient) {
                        out.push(Mutant {
                            def,
                            at: at.clone(),
                            was: Change::Op(*p),
                            to: Change::Op(to),
                            offset,
                        });
                    }
                    stack.push((&ms[1], &us[1], at.child(1)));
                    stack.push((&ms[0], &us[0], at.child(0)));
                }
                (Term::Prim(Prim::Neg, ms), Term::Lit(v)) if matches!(&ms[0], Term::Lit(w) if w == v) =>
                {
                    let n = v.as_bigint().expect("a marked constant is an integer");
                    for to in [&n - 1, &n + 1] {
                        out.push(Mutant {
                            def,
                            at: at.clone(),
                            was: Change::Int(v.clone()),
                            to: Change::Int(Value::int(to)),
                            offset: mark.span.start,
                        });
                    }
                }
                _ => return differs("a marked node has another shape"),
            }
            continue;
        }
        if std::mem::discriminant(m) != std::mem::discriminant(u) {
            return differs("the nodes are of different kinds");
        }
        let mut kids = Vec::new();
        let mut i = 0;
        while let Some(mc) = child(m, i) {
            let Some(uc) = child(u, i) else {
                return differs("the marked node has more children");
            };
            kids.push((mc, uc, at.child(i)));
            i += 1;
        }
        if child(u, i).is_some() {
            return differs("the marked node has fewer children");
        }
        stack.extend(kids.into_iter().rev());
    }
    Ok(())
}

/// `term` with the node at `at` replaced as `to` says. It copies the nodes on the path to
/// `at`, and shares or copies the rest as [`with_child`] does.
pub fn apply(term: &Term, at: &Position, to: &Change) -> Term {
    let path = at.path();
    let mut nodes = Vec::with_capacity(path.len() + 1);
    nodes.push(term);
    for &i in &path {
        let up = nodes.last().expect("the root is pushed");
        nodes.push(child(up, i).expect("a mutant's position is in its definition"));
    }
    let mut out = match (nodes.pop().expect("the root is pushed"), to) {
        (Term::Prim(_, args), Change::Op(p)) => Term::Prim(*p, args.clone()),
        (Term::Lit(_), Change::Int(v)) => Term::Lit(v.clone()),
        _ => unreachable!("a mutant replaces an operator by one, a constant by one"),
    };
    for (up, &i) in nodes.into_iter().zip(&path).rev() {
        out = with_child(up, i, out).expect("child `i` exists");
    }
    out
}

/// Each mutant of the unit `unit`, elaborated from `stmts`, with its verdict, in the order of
/// [`mutants`]. Each row's closed term is run by `map`. The caller has run the tables against
/// the original, and they pass.
pub fn run(
    text: &str,
    stmts: &[Stmt],
    unit: &Unit,
    map: &Through<'_>,
) -> Result<Vec<(Mutant, Verdict)>, String> {
    let mutants = mutants(text, stmts, unit)?;
    let cones = Cones::new(unit);
    let has_main = stmts
        .iter()
        .any(|s| matches!(&s.kind, StmtKind::Function(f) if f.name == "main"));
    let program = if has_main {
        run::program(stmts, unit.clone()).ok()
    } else {
        None
    };
    let main = unit.defs.iter().find(|d| d.name == "main");
    // The rows that reach each definition, in written order: an index built once from each
    // row's cone, so a mutant finds its rows by its definition.
    let mut rows: Vec<Vec<usize>> = vec![Vec::new(); unit.defs.len()];
    for (j, t) in unit.tests.iter().enumerate() {
        let reach = match (t.function.as_str(), main, &program) {
            ("main", Some(main), Some(_)) => {
                let main = Term::Var(main.kernel.clone());
                let mut roots = vec![&main, &t.want];
                roots.extend(&t.args);
                cones.reach(&roots)
            }
            ("main", _, _) => continue,
            _ => cones.reach(&[&t.check]),
        };
        for i in reach {
            rows[i].push(j);
        }
    }
    let (_, mut remix) = Remix::new(unit);
    let mut built: Vec<Option<Term>> = vec![None; unit.defs.len()];
    let mut out = Vec::with_capacity(mutants.len());
    for mutant in mutants {
        let def = mutant.def;
        let original = &unit.defs[def].term;
        if built[def].is_none() {
            built[def] = Some(remix.mix(original));
        }
        let term = Arc::new(apply(original, &mutant.at, &mutant.to));
        let verdict = if built[def].as_ref() == Some(&remix.mix(&term)) {
            Verdict::Skipped
        } else if rows[def].is_empty() {
            Verdict::Undetected("no table reaches the definition")
        } else {
            let swap = Some((def, &term));
            let mut verdict = Verdict::Undetected("every row that reaches it passes");
            for &j in &rows[def] {
                let t = &unit.tests[j];
                let closed = match (t.function.as_str(), main) {
                    ("main", Some(main)) => {
                        let main = Term::Var(main.kernel.clone());
                        let mut roots: Vec<Term> = vec![cones.close_with(main, swap)];
                        roots.push(cones.close_with(t.want.clone(), swap));
                        roots.extend(t.args.iter().map(|a| cones.close_with(a.clone(), swap)));
                        roots
                    }
                    _ => vec![cones.close_with(t.check.clone(), swap)],
                };
                // Complexity tradeoff: a row of a mutant runs only when its form shows that
                // it ends (`stage::ends`, docs/thresholds.md, replacement 6). Why: a
                // mutant may not end where the original does (`n - 1` replaced by `n + 1`
                // in a recursive call), whether it ends is undecidable, and a step count would
                // switch behavior at a size. What is given up: rows through recursion, `fix`
                // or `gen` are not run against mutants; such a mutant is reported as not
                // run, never as detected or undetected. Trigger: those forms in the row's
                // closed term. Tests: `l25_08_mutate::examples::a_mutant_of_a_recursive_function_is_not_run`.
                if !closed.iter().all(stage::ends) {
                    verdict = Verdict::NotRun;
                    continue;
                }
                let failed = match (t.function.as_str(), &program) {
                    ("main", Some(p)) => testing::wave(&cones, swap, p, t, map).is_err(),
                    _ => testing::row(&cones, swap, t, map).is_err(),
                };
                if failed {
                    verdict = Verdict::Detected;
                    break;
                }
            }
            verdict
        };
        out.push((mutant, verdict));
    }
    Ok(out)
}

/// The report of a mutant whose verdict is not `Detected`: `line:col: verdict: …`, with
/// `name` the definition's source name.
pub fn describe(text: &str, name: &str, m: &Mutant, v: &Verdict) -> Option<String> {
    let (line, col) = source::line_col(text.as_bytes(), m.offset);
    let what = format!("`{}` replaced by `{}` in `{name}` at {}", m.was, m.to, m.at);
    let says = match v {
        Verdict::Detected => return None,
        Verdict::Undetected(why) => format!("undetected: {what}: {why}"),
        Verdict::Skipped => {
            format!("skipped: {what}: the build stage gives the definition the original's term")
        }
        Verdict::NotRun => format!(
            "not run: {what}: no row that ran fails, and the form of a row that reaches it \
             does not show that it ends"
        ),
    };
    Some(format!("{line}:{col}: {says}"))
}
