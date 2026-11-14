//! Mutation testing (step L25.8): `zedc test --mutate` replaces one operator or integer
//! constant of a definition at a time, and runs the `test { }` tables (step L1.21) against
//! each such mutant.
//!
//! The replacements: a comparison by its neighbor (`<=` and `<`, `>=` and `>`, `==` and
//! `!=`, each way), `+` and `-` each way, `*` by `/` where `/` is defined (the checker types
//! the product with no `int`) and `/` by `*`, and an integer literal `n` by `n - 1` and by
//! `n + 1` at the carrier it adopted (`int`, `rat`, `f64` or `f32`), in every arm where a
//! generic literal is built once per carrier (L1.26a). A mutant is named by its definition's
//! source name, the position of the node in the definition's kernel term, and the
//! replacement, so the name does not change when other declarations move; mutants are taken
//! in that order (definitions by name, nodes in preorder), never in the order of a hash.
//!
//! A mutant is skipped when the optimizer of today, the build stage (`stage::mix`, step
//! L1.28), gives its definition the same term as the original's: the two programs are then
//! the same program. Otherwise it is detected when a row of a table that reaches the
//! definition fails on it, and undetected when every such row passes.
//!
//! Mutants work on the original's elaborated unit: a mutant is the unit with one
//! definition's term replaced, so it costs that definition and the tables that reach it, not
//! a new parse, check or elaboration.

use std::collections::HashMap;
use std::mem;
use std::ops::Range;
use std::sync::Arc;

use zed_kernel::num::TooLarge;
use zed_kernel::provenance::{Position, child, child_mut};
use zed_kernel::{Prim, Rat, Shared, Term, Value};

use crate::ast::{Stmt, StmtKind};
use crate::elab::mark::{self, Mark};
use crate::elab::{self, Cones, Unit};
use crate::lex::Span;
use crate::rows;
use crate::run::{self, Through};
use crate::source;
use crate::stage::{self, Remix};

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
            Change::Op(p) => f.write_str(p.written()),
            Change::Int(v) => write!(f, "{v}"),
        }
    }
}

/// One mutant: the node of a definition it replaces, and the replacement.
#[derive(Clone, Debug)]
pub struct Mutant {
    /// The definition's position in the unit.
    pub def: usize,
    /// The node's position in the definition's term: of an operator, the first in preorder of
    /// its nodes; of a constant, the last, its own value's ([`Self::also`]).
    pub at: Position,
    /// The other nodes of the same written operator or constant, which the mutant replaces too,
    /// each with what replaces it there: one in each arm of an operation on generic literals
    /// built once per carrier, and one in each arm of a generic literal taking its carrier
    /// (L1.26a); none elsewhere. An operator's arms take [`Self::to`]; a constant's arm takes
    /// its neighbor at that arm's carrier, as `2.0` is replaced by `1.0` where `2` is by `1`.
    pub also: Vec<(Position, Change)>,
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
        _ => unreachable!("only the operators `elab::mark::mutable` admits are marked"),
    }
}

/// The neighbors `n - 1` and `n + 1` of the integer literal `n`, at the carrier it adopted:
/// `int`, `rat`, `f64` or `f32`; an error when the system refuses the memory to build one.
fn beside(n: &Value) -> Result<[Value; 2], String> {
    let exact = |r: &Rat| -> Result<[Rat; 2], String> {
        let one = Rat::int(1.into());
        let refused = |e: TooLarge| {
            format!(
                "Number too large for memory: a neighbor of an integer literal needs {}",
                e.number()
            )
        };
        Ok([r.sub(&one).map_err(refused)?, r.add(&one).map_err(refused)?])
    };
    match n {
        Value::Rat(r) => Ok(exact(r)?.map(Value::rat)),
        Value::Float(x) => Ok([Value::float(x.get() - 1.0), Value::float(x.get() + 1.0)]),
        Value::Float32(x) => Ok([Value::float32(x.get() - 1.0), Value::float32(x.get() + 1.0)]),
        _ => {
            let n = n
                .as_integer()
                .expect("an integer literal is an int, a rat, an f64 or an f32");
            Ok(exact(&n)?.map(Value::integer))
        }
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
/// source name, then nodes in preorder, then replacements in the order `neighbors` gives
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
    // The mutants made at each mark, by its index, so a mark met again adds its node to them.
    let mut first: HashMap<usize, Range<usize>> = HashMap::new();
    let mut stack = vec![(m, u, Position::root())];
    while let Some((m, u, at)) = stack.pop() {
        let differs = |what: &str| {
            Err(format!(
                "definition {def}'s marked elaboration differs from its elaboration at {at}: {what}"
            ))
        };
        if let Some(k) = mark::mark_of(m) {
            let Some(mark) = marks.get(k) else {
                return differs("a mark has no entry");
            };
            let (was, offset) = match (m, u) {
                (Term::Prim(p, ms), Term::Prim(q, us)) if p == q && us.len() == 2 => {
                    stack.push((&ms[1], &us[1], at.child(1)));
                    stack.push((&ms[0], &us[0], at.child(0)));
                    (Change::Op(*p), operator_at(text, mark.span))
                }
                (Term::Prim(Prim::Neg, ms), Term::Lit(v)) if matches!(&ms[0], Term::Lit(w) if w == v) => {
                    (Change::Int(v.clone()), mark.span.start)
                }
                _ => return differs("a marked node has another shape"),
            };
            // One written operator is a node in each arm of an operation on generic literals
            // built once per carrier (`elab::walk::per_carrier`), all with its mark: its mutants
            // are made at the first and replace it in every arm, as a mutant of the operation
            // written once replaces it at every carrier. One written constant is likewise a
            // node in each arm of a generic literal taking its carrier (`elab::walk::marked_as`),
            // of that arm's value: each mutant replaces it in every arm by its neighbor there,
            // `n - 1` or `n + 1` at the arm's carrier, and is named by the last node, the
            // literal's own value, which the source writes.
            if let Some(made) = first.get(&k) {
                let made = &mut out[made.clone()];
                match &was {
                    Change::Op(_) => {
                        if made.iter().any(|x| x.was != was) {
                            return differs("one mark is on nodes of two kinds");
                        }
                        for x in made {
                            x.also.push((at.clone(), x.to.clone()));
                        }
                    }
                    Change::Int(v) => {
                        if made.iter().any(|x| !matches!(x.was, Change::Int(_))) {
                            return differs("one mark is on nodes of two kinds");
                        }
                        for (x, to) in made.iter_mut().zip(beside(v)?) {
                            let at = mem::replace(&mut x.at, at.clone());
                            let to = mem::replace(&mut x.to, Change::Int(to));
                            x.also.push((at, to));
                            x.was = was.clone();
                        }
                    }
                }
                continue;
            }
            let to: Vec<Change> = match &was {
                Change::Op(p) => (neighbors(*p, mark.quotient).iter())
                    .map(|&q| Change::Op(q))
                    .collect(),
                Change::Int(v) => beside(v)?.into_iter().map(Change::Int).collect(),
            };
            let start = out.len();
            out.extend(to.into_iter().map(|to| Mutant {
                def,
                at: at.clone(),
                also: Vec::new(),
                was: was.clone(),
                to,
                offset,
            }));
            first.insert(k, start..out.len());
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

/// `term` with each node of `at` replaced as its change says: one copy of `term`, O(its size, the
/// order of the remix that follows), then each node changed in place. The copy shares what
/// `term` holds behind an `Arc` until the path to a node reaches it ([`child_mut`]). `at` holds
/// one node, or one per carrier of an operation on generic literals or of a generic literal
/// ([`Mutant::also`]), each with what replaces it.
pub fn apply<'p>(term: &Term, at: impl IntoIterator<Item = (&'p Position, &'p Change)>) -> Term {
    // Complexity tradeoff (COMPLEXITY.md F58): a rebuild along the path by `with_child`, which
    // copies each inline child list, costs O(size × depth), cubic over the mutants of one
    // chain; one copy of the term and the nodes changed in place through `child_mut` costs
    // O(size + k × depth) for k ≤ 6 nodes, the order of the remix that follows. Precondition:
    // each position lies in `term`.
    let mut out = term.clone();
    for (at, to) in at {
        let mut node = &mut out;
        for i in at.path() {
            node = child_mut(node, i).expect("a mutant's position is in its definition");
        }
        match (node, to) {
            (Term::Prim(p, _), Change::Op(q)) => *p = *q,
            (Term::Lit(v), Change::Int(w)) => *v = w.clone(),
            _ => unreachable!("a mutant replaces an operator by one, a constant by one"),
        }
    }
    out
}

/// The program of the original unit `unit`, elaborated from `stmts`, sharing `unit`: none when
/// the unit has no `main` or `run::program` refuses it, and its `main` rows then do not run.
fn original(stmts: &[Stmt], unit: &Arc<Unit>) -> Option<run::Program> {
    let has_main = stmts
        .iter()
        .any(|s| matches!(&s.bare().kind, StmtKind::Function(f) if f.name == "main"));
    if has_main {
        run::program(stmts, Arc::clone(unit)).ok()
    } else {
        None
    }
}

/// Each mutant of the unit `unit`, elaborated from `stmts`, with its verdict, in the order of
/// [`mutants`]. Each row's closed term is run by `map`. The caller has run the tables against
/// the original, and they pass. The original's program shares `unit`.
pub fn run(
    text: &str,
    stmts: &[Stmt],
    unit: &Arc<Unit>,
    map: &Through<'_>,
) -> Result<Vec<(Mutant, Verdict)>, String> {
    let mutants = mutants(text, stmts, unit)?;
    let cones = Cones::new(unit);
    let program = original(stmts, unit);
    let main = unit.defs.iter().find(|d| d.name == "main");
    // The rows that reach each definition, in written order: an index built once from each
    // row's cone, so a mutant finds its rows by its definition.
    // A row `zedc test` does not run, of a function only branches the build does not take
    // reach (plan row TEST-staged), detects no mutant: it is in no definition's list.
    let untaken = (program.as_ref())
        .map(|p| p.stage().1.untaken)
        .unwrap_or_default();
    let mut rows: Vec<Vec<usize>> = vec![Vec::new(); unit.defs.len()];
    for (j, t) in unit.tests.iter().enumerate() {
        if untaken.contains(&t.kernel) {
            continue;
        }
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
        let at = std::iter::once((&mutant.at, &mutant.to))
            .chain(mutant.also.iter().map(|(at, to)| (at, to)));
        let term = Shared::new(apply(original, at));
        let verdict = if built[def].as_ref() == Some(&remix.mix(&term)) {
            Verdict::Skipped
        } else if rows[def].is_empty() && untaken.contains(&unit.defs[def].kernel) {
            Verdict::Undetected(
                "the build takes no branch that reaches the definition, so no row that reaches it runs",
            )
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
                // Complexity tradeoff: a row of a mutant runs only when the form of its
                // closed term shows that it ends (`stage::ends`, docs/thresholds.md,
                // replacement 6). What is given up: a row whose form does not show it, though
                // it may end, is not run against the mutant, and a mutant with such a row
                // and no failing row is reported "not run", never detected or undetected.
                // Why: a mutant may not end where the original does (`if x > 0 { w(w) }`
                // with `0` replaced by `-1` never ends), whether it ends is undecidable, and
                // a step count would switch behavior at a size. Trigger: a call through a
                // parameter or a pattern variable in the row's closed term, as in `w(w)` or
                // `twice(f: inc, x)` (L1 has no recursion; `fix` and `gen` would also
                // trigger it). Test:
                // `l25_08_mutate::examples::a_mutant_whose_row_may_not_end_is_not_run`.
                // COMPLEXITY.md row F58. A complete solution cannot exist; a stronger sound
                // one would add a termination proof by decreasing measures (size-change
                // termination, PSPACE-complete in the call graph), as `stage::ends` says.
                // Naive version: every row run, which need not end; used: the form check of
                // `stage::ends`, in time near the number of distinct parts of the term.
                if !closed.iter().all(stage::ends) {
                    verdict = Verdict::NotRun;
                    continue;
                }
                let failed = match (t.function.as_str(), &program) {
                    ("main", Some(p)) => rows::wave(&cones, swap, p, t, map).is_err(),
                    _ => rows::row(&cones, swap, t, map).is_err(),
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

/// The text a report gives for `c`. A wide number's digits are written only after the system
/// gives the memory to build and write them ([`Rat::text_room`]); when it refuses, the report
/// names the number by that memory instead of an abort.
fn reported(c: &Change) -> String {
    match c {
        Change::Int(Value::Big(r) | Value::Rat(r)) => match r.text_room() {
            Ok(()) => c.to_string(),
            Err(e) => format!("an integer of {}", e.amount("")),
        },
        _ => c.to_string(),
    }
}

/// The report of a mutant whose verdict is not `Detected`: `line:col: verdict: …`, with
/// `name` the definition's source name.
pub fn describe(text: &str, name: &str, m: &Mutant, v: &Verdict) -> Option<String> {
    let (line, col) = source::line_col(text.as_bytes(), m.offset);
    let (was, to) = (reported(&m.was), reported(&m.to));
    let what = format!("`{was}` replaced by `{to}` in `{name}` at {}", m.at);
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

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::original;
    use crate::query::Db;

    #[test]
    fn the_original_program_of_a_mutation_run_shares_the_unit_of_the_front_end() {
        let front = Db::new().front("main(m: MainArgs) {\n  m.stdout <- \"x\";\n}\n");
        let Ok((stmts, unit, _)) = &*front else {
            panic!("the unit is accepted")
        };
        let p = original(stmts, unit).expect("`main`'s ports are `Lines`");
        assert!(Arc::ptr_eq(&p.unit, unit));
    }
}
