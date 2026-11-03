//! The test runner (step L1.21, DESIGN.md sec:lexical, the test table row): `zedc test` runs
//! every `test { }` table of a unit and checks its `// ✗` marks.
//!
//! A row of a function's table passes when the call equals the expected value under `==`. A
//! row of `main`'s table is a wave: the key gives the input ports, a `Lines` port as the
//! `String` of its bytes and a `Files` port as a function from path to contents, and the
//! value gives the `String` each output port writes. A unit that is rejected passes when
//! every diagnostic is on a line marked ✗ and every marked line has one, of the row of the
//! rejection table its comment names if it names one (`// ✗ Missing argument: …`); its tables
//! do not run. A wave that aborts fails its row: no form expects an abort at L1.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::io::Write;
use std::sync::Arc;

use zed_kernel::{Evaluator, Lookup, Term, Value, World};

use crate::ast::StmtKind;
use crate::elab::{Cones, Test};
use crate::query::{self, Db, Query};
use crate::rejection::Row;
use crate::run::{self, PortKind, Program, Through};
use crate::{fence, interp, source};

/// One check of a unit: a row of a table, a marked line, or a diagnostic on an unmarked line.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Outcome {
    /// Its line, counted from 1.
    pub line: usize,
    /// Its column, counted from 1.
    pub col: usize,
    /// Why it fails; `None` when it passes.
    pub failure: Option<String>,
}

/// The checks of the unit `text`, in source order.
pub fn test(text: &str) -> Vec<Outcome> {
    test_in(&mut Db::new(), text)
}

/// The checks of the unit `text`, in source order, reusing what `db` holds (step L1.30).
pub fn test_in(db: &mut Db, text: &str) -> Vec<Outcome> {
    checks(db, text, &run::direct)
}

/// The checks of the unit `text`, each row's closed term run by `map` (steps L1.33, L1.34): a
/// way to run the tables through another form of the program. Nothing is cached, since the
/// outcomes depend on `map`.
pub fn test_through(text: &str, map: &Through<'_>) -> Vec<Outcome> {
    checks(&mut Db::new(), text, map)
}

fn checks(db: &mut Db, text: &str, map: &Through<'_>) -> Vec<Outcome> {
    let marked = fence::marks(text).lines;
    let mut out = Vec::new();
    match &*db.front(text) {
        Err(diagnostics) => {
            // The diagnostics on each line, and the marked lines, each found in a map.
            let mut on: BTreeMap<usize, Vec<&run::Diagnostic>> = BTreeMap::new();
            for d in diagnostics {
                on.entry(d.line).or_default().push(d);
            }
            let is_marked: BTreeSet<usize> = marked.iter().copied().collect();
            let source: Vec<&str> = text.split('\n').collect();
            for &line in &marked {
                let ds = on.get(&line).map_or(&[][..], Vec::as_slice);
                let named = source[line - 1]
                    .split_once('✗')
                    .and_then(|(_, comment)| Row::named_by(comment));
                out.push(Outcome {
                    line,
                    col: ds.first().map_or(1, |d| d.col),
                    failure: mark_failure(ds, named),
                });
            }
            for d in diagnostics.iter().filter(|d| !is_marked.contains(&d.line)) {
                out.push(Outcome {
                    line: d.line,
                    col: d.col,
                    // The message and its derivation (DESIGN.md "Diagnostics"), after the place
                    // the outcome already gives.
                    failure: Some(
                        d.to_string()
                            .split_once(": ")
                            .expect("`line:col: `")
                            .1
                            .into(),
                    ),
                });
            }
        }
        Ok((stmts, unit)) => {
            let lines = source::Lines::new(text.as_bytes());
            let cones = Cones::new(unit);
            for &line in &marked {
                out.push(Outcome {
                    line,
                    col: 1,
                    failure: Some("the line is marked ✗ and the unit is accepted".into()),
                });
            }
            let main = stmts
                .iter()
                .find(|s| matches!(&s.kind, StmtKind::Function(f) if f.name == "main"));
            let mut program = None;
            if let Some(main) = main {
                match run::program(stmts, unit.clone()) {
                    Ok(p) => program = Some(p),
                    Err(why) => {
                        let (line, col) = lines.line_col(text.as_bytes(), main.span.start);
                        out.push(Outcome {
                            line,
                            col,
                            failure: Some(why),
                        });
                    }
                }
            }
            let main_def = unit.defs.iter().find(|d| d.name == "main");
            for t in unit.tests.iter() {
                let (line, col) = lines.line_col(text.as_bytes(), t.span.start);
                let case = &text[t.span.start..t.span.end];
                let failure = match (&program, t.function.as_str()) {
                    (Some(p), "main") => {
                        let main =
                            Term::Var(main_def.expect("`main` was elaborated").kernel.clone());
                        let mut roots = vec![&main, &t.want];
                        roots.extend(&t.args);
                        let ports = format!("{:?} {:?}", p.inputs(), p.outputs());
                        let k =
                            query::key("wave", &[&query::cone(&cones, &roots), ports.as_bytes()]);
                        db.row(Query::Wave, k, || wave(&cones, p, t, map)).err()
                    }
                    (None, "main") => continue,
                    _ => {
                        let k = query::key("row", &[&query::cone(&cones, &[&t.check])]);
                        db.row(Query::Row, k, || row(&cones, t, map)).err()
                    }
                };
                out.push(Outcome {
                    line,
                    col,
                    failure: failure.map(|why| format!("`{case}` of `{}`: {why}", t.function)),
                });
            }
        }
    }
    out.sort_by_key(|o| (o.line, o.col));
    out
}

/// Why a line marked ✗ fails, given its diagnostics `ds` and the row its comment names: it
/// has no diagnostic, or it names a row and no diagnostic on it is a case of that row. A mark
/// that names no row accepts any diagnostic.
fn mark_failure(ds: &[&run::Diagnostic], named: Option<Row>) -> Option<String> {
    let Some(first) = ds.first() else {
        return Some("the line is marked ✗ and has no diagnostic".into());
    };
    let want = named?;
    if ds.iter().any(|d| d.row == Some(want)) {
        return None;
    }
    Some(match first.row {
        Some(got) => format!(
            "the mark names the row \"{}\", and the diagnostic is in the row \"{}\": {}",
            want.name(),
            got.name(),
            first.message
        ),
        None => format!(
            "the mark names the row \"{}\", and the diagnostic is in no row of the rejection \
             table: {}",
            want.name(),
            first.message
        ),
    })
}

/// The value of `term` under the definitions it reaches and the prelude.
fn value(cones: &Cones<'_>, term: &Term, map: &Through<'_>) -> Result<Value, String> {
    map(
        &interp::prelude(cones.close(term.clone())),
        &mut Evaluator::new(World::new()),
    )
}

/// Checks a row of a function's table.
fn row(cones: &Cones<'_>, t: &Test, map: &Through<'_>) -> Result<(), String> {
    match value(cones, &t.check, map)? {
        Value::Bool(true) => Ok(()),
        _ => {
            let Term::Prim(_, sides) = &t.check else {
                unreachable!("a check is `call == want`")
            };
            Err(format!("the result is {}", value(cones, &sides[0], map)?))
        }
    }
}

/// Checks a row of `main`'s table: runs the wave its key gives, and compares the writes.
fn wave(cones: &Cones<'_>, program: &Program, t: &Test, map: &Through<'_>) -> Result<(), String> {
    let mut lines = BTreeMap::new();
    let mut files: BTreeMap<&str, Arc<dyn Lookup>> = BTreeMap::new();
    for ((name, kind), arg) in program.inputs().iter().zip(&t.args) {
        match kind {
            PortKind::Lines => match value(cones, arg, map)? {
                Value::Str(s) => {
                    lines.insert(name.clone(), s.as_bytes().to_vec());
                }
                v => {
                    return Err(format!(
                        "the `Lines` port `{name}` is given as a String, not {v}"
                    ));
                }
            },
            PortKind::Files => {
                files.insert(
                    name,
                    Arc::new(Given(interp::prelude(cones.close(arg.clone())))),
                );
            }
        }
    }
    let wave = program.run_through(&lines, |name| files[name].clone(), map)?;
    let outputs = program.outputs();
    let wants = match (outputs.len(), value(cones, &t.want, map)?) {
        (1, v) => vec![v],
        (n, Value::Tuple(xs)) if xs.len() == n => xs.into_vec(),
        (n, v) => {
            return Err(format!(
                "the expected value is a String for each of the {n} output ports, not {v}"
            ));
        }
    };
    // The first write to each port.
    let mut written: HashMap<&str, &[u8]> = HashMap::new();
    for (p, b) in &wave.writes {
        written.entry(&**p).or_insert(&b[..]);
    }
    for (name, want) in outputs.iter().zip(wants) {
        let Value::Str(want) = want else {
            return Err(format!(
                "the expected value of port `{name}` is a String, not {want}"
            ));
        };
        let got = written.get(&**name).copied().unwrap_or(&[]);
        if got != want.as_bytes() {
            let got = Value::str(&String::from_utf8_lossy(got));
            return Err(format!("port `{name}` writes {got}"));
        }
    }
    Ok(())
}

/// A `Files` port a test gives as a function from path to contents.
#[derive(Debug)]
struct Given(Term);

impl Lookup for Given {
    fn get(&self, key: &Value) -> Result<Value, String> {
        let read = Term::App(Arc::new(self.0.clone()), vec![Term::Lit(key.clone())]);
        Evaluator::new(World::new())
            .run(&read)
            .map_err(|e| e.to_string())
    }
}

/// `zedc test <file> …`, with `args` the words after `test`: writes each failing check as
/// `file:line:col: why`, then the counts: checks passed and failed, and the rejection units
/// run, those with a line marked ✗. A file with no table row and no ✗ mark fails, so a run
/// that finds no tests fails. Returns the exit status: 0 when every check passes, 1 when
/// one fails (a unit that does not compile, a row that fails or aborts, a marked line), 2 for
/// a usage error or a file that cannot be read.
pub fn command(args: &[String], stdout: &mut dyn Write, stderr: &mut dyn Write) -> u8 {
    if args.is_empty() {
        let _ = writeln!(stderr, "usage: zedc test <file> …");
        return 2;
    }
    let (mut passed, mut failed, mut rejection) = (0, 0, 0);
    let mut db = Db::new();
    for file in args {
        let text = match std::fs::read(file) {
            Ok(bytes) => source::load(&bytes).map_err(|e| e.to_string()),
            Err(e) => {
                let _ = writeln!(stderr, "{file}: {e}");
                return 2;
            }
        };
        let text = match text {
            Ok(text) => text,
            Err(why) => {
                let _ = writeln!(stdout, "{file}: {why}");
                failed += 1;
                continue;
            }
        };
        if !fence::marks(&text).lines.is_empty() {
            rejection += 1;
        }
        let outcomes = test_in(&mut db, &text);
        if outcomes.is_empty() {
            let _ = writeln!(
                stdout,
                "{file}: no test: the unit has no table row and no ✗ mark"
            );
            failed += 1;
        }
        for o in outcomes {
            match o.failure {
                None => passed += 1,
                Some(why) => {
                    let _ = writeln!(stdout, "{file}:{}:{}: {why}", o.line, o.col);
                    failed += 1;
                }
            }
        }
    }
    let units = if rejection == 1 { "unit" } else { "units" };
    let _ = writeln!(
        stdout,
        "{passed} passed, {failed} failed, {rejection} rejection {units}"
    );
    u8::from(failed > 0)
}
