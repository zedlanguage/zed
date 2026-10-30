//! The test runner (step L1.21, DESIGN.md sec:lexical, the test table row): `zedc test` runs
//! every `test { }` table of a unit and checks its `// ✗` marks.
//!
//! A row of a function's table passes when the call equals the expected value under `==`. A
//! row of `main`'s table is a wave: the key gives the input ports, a `Lines` port as the
//! `String` of its bytes and a `Files` port as a function from path to contents, and the
//! value gives the `String` each output port writes. A unit that is rejected passes when
//! every diagnostic is on a line marked ✗ and every marked line has one; its tables do not
//! run. A wave that aborts fails its row: no form expects an abort at L1.

use std::collections::BTreeMap;
use std::io::Write;
use std::sync::Arc;

use zed_kernel::{Evaluator, Lookup, Term, Value, World};

use crate::ast::StmtKind;
use crate::elab::{Test, Unit};
use crate::query::{self, Db, Query};
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
    checks(db, text, &|t| Ok(t.clone()))
}

/// The checks of the unit `text`, each row's closed term replaced by what `map` makes of it
/// before it runs (step L1.33): a way to run the tables through another form of the program.
/// Nothing is cached, since the outcomes depend on `map`.
pub fn test_through(text: &str, map: &Through<'_>) -> Vec<Outcome> {
    checks(&mut Db::new(), text, map)
}

fn checks(db: &mut Db, text: &str, map: &Through<'_>) -> Vec<Outcome> {
    let marked = fence::marks(text).lines;
    let mut out = Vec::new();
    match &*db.front(text) {
        Err(diagnostics) => {
            for &line in &marked {
                let d = diagnostics.iter().find(|d| d.line == line);
                out.push(Outcome {
                    line,
                    col: d.map_or(1, |d| d.col),
                    failure: d
                        .is_none()
                        .then(|| "the line is marked ✗ and has no diagnostic".into()),
                });
            }
            for d in diagnostics.iter().filter(|d| !marked.contains(&d.line)) {
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
                        let (line, col) = source::line_col(text.as_bytes(), main.span.start);
                        out.push(Outcome {
                            line,
                            col,
                            failure: Some(why),
                        });
                    }
                }
            }
            let main_def = unit.defs.iter().find(|d| d.name == "main");
            for t in &unit.tests {
                let (line, col) = source::line_col(text.as_bytes(), t.span.start);
                let case = &text[t.span.start..t.span.end];
                let failure = match (&program, t.function.as_str()) {
                    (Some(p), "main") => {
                        let main =
                            Term::Var(main_def.expect("`main` was elaborated").kernel.clone());
                        let mut roots = vec![&main, &t.want];
                        roots.extend(&t.args);
                        let ports = format!("{:?} {:?}", p.inputs(), p.outputs());
                        let k = query::key("wave", &[&query::cone(unit, &roots), ports.as_bytes()]);
                        db.row(Query::Wave, k, || wave(unit, p, t, map)).err()
                    }
                    (None, "main") => continue,
                    _ => {
                        let k = query::key("row", &[&query::cone(unit, &[&t.check])]);
                        db.row(Query::Row, k, || row(unit, t, map)).err()
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

/// The value of `term` under the unit's definitions and the prelude.
fn value(unit: &Unit, term: &Term, map: &Through<'_>) -> Result<Value, String> {
    Evaluator::new(World::new())
        .run(&map(&interp::prelude(unit.close(term.clone())))?)
        .map_err(|e| e.to_string())
}

/// Checks a row of a function's table.
fn row(unit: &Unit, t: &Test, map: &Through<'_>) -> Result<(), String> {
    match value(unit, &t.check, map)? {
        Value::Bool(true) => Ok(()),
        _ => {
            let Term::Prim(_, sides) = &t.check else {
                unreachable!("a check is `call == want`")
            };
            Err(format!("the result is {}", value(unit, &sides[0], map)?))
        }
    }
}

/// Checks a row of `main`'s table: runs the wave its key gives, and compares the writes.
fn wave(unit: &Unit, program: &Program, t: &Test, map: &Through<'_>) -> Result<(), String> {
    let mut lines = BTreeMap::new();
    let mut files: BTreeMap<&str, Arc<dyn Lookup>> = BTreeMap::new();
    for ((name, kind), arg) in program.inputs().iter().zip(&t.args) {
        match kind {
            PortKind::Lines => match value(unit, arg, map)? {
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
                    Arc::new(Given(interp::prelude(unit.close(arg.clone())))),
                );
            }
        }
    }
    let wave = program.run_through(&lines, |name| files[name].clone(), map)?;
    let outputs = program.outputs();
    let wants = match (outputs.len(), value(unit, &t.want, map)?) {
        (1, v) => vec![v],
        (n, Value::Tuple(xs)) if xs.len() == n => xs,
        (n, v) => {
            return Err(format!(
                "the expected value is a String for each of the {n} output ports, not {v}"
            ));
        }
    };
    for (name, want) in outputs.iter().zip(wants) {
        let Value::Str(want) = want else {
            return Err(format!(
                "the expected value of port `{name}` is a String, not {want}"
            ));
        };
        let got = wave
            .writes
            .iter()
            .find(|(p, _)| p == name)
            .map_or(&[][..], |(_, b)| b);
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
/// `file:line:col: why`, then the counts. Returns the exit status: 0 when every check passes,
/// 1 when one fails, 2 for a usage error or a file that cannot be read.
pub fn command(args: &[String], stdout: &mut dyn Write, stderr: &mut dyn Write) -> u8 {
    if args.is_empty() {
        let _ = writeln!(stderr, "usage: zedc test <file> …");
        return 2;
    }
    let (mut passed, mut failed) = (0, 0);
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
        for o in test_in(&mut db, &text) {
            match o.failure {
                None => passed += 1,
                Some(why) => {
                    let _ = writeln!(stdout, "{file}:{}:{}: {why}", o.line, o.col);
                    failed += 1;
                }
            }
        }
    }
    let _ = writeln!(stdout, "{passed} passed, {failed} failed");
    u8::from(failed > 0)
}
