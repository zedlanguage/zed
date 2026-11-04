//! The test runner (step L1.21, DESIGN.md sec:lexical, the test table row): `zedc test` runs
//! every `test { }` table of a unit and checks its `// ✗` marks.
//!
//! A row of a function's table passes when the call equals the expected value under `==`. A
//! row of `main`'s table is a wave: the key gives the input ports, a `Lines` port as the
//! `String` of its bytes, a `Files` port as a function from path to contents and a
//! `CommandLine` port as a `String` holding its arguments one per line, and the
//! value gives the `String` each output port writes. A unit that is rejected passes when
//! every diagnostic is on a line marked ✗ and every marked line has one, of the row of the
//! rejection table its comment names if it names one (`// ✗ Missing argument: …`); its tables
//! do not run. A wave that aborts fails its row: no form expects an abort at L1.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::io::Write;
use std::sync::Arc;

use zed_kernel::{Evaluator, Lookup, Shared, Term, Value, World};

use crate::ast::StmtKind;
use crate::elab::{Cones, Test};
use crate::mutate::{self, Verdict};
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
        Ok((stmts, unit, _)) => {
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
                        db.row(Query::Wave, k, || wave(&cones, None, p, t, map))
                            .err()
                    }
                    (None, "main") => continue,
                    _ => {
                        let k = query::key("row", &[&query::cone(&cones, &[&t.check])]);
                        db.row(Query::Row, k, || row(&cones, None, t, map)).err()
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

/// A definition of the unit and the term that replaces its own (step L25.8, a mutant): its
/// position in the unit and the term.
pub(crate) type Swap<'a> = Option<(usize, &'a Shared)>;

/// The value of `term` under the definitions it reaches, with `swap`, and the prelude.
fn value(
    cones: &Cones<'_>,
    swap: Swap<'_>,
    term: &Term,
    map: &Through<'_>,
) -> Result<Value, String> {
    map(
        &interp::prelude(cones.close_with(term.clone(), swap)),
        &mut Evaluator::new(World::new()),
    )
}

/// Checks a row of a function's table, with `swap`.
pub(crate) fn row(
    cones: &Cones<'_>,
    swap: Swap<'_>,
    t: &Test,
    map: &Through<'_>,
) -> Result<(), String> {
    match value(cones, swap, &t.check, map)? {
        Value::Bool(true) => Ok(()),
        _ => {
            let Term::Prim(_, sides) = &t.check else {
                unreachable!("a check is `call == want`")
            };
            Err(format!(
                "the result is {}",
                value(cones, swap, &sides[0], map)?
            ))
        }
    }
}

/// Checks a row of `main`'s table: runs the wave its key gives, and compares the writes. With
/// `swap`, the wave runs `main` closed under the unit with `swap`.
pub(crate) fn wave(
    cones: &Cones<'_>,
    swap: Swap<'_>,
    program: &Program,
    t: &Test,
    map: &Through<'_>,
) -> Result<(), String> {
    let mut lines = BTreeMap::new();
    let mut files: BTreeMap<&str, Arc<dyn Lookup>> = BTreeMap::new();
    // The arguments the first `CommandLine` port is given, and its name.
    let mut args: Option<(&str, Vec<String>)> = None;
    for ((name, kind), arg) in program.inputs().iter().zip(&t.args) {
        match kind {
            PortKind::Lines => match value(cones, swap, arg, map)? {
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
                    Arc::new(Given(interp::prelude(cones.close_with(arg.clone(), swap)))),
                );
            }
            PortKind::CommandLine => match value(cones, swap, arg, map)? {
                Value::Str(s) => {
                    let given = given_args(&s);
                    match &args {
                        Some((first, a)) if *a != given => {
                            return Err(format!(
                                "the `CommandLine` ports `{first}` and `{name}` are given \
                                 different arguments; a run has one command line"
                            ));
                        }
                        Some(_) => {}
                        None => args = Some((name, given)),
                    }
                }
                v => {
                    return Err(format!(
                        "the `CommandLine` port `{name}` is given as a String, one argument \
                         per line, not {v}"
                    ));
                }
            },
        }
    }
    let args = args.map(|(_, a)| a).unwrap_or_default();
    let wave = match swap {
        None => program.run_through(&lines, &args, |name| files[name].clone(), map)?,
        Some(_) => {
            let main = program.unit.defs.iter().find(|d| d.name == "main");
            let main = Term::Var(main.expect("`main` was elaborated").kernel.clone());
            let main = cones.close_with(main, swap);
            program.run_main_through(&main, &lines, &args, |name| files[name].clone(), map)?
        }
    };
    let outputs = program.outputs();
    let wants = match (outputs.len(), value(cones, swap, &t.want, map)?) {
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

/// The arguments a test gives a `CommandLine` port as the `String` `s`, one per line, the
/// lines read as a `Lines` input's are: a line ends at `\n`, a `\r` before it is dropped, and a
/// last line needs no `\n`.
fn given_args(s: &str) -> Vec<String> {
    let mut lines: Vec<&str> = s.split('\n').collect();
    if lines.last().is_some_and(|l| l.is_empty()) {
        lines.pop();
    }
    lines
        .into_iter()
        .map(|l| l.strip_suffix('\r').unwrap_or(l).to_string())
        .collect()
}

/// A `Files` port a test gives as a function from path to contents.
#[derive(Debug)]
struct Given(Term);

impl Lookup for Given {
    fn get(&self, key: &Value) -> Result<Value, String> {
        let read = Term::App(Shared::new(self.0.clone()), vec![Term::Lit(key.clone())]);
        Evaluator::new(World::new())
            .run(&read)
            .map_err(|e| e.to_string())
    }
}

/// `zedc test <file> …`, with `args` the words after `test`: writes the warnings of each unit
/// that compiles to `stderr`, as `zedc run` does, and each failing check as `file:line:col: why`
/// to `stdout`, then the counts: checks passed and failed, and the rejection units
/// run, those with a line marked ✗. A file with no table row and no ✗ mark fails, so a run
/// that finds no tests fails. Returns the exit status: 0 when every check passes, 1 when
/// one fails (a unit that does not compile, a row that fails or aborts, a marked line), 2 for
/// a usage error or a file that cannot be read.
///
/// `zedc test --mutate <file> …` then runs the tables against each mutant of each unit that
/// compiles (step L25.8, [`crate::mutate`]) when every check passes, and writes each mutant
/// no row detects, each skipped and each not run as `file:line:col: …`, then the counts. The
/// mutants change no exit status: there is no fraction to reach. When a check fails, no
/// mutant runs and the status is the one above. A unit whose mutants cannot be made, an
/// error of the compiler, gives 1.
pub fn command(args: &[String], stdout: &mut dyn Write, stderr: &mut dyn Write) -> u8 {
    let (mutate, args) = match args {
        [flag, rest @ ..] if flag == "--mutate" => (true, rest),
        _ => (false, args),
    };
    if args.is_empty() {
        let _ = writeln!(stderr, "usage: zedc test [--mutate] <file> …");
        return 2;
    }
    let (mut passed, mut failed, mut rejection) = (0, 0, 0);
    let mut db = Db::new();
    let mut texts = Vec::new();
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
        if let Ok((_, _, warnings)) = &*db.front(&text) {
            let _ = run::write_warnings(stderr, file, warnings);
        }
        let outcomes = test_in(&mut db, &text);
        texts.push((file, text));
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
    if failed > 0 {
        if mutate {
            let _ = writeln!(stdout, "no mutant runs: the original's checks fail");
        }
        return 1;
    }
    if mutate {
        return mutants(&mut db, &texts, stdout);
    }
    0
}

/// Runs the mutants of each unit of `texts` that compiles, and writes the report.
fn mutants(db: &mut Db, texts: &[(&String, String)], stdout: &mut dyn Write) -> u8 {
    let (mut detected, mut undetected, mut skipped, mut not_run) = (0, 0, 0, 0);
    let mut status = 0;
    for (file, text) in texts {
        let front = db.front(text);
        let Ok((stmts, unit, _)) = &*front else {
            continue;
        };
        let found = match mutate::run(text, stmts, unit, &run::direct) {
            Ok(found) => found,
            Err(why) => {
                let _ = writeln!(stdout, "{file}: no mutants: {why}");
                status = 1;
                continue;
            }
        };
        for (m, v) in &found {
            match v {
                Verdict::Detected => detected += 1,
                Verdict::Undetected(_) => undetected += 1,
                Verdict::Skipped => skipped += 1,
                Verdict::NotRun => not_run += 1,
            }
            if let Some(line) = mutate::describe(text, &unit.defs[m.def].name, m, v) {
                let _ = writeln!(stdout, "{file}:{line}");
            }
        }
    }
    let total = detected + undetected + skipped + not_run;
    let _ = writeln!(
        stdout,
        "{total} mutants: {detected} detected, {undetected} undetected, {skipped} skipped, \
         {not_run} not run"
    );
    status
}
