//! The test runner (step L1.21, DESIGN.md sec:lexical, the test table row): `zedc test` runs
//! every `test { }` table of a unit and checks its `// ✗` marks.
//!
//! A row of a function's table passes when the call equals the expected value under `==`. A
//! row of `main`'s table is a wave: the key gives the input ports, a `Lines` port as the
//! `String` of its bytes, a `Files` port as a function from path to contents and a
//! `CommandLine` port as a `String` holding its arguments one per line, and the
//! value gives the `String` each output port writes. A unit that is rejected passes when
//! every diagnostic is on a line marked ✗ and every marked line has one, of the row of the
//! rejection table its comment names if it names one (`// ✗ Missing argument: …`) and it has
//! no table: its tables cannot run, so each of their rows fails. A wave that aborts fails its
//! row: no form expects an abort at L1.

use std::collections::{BTreeMap, BTreeSet};
use std::io::Write;

use zed_kernel::Term;

use crate::address::ContentAddress;
use crate::ast::StmtKind;
use crate::elab::Cones;
use crate::mutate::{self, Verdict};
use crate::query::{self, Db, Query};
use crate::rejection::Row;
use crate::rows::{row, wave};
use crate::run::{self, Through};
use crate::suppress::{InFile, Severity, Suppress};
use crate::work::{self, Stage};
use crate::{fence, front, source};

/// One check of a unit: a row of a table, a marked line, or a diagnostic on an unmarked line.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Outcome {
    /// Its line, counted from 1.
    pub line: usize,
    /// Its column, counted from 1.
    pub col: usize,
    /// Why it fails; `None` when it passes.
    pub failure: Option<String>,
    /// The part its text decides ([`front::Diagnostic::address`]) of the address of the
    /// rejection its failure reports, if it reports one: `zedc test` prints the address under
    /// it, joined with the file's part, as it prints a warning's (DIAG-addr-rest).
    pub address: Option<ContentAddress>,
}

/// The checks of the unit `text`, in source order.
pub fn test(text: &str) -> Vec<Outcome> {
    test_in(&mut Db::new(), text)
}

/// The checks of the unit `text`, in source order, reusing what `db` holds (step L1.30).
pub fn test_in(db: &mut Db, text: &str) -> Vec<Outcome> {
    checks(db, text, &run::direct).0
}

/// The checks of the unit `text`, each row's closed term run by `map` (steps L1.33, L1.34): a
/// way to run the tables through another form of the program. Nothing is cached, since the
/// outcomes depend on `map`.
pub fn test_through(text: &str, map: &Through<'_>) -> Vec<Outcome> {
    checks(&mut Db::new(), text, map).0
}

/// Whether a unit is accepted as `run::load` accepts it.
enum Accepted {
    /// Its front end accepts it and, if it has a `main`, so does `run::program`.
    Yes,
    /// Its front end rejects it.
    Rejected,
    /// Its front end accepts it and `run::program` refuses it, with this rejection.
    Refused(front::Diagnostic),
}

/// The checks of the unit `text`, each row run by `map`, and whether the unit is accepted.
fn checks(db: &mut Db, text: &str, map: &Through<'_>) -> (Vec<Outcome>, Accepted) {
    let marked = fence::marks(text).lines;
    let mut out = Vec::new();
    let mut accepted = Accepted::Rejected;
    match &*db.front(text) {
        Err(diagnostics) => {
            // The diagnostics on each line, and the marked lines, each found in a map.
            let mut on: BTreeMap<usize, Vec<&front::Diagnostic>> = BTreeMap::new();
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
                let failure = mark_failure(ds, named);
                // A mark that names another row than the diagnostic's reports that diagnostic.
                let address = match (&failure, named, ds.first()) {
                    (Some(_), Some(_), Some(d)) => Some(d.address),
                    _ => None,
                };
                out.push(Outcome {
                    line,
                    col: ds.first().map_or(1, |d| d.col),
                    failure,
                    address,
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
                    address: Some(d.address),
                });
            }
            // A rejected unit runs no table, and a row that does not run does not pass (DESIGN.md
            // L1.21: no check passes on a fraction of its cases), so each row fails. A unit the
            // parser rejects has no rows to show.
            if let Ok((stmts, _)) = &*db.parse(text) {
                let lines = source::Lines::new(text.as_bytes());
                for s in stmts {
                    let StmtKind::Function(f) = &s.kind else {
                        continue;
                    };
                    for (input, expected) in &f.tests {
                        let (line, col) = lines.line_col(text.as_bytes(), input.span.start);
                        let case = &text[input.span.start..expected.span.end];
                        out.push(Outcome {
                            line,
                            col,
                            failure: Some(format!(
                                "`{case}` of `{}`: not run, since the unit is rejected",
                                f.name
                            )),
                            address: None,
                        });
                    }
                }
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
                    address: None,
                });
            }
            let main = stmts
                .iter()
                .find(|s| matches!(&s.kind, StmtKind::Function(f) if f.name == "main"));
            let mut program = None;
            accepted = Accepted::Yes;
            if main.is_some() {
                match work::stage(Stage::Program, None, || run::program(stmts, unit.clone())) {
                    Ok(p) => program = Some(p),
                    Err(e) => {
                        // Placed and addressed as the front end's rejections are, with its
                        // derivation after the place the outcome already gives.
                        let d = front::placed(text, &lines, stmts, Severity::Rejection, vec![e])
                            .pop()
                            .expect("one diagnostic for one error");
                        out.push(Outcome {
                            line: d.line,
                            col: d.col,
                            failure: Some(
                                d.to_string()
                                    .split_once(": ")
                                    .expect("`line:col: `")
                                    .1
                                    .into(),
                            ),
                            address: Some(d.address),
                        });
                        accepted = Accepted::Refused(d);
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
                        let k = query::key("wave", &[&db.cone(&cones, &roots), ports.as_bytes()]);
                        counted_row(db, Query::Wave, k, &t.function, || {
                            wave(&cones, None, p, t, map)
                        })
                        .err()
                    }
                    (None, "main") => continue,
                    _ => {
                        let k = query::key("row", &[&db.cone(&cones, &[&t.check])]);
                        counted_row(db, Query::Row, k, &t.function, || row(&cones, None, t, map))
                            .err()
                    }
                };
                out.push(Outcome {
                    line,
                    col,
                    failure: failure.map(|why| format!("`{case}` of `{}`: {why}", t.function)),
                    address: None,
                });
            }
        }
    }
    out.sort_by_key(|o| (o.line, o.col));
    (out, accepted)
}

/// The row of `definition`'s table that `db` keeps under `k`, a key of `q`, computed by `check`
/// when none is kept: counted as the work of [`Stage::Test`] on `definition` when computed, and
/// as taken from the cache otherwise (TIME-report).
fn counted_row(
    db: &mut Db,
    q: Query,
    k: query::Key,
    definition: &str,
    check: impl FnOnce() -> Result<(), String>,
) -> Result<(), String> {
    let mut computed = false;
    let r = db.row(q, k, || {
        computed = true;
        work::stage(Stage::Test, Some(definition), check)
    });
    if !computed {
        work::cached(Stage::Test, Some(definition));
    }
    r
}

/// Why a line marked ✗ fails, given its diagnostics `ds` and the row its comment names: it
/// names no row, it has no diagnostic, or no diagnostic on it is a case of the row it names
/// (DESIGN.md, "The document is the first test suite").
fn mark_failure(ds: &[&front::Diagnostic], named: Option<Row>) -> Option<String> {
    let Some(want) = named else {
        return Some(
            "the line is marked ✗ and its comment names no row of the rejection table: write \
             `// ✗ <row>: …` with the row's name"
                .into(),
        );
    };
    let Some(first) = ds.first() else {
        return Some("the line is marked ✗ and has no diagnostic".into());
    };
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

/// `zedc test <file> …`, with `args` the words after `test`: writes the warnings of each unit
/// that compiles to `stderr`, as `zedc run` does, and each failing check as `file:line:col: why`
/// to `stdout`, followed by `  address: <hex>` when it reports a rejection, then the counts: checks passed and failed, and the rejection units
/// run, those with a line marked ✗. A file with no table row and no ✗ mark fails, so a run
/// that finds no tests fails. Returns the exit status: 0 when every check passes, 1 when
/// one fails (a unit that does not compile, a row that fails or aborts, a marked line), 2 for
/// a usage error, a file that cannot be read, or a file that cannot be resolved to the place
/// its addresses name ([`InFile::of`]).
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
    let words: Vec<&str> = args.iter().map(String::as_str).collect();
    let (mut suppress, args) = match Suppress::take(&words) {
        Ok(taken) => taken,
        Err(why) => {
            let _ = writeln!(stderr, "{why}");
            return 2;
        }
    };
    if args.is_empty() {
        let _ = writeln!(
            stderr,
            "usage: zedc test [--mutate] [--suppress <address> …] <file> …"
        );
        return 2;
    }
    let (mut passed, mut failed, mut rejection) = (0, 0, 0);
    let mut db = Db::new();
    let mut texts = Vec::new();
    for file in args {
        work::unit(file);
        let text = match std::fs::read(file) {
            Ok(bytes) => work::stage(Stage::Load, None, || source::load(&bytes))
                .map_err(|e| e.render(&bytes)),
            Err(e) => {
                let _ = writeln!(stderr, "{file}: {e}");
                return 2;
            }
        };
        let at = match InFile::of(std::path::Path::new(file)) {
            Ok(at) => at,
            Err(why) => {
                let _ = writeln!(stderr, "{why}");
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
        let (outcomes, accepted) = checks(&mut db, &text, &run::direct);
        // A unit with a rejection reports no warning (DESIGN.md L1.29): the warnings are
        // printed only when the front end and `run::program` accept it.
        // A rejection cannot be suppressed: naming one fails the run.
        let refused = match (&*db.front(&text), &accepted) {
            (Ok((_, _, warnings)), Accepted::Yes) => {
                let _ = run::write_warnings(stderr, file, at, warnings, &mut suppress);
                Vec::new()
            }
            (Err(rejections), _) => suppress.refused(file, at, rejections),
            (Ok(_), Accepted::Refused(d)) => suppress.refused(file, at, std::slice::from_ref(d)),
            (Ok(_), Accepted::Rejected) => Vec::new(),
        };
        for line in refused {
            let _ = writeln!(stdout, "{line}");
            failed += 1;
        }
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
                    if let Some(a) = o.address {
                        let _ = writeln!(stdout, "  address: {}", at.join(a));
                    }
                    failed += 1;
                }
            }
        }
    }
    for line in suppress.unmatched() {
        let _ = writeln!(stderr, "{line}");
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
fn mutants(db: &mut Db, texts: &[(&str, String)], stdout: &mut dyn Write) -> u8 {
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
