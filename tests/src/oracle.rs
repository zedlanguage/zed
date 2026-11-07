//! The differential oracle (step L1.37, DESIGN.md Part G): the interpreter and the native code
//! of `zed-native` run the same source, and what each gives is compared byte for byte.
//!
//! A unit is compared two ways. Each top-level binding bound by `=` whose type, as the checker
//! gives it, has no function component has its outcome compared, as a run of it alone would
//! give it: the value as [`Value`]'s `Display` prints it, or the error. The bindings are run
//! together, each definition once (see [`bindings`]). A binding the checker types `_` may still
//! be a function; both engines then refuse it with the same error, so its outcome is still
//! compared. And every check of the unit's `test` tables, `main`'s waves included, is run by
//! each engine and compared with the interpreter's. A program is compared by the bytes of each
//! port it writes, or by its error.
//!
//! A float whose type carries the reorder facet of `unordered` is to be compared by its type
//! and keys only; the facet arrives at layer L9, and with it that rule.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use zed_kernel::{Evaluator, Lookup, Prim, Shared, Term, Value, World};
use zedc::elab::{Cones, Unit};
use zedc::interp;
use zedc::query::Db;
use zedc::run::{self, PortKind, Through};
use zedc::testing::{test, test_through};

/// The highest layer whose fences and corpus programs are enabled.
pub const ENABLED: u32 = 1;

/// A named way to run a closed term, compared against the interpreter.
pub type Engine<'a> = (&'a str, &'a Through<'a>);

/// What one comparison found.
#[derive(Debug, Default)]
pub struct Report {
    /// How many outcomes were compared, counting each engine once.
    pub compared: usize,
    /// Each disagreement, with both outcomes.
    pub mismatches: Vec<String>,
    /// Each binding the interpreter's runs leave without an outcome, with why (see `Runs`):
    /// it is not compared, unless an engine gives it one.
    pub not_compared: Vec<String>,
}

impl Report {
    fn compare(&mut self, what: &str, engine: &str, want: &str, got: &str) {
        self.compared += 1;
        if want != got {
            self.mismatches.push(format!(
                "{what}: the interpreter gives {want}, and {engine} gives {got}"
            ));
        }
    }

    /// Adds `other`'s counts and mismatches, each prefixed with `at`.
    pub fn add(&mut self, at: &str, other: Report) {
        self.compared += other.compared;
        self.mismatches
            .extend(other.mismatches.into_iter().map(|m| format!("{at}: {m}")));
        self.not_compared
            .extend(other.not_compared.into_iter().map(|m| format!("{at}: {m}")));
    }
}

/// The two native engines: the plan with fused match release, and without it. Returns what
/// `f` gives and how many native runs it made; every one of those runs, whichever way it
/// ended, must leave no cell live, and the runtime's report names any it left by type and
/// allocating node.
pub fn native<R>(f: impl FnOnce(&[Engine<'_>]) -> R) -> (R, u64) {
    let fused = zed_native::through(true);
    let unfused = zed_native::through(false);
    zed_native::counted();
    let r = f(&[("native (fused)", &fused), ("native (unfused)", &unfused)]);
    let c = zed_native::counted();
    assert_eq!(
        c.left,
        Vec::<String>::new(),
        "cells live at the end of a native run"
    );
    (r, c.runs)
}

/// The outcome of a run, as the oracle compares it.
fn printed(r: Result<Value, String>) -> Outcome {
    Outcome::Gives(match r {
        Ok(v) => format!("the value {v}"),
        Err(e) => format!("the error `{e}`"),
    })
}

/// What an engine's runs give a binding.
#[derive(Clone, PartialEq, Eq)]
enum Outcome {
    /// The value or the error a run of the binding alone gives, printed.
    Gives(String),
    /// None, as [`Runs`] stopped before the binding, for the reason given.
    NotCompared(String),
}

impl std::fmt::Display for Outcome {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Outcome::Gives(o) => f.write_str(o),
            Outcome::NotCompared(why) => write!(f, "no outcome, as {why}"),
        }
    }
}

/// Compares each binding of the elaborated unit `u` with no function component under each of
/// `engines`: the interpreter and each engine give each binding's outcome as a run of that
/// binding alone, closed over the definitions it reaches, would give it (`outcomes`), and
/// each pair is compared, binding by binding. A binding the interpreter gives no outcome is
/// listed in the report's `not_compared`; an engine that gives it one is a mismatch.
pub fn bindings(u: &Unit, engines: &[Engine<'_>]) -> Report {
    let mut r = Report::default();
    let firsts: Vec<usize> = (0..u.defs.len())
        .filter(|&i| u.defs[i].first_order)
        .collect();
    if firsts.is_empty() {
        return r;
    }
    let cones = Cones::new(u);
    let all = interp::prelude(
        cones.close(Term::Prim(
            Prim::Tuple,
            firsts
                .iter()
                .map(|&i| Term::Var(u.defs[i].kernel.clone()))
                .collect(),
        )),
    );
    let want = outcomes(u, &cones, &all, firsts.len(), &run::direct);
    let got: Vec<Vec<Outcome>> = engines
        .iter()
        .map(|(_, engine)| outcomes(u, &cones, &all, firsts.len(), engine))
        .collect();
    for (k, &i) in firsts.iter().enumerate() {
        let what = format!("binding `{}`", u.defs[i].name);
        if let Outcome::NotCompared(why) = &want[k] {
            r.not_compared
                .push(format!("{what}: not compared, as {why}"));
        }
        for ((name, _), got) in engines.iter().zip(&got) {
            match (&want[k], &got[k]) {
                (Outcome::NotCompared(_), g) if *g == want[k] => {}
                (w, g) => r.compare(&what, name, &w.to_string(), &g.to_string()),
            }
        }
    }
    r
}

/// The outcome of each of the `n` bindings of `u` with no function component under `engine`,
/// in the unit's order, as [`printed`] gives it: what a run of the binding alone, closed over
/// the definitions it reaches, gives. `all` is the tuple of those bindings closed over the
/// definitions they reach.
///
/// One run of `all` evaluates every definition once, so a chain of bindings, each reading the
/// one before, costs its length and not the sum of its cones. Each element of the tuple is
/// the value its binding's own run gives, since a definition's value depends only on those
/// it reads. Where the run of `all` stops, or gives no tuple of `n` values, as when a binding
/// the checker types `_` is a function, the outcomes come from [`Runs`], which may leave a
/// binding with none.
fn outcomes(
    u: &Unit,
    cones: &Cones<'_>,
    all: &Term,
    n: usize,
    engine: &Through<'_>,
) -> Vec<Outcome> {
    match engine(all, &mut Evaluator::new(World::new())) {
        Ok(Value::Tuple(values)) if values.len() == n => values
            .iter()
            .map(|v| Outcome::Gives(format!("the value {v}")))
            .collect(),
        _ => Runs::new(u, cones, engine).outcomes(),
    }
}

/// What [`Runs`] knows of a definition under one engine.
#[derive(Clone)]
enum Known {
    /// Not run yet, or run and kept as its own term, as a let: a definition with a function
    /// component, or a binding whose value is not data.
    Term,
    /// Run, and a binding: the literal of its value.
    Value(Shared),
    /// Its let stops with this error, the definitions it reads having values.
    Stops(String),
    /// It reads, at any depth, a definition whose let stops: the first such, at this position.
    After(usize),
    /// Not run, as the walk ended before it, and reads no stop: its outcome is unknown.
    Unrun,
}

/// How the runs of the definitions from one stop, or the start, to the next end.
enum End {
    /// They all run.
    Ran,
    /// The definition at this position in the prefix stops, with this error.
    Stops(usize, String),
    /// A run of them stops, binding again a definition with no literal that a run before the
    /// last stop bound: the walk ends.
    Again,
}

/// One engine's runs of the definitions of a unit, in its order, for the outcomes of its
/// bindings with no function component where they cannot run as one tuple (see [`outcomes`]).
///
/// A binding's own run evaluates the lets of the definitions it reaches in the unit's order,
/// and each let reads only lets before it, so the run stops exactly at the first definition
/// it reaches whose let stops with values for all it reads: the binding's outcome is that
/// let's error. A let is such a stop or not whatever run it is in, as its value depends only
/// on those it reads. So the definitions are walked in the unit's order: one that reads a
/// stop is marked with the first stop it reaches and not run, and the others run together,
/// in prefixes of 1, 2, 4, … definitions until one stops, then halved down to the first
/// prefix that stops, whose last definition is the next stop. Each run binds each binding
/// already run to its value, as a literal, and binds the other definitions it reaches as
/// their own terms. The bindings of the definitions that ran get their values from one run of
/// their tuple, split in halves where it gives no tuple of data, down to a binding run alone,
/// whose run gives its own outcome, as for a function the checker typed `_`.
///
/// The walk ends at a run, after a stop, that stops and binds again a definition with no
/// literal (one with a function component, or a binding whose value is a function) that a run
/// before that stop bound. The bindings of the prefix before that run get their values; each
/// definition after it that reads a known stop takes that stop's error, as above; every other
/// is left unrun, and a binding among them has no outcome, with the reason (see below).
//
// Complexity tradeoff: what is given up is the outcome of each binding left unrun, which the
// report lists as not compared, with the reason, where it would have compared it. Why: a run
// stops at its first stop, so each stop costs a run of its own, and that run binds again the
// definitions with a function component the stop reaches, which have no literal: going on
// would cost O((n + s·F) log n) for `s` stops reaching `F` such definitions in a unit of `n`
// definitions. No order of runs does better: the kernel has no form that catches an error and
// goes on, and neither engine keeps an environment from one run to the next (`run::Through`
// takes a closed term, and the native code compiles each term into a JIT module freed after
// its run). Trigger: a second stop whose run binds definitions with a function component that
// a run before the first stop bound, as `n` bindings that each call a function of the unit and
// each stop. With the walk ended there, it costs O(n log n): each run before the end binds the
// definitions between one stop and the next, which run there for the first time, and literals
// for the bindings before them, and these runs are O(log n) prefixes and halvings of that
// stretch. Tests: `l01_37_oracle::alone::stops_that_reach_functions_scale` and
// `a_second_stop_through_functions_is_not_compared`; COMPLEXITY.md F107. A complete solution
// builds the unit's function definitions once, in an environment each run starts from: both
// engines would have to take one, the interpreter keeping closures beyond a run and the native
// code keeping a JIT module of them, and their cells, from run to run (see NATIVE-stop-cells).
// Likewise each binding that is a function, which the checker typed `_`, costs O(log n) runs in
// `values`, as no tuple holding it gives data.
// A unit with no stop and no function in a binding runs as one tuple in `outcomes` instead.
struct Runs<'a> {
    unit: &'a Unit,
    cones: &'a Cones<'a>,
    engine: &'a Through<'a>,
    known: Vec<Known>,
    /// The walk that last met each definition: one visited set for all the walks.
    met: Vec<usize>,
    walks: usize,
    /// Whether the last run bound a definition with no literal that it does not run for the
    /// first time: one run before it bound that definition already.
    again: bool,
    /// The outcome of each binding, by position, once known.
    out: Vec<Option<Outcome>>,
}

impl<'a> Runs<'a> {
    fn new(unit: &'a Unit, cones: &'a Cones<'a>, engine: &'a Through<'a>) -> Self {
        let n = unit.defs.len();
        Runs {
            unit,
            cones,
            engine,
            known: vec![Known::Term; n],
            met: vec![0; n],
            walks: 0,
            again: false,
            out: vec![None; n],
        }
    }

    /// The outcome of each binding with no function component, in the unit's order.
    fn outcomes(mut self) -> Vec<Outcome> {
        let n = self.unit.defs.len();
        let mut at = 0;
        // The definitions from `at` on that read no stop, as far as the prefixes have gone.
        let mut ready = Vec::new();
        while at < n {
            ready.clear();
            let (mut next, mut ran, mut want) = (at, 0, 1);
            let end = loop {
                while ready.len() < want && next < n {
                    if !self.reads_a_stop(next) {
                        ready.push(next);
                    }
                    next += 1;
                }
                if ready.len() > ran {
                    if let Err(e) = self.run(&ready, Self::nothing()) {
                        if self.again {
                            break End::Again;
                        }
                        let (q, e) = self.first_stop(&ready, ran, e);
                        break End::Stops(q, e);
                    }
                    ran = ready.len();
                }
                if next == n {
                    break End::Ran;
                }
                want *= 2;
            };
            let ran = match &end {
                End::Ran => ready.len(),
                End::Stops(q, _) => *q,
                End::Again => ran,
            };
            let bindings: Vec<usize> = ready[..ran]
                .iter()
                .copied()
                .filter(|&i| self.unit.defs[i].first_order)
                .collect();
            self.values(&bindings);
            match end {
                End::Stops(q, e) => {
                    let q = ready[q];
                    if self.unit.defs[q].first_order {
                        self.out[q] = Some(printed(Err(e.clone())));
                    }
                    self.known[q] = Known::Stops(e);
                    at = q + 1;
                }
                End::Ran => at = n,
                End::Again => {
                    self.leave(at - 1, ready[ran]);
                    at = n;
                }
            }
        }
        (0..n)
            .filter(|&i| self.unit.defs[i].first_order)
            .map(|i| {
                self.out[i]
                    .take()
                    .expect("each binding is run, reads a stop or is left unrun")
            })
            .collect()
    }

    /// The empty tuple, the body of a run for its lets alone.
    fn nothing() -> Term {
        Term::Lit(Value::tuple(Vec::new()))
    }

    /// Whether the definition at `i` reads a definition whose let stops, or one that reads
    /// one; if so it is marked with the first such stop, and a binding gets its error.
    fn reads_a_stop(&mut self, i: usize) -> bool {
        let cones = self.cones;
        let first = cones
            .reads(i)
            .iter()
            .filter_map(|&r| match self.known[r] {
                Known::Stops(_) => Some(r),
                Known::After(p) => Some(p),
                Known::Term | Known::Value(_) | Known::Unrun => None,
            })
            .min();
        let Some(p) = first else { return false };
        if self.unit.defs[i].first_order {
            let Known::Stops(e) = &self.known[p] else {
                unreachable!("a definition is marked with the position of a stop")
            };
            self.out[i] = Some(printed(Err(e.clone())));
        }
        self.known[i] = Known::After(p);
        true
    }

    /// Ends the walk at a run that binds again definitions a run before the stop at `stop`
    /// bound, and stops: each definition from `from` on that is not yet known is left unrun,
    /// unless it reads a stop. A stop it reads comes first in its own run, before any
    /// definition left unrun, since every stop known lies before `from`.
    fn leave(&mut self, stop: usize, from: usize) {
        let defs = &self.unit.defs[..];
        let why = Outcome::NotCompared(format!(
            "the run of the definitions from `{}` on, after the stop at `{}`, binds again \
             definitions with a function component, and stops",
            defs[from].name, defs[stop].name
        ));
        for (i, d) in defs.iter().enumerate().skip(from) {
            if matches!(self.known[i], Known::Term) && !self.reads_a_stop(i) {
                self.known[i] = Known::Unrun;
                if d.first_order {
                    self.out[i] = Some(why.clone());
                }
            }
        }
    }

    /// The position in `ready` of the first definition whose let stops, and its error, given
    /// that the prefix of `ready` of length `ran` runs and all of `ready`, stopping with
    /// `error`, does not.
    fn first_stop(
        &mut self,
        ready: &[usize],
        mut ran: usize,
        mut error: String,
    ) -> (usize, String) {
        let mut stops = ready.len();
        while ran + 1 < stops {
            let mid = ran + (stops - ran) / 2;
            match self.run(&ready[..mid], Self::nothing()) {
                Err(e) => (stops, error) = (mid, e),
                Ok(_) => ran = mid,
            }
        }
        (stops - 1, error)
    }

    /// The outcome of each of `bindings`, whose lets all run: their tuple, run in halves where
    /// it gives no tuple of data, down to each binding alone.
    fn values(&mut self, bindings: &[usize]) {
        let var = |i: usize| Term::Var(self.unit.defs[i].kernel.clone());
        let mut todo = vec![bindings];
        while let Some(part) = todo.pop() {
            match part {
                [] => {}
                [b] => {
                    let out = self.run(part, var(*b));
                    if let Ok(v) = &out {
                        self.known[*b] = Known::Value(Shared::new(Term::Lit(v.clone())));
                    }
                    self.out[*b] = Some(printed(out));
                }
                _ => {
                    let all = Term::Prim(Prim::Tuple, part.iter().map(|&b| var(b)).collect());
                    match self.run(part, all) {
                        Ok(Value::Tuple(values)) if values.len() == part.len() => {
                            for (&b, v) in part.iter().zip(values.iter()) {
                                let lit = Shared::new(Term::Lit(v.clone()));
                                self.known[b] = Known::Value(lit);
                                self.out[b] = Some(Outcome::Gives(format!("the value {v}")));
                            }
                        }
                        _ => {
                            let (left, right) = part.split_at(part.len() / 2);
                            todo.push(right);
                            todo.push(left);
                        }
                    }
                }
            }
        }
    }

    /// Runs `body` under `targets`, each as its own term, and the definitions they reach, each
    /// a let in the unit's order: a binding already run as the literal of its value, which
    /// ends the walk there, and the others as their own terms. Sets `again` when one of those
    /// others is not among `targets`.
    fn run(&mut self, targets: &[usize], body: Term) -> Result<Value, String> {
        self.walks += 1;
        let walk = self.walks;
        let cones = self.cones;
        let mut lets = targets.to_vec();
        let mut todo = Vec::new();
        for &t in targets {
            self.met[t] = walk;
            todo.extend(cones.reads(t));
        }
        self.again = false;
        while let Some(i) = todo.pop() {
            if std::mem::replace(&mut self.met[i], walk) == walk {
                continue;
            }
            lets.push(i);
            match self.known[i] {
                Known::Value(_) => {}
                Known::Term => {
                    self.again = true;
                    todo.extend(cones.reads(i));
                }
                Known::Stops(_) | Known::After(_) | Known::Unrun => {
                    unreachable!("a run holds no definition that reads a stop or is left unrun")
                }
            }
        }
        lets.sort_unstable();
        let t = lets.iter().rev().fold(body, |body, &i| {
            let d = &self.unit.defs[i];
            let term = match &self.known[i] {
                Known::Value(v) => v.clone(),
                _ => d.term.clone(),
            };
            Term::Let(d.kernel.clone(), term, Shared::new(body))
        });
        (self.engine)(&interp::prelude(t), &mut Evaluator::new(World::new()))
    }
}

/// Compares the unit `text` under each of `engines`: its bindings with no function component,
/// and the checks of its tables. A rejected unit compares nothing.
pub fn unit(text: &str, engines: &[Engine<'_>]) -> Report {
    let front = Db::new().front(text);
    let Ok((_, u, _)) = &*front else {
        return Report::default();
    };
    let mut r = bindings(u, engines);
    let want = test(text);
    for (name, engine) in engines {
        let got = test_through(text, engine);
        r.compared += 1;
        if got != want {
            r.mismatches.push(format!(
                "the table checks: the interpreter gives {want:?}, and {name} gives {got:?}"
            ));
        }
    }
    r
}

/// The bytes each port writes, or the error, as the oracle compares them.
fn writes(r: Result<run::Wave, String>) -> String {
    match r {
        Err(e) => format!("the error `{e}`"),
        Ok(w) if w.writes.is_empty() => "no writes".into(),
        Ok(w) => w
            .writes
            .iter()
            .map(|(port, bytes)| {
                let text = Value::str(&String::from_utf8_lossy(bytes));
                format!("port `{port}` writes {text}")
            })
            .collect::<Vec<_>>()
            .join(", "),
    }
}

/// A `Files` port whose every path holds the same text.
#[derive(Debug)]
struct Same(Value);

impl Lookup for Same {
    fn get(&self, _: &Value) -> Result<Value, String> {
        Ok(self.0.clone())
    }
}

/// Runs the program `text` with every `Lines` input given `input` and every path of every
/// `Files` input holding `input` as a `String`, and compares its writes under each of `engines`. The interpreter's writes are
/// returned beside the report; a program that does not load compares nothing.
pub fn program(text: &str, input: &[u8], engines: &[Engine<'_>]) -> (Report, Option<String>) {
    let mut r = Report::default();
    let Ok(p) = run::load(text.as_bytes()) else {
        return (r, None);
    };
    let lines: BTreeMap<String, Vec<u8>> = p
        .inputs()
        .iter()
        .filter(|(_, k)| *k == PortKind::Lines)
        .map(|(n, _)| (n.clone(), input.to_vec()))
        .collect();
    let text = Value::str(&String::from_utf8_lossy(input));
    let files = |_: &str| -> Arc<dyn Lookup> { Arc::new(Same(text.clone())) };
    let want = writes(p.run(&lines, files));
    for (name, engine) in engines {
        let got = writes(p.run_through(&lines, &[], files, engine));
        r.compare("the wave", name, &want, &got);
    }
    (r, Some(want))
}

/// The corpus directory, `zed/corpus/`.
pub fn corpus_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../zed/corpus")
}

/// Each corpus program's path and the layer its first line labels, in name order.
pub fn corpus() -> Vec<(PathBuf, u32)> {
    labeled(&corpus_dir())
}

/// Each `.zed` program in `dir`, with the layer its first line labels (`// layer L<n>`), in name
/// order.
pub fn labeled(dir: &Path) -> Vec<(PathBuf, u32)> {
    let mut out: Vec<(PathBuf, u32)> = std::fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("{}: {e}", dir.display()))
        .map(|e| e.expect("an entry").path())
        .filter(|p| p.extension().is_some_and(|e| e == "zed"))
        .map(|p| {
            let text = std::fs::read_to_string(&p).expect("a readable program");
            let layer = text
                .lines()
                .next()
                .and_then(|l| l.strip_prefix("// layer L"))
                .and_then(|n| n.trim().parse().ok())
                .unwrap_or_else(|| panic!("{} has no `// layer L<n>` line", p.display()));
            (p, layer)
        })
        .collect();
    out.sort();
    out
}

/// The step units, `tests/steps/*/zed/*.zed`, in path order.
pub fn step_units() -> Vec<PathBuf> {
    let mut out = Vec::new();
    for step in std::fs::read_dir(crate::steps_dir()).expect("the steps directory") {
        let dir = step.expect("an entry").path().join("zed");
        if let Ok(entries) = std::fs::read_dir(&dir) {
            out.extend(entries.map(|e| e.expect("an entry").path()));
        }
    }
    out.sort();
    out
}

/// Replays each counterexample the checker reports for the unit `text` (step L1.37a): for each
/// failing row of a table other than `main`'s, whose failure names the result of its call,
/// the call is run alone under the interpreter and each of `engines`, and each must give the
/// result the failure names. Returns the comparisons and how many rows were replayed; a
/// rejected unit replays nothing.
pub fn counterexamples(text: &str, engines: &[Engine<'_>]) -> (Report, usize) {
    let mut r = Report::default();
    let front = Db::new().front(text);
    let Ok((_, u, _)) = &*front else {
        return (r, 0);
    };
    let failures: Vec<String> = test(text).into_iter().filter_map(|o| o.failure).collect();
    // Each failure's text and its first place in source order. The failures that begin with
    // a row's text are one range of this map, and the first of them in source order is the
    // row's: a lookup per row in place of a pass over the failures.
    let mut first: BTreeMap<&str, usize> = BTreeMap::new();
    for (i, f) in failures.iter().enumerate() {
        first.entry(f.as_str()).or_insert(i);
    }
    let cones = Cones::new(u);
    let mut replayed = 0;
    for t in u.tests.iter().filter(|t| t.function != "main") {
        let row = format!(
            "`{}` of `{}`: ",
            &text[t.span.start..t.span.end],
            t.function
        );
        let Some(why) = first
            .range(row.as_str()..)
            .take_while(|(f, _)| f.starts_with(row.as_str()))
            .min_by_key(|&(_, i)| i)
            .map(|(f, _)| &f[row.len()..])
        else {
            continue;
        };
        let row = &row[..row.len() - ": ".len()];
        if !why.starts_with("the result is ") {
            continue;
        }
        let zed_kernel::Term::Prim(_, sides) = &t.check else {
            unreachable!("a check is `call == want`")
        };
        let call = interp::prelude(cones.close(sides[0].clone()));
        let named = |v: Result<Value, String>| match v {
            Ok(v) => format!("the result is {v}"),
            Err(e) => format!("the error `{e}`"),
        };
        let direct: &Through<'_> = &run::direct;
        for (name, engine) in std::iter::once(&("the interpreter", direct)).chain(engines) {
            let got = named(engine(&call, &mut Evaluator::new(World::new())));
            r.compared += 1;
            if got != why {
                r.mismatches.push(format!(
                    "the counterexample {row}: the checker names {why}, and {name} gives {got}"
                ));
            }
        }
        replayed += 1;
    }
    (r, replayed)
}
