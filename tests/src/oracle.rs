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
//! port it writes and its exit status, or by its error.
//!
//! The native engines run in one build mode, the one the test run asks for ([`mode`]; DESIGN.md
//! "Build modes"): the two builds are proved equal, so only the asked-for one runs.
//!
//! A float whose type carries the reorder facet of `unordered` is to be compared by its type
//! and keys only; the facet arrives at layer L9, and with it that rule.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use zed_kernel::{Evaluator, Lookup, Prim, Shared, Term, Value, World};
use zedc::build::Mode;
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

/// The environment variable that names the build mode the oracle runs: `debug` or `optimized`.
pub const MODE_VARIABLE: &str = "ZED_BUILD_MODE";

/// The build mode the oracle runs, from [`MODE_VARIABLE`]: the one place it is read. Unset, it is
/// `optimized`, the build that ships and the one that applies the most rewrites.
///
/// One mode per run, not both (author, 2026-11-20, correcting A25: "all code that performs
/// rewrites must prove that the rewritten code has exactly the same semantics as the original
/// code ... if the equivalence of a debug build and an optimized build is formally proved, then
/// there is no need to run both: only run the build the user asked for"). Every rewrite carries
/// a certificate that it keeps the semantics, checked by an independent checker (DESIGN.md
/// sec:optimizer, "Certificates"; step L3.21), so the two builds are proved equal and running
/// both would only double the native runs. Until the optimizer exists both modes run the same
/// code (`zedc::build::Mode`).
pub fn mode() -> Mode {
    match mode_of(std::env::var(MODE_VARIABLE).ok().as_deref()) {
        Ok(mode) => mode,
        Err(e) => panic!("{e}"),
    }
}

/// The build mode a value of [`MODE_VARIABLE`] names, `None` being unset; any other value is an
/// error that names the variable, the value and the two it may take.
pub fn mode_of(setting: Option<&str>) -> Result<Mode, String> {
    match setting {
        None => Ok(Mode::Optimized),
        Some(s) => Mode::ALL.into_iter().find(|m| m.name() == s).ok_or_else(|| {
            format!("{MODE_VARIABLE}={s:?} names no build mode: write `debug` or `optimized`, or leave it unset for `optimized`")
        }),
    }
}

/// The two native engines of the build mode the run asks for ([`mode`]): the plan with fused
/// match release, and without it. Returns what `f` gives and how many native runs it made;
/// every one of those runs, whichever way it ended, must leave no cell live, and the runtime's
/// report names any it left by type and allocating node.
pub fn native<R>(f: impl FnOnce(&[Engine<'_>]) -> R) -> (R, u64) {
    native_by(
        mode(),
        |mode, fuse| Box::new(zed_native::through(mode, fuse)),
        f,
    )
}

/// [`native`] in `mode`, with the engine of each plan made by `make`, which is given the mode
/// and whether the plan fuses match release: the tests of `l01_37_oracle::modes` count what it
/// is asked for, and give an engine another output to show the oracle reports it.
pub fn native_by<R>(
    mode: Mode,
    make: impl Fn(Mode, bool) -> Box<Through<'static>>,
    f: impl FnOnce(&[Engine<'_>]) -> R,
) -> (R, u64) {
    let made: Vec<(String, Box<Through<'static>>)> = [(true, "fused"), (false, "unfused")]
        .into_iter()
        .map(|(fuse, plan)| {
            (
                format!("native ({}, {plan})", mode.name()),
                make(mode, fuse),
            )
        })
        .collect();
    let engines: Vec<Engine<'_>> = made.iter().map(|(n, e)| (n.as_str(), &**e)).collect();
    zed_native::counted();
    let r = f(&engines);
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
// for the bindings before them, and these runs are O(log n) doubling prefixes of that stretch,
// O(stretch) lets in all, and, at a stop, three runs of the window the stop lies in (see
// `first_stop`), each binding the window, the literals it reads and the function definitions
// it reaches once, so O(stretch + F) lets per stop. Until SCALE-near-oracle-stops,
// `first_stop` halved the window, O(log m) probes that each bound those `F` function
// definitions again, O(F log n) lets: O(n log² n) work for `n` bindings reaching `n`
// functions, though this comment said O(n log n); before BENCH-over-nlogn-prediction it also
// reran each prefix whole. Tests:
// `l01_37_oracle::bench::stops_that_reach_functions_scale` and
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
            // `first_stop` gave the bindings before a stop their outcomes already.
            if !matches!(end, End::Stops(..)) {
                self.values_of(&ready[..ran]);
            }
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
    /// `error`, does not. The bindings of the prefix before that position get their outcomes.
    //
    // Complexity tradeoff: the naive search halves `ready[ran..]` by running each prefix
    // `ready[..mid]` from the start: O(log m) runs of up to `ready.len()` lets for a stretch of
    // `m = ready.len() - ran`, O(len · log m · log n) with a let O(log n) (COMPLEXITY.md K8),
    // which is O(n log² n) for a unit of `n` definitions whose stretch is the whole unit, as a
    // chain whose last let stops (10.24 times the instructions at 8 times 20,000 definitions,
    // bench `a_chain_that_stops_scales`). Here the prefix known to run, `ready[..lo]`, gets
    // its values first, so a probe runs `ready[lo..mid]` alone and reaches the definitions
    // before it as one literal let each, where it does not reach them through a function
    // definition. Proof of the bound: the window `hi - lo` halves at each probe, so the probes
    // and the `values` of each piece that runs bind Σ_k 2·m/2^k ≤ 4m lets of the window, and
    // the prefix's `values` binds `ran` once; each probe also binds the literals and the
    // function definitions its window reaches (the `F` of `Runs`), at most the reads of the
    // window's definitions plus `F`. Total O((len + reads + F log m) log n): O(n log n) for a
    // chain. Measured 2026-11-20: 4.9 and 4.6 lets a definition at 4,096 and 16,384 definitions,
    // against 14.8 at 4,096 for the naive search (test
    // `the_search_for_the_stop_binds_each_definition_a_bounded_number_of_times`). The outcomes are
    // the same: a probe's run stops at its first let that stops, every definition before `lo`
    // running, and that let's error is its own.
    //
    // The `F log m` term is O(n log n) lets, O(n log² n) work, where `n` bindings reach `n`
    // function definitions, which have no literal (`stops_reaching_functions`, plan row
    // SCALE-near-oracle-stops). So the stop is first located by one run of the
    // interpreter over the window, which pushes each let's position to an output port as it
    // runs ([`Runs::located`]): the stop is the let after the last pushed. Two runs of the
    // engine confirm it, `ready[lo..q]` running and `ready[lo..=q]` stopping, which is what
    // the halving would conclude, as the stop is the first let of the window that stops. That
    // is three runs, O(m + reads + F) lets, for each stop. An engine that disagrees with the
    // interpreter there falls back to the halving, which then finds its own stop, so a
    // mismatch still shows. Alternatives weighed: an environment kept by the engines from one
    // run to the next (the complete solution of `Runs`), which needs a change of both engines'
    // `Through` and of the native code's JIT modules; and a catch of a stop in the kernel,
    // which has none. The port needs neither, and the pushes leave every value as it was.
    // Test:
    // `l01_37_oracle::alone::the_search_for_a_stop_through_functions_binds_them_once_a_probe`.
    fn first_stop(&mut self, ready: &[usize], ran: usize, mut error: String) -> (usize, String) {
        let (mut lo, mut hi) = (ran, ready.len());
        self.values_of(&ready[..lo]);
        // The interpreter's run of the window with pushes names the stop `q`; the engine's run
        // of `ready[lo..q]` running and of `ready[lo..=q]` stopping confirm it, as a probe
        // would. So where the engine agrees, a stop costs three runs of the window, each
        // binding the function definitions it reaches once, not one per probe.
        if let Some(q) = self
            .located(&ready[lo..hi])
            .map(|q| lo + q)
            .filter(|&q| q < hi)
            && (q == lo || self.run(&ready[lo..q], Self::nothing()).is_ok())
        {
            self.values_of(&ready[lo..q]);
            lo = q;
            match self.run(&ready[lo..=q], Self::nothing()) {
                Err(e) => return (q, e),
                // The engine runs the let the interpreter stops at: the halving below
                // searches the rest, `ready[..hi]` stopping as before.
                Ok(_) if q + 1 < hi => {
                    self.values_of(&ready[lo..=q]);
                    lo = q + 1;
                }
                Ok(_) => {}
            }
        }
        // `ready[..lo]` runs and `ready[..hi]` stops with `error`, its own let at `hi - 1`
        // when `hi == lo + 1`.
        while hi - lo > 1 {
            let mid = lo + (hi - lo) / 2;
            match self.run(&ready[lo..mid], Self::nothing()) {
                Err(e) => {
                    error = e;
                    hi = mid;
                }
                Ok(_) => {
                    self.values_of(&ready[lo..mid]);
                    lo = mid;
                }
            }
        }
        (lo, error)
    }

    /// The outcomes, by [`Runs::values`], of the bindings among `defs`, whose lets all run.
    fn values_of(&mut self, defs: &[usize]) {
        let bindings: Vec<usize> = defs
            .iter()
            .copied()
            .filter(|&i| self.unit.defs[i].first_order)
            .collect();
        self.values(&bindings);
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
        let t = self.lets(targets, body, false);
        (self.engine)(&interp::prelude(t), &mut Evaluator::new(World::new()))
    }

    /// The position in `targets` of the first whose let stops in the interpreter's run of the
    /// term [`Runs::run`] makes of them, found from that one run: after each target's let the
    /// run pushes the target's position to the port [`PROGRESS`], so the stop is the target
    /// after the last pushed. `None` where that run does not stop. A guess for the engine:
    /// [`Runs::first_stop`] confirms it by the engine's own runs.
    fn located(&mut self, targets: &[usize]) -> Option<usize> {
        let t = self.lets(targets, Self::nothing(), true);
        let mut ev = Evaluator::new(World::new().output(PROGRESS));
        run::direct(&interp::prelude(t), &mut ev).err()?;
        let last = ev.world.outputs[PROGRESS].log.last();
        Some(match last {
            Some(Value::Int(i)) => targets.partition_point(|&t| t as i64 <= *i),
            _ => 0,
        })
    }

    /// The term [`Runs::run`] runs: `body` under the lets of `targets` and of the definitions
    /// they reach, in the unit's order. With `progress`, each target's let is followed by a
    /// push of its position to [`PROGRESS`], bound to a name no definition has.
    fn lets(&mut self, targets: &[usize], body: Term, progress: bool) -> Term {
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
        lets.iter().rev().fold(body, |body, &i| {
            let d = &self.unit.defs[i];
            let term = match &self.known[i] {
                Known::Value(v) => v.clone(),
                _ => d.term.clone(),
            };
            let body = if progress && targets.binary_search(&i).is_ok() {
                let push = Term::Push(
                    PROGRESS.into(),
                    Shared::new(Term::Lit(Value::Int(i as i64))),
                );
                Term::Let(PROGRESS.into(), Shared::new(push), Shared::new(body))
            } else {
                body
            };
            Term::Let(d.kernel.clone(), term, Shared::new(body))
        })
    }
}

/// The output port of the interpreter's run that locates a stop ([`Runs::located`]), and the
/// name its pushes are bound to: not an identifier, so no unit's port or definition has it.
const PROGRESS: &str = "oracle progress";

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

/// The bytes each port writes and the exit status, or the error, as the oracle compares them.
/// A status of 0 is not named, so the common case reads as the writes alone; any other status
/// is named after them, since `main`'s `int` result is an output of the program (DESIGN.md
/// sec:ports; step L1.36a compares it for executables), and a run that wrote the same bytes
/// with another status would otherwise pass.
fn writes(r: Result<run::Wave, String>) -> String {
    let w = match r {
        Err(e) => return format!("the error `{e}`"),
        Ok(w) => w,
    };
    let mut out = match &w.writes[..] {
        [] => "no writes".to_string(),
        all => all
            .iter()
            .map(|(port, bytes)| {
                let text = Value::str(&String::from_utf8_lossy(bytes));
                format!("port `{port}` writes {text}")
            })
            .collect::<Vec<_>>()
            .join(", "),
    };
    if w.status != 0 {
        out.push_str(&format!(", and the exit status {}", w.status));
    }
    out
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
/// `Files` input holding `input` as a `String`, and compares its writes under each of `engines`.
/// The interpreter's writes are returned beside the report; a program that does not load compares
/// nothing.
pub fn program(text: &str, input: &[u8], engines: &[Engine<'_>]) -> (Report, Option<String>) {
    let mut r = Report::default();
    let Ok(p) = run::load(text.as_bytes()) else {
        return (r, None);
    };
    let bytes: Arc<[u8]> = Arc::from(input);
    let lines: BTreeMap<String, Arc<[u8]>> = p
        .inputs()
        .iter()
        .filter(|(_, k)| *k == PortKind::Lines)
        .map(|(n, _)| (n.clone(), Arc::clone(&bytes)))
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

/// Each corpus program's path and the layer its first line labels, in name order. A program is
/// a file `NN-name.zed`, or, for a program with units, `NN-name/main.zed` in the package root a
/// `zed.manifest` marks (DESIGN.md sec:units: a unit with no manifest at or above it imports no
/// unit), beside the units it imports.
pub fn corpus() -> Vec<(PathBuf, u32)> {
    let dir = corpus_dir();
    let mut out = labeled(&dir);
    for e in std::fs::read_dir(&dir).unwrap_or_else(|e| panic!("{}: {e}", dir.display())) {
        let root = e.expect("an entry").path();
        if root.join("zed.manifest").is_file() {
            let main = root.join("main.zed");
            assert!(main.is_file(), "{} holds no main.zed", root.display());
            out.push((main.clone(), label(&main)));
        }
    }
    out.sort();
    out
}

/// The corpus program `program` (a path [`corpus`] gives) with `extension` in place of its own:
/// `07-json-parser/main.zed` with `in` is `07-json-parser.in`, beside the package root, as for
/// a program of one file. Its input is `"in"`, its expected output `"out"`.
pub fn corpus_file(program: &Path, extension: &str) -> PathBuf {
    let in_package = program.file_name().is_some_and(|f| f == "main.zed")
        && program.with_file_name("zed.manifest").is_file();
    let base = if in_package {
        program.parent().expect("a package root")
    } else {
        program
    };
    base.with_extension(extension)
}

/// The corpus program `program`'s name, its path under the corpus directory:
/// `03-edit-distance.zed`, or `07-json-parser/main.zed` for a program with units.
pub fn corpus_name(program: &Path) -> String {
    program
        .strip_prefix(corpus_dir())
        .expect("a corpus program")
        .display()
        .to_string()
}

/// The layer the first line of the program at `p` labels (`// layer L<n>`).
fn label(p: &Path) -> u32 {
    let text = std::fs::read_to_string(p).expect("a readable program");
    text.lines()
        .next()
        .and_then(|l| l.strip_prefix("// layer L"))
        .and_then(|n| n.trim().parse().ok())
        .unwrap_or_else(|| panic!("{} has no `// layer L<n>` line", p.display()))
}

/// Each `.zed` program in `dir`, with the layer its first line labels (`// layer L<n>`), in name
/// order.
pub fn labeled(dir: &Path) -> Vec<(PathBuf, u32)> {
    let mut out: Vec<(PathBuf, u32)> = std::fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("{}: {e}", dir.display()))
        .map(|e| e.expect("an entry").path())
        .filter(|p| p.extension().is_some_and(|e| e == "zed"))
        .map(|p| {
            let layer = label(&p);
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
    // Complexity tradeoff (COMPLEXITY.md row F107): naive version, each row searching every
    // failure and each binding asking `Unit::get` with a new `Cones` of the unit, O(n^2) in the
    // definitions. Used: one `Cones` per unit and this ordered map, O(n log n). Tradeoff: the
    // map holds a reference to each failure until the replay ends.
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
