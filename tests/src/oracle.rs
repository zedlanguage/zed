//! The differential oracle (step L1.37, DESIGN.md Part G): the interpreter and the native code
//! of `zed-native` run the same source, and what each gives is compared byte for byte.
//!
//! A unit is compared two ways. Each top-level binding bound by `=` whose type, as the checker
//! gives it, has no function component is run alone, and its outcome is compared: the value
//! as [`Value`]'s `Display` prints it, or the error. A binding the checker types `_` may still
//! be a function; both engines then refuse it with the same error, so its outcome is still
//! compared. And every check of the unit's `test` tables, `main`'s waves included, is run by
//! each engine and compared with the interpreter's. A program is compared by the bytes of each
//! port it writes, or by its error.
//!
//! A float whose type carries the reorder facet of `unordered` is to be compared by its type
//! and keys only; the facet arrives at layer L9, and with it that rule.

use std::collections::BTreeMap;
use std::path::PathBuf;
use std::sync::Arc;

use zed_kernel::{Evaluator, Lookup, Value, World};
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
    }
}

/// The two native engines: the plan with fused match release, and without it.
pub fn native<R>(f: impl FnOnce(&[Engine<'_>]) -> R) -> R {
    let fused = zed_native::through(true);
    let unfused = zed_native::through(false);
    f(&[("native (fused)", &fused), ("native (unfused)", &unfused)])
}

/// The outcome of a run, as the oracle compares it.
fn printed(r: Result<Value, String>) -> String {
    match r {
        Ok(v) => format!("the value {v}"),
        Err(e) => format!("the error `{e}`"),
    }
}

/// Compares the unit `text` under each of `engines`: its bindings with no function component,
/// and the checks of its tables. A rejected unit compares nothing.
pub fn unit(text: &str, engines: &[Engine<'_>]) -> Report {
    let mut r = Report::default();
    let front = Db::new().front(text);
    let Ok((_, u)) = &*front else {
        return r;
    };
    for d in u.defs.iter().filter(|d| d.first_order) {
        let t = interp::prelude(u.get(&d.name).expect("a definition of the unit"));
        let want = printed(run::direct(&t, &mut Evaluator::new(World::new())));
        for (name, engine) in engines {
            let got = printed(engine(&t, &mut Evaluator::new(World::new())));
            r.compare(&format!("binding `{}`", d.name), name, &want, &got);
        }
    }
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
        let got = writes(p.run_through(&lines, files, engine));
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
    let mut out: Vec<(PathBuf, u32)> = std::fs::read_dir(corpus_dir())
        .expect("the corpus directory")
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
