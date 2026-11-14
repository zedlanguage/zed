//! Step L25.8: `zedc test --mutate`. Each operator or integer constant of a definition is
//! replaced at a time, mutants the build stage proves equal to the original are skipped, the
//! tables run against the rest, and each mutant no row detects is reported.

mod bench;
mod cases;
mod command;
mod examples;
mod order;
mod scaling;

use zedc::mutate::{self, Verdict};
use zedc::query::Db;
use zedc::run;

/// The report of the unit `text`: a line for each mutant that is not detected, as `zedc test
/// --mutate` writes it after the file name, then the counts.
pub(crate) fn report(text: &str) -> Vec<String> {
    let mut db = Db::new();
    let front = db.front(text);
    let (stmts, unit, _) = front.as_ref().as_ref().expect("the unit compiles");
    let found = mutate::run(text, stmts, unit, &run::direct).expect("the mutants are made");
    let mut out = Vec::new();
    let mut counts = [0; 4];
    for (m, v) in &found {
        counts[match v {
            Verdict::Detected => 0,
            Verdict::Undetected(_) => 1,
            Verdict::Skipped => 2,
            Verdict::NotRun => 3,
        }] += 1;
        out.extend(mutate::describe(text, &unit.defs[m.def].name, m, v));
    }
    let [d, u, s, r] = counts;
    out.push(format!(
        "{} mutants: {d} detected, {u} undetected, {s} skipped, {r} not run",
        found.len()
    ));
    out
}
