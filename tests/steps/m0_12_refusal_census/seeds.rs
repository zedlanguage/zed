//! No checker result depends on the seed of the maps keyed by program text
//! (TEST-text-map-seed-determinism). Since 0f0b8c410 every `TextMap`, `TextSet` and
//! `text_hash` of `zed_kernel::digest` is seeded at random, so their iteration order changes
//! from run to run; a result that read that order would change with it. Each test here checks
//! one piece of a broad set of programs (every `.zed` file of the repository's `zed/` and of the
//! steps, then the units of `programs.txt`) in child processes of this test binary, one under
//! each of [`SEEDS`] (`ZED_TEXT_SEED`, `zed_kernel::digest::text_state`), and compares their
//! output byte for byte. Each child checks every unit of its piece alone, on a thread of its
//! own with nothing cached, and all of them one after another on one thread (batch checking),
//! and the two outputs must agree too.
//!
//! What a child writes of a unit ([`output`]): the whole report of `zedc::run::load` when it
//! rejects the unit, and when it accepts it each warning with its steps, menu, row and address,
//! the elaborated definitions and tests, the names of each definition's parameters and the
//! program's content address; then the same of `Db::front`, the front end alone. The maps of
//! the elaborated unit, which are the standard library's and iterate in an order of their own
//! seed, are written sorted, so that an order that reaches no result is not reported as one.
//!
//! The test can fail: with a scratch change that wrote the variables of a `TextMap` in its
//! iteration order into a message (not committed; see the row's Done note in docs/plan_dag.md),
//! the pieces holding a unit that reached it failed with the first line that differed.

use std::collections::BTreeMap;
use std::fmt::Write;
use std::path::PathBuf;

use zedc::front::{Diagnostic, Front};
use zedc::query::Db;
use zedc::run;

use super::programs;

/// The variable that makes a run of a test here a child, checking that piece and printing its
/// output; unset, the test is the parent, which runs the children and compares them.
const CHILD: &str = "ZED_SEEDS_CHILD";

/// The seed of each child: two fixed seeds and one drawn at random (`ZED_TEXT_SEED` unset).
const SEEDS: [Option<u64>; 3] = [Some(1), Some(0x9e37_79b9_7f4a_7c15), None];

/// The lines a child writes its output between, apart from what the test harness writes.
const BEGIN: &str = "\n=== seeds: output begins\n";
const END: &str = "\n=== seeds: output ends\n";

/// The number of pieces. Measured 2026-11-19, all eight run at once at load average 45 on 32
/// cores: 0.6 s to 10.5 s a piece (the last four hold the `programs.txt` units, which reach the
/// checker; most `.zed` files of `zed/` stop at a feature this zedc does not support yet).
const PIECES: usize = 8;

/// Every unit checked, its name and its text: each `.zed` file under the repository's `zed/`
/// and under the steps, in path order, then each unit of `programs.txt` in its order.
fn units() -> &'static [(String, String)] {
    static UNITS: std::sync::OnceLock<Vec<(String, String)>> = std::sync::OnceLock::new();
    UNITS.get_or_init(|| {
        let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let root = manifest
            .parent()
            .expect("the tests package is in the repository");
        let mut paths = Vec::new();
        super::units(&root.join("zed"), &mut paths);
        super::units(&zed_tests::steps_dir(), &mut paths);
        let mut out: Vec<(String, String)> = (paths.iter())
            .map(|p| {
                let name = p.strip_prefix(root).expect("under the repository");
                let text = std::fs::read_to_string(p).expect("a `.zed` file");
                (name.display().to_string(), text)
            })
            .collect();
        out.extend(programs::all().iter().cloned());
        out
    })
}

/// The units of piece `k`: the k-th of [`PIECES`] runs of consecutive units of nearly equal
/// number.
fn piece(k: usize) -> &'static [(String, String)] {
    let units = units();
    &units[units.len() * k / PIECES..units.len() * (k + 1) / PIECES]
}

/// Everything the checker says of the unit `text` (module doc).
fn output(text: &str) -> String {
    let mut out = String::new();
    match run::load(text.as_bytes()) {
        Err(report) => writeln!(out, "load rejects:\n{report}"),
        Ok(p) => writeln!(out, "load accepts").and_then(|()| {
            diagnostics(&mut out, p.warnings());
            unit(&mut out, p.unit());
            writeln!(out, "address {:?}", p.address())
        }),
    }
    .expect("a String takes any write");
    front(&mut out, &Db::new().front(text));
    out
}

/// The front end's result, written to `out`.
fn front(out: &mut String, f: &Front) {
    match f {
        Err(ds) => {
            out.push_str("front rejects\n");
            diagnostics(out, ds);
        }
        Ok((_, u, warnings)) => {
            out.push_str("front accepts\n");
            diagnostics(out, warnings);
            unit(out, u);
        }
    }
}

/// Each diagnostic in full, in its order, written to `out`.
fn diagnostics(out: &mut String, ds: &[Diagnostic]) {
    for d in ds {
        writeln!(out, "{d:?}").expect("a String takes any write");
    }
}

/// The elaborated unit, its maps sorted by key, written to `out`.
fn unit(out: &mut String, u: &zedc::elab::Unit) {
    let ints: BTreeMap<_, _> = u.int_params.iter().collect();
    let names: BTreeMap<_, _> = u.param_names.iter().collect();
    writeln!(
        out,
        "defs {:?}\ntests {:?}\nwarnings {:?}\nint params {ints:?}\nparam names {names:?}\nlimits {:?}",
        u.defs, u.tests, u.warnings, u.limits
    )
    .expect("a String takes any write");
}

/// The output of the piece `k`, as a child writes it: each unit checked alone, then each
/// checked in a batch, the batch on a thread run beside the units' own threads.
fn child(k: usize) -> String {
    let units = piece(k);
    let (alone, batch) = std::thread::scope(|s| {
        let batch = s.spawn(|| units.iter().map(|(_, t)| output(t)).collect::<Vec<_>>());
        let alone: Vec<_> = (units.iter())
            .map(|(_, t)| s.spawn(move || output(t)))
            .collect();
        let alone: Vec<String> = alone.into_iter().map(|h| h.join().unwrap()).collect();
        (alone, batch.join().unwrap())
    });
    let mut out = String::new();
    for (mode, outs) in [("alone", alone), ("batch", batch)] {
        for ((name, _), o) in units.iter().zip(outs) {
            write!(out, "== {mode} {name}\n{o}").expect("a String takes any write");
        }
    }
    out
}

/// Runs the piece `k` as a child of this test binary under `seed`, giving its output.
fn run_child(test: &str, k: usize, seed: Option<u64>) -> String {
    let mut cmd = std::process::Command::new(std::env::current_exe().unwrap());
    cmd.args(["--exact", test, "--nocapture", "--test-threads=1"])
        .env(CHILD, k.to_string())
        .env_remove("ZED_TEXT_SEED");
    if let Some(s) = seed {
        cmd.env("ZED_TEXT_SEED", s.to_string());
    }
    let done = cmd.output().unwrap();
    let stdout = String::from_utf8_lossy(&done.stdout);
    assert!(
        done.status.success(),
        "the child of piece {k} at seed {seed:?} failed: {}\n{}",
        done.status,
        String::from_utf8_lossy(&done.stderr)
    );
    let from = stdout.find(BEGIN).expect("the child writes its output") + BEGIN.len();
    let to = stdout[from..].find(END).expect("the child ends its output") + from;
    stdout[from..to].to_string()
}

/// The units of an output, by the line `== <mode> <name>` that begins each.
fn by_unit(out: &str) -> BTreeMap<&str, &str> {
    let mut map = BTreeMap::new();
    let mut rest = out;
    while let Some(head) = rest.strip_prefix("== ") {
        let (name, body) = head.split_once('\n').expect("a unit's line");
        let end = body.find("\n== ").map_or(body.len(), |i| i + 1);
        map.insert(name, &body[..end]);
        rest = &body[end..];
    }
    assert!(rest.is_empty(), "the output is units only");
    map
}

/// The first line where `a` and `b` differ, with its number, for the message of a failure.
fn first_difference(a: &str, b: &str) -> String {
    let (mut la, mut lb) = (a.lines(), b.lines());
    for n in 1.. {
        match (la.next(), lb.next()) {
            (None, None) => break,
            (x, y) if x == y => {}
            (x, y) => return format!("line {n}:\n  {x:?}\n  {y:?}"),
        }
    }
    "none".into()
}

/// The test of piece `k`: in a child, its output; in the parent, the children's outputs
/// compared.
fn piece_test(k: usize, test: &str) {
    if let Ok(asked) = std::env::var(CHILD) {
        assert_eq!(
            asked,
            k.to_string(),
            "the child runs the piece it was asked for"
        );
        print!("{BEGIN}{}{END}", child(k));
        return;
    }
    assert!(!piece(k).is_empty(), "piece {k} holds units");
    let path = module_path!().split_once("::").unwrap().1;
    let test = format!("{path}::{test}");
    let outs: Vec<String> = std::thread::scope(|s| {
        let runs: Vec<_> = (SEEDS.iter())
            .map(|&seed| {
                let test = &test;
                s.spawn(move || run_child(test, k, seed))
            })
            .collect();
        runs.into_iter().map(|h| h.join().unwrap()).collect()
    });
    let first = by_unit(&outs[0]);
    assert_eq!(
        first.len(),
        2 * piece(k).len(),
        "each unit alone and in a batch"
    );
    for (out, seed) in outs.iter().zip(SEEDS).skip(1) {
        let other = by_unit(out);
        for (name, a) in &first {
            let b = other.get(name).expect("each child checks every unit");
            assert!(
                a == b,
                "{name}: the output at seed {:?} and at seed {seed:?} differ at {}",
                SEEDS[0],
                first_difference(a, b)
            );
        }
    }
    for (name, _) in piece(k) {
        let (a, b) = (
            first[&*format!("alone {name}")],
            first[&*format!("batch {name}")],
        );
        assert!(
            a == b,
            "{name}: alone and in a batch differ at {}",
            first_difference(a, b)
        );
    }
}

#[test]
fn text_maps_reach_no_result_at_any_seed_0() {
    piece_test(0, "text_maps_reach_no_result_at_any_seed_0");
}

#[test]
fn text_maps_reach_no_result_at_any_seed_1() {
    piece_test(1, "text_maps_reach_no_result_at_any_seed_1");
}

#[test]
fn text_maps_reach_no_result_at_any_seed_2() {
    piece_test(2, "text_maps_reach_no_result_at_any_seed_2");
}

#[test]
fn text_maps_reach_no_result_at_any_seed_3() {
    piece_test(3, "text_maps_reach_no_result_at_any_seed_3");
}

#[test]
fn text_maps_reach_no_result_at_any_seed_4() {
    piece_test(4, "text_maps_reach_no_result_at_any_seed_4");
}

#[test]
fn text_maps_reach_no_result_at_any_seed_5() {
    piece_test(5, "text_maps_reach_no_result_at_any_seed_5");
}

#[test]
fn text_maps_reach_no_result_at_any_seed_6() {
    piece_test(6, "text_maps_reach_no_result_at_any_seed_6");
}

#[test]
fn text_maps_reach_no_result_at_any_seed_7() {
    piece_test(7, "text_maps_reach_no_result_at_any_seed_7");
}
