//! The address of a unit whose exports' types hold function types, written by separate `zedc`
//! processes (TEST-param-digest-pinned): `zedc run` on a package whose `main` imports the unit
//! alone (single-file) and on one whose `main` imports two other units first, one of which
//! imports it too (batch), each run in a process of its own, write the one pinned address, the
//! address this process computes, and the address `digest_pin.rs` pins. Each process hashes with
//! its own random hash-map keys and lays out its heap at its own addresses, so a digest that
//! followed either would differ between them. `crates/zed-native/Cargo.toml` names this test,
//! since only a test of that package can name the executable.

/// This process's scratch directory, as the step tests have it. A test target of zed-native
/// cannot depend on zed-tests, so the module is compiled in; a target may use part of it.
#[allow(dead_code)]
#[path = "../../src/scratch.rs"]
mod scratch;

#[allow(dead_code)]
#[path = "digest_program.rs"]
mod digest_program;

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::Arc;

use digest_program::{ADDRESS, BATCH_MAIN, OTHERS, SINGLE_MAIN, UNIT};

/// The number of `zedc` processes run on each package.
const RUNS: usize = 4;

/// The files of the single-file package and of the batch package, each a name and its text.
fn packages() -> [Vec<(&'static str, &'static str)>; 2] {
    let mut batch = vec![("main.zed", BATCH_MAIN), ("u.zed", UNIT)];
    batch.extend(OTHERS);
    [vec![("main.zed", SINGLE_MAIN), ("u.zed", UNIT)], batch]
}

/// The package directory `name` of this test, holding a manifest and `files`, each overwritten.
fn package_dir(name: &str, files: &[(&str, &str)]) -> PathBuf {
    let d = scratch::scratch_dir(format!("pins_binary/{name}"));
    std::fs::write(d.join("zed.manifest"), "// the digest test\n").unwrap();
    for (file, text) in files {
        std::fs::write(d.join(file), text).unwrap();
    }
    d
}

/// The address the import of `u` in the unit `text` is pinned to.
fn pin_of_u(text: &str) -> String {
    let line = (text.lines().find(|l| l.starts_with("import u ")))
        .unwrap_or_else(|| panic!("no import of u in\n{text}"));
    let hex = (line
        .strip_prefix("import u @hash(\"")
        .and_then(|r| r.strip_suffix("\");")))
    .unwrap_or_else(|| panic!("no pin in {line}"));
    assert_eq!(hex.len(), 64, "{line}");
    hex.to_string()
}

/// Runs `zedc run main.zed` in `dir` as a process of its own, and gives the pins of `u` the run
/// wrote into each importer of `importers`. The run stops at the imports, which this zedc does
/// not link yet; every line it writes to standard error must say so, and nothing else.
fn run(dir: &Path, importers: &[&str]) -> Vec<String> {
    let out = Command::new(env!("CARGO_BIN_EXE_zedc"))
        .arg("run")
        .arg(dir.join("main.zed"))
        .stdin(Stdio::null())
        .output()
        .unwrap();
    let err = String::from_utf8(out.stderr).unwrap();
    let not_yet = |l: &str| {
        l.contains("this version of zedc does not yet tie")
            || l.contains("this version of zedc does not yet link")
    };
    assert!(err.lines().all(not_yet), "{err}");
    (importers.iter())
        .map(|f| pin_of_u(&std::fs::read_to_string(dir.join(f)).unwrap()))
        .collect()
}

/// The address of `u` computed in this process from the package `files`.
fn in_process(files: &[(&str, &str)]) -> String {
    let fs = zedc::unit::Memory(
        (files.iter())
            .map(|&(n, t)| (n.to_string(), Arc::from(t)))
            .collect::<HashMap<_, _>>(),
    );
    let p = zedc::unit::load(&mut zedc::query::Db::new(), &fs, &["main"]);
    pin_of_u(&p.pinned("main").expect("the import is pinned"))
}

#[test]
fn separate_processes_write_the_pinned_address_alone_and_in_a_batch() {
    let [single, batch] = packages();
    // Each run in a directory of its own, all at once.
    let runs: Vec<(String, Vec<String>)> = std::thread::scope(|s| {
        let handles: Vec<_> = (0..RUNS)
            .flat_map(|i| {
                [
                    ("single", &single, &["main.zed"][..]),
                    ("batch", &batch, &["main.zed", "b.zed"][..]),
                ]
                .map(|p| (i, p))
            })
            .map(|(i, (kind, files, importers))| {
                let name = format!("{kind}{i}");
                let dir = package_dir(&name, files);
                s.spawn(move || (name, run(&dir, importers)))
            })
            .collect();
        handles.into_iter().map(|h| h.join().unwrap()).collect()
    });
    let first = &runs[0].1[0];
    for (name, pins) in &runs {
        for pin in pins {
            assert_eq!(pin, first, "{name} and {} disagree", runs[0].0);
        }
    }
    assert_eq!(*first, in_process(&single), "a process and this one");
    assert_eq!(*first, in_process(&batch), "a process and this one, batch");
    assert_eq!(first, ADDRESS, "the processes and the pinned address");
}
