//! The messages of a run that stops, as a user meets them (plan row MSG-kinds-e2e-tests,
//! DESIGN.md sec:diagnostics): each kind of stop reached by a small program through `zedc run`
//! and through the executable `zedc build` makes, each in a child process under `timeout 60`,
//! and its message checked in full. Each stops with status 3, as every fault of a run does.
//! The part of a message that depends on the machine, the memory it has and the memory the run
//! holds when it stops, is masked ([`masked`]). `crates/zed-native/Cargo.toml` names this test,
//! since only a test of that package can name the executable.
//!
//! The kinds no program reaches are not here, and the comment at each says why:
//! `OutOfFuel` (no run of `zedc` counts steps) and `Stalled` (no program holds a definedness
//! `fix` until step L6.4) at their variants in `zed_kernel::value::KernelError`; an atom's name
//! too large for memory, a kind removed because every atom name is one block of the source
//! (`zed_kernel` `eval::atom_name`); and a fault of zedc itself (`KernelError::Type`), which only
//! a bug in zedc gives, and whose text `zed_kernel`'s own tests check.
#![cfg(target_os = "linux")]

/// This process's scratch directory, as the step tests have it. A test target of zed-native
/// cannot depend on zed-tests, so the module is compiled in; a target may use part of it.
#[allow(dead_code)]
#[path = "../../src/scratch.rs"]
mod scratch;

use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};

/// A directory of its own for this test, under the test target's scratch directory; files in
/// it are overwritten by each run, never deleted.
fn dir() -> PathBuf {
    let d = scratch::process_tmpdir().join("run_stops_binary");
    std::fs::create_dir_all(&d).unwrap();
    d
}

/// The runtime library built with `zedc`, as `tests/steps/l01_36a_executables/binary.rs` finds
/// it.
fn runtime() -> PathBuf {
    let exe = std::env::current_exe().unwrap();
    zed_native::link::runtime_of(Path::new(env!("CARGO_BIN_EXE_zedc")), exe.parent().unwrap())
        .unwrap_or_else(|e| panic!("{e}"))
}

/// The status, standard output and standard error of a run.
fn ran(out: Output) -> (Option<i32>, String, String) {
    (
        out.status.code(),
        String::from_utf8(out.stdout).unwrap(),
        String::from_utf8(out.stderr).unwrap(),
    )
}

/// `zedc` with `args` and no input, under `timeout 60`.
fn zedc(args: &[&str]) -> (Option<i32>, String, String) {
    ran(Command::new("timeout")
        .arg("60")
        .arg(env!("CARGO_BIN_EXE_zedc"))
        .args(args)
        .env("ZED_RUNTIME", runtime())
        .env("CC", "cc")
        .stdin(Stdio::null())
        .output()
        .unwrap())
}

/// The program `src` written to `<name>.zed`, and the path of the file.
fn file(name: &str, src: &str) -> String {
    let f = dir().join(format!("{name}.zed"));
    std::fs::write(&f, src).unwrap();
    f.display().to_string()
}

/// What `zedc run` and the executable `zedc build` makes of the program `src` each give for the
/// words `args`, written after `--` as both take them; and the path of the program's file.
fn both(name: &str, src: &str, args: &[&str]) -> (String, [(Option<i32>, String, String); 2]) {
    let file = file(name, src);
    let exe = dir().join(name).display().to_string();
    let built = zedc(&["build", &file, "-o", &exe]);
    assert_eq!(built.0, Some(0), "building {name}: {built:?}");
    let run = zedc(&[&["run", file.as_str(), "--"], args].concat());
    let native = ran(Command::new("timeout")
        .args(["60", &exe, "--"])
        .args(args)
        .stdin(Stdio::null())
        .output()
        .unwrap());
    (file, [run, native])
}

/// `text` with the amounts that depend on the machine and the moment written `_`: the memory
/// in "this machine has 126 GiB of memory" and in "the run holds 25 MiB of 32 MiB".
fn masked(text: &str) -> String {
    let mut out = text.to_string();
    for (before, after) in [
        ("this machine has ", " of memory"),
        ("the run holds ", " of "),
    ] {
        if let Some(i) = out.find(before) {
            let from = i + before.len();
            if let Some(j) = out[from..].find(after) {
                out.replace_range(from..from + j, "_");
            }
        }
    }
    out
}

/// Each engine's run of `src` stops with status 3, no output, and the message `want` on
/// standard error, `want` given the program's file and with the machine's amounts masked.
fn stops(name: &str, src: &str, args: &[&str], want: impl Fn(&str) -> String) {
    let (file, runs) = both(name, src, args);
    for (engine, (code, out, err)) in ["zedc run", "executable"].iter().zip(runs) {
        assert_eq!(
            (code, out.as_str(), masked(&err)),
            (Some(3), "", want(&file)),
            "{engine}"
        );
    }
}

/// `main` under `limit`, reading the `int` `k` from its first argument and `j` from its
/// second, then running `body`: the numbers it builds from them the checker cannot size.
fn with_args(limit: &str, body: &str) -> String {
    format!(
        "{limit}\nmain(m: MainArgs) {{\n    k = int(m.args[0] else \"\") else 0;\n    \
         j = int(m.args[1] else \"\") else 0;\n{body}}}\n"
    )
}

#[test]
fn a_text_too_large_for_memory_stops_the_run() {
    // `a70` is a tuple of 2^70 copies of the argument, held as 71 shared pairs; its text,
    // two bytes and more for each copy, is past any machine's memory.
    let mut src = "main(m: MainArgs) {\n    a0 = m.args[0] else \"\";\n".to_string();
    for i in 1..=70 {
        src += &format!("    a{i} = (a{}, a{});\n", i - 1, i - 1);
    }
    src += "    m.stdout <- String(a70);\n}\n";
    stops("text", &src, &["x"], |file| {
        format!(
            "{file}:73:17: Text too large for memory: `String(a70)` would write up to 7.0 ZiB \
             of text; this machine has _ of memory.\n  \
             [1] 73:17: the run stopped here\n      \
             73 |     m.stdout <- String(a70);\n         \
             |                 ^^^^^^^^^^^\n"
        )
    });
}

#[test]
fn two_numbers_too_close_to_order_stop_the_run_past_its_memory_limit() {
    // 2^k + 1 and 2^k agree in all but the last of their k + 1 bits.
    let src = with_args(
        "@limits(memory: 33554432)",
        "    a = if k >= 0 { 2 ^ k + 1 } else { 0 };\n    \
         b = if k >= 0 { 2 ^ k } else { 0 };\n    m.stdout <- String(a < b);\n",
    );
    stops("order", &src, &["23592961"], |file| {
        format!(
            "{file}:7:24: Memory limit of `main` passed: `a < b` compares two numbers so close \
             that ordering them needs about 2.8 × 10^7 digits of them (11 MiB), and about 44 \
             MiB of memory to compute it; the run holds _ of 32 MiB.\n  \
             [1] 7:24: the run stopped here\n      \
             7 |     m.stdout <- String(a < b);\n        \
             |                        ^^^^^\n"
        )
    });
}

#[test]
fn two_numbers_too_large_to_compare_stop_the_run_past_its_memory_limit() {
    // 3 · (2^k + 1) and 3^j share the factor 3, and are compared in one form.
    let src = with_args(
        "@limits(memory: 67108864)",
        "    a = if k >= 0 { 3 * (2 ^ k + 1) } else { 0 };\n    \
         b = if j >= 0 { 3 ^ j } else { 0 };\n    m.stdout <- String(a == b);\n",
    );
    stops("equal", &src, &["33554432", "1048576"], |file| {
        format!(
            "{file}:7:24: Memory limit of `main` passed: `a == b` must write two numbers in one \
             form to compare them, which needs about 1.0 × 10^7 digits of them (4.0 MiB), and \
             about 64 MiB of memory to compute it; the run holds _ of 64 MiB.\n  \
             [1] 7:24: the run stopped here\n      \
             7 |     m.stdout <- String(a == b);\n        \
             |                        ^^^^^^\n"
        )
    });
}

#[test]
fn a_number_too_close_to_a_rounding_boundary_stops_the_run_past_its_memory_limit() {
    // (2^k + 2^(k-53) - 1) / 2^k lies just below the midpoint of two neighboring `f64`s.
    let src = with_args(
        "@limits(memory: 67108864)",
        "    q = if k >= 53 { (2r ^ k + 2r ^ (k - 53) - 1) / 2r ^ k } else { 0r };\n    \
         m.stdout <- String(f64(q)) else \"\";\n",
    );
    stops("round", &src, &["16777216"], |file| {
        format!(
            "{file}:6:24: Memory limit of `main` passed: `f64(q)` must round a number so close \
             to a rounding boundary that it needs about 1.4 × 10^7 digits of it (5.6 MiB), and \
             about 89 MiB of memory to compute it; the run holds _ of 64 MiB.\n  \
             [1] 6:24: the run stopped here\n      \
             6 |     m.stdout <- String(f64(q)) else \"\";\n        \
             |                        ^^^^^^\n"
        )
    });
}

#[test]
fn a_read_the_record_lacks_stops_the_replay() {
    // The record of a run that read the file, cut after the program's address: a replay has
    // only the record to read from, and it holds no read. The executable has no replay, and a
    // run that is not a replay reads the world, so only `zedc replay` reaches this message.
    let d = dir();
    let (input, rec, cut) = (d.join("input.txt"), d.join("port.rec"), d.join("cut.rec"));
    std::fs::write(&input, "hello\n").unwrap();
    let src = format!(
        "main(m: MainArgs) {{\n    fs = main::files;\n    \
         m.stdout <- fs[\"{}\"] else \"none\";\n}}\n",
        input.display()
    );
    let file = file("port", &src);
    let recorded = zedc(&["run", &file, "--record", rec.to_str().unwrap()]);
    assert_eq!(recorded, (Some(0), "hello\n\n".into(), String::new()));
    let record = std::fs::read_to_string(&rec).unwrap();
    let head: Vec<&str> = record.lines().take(3).collect();
    assert_eq!(head[..2], ["zed record 1", "program 64"], "{record}");
    std::fs::write(&cut, head.join("\n") + "\n").unwrap();
    let replayed = zedc(&["replay", &file, cut.to_str().unwrap()]);
    let at = input.display();
    let marks = "^".repeat(format!("fs[\"{at}\"]").len());
    assert_eq!(
        replayed,
        (
            Some(1),
            String::new(),
            format!(
                "{file}:3:17: the port `main::files` could not answer a read: the program reads \
                 \"{at}\" here, and the record holds no read of it, so the replay cannot go on: \
                 a replay reads nothing from outside, only what the record holds. The run that \
                 wrote the record did not read \"{at}\", so its inputs differed from these, or \
                 the record has been changed. Replay with the inputs of the recorded run, or \
                 make a new record with `zedc run <file> --record <out>`.\n  \
                 [1] 3:17: the run stopped here\n      \
                 3 |     m.stdout <- fs[\"{at}\"] else \"none\";\n        \
                 |                 {marks}\n"
            )
        )
    );
}
