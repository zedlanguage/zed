//! The limits `main` sets on its own run (plan row MAIN-limits; DESIGN.md sec:ports, "`main`
//! may limit its own run"), run as a user runs a program: `zedc run` and the executable `zedc
//! build` makes, each in a child process of its own under `timeout 60`, since a limit holds
//! for the whole process. Each limit is hit and not hit; a run that passes one stops with
//! status 3 and a message naming the limit, as every fault of a run does, and "Number too large
//! for memory" too. `crates/zed-native/Cargo.toml` names this test, since only a test of that
//! package can name the zedc executable.
#![cfg(target_os = "linux")]

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

/// A directory of its own for this test, under the test target's scratch directory; files in
/// it are overwritten by each run, never deleted.
fn dir() -> PathBuf {
    let d = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("main_limits_binary");
    std::fs::create_dir_all(&d).unwrap();
    d
}

/// The runtime library built with `zedc`: of the `libzed_native-<hash>.a` Cargo keeps beside
/// this test, the one holding the symbol `zedc` holds.
fn runtime() -> PathBuf {
    let exe = std::env::current_exe().unwrap();
    zed_native::link::runtime_of(Path::new(env!("CARGO_BIN_EXE_zedc")), exe.parent().unwrap())
        .unwrap_or_else(|e| panic!("{e}"))
}

/// `zedc` with `args`, under `timeout 60`.
fn zedc(args: &[&str]) -> Output {
    Command::new("timeout")
        .arg("60")
        .arg(env!("CARGO_BIN_EXE_zedc"))
        .args(args)
        .env("ZED_RUNTIME", runtime())
        .env("CC", "cc")
        .output()
        .unwrap()
}

/// The status, standard output and standard error of a run.
fn ran(out: &Output) -> (Option<i32>, String, String) {
    (
        out.status.code(),
        String::from_utf8(out.stdout.clone()).unwrap(),
        String::from_utf8(out.stderr.clone()).unwrap(),
    )
}

/// The program `src` written to `<name>.zed` and built into the executable `<name>`; the
/// paths of both.
fn program(name: &str, src: &str) -> (String, String) {
    let d = dir();
    let (file, exe) = (d.join(format!("{name}.zed")), d.join(name));
    std::fs::write(&file, src).unwrap();
    let (file, exe) = (file.display().to_string(), exe.display().to_string());
    let built = zedc(&["build", &file, "-o", &exe]);
    assert_eq!(ran(&built).0, Some(0), "building {name}: {:?}", ran(&built));
    (file, exe)
}

/// What `zedc run` and the executable each give for the word `word`, the run's first
/// argument, written after `--` as both take it.
fn both(file: &str, exe: &str, word: &str) -> [(Option<i32>, String, String); 2] {
    let run = zedc(&["run", file, "--", word]);
    let native = Command::new("timeout")
        .args(["60", exe, "--", word])
        .output()
        .unwrap();
    [ran(&run), ran(&native)]
}

/// `main` under `limit`, writing `String(<b> ^ k)` for the `int` `k` of its first argument: a
/// number of about `k` bits whose computation, from an argument, the checker cannot size.
fn power_program(limit: &str, b: u128) -> String {
    format!(
        "{limit}\nmain(m: MainArgs) {{\n    k = int(m.args[0] else \"\") else 0;\n    \
         m.stdout <- String(if k >= 0 {{ {b} ^ k }} else {{ 0 }});\n}}\n"
    )
}

#[test]
fn a_run_within_its_memory_limit_runs_and_one_past_it_stops_with_status_3() {
    let (file, exe) = program("memory", &power_program("@limits(memory: 16777216)", 2));
    for (engine, got) in ["zedc run", "executable"]
        .iter()
        .zip(both(&file, &exe, "10"))
    {
        assert_eq!(got, (Some(0), "1024\n".into(), String::new()), "{engine}");
    }
    // 2^(10^9): a number of 10^9 bits, 125 MB, past the 16 MiB limit.
    for (engine, (code, out, err)) in
        ["zedc run", "executable"]
            .iter()
            .zip(both(&file, &exe, "1000000000"))
    {
        assert_eq!((code, out.as_str()), (Some(3), ""), "{engine}: {err}");
        assert!(
            err.contains(
                ": Memory limit of `main` passed: `String` would write about 3.0 × 10^8 digits"
            ) && err.contains("of 16 MiB.")
                && err.contains("memory.zed"),
            "{engine}: {err}"
        );
    }
}

#[test]
fn a_run_within_its_processor_time_runs_and_one_past_it_stops_with_status_3() {
    let (file, exe) = program("cpu", &power_program("@limits(cpu: 1r/2r)", 3));
    for (engine, got) in ["zedc run", "executable"]
        .iter()
        .zip(both(&file, &exe, "10"))
    {
        assert_eq!(got, (Some(0), "59049\n".into(), String::new()), "{engine}");
    }
    // 3^(10^8): seconds of processor time to write in decimal.
    for (engine, (code, out, err)) in
        ["zedc run", "executable"]
            .iter()
            .zip(both(&file, &exe, "100000000"))
    {
        assert_eq!((code, out.as_str()), (Some(3), ""), "{engine}: {err}");
        assert!(
            err.starts_with("Processor-time limit of `main` passed: 0.5 s. The run used 0.5"),
            "{engine}: {err}"
        );
    }
}

#[test]
fn a_run_within_its_deadline_runs_and_one_past_it_stops_with_status_3() {
    let (file, exe) = program("timeout", &power_program("@timeout(1r/2r)", 3));
    for (engine, got) in ["zedc run", "executable"]
        .iter()
        .zip(both(&file, &exe, "10"))
    {
        assert_eq!(got, (Some(0), "59049\n".into(), String::new()), "{engine}");
    }
    for (engine, got) in ["zedc run", "executable"]
        .iter()
        .zip(both(&file, &exe, "100000000"))
    {
        assert_eq!(
            got,
            (
                Some(3),
                String::new(),
                "Deadline of `main` passed: 0.5 s.\n".into()
            ),
            "{engine}"
        );
    }
}

#[test]
fn a_number_too_large_for_memory_stops_the_run_with_status_3() {
    // No limit: `(2^64 + 13) ^ (2^64)` needs 130 EiB, past the 2^64 bits a number may have.
    // Before MAIN-limits the run stopped with status 1, as a `#bug` does.
    let (file, exe) = program("too_large", &power_program("", (1 << 64) + 13));
    for (engine, (code, out, err)) in
        ["zedc run", "executable"]
            .iter()
            .zip(both(&file, &exe, "18446744073709551616"))
    {
        assert_eq!((code, out.as_str()), (Some(3), ""), "{engine}: {err}");
        assert!(
            err.contains(": Number too large for memory: `18446744073709551629 ^ k` needs"),
            "{engine}: {err}"
        );
    }
    // `2 ^ (2^62)` is a number the run could build, but its 1.4 × 10^18 digits are not.
    let (file, exe) = program("text_too_large", &power_program("", 2));
    for (engine, (code, out, err)) in
        ["zedc run", "executable"]
            .iter()
            .zip(both(&file, &exe, "4611686018427387904"))
    {
        assert_eq!((code, out.as_str()), (Some(3), ""), "{engine}: {err}");
        assert!(
            err.contains(": Text too large for memory: `String("),
            "{engine}: {err}"
        );
    }
}
