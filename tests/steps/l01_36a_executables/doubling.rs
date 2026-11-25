//! A program that doubles a string, `s1 = s0 ++ s0` and on, 62 and 63 times (plan row
//! BUILD-doubling-60s), built and run as a user does: `zedc build`, `zedc run` and the
//! executable, each in a child process under `timeout 60`. The string doubled 62 times is
//! 2^63 bytes held in a few thousand shared nodes. The build wrote its bytes out, and hashed
//! them, for over 60 s; the executable compared two such constants byte by byte when it
//! started; and `zedc run` compared `s61 < s62` byte by byte. Each now takes time in the
//! nodes. Doubled 63 times the string is past the longest a length can hold, and the run
//! stops at the join with the same message under `zedc run` and the executable.
//! `crates/zed-native/Cargo.toml` names this test, since only a test of that package can name
//! the zedc executable.
#![cfg(target_os = "linux")]

/// This process's scratch directory, as the step tests have it. A test target of zed-native
/// cannot depend on zed-tests, so the module is compiled in; a target may use part of it.
#[allow(dead_code)]
#[path = "../../src/scratch.rs"]
mod scratch;

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

/// A directory of its own for the calling test, under the test target's scratch directory,
/// claimed by `scratch`; files in it are overwritten by each run, never deleted.
fn dir() -> PathBuf {
    scratch::test_dir("doubling_binary")
}

/// The runtime library built with `zedc`: of the `libzed_native-<hash>.a` Cargo keeps beside
/// this test, the one holding the symbol `zedc` holds.
fn runtime() -> PathBuf {
    let exe = std::env::current_exe().unwrap();
    zed_native::link::runtime_of(Path::new(env!("CARGO_BIN_EXE_zedc")), exe.parent().unwrap())
        .unwrap_or_else(|e| panic!("{e}"))
}

/// `program` with `args`, under `timeout 60`.
fn timed(program: &str, args: &[&str]) -> Output {
    Command::new("timeout")
        .arg("60")
        .arg(program)
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

/// `main` doubling `"ab"` `k` times, `s1` to `s<k>`, then writing `tail`.
fn doubling(k: usize, tail: &str) -> String {
    let mut src = String::from("main(m: MainArgs) {\n    s0 = \"ab\";\n");
    for i in 1..=k {
        src.push_str(&format!("    s{i} = s{} ++ s{};\n", i - 1, i - 1));
    }
    src.push_str(&format!("    m.stdout <- {tail};\n}}\n"));
    src
}

/// What `zedc run` and the executable `zedc build` makes each give for `src`, written to
/// `<name>.zed`; the build must succeed.
fn both(name: &str, src: &str) -> [(Option<i32>, String, String); 2] {
    let d = dir();
    let (file, exe) = (d.join(format!("{name}.zed")), d.join(name));
    std::fs::write(&file, src).unwrap();
    let (file, exe) = (file.display().to_string(), exe.display().to_string());
    let zedc = env!("CARGO_BIN_EXE_zedc");
    let built = timed(zedc, &["build", &file, "-o", &exe]);
    assert_eq!(ran(&built).0, Some(0), "building {name}: {:?}", ran(&built));
    [ran(&timed(zedc, &["run", &file])), ran(&timed(&exe, &[]))]
}

#[test]
fn a_string_doubled_62_times_is_built_and_run() {
    let tail = "String(len(s62)) ++ \" \" ++ String(s61 < s62) ++ \" \" \
                ++ String(s62 == s61 ++ \"c\")";
    let want = (
        Some(0),
        "9223372036854775808 true false\n".to_string(),
        String::new(),
    );
    for got in both("doubled62", &doubling(62, tail)) {
        assert_eq!(got, want);
    }
}

#[test]
fn a_string_doubled_63_times_stops_at_the_join() {
    let [run, native] = both("doubled63", &doubling(63, "String(len(s63))"));
    assert_eq!(run.0, Some(1), "{run:?}");
    assert!(
        run.2.contains(
            "String too long: `s62 ++ s62` would join strings of 8.0 EiB and 8.0 EiB, 16 EiB \
             in all; a string holds at most 2^64 - 1 bytes."
        ),
        "{run:?}"
    );
    assert_eq!(native, run);
}
