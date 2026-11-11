//! The zedc executable, run as a user runs it, given environment variables (DESIGN.md step
//! L1.19c): a variable reaches `zedc run` as the system gives it, so a value that is not UTF-8
//! is a usage error naming the variable, and a replay reads the recorded values with the
//! variables unset. `crates/zed-native/Cargo.toml` names this test, since only a test of that
//! package can name the executable.

use std::ffi::OsString;
use std::os::unix::ffi::OsStringExt;
use std::path::PathBuf;
use std::process::{Command, Output, Stdio};

const READ: &str = "main(m: MainArgs) {\n  \
    m.stdout <- m.env[\"ZED_ENV_TEST\"] else \"unset\";\n}\n";

/// What `zedc run`, and an executable `zedc build` wrote, print when [`READ`] reads a value
/// that is not UTF-8.
const NOT_UTF8: &str = "the program reads the environment variable `ZED_ENV_TEST`, and its value \
    is not UTF-8 text, which a Zed string must be. Set `ZED_ENV_TEST` to UTF-8 text before \
    running, or unset it, which the program reads as `#notFound`.\n";

/// A file of its own for test `name` and `what`.
fn file(name: &str, what: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("environment_{name}_{}.{what}", std::process::id()))
}

/// `zedc <words>` with `ZED_ENV_TEST` set to `value`, or unset when it is `None`.
fn zedc_run(words: &[&std::ffi::OsStr], value: Option<OsString>) -> Output {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_zedc"));
    cmd.args(words).stdin(Stdio::null());
    match value {
        Some(v) => cmd.env("ZED_ENV_TEST", v),
        None => cmd.env_remove("ZED_ENV_TEST"),
    };
    cmd.output().unwrap()
}

#[test]
fn zedc_gives_main_a_variable_and_replays_it_unset() {
    let (prog, rec) = (file("replay", "zed"), file("replay", "rec"));
    std::fs::write(&prog, READ).unwrap();
    let ran = zedc_run(
        &[
            "run".as_ref(),
            prog.as_ref(),
            "--record".as_ref(),
            rec.as_ref(),
        ],
        Some("from the shell".into()),
    );
    assert_eq!(
        ran.status.code(),
        Some(0),
        "{}",
        String::from_utf8_lossy(&ran.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&ran.stdout), "from the shell\n");
    let unset = zedc_run(&["run".as_ref(), prog.as_ref()], None);
    assert_eq!(String::from_utf8_lossy(&unset.stdout), "unset\n");
    let replayed = zedc_run(&["replay".as_ref(), prog.as_ref(), rec.as_ref()], None);
    assert_eq!(replayed.status.code(), Some(0));
    assert_eq!(
        String::from_utf8_lossy(&replayed.stdout),
        "from the shell\n"
    );
    std::fs::remove_file(&prog).unwrap();
    std::fs::remove_file(&rec).unwrap();
}

#[test]
fn zedc_names_the_variable_that_is_not_utf8() {
    let prog = file("not_utf8", "zed");
    std::fs::write(&prog, READ).unwrap();
    let out = zedc_run(
        &["run".as_ref(), prog.as_ref()],
        Some(OsString::from_vec(vec![b'x', 255])),
    );
    std::fs::remove_file(&prog).unwrap();
    assert_eq!(out.status.code(), Some(2));
    assert_eq!(String::from_utf8_lossy(&out.stderr), NOT_UTF8);
    assert!(out.stdout.is_empty());
}

/// An executable `zedc build` makes from `READ` reads its own process's variables as `zedc run`
/// does, and `zedc replay` replays its record.
#[cfg(target_os = "linux")]
#[test]
fn an_executable_reads_its_own_variables() {
    let (prog, exe, rec) = (file("exe", "zed"), file("exe", "exe"), file("exe", "rec"));
    std::fs::write(&prog, READ).unwrap();
    let test = std::env::current_exe().unwrap();
    let zedc = std::path::Path::new(env!("CARGO_BIN_EXE_zedc"));
    let runtime = zed_native::link::runtime_of(zedc, test.parent().unwrap())
        .unwrap_or_else(|e| panic!("{e}"));
    let built = Command::new(zedc)
        .arg("build")
        .arg(&prog)
        .arg("-o")
        .arg(&exe)
        .env("ZED_RUNTIME", runtime)
        .env("CC", "cc")
        .output()
        .unwrap();
    assert_eq!(
        built.status.code(),
        Some(0),
        "{}",
        String::from_utf8_lossy(&built.stderr)
    );
    let run = |value: Option<OsString>, more: &[&std::ffi::OsStr]| {
        let mut cmd = Command::new(&exe);
        cmd.args(more).stdin(Stdio::null());
        match value {
            Some(v) => cmd.env("ZED_ENV_TEST", v),
            None => cmd.env_remove("ZED_ENV_TEST"),
        };
        cmd.output().unwrap()
    };
    let ran = run(Some("set".into()), &["--record".as_ref(), rec.as_ref()]);
    assert_eq!(
        ran.status.code(),
        Some(0),
        "{}",
        String::from_utf8_lossy(&ran.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&ran.stdout), "set\n");
    assert_eq!(String::from_utf8_lossy(&run(None, &[]).stdout), "unset\n");
    let bad = run(Some(OsString::from_vec(vec![255])), &[]);
    assert_eq!(bad.status.code(), Some(2));
    assert_eq!(String::from_utf8_lossy(&bad.stderr), NOT_UTF8);
    let replayed = zedc_run(&["replay".as_ref(), prog.as_ref(), rec.as_ref()], None);
    assert_eq!(String::from_utf8_lossy(&replayed.stdout), "set\n");
    for f in [&prog, &exe, &rec] {
        std::fs::remove_file(f).unwrap();
    }
}
