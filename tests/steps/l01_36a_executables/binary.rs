//! `zedc build`, run as a user runs it (DESIGN.md step L1.36a): it builds an executable that
//! runs, and a missing linker or runtime library, or a wrong command line, is a usage error,
//! status 2, naming what is missing. `crates/zed-native/Cargo.toml` names this test, since
//! only a test of that package can name the executable.
#![cfg(target_os = "linux")]

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

/// A directory of its own for this test, under the test target's scratch directory; files in
/// it are overwritten by each run, never deleted.
fn dir() -> PathBuf {
    let d = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("l01_36a_binary");
    std::fs::create_dir_all(&d).unwrap();
    d
}

/// The runtime library this test was built with: Cargo writes it only beside this
/// executable, under its hash, so the newest `libzed_native-*.a` there is the current one.
fn runtime() -> PathBuf {
    let exe = std::env::current_exe().unwrap();
    let deps = exe.parent().unwrap();
    std::fs::read_dir(deps)
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| {
            let name = p.file_name().unwrap().to_string_lossy();
            name.starts_with("libzed_native-") && name.ends_with(".a")
        })
        .max_by_key(|p| std::fs::metadata(p).unwrap().modified().unwrap())
        .unwrap_or_else(|| panic!("no libzed_native-*.a in {}", deps.display()))
}

/// `zedc build src -o out` with the runtime library and linker `cc` named in the environment,
/// each replaced by `env` where it names one.
fn zedc_build(src: &Path, out: &Path, env: &[(&str, &str)]) -> Output {
    let mut c = Command::new(env!("CARGO_BIN_EXE_zedc"));
    c.arg("build").arg(src).arg("-o").arg(out);
    c.env("ZED_RUNTIME", runtime()).env("CC", "cc");
    for (k, v) in env {
        c.env(k, v);
    }
    c.output().unwrap()
}

/// The status and standard error of `out`, and that it wrote nothing to standard output.
fn failed(out: &Output) -> (Option<i32>, String) {
    assert_eq!(String::from_utf8_lossy(&out.stdout), "");
    (
        out.status.code(),
        String::from_utf8(out.stderr.clone()).unwrap(),
    )
}

#[test]
fn a_built_executable_runs() {
    let d = dir();
    let src = d.join("hello.zed");
    std::fs::write(
        &src,
        "main(args: CommandLine) -> (stdout: Lines) {\n  \
         stdout <- \"Hello, ${args[1] else \"world\"}!\";\n}\n",
    )
    .unwrap();
    let exe = d.join("hello");
    let out = zedc_build(&src, &exe, &[]);
    assert_eq!(failed(&out), (Some(0), String::new()));
    let ran = Command::new(&exe).args(["--", "Ann"]).output().unwrap();
    assert_eq!(
        (ran.status.code(), String::from_utf8(ran.stdout).unwrap()),
        (Some(0), "Hello, Ann!\n".to_string())
    );
    // The object file the link reads is not left behind.
    assert!(!d.join("hello.zed.o").exists());
}

#[test]
fn a_missing_tool_is_a_usage_error_naming_it() {
    let d = dir();
    let src = d.join("quiet.zed");
    std::fs::write(&src, "main() -> (stdout: Lines) {\n  stdout <- \"x\";\n}\n").unwrap();
    let out = d.join("quiet");
    let missing = d.join("no-such-runtime.a");
    assert_eq!(
        failed(&zedc_build(
            &src,
            &out,
            &[("ZED_RUNTIME", missing.to_str().unwrap())]
        )),
        (
            Some(2),
            format!(
                "the runtime library {} is missing: build it with `cargo build -p zed-native`, \
                 or name it in ZED_RUNTIME\n",
                missing.display()
            )
        )
    );
    assert_eq!(
        failed(&zedc_build(&src, &out, &[("CC", "no-such-cc")])),
        (
            Some(2),
            "the linker `no-such-cc` is missing: install a C compiler, or name one in CC\n"
                .to_string()
        )
    );
    // A failed link leaves no object file.
    assert!(!d.join("quiet.zed.o").exists());
}

#[test]
fn a_wrong_command_line_is_a_usage_error() {
    let usage = (Some(2), "usage: zedc build <file> -o <out>\n".to_string());
    for words in [
        &["build"][..],
        &["build", "a.zed"],
        &["build", "a.zed", "-x", "out"],
    ] {
        let out = Command::new(env!("CARGO_BIN_EXE_zedc"))
            .args(words)
            .output()
            .unwrap();
        assert_eq!(failed(&out), usage, "{words:?}");
    }
}

#[test]
fn a_rejected_program_builds_nothing() {
    let d = dir();
    let src = d.join("rejected.zed");
    std::fs::write(
        &src,
        "main() -> (stdout: Lines) {\n  stdout <- nothing;\n}\n",
    )
    .unwrap();
    let out = d.join("rejected");
    let (status, stderr) = failed(&zedc_build(&src, &out, &[]));
    assert_eq!(status, Some(1), "{stderr}");
    assert!(stderr.starts_with(src.to_str().unwrap()), "{stderr}");
    assert!(!out.exists());
}
