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

/// The runtime library built with `zedc`: of the `libzed_native-<hash>.a` Cargo keeps beside
/// this test, one for each set of features it has built zed-native with, the one holding the
/// symbol `zedc` holds, not the newest.
fn runtime() -> PathBuf {
    let exe = std::env::current_exe().unwrap();
    zed_native::link::runtime_of(Path::new(env!("CARGO_BIN_EXE_zedc")), exe.parent().unwrap())
        .unwrap_or_else(|e| panic!("{e}"))
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

/// The working directories of builds of `name` in `d` (`<name>.zed-build.<pid>.<k>`), and the
/// object file that builds before LINK-obj-leftover wrote (`<name>.zed.o`).
fn working(d: &Path, name: &str) -> Vec<String> {
    let (prefix, old) = (format!("{name}.zed-build."), format!("{name}.zed.o"));
    let mut names: Vec<String> = std::fs::read_dir(d)
        .unwrap()
        .map(|e| e.unwrap().file_name().into_string().unwrap())
        .filter(|n| n.starts_with(&prefix) || *n == old)
        .collect();
    names.sort_unstable();
    names
}

/// Writes `bytes` at `path` as a runnable file, in a process of its own: a file this process
/// held open for writing could be inherited by a child that another test thread forks at that
/// moment, and running it would then fail with "Text file busy" (ETXTBSY). As
/// `tests/steps/l01_36b_link_identity`'s `script` does.
fn install(path: &Path, bytes: &[u8]) {
    let text = path.with_extension("bytes");
    std::fs::write(&text, bytes).unwrap();
    let installed = Command::new("install")
        .arg("-m")
        .arg("755")
        .arg(&text)
        .arg(path)
        .status()
        .unwrap();
    assert!(
        installed.success(),
        "install {}: {installed}",
        path.display()
    );
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
    // The directory the link works in, with the object file it reads, is not left behind.
    assert_eq!(working(&d, "hello"), Vec::<String>::new());
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
                "zedc cannot build an executable: the runtime library {}, which every executable \
                 is linked with, is missing. Repairs: build it with `cargo build -p zed-native`, \
                 which writes it beside zedc, or name its path in the environment variable \
                 ZED_RUNTIME\n",
                missing.display()
            )
        )
    );
    assert_eq!(
        failed(&zedc_build(&src, &out, &[("CC", "no-such-cc")])),
        (
            Some(2),
            "zedc cannot link an executable: the linker `no-such-cc` is missing. Repairs: \
             install a C compiler, or name one in the environment variable CC\n"
                .to_string()
        )
    );
    // A failed link leaves no object file.
    assert_eq!(working(&d, "quiet"), Vec::<String>::new());
}

/// A runtime library that is not the one built with `zedc` (here an archive holding nothing,
/// so not `zedc`'s build) is a usage error naming it:
/// linking it would join code generated by one build to a runtime of another.
#[test]
fn a_runtime_library_of_another_build_is_a_usage_error() {
    let d = dir();
    let src = d.join("other.zed");
    std::fs::write(&src, "main() -> (stdout: Lines) {\n  stdout <- \"x\";\n}\n").unwrap();
    let other = d.join("libzed_native-other.a");
    std::fs::write(&other, b"!<arch>\n").unwrap();
    let out = d.join("other");
    assert_eq!(
        failed(&zedc_build(
            &src,
            &out,
            &[("ZED_RUNTIME", other.to_str().unwrap())]
        )),
        (
            Some(2),
            format!(
                "zedc cannot build an executable: the runtime library {} comes from another build \
                 of zed-native than this zedc, {}, and code one build makes does not run with \
                 another's library. Repairs: build both again with `cargo build -p zed-native`, \
                 or name the library built with this zedc in ZED_RUNTIME\n",
                other.display(),
                env!("CARGO_BIN_EXE_zedc")
            )
        )
    );
    assert!(!out.exists());
    assert_eq!(working(&d, "other"), Vec::<String>::new());
}

/// `zedc` with its symbol table removed, as `strip` removes it, still builds: the build it
/// holds is read from its section `.zed_native.build`, which stays (NATIVE-build-id). The
/// copy is stripped here with the `object` crate, so the test needs no `strip` program.
#[test]
fn a_stripped_zedc_builds() {
    use object::Object as _;
    let d = dir();
    let bytes = std::fs::read(env!("CARGO_BIN_EXE_zedc")).unwrap();
    let mut elf = object::build::elf::Builder::read(&*bytes).unwrap();
    for s in &mut elf.sections {
        if [&b".symtab"[..], b".strtab"].contains(&&*s.name) {
            s.delete = true;
        }
    }
    for s in &mut elf.symbols {
        s.delete = true;
    }
    let mut stripped = Vec::new();
    elf.write(&mut stripped).unwrap();
    // No symbol is left, so `link::build`'s, which named the build before, is gone too.
    assert_eq!(
        object::File::parse(&*stripped).unwrap().symbols().count(),
        0
    );
    let zedc = d.join("zedc-stripped");
    install(&zedc, &stripped);
    let src = d.join("stripped.zed");
    std::fs::write(
        &src,
        "main() -> (stdout: Lines) {\n  stdout <- \"stripped\";\n}\n",
    )
    .unwrap();
    let exe = d.join("stripped");
    let out = Command::new(&zedc)
        .arg("build")
        .arg(&src)
        .arg("-o")
        .arg(&exe)
        .env("ZED_RUNTIME", runtime())
        .env("CC", "cc")
        .output()
        .unwrap();
    assert_eq!(failed(&out), (Some(0), String::new()));
    let ran = Command::new(&exe).output().unwrap();
    assert_eq!(
        (ran.status.code(), String::from_utf8(ran.stdout).unwrap()),
        (Some(0), "stripped\n".to_string())
    );
}

#[test]
fn a_wrong_command_line_is_a_usage_error() {
    let usage = (Some(2), format!("{}\n", zed_native::link::USAGE));
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

/// A build stopped by SIGKILL while its linker runs leaves its working directory, with the
/// object file in it; the next build to the same output succeeds and removes it
/// (LINK-obj-leftover). The driver here stands for a slow linker: it says when the link has
/// begun, and waits until the build that ran it has ended, then fails.
#[test]
fn a_build_killed_while_linking_blocks_no_later_build() {
    let d = dir();
    let src = d.join("killed.zed");
    std::fs::write(
        &src,
        "main() -> (stdout: Lines) {\n  stdout <- \"again\";\n}\n",
    )
    .unwrap();
    let (out, linking) = (d.join("killed"), d.join("killed.linking"));
    // An executable of the run before records the key, and the build would not link.
    for f in [&out, &linking] {
        match std::fs::remove_file(f) {
            Err(e) if e.kind() != std::io::ErrorKind::NotFound => panic!("{}: {e}", f.display()),
            _ => {}
        }
    }
    let waits = d.join("cc-waits");
    install(
        &waits,
        format!(
            "#!/bin/sh\ncase \"$1\" in --version|-Wl,--version) exec cc \"$@\" ;; esac\n\
             : > '{}'\nwhile kill -0 \"$PPID\" 2>/dev/null; do sleep 0.01; done\nexit 1\n",
            linking.display()
        )
        .as_bytes(),
    );
    let mut build = Command::new(env!("CARGO_BIN_EXE_zedc"))
        .arg("build")
        .arg(&src)
        .arg("-o")
        .arg(&out)
        .env("ZED_RUNTIME", runtime())
        .env("CC", &waits)
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .spawn()
        .unwrap();
    while !linking.exists() {
        if let Some(status) = build.try_wait().unwrap() {
            panic!("the build ended before its link began: {status}");
        }
        std::thread::sleep(std::time::Duration::from_millis(10));
    }
    build.kill().unwrap();
    build.wait().unwrap();
    let left = working(&d, "killed");
    assert_eq!(left.len(), 1, "{left:?}");
    assert!(d.join(&left[0]).join("killed.o").is_file(), "{left:?}");
    assert!(!out.exists());

    assert_eq!(
        failed(&zedc_build(&src, &out, &[])),
        (Some(0), String::new())
    );
    let ran = Command::new(&out).output().unwrap();
    assert_eq!(
        (ran.status.code(), String::from_utf8(ran.stdout).unwrap()),
        (Some(0), "again\n".to_string())
    );
    assert_eq!(working(&d, "killed"), Vec::<String>::new());
}

/// A function that pushes to a port and is used as a value, here passed to another function
/// that calls it, runs under `zedc run`; `zedc build` refuses it with status 1, naming the
/// function, its port and the repairs, and writes nothing.
#[test]
fn a_pushing_function_used_as_a_value_is_refused_by_the_build() {
    let d = dir();
    let src = d.join("passed.zed");
    std::fs::write(
        &src,
        "say(positional s) -> (stdout: Lines) {\n  stdout <- s;\n}\n\
         apply(g, s) = g(s);\n\
         main() -> (stdout: Lines) {\n  a = apply(g: say, s: \"one\");\n}\n",
    )
    .unwrap();
    let out = d.join("passed");
    // A file left by an earlier run would hide a build that wrote one.
    let _ = std::fs::remove_file(&out);
    let (status, stderr) = failed(&zedc_build(&src, &out, &[]));
    assert_eq!(status, Some(1), "{stderr}");
    assert_eq!(
        stderr,
        format!(
            "{}: `zedc build` cannot compile this program: the function `say`, of 1 \
             parameter, reads or pushes the port `stdout`, and the program uses `say` as a \
             value (it passes, stores or returns it) instead of calling it. Built code carries \
             the state of a port only through a call that names the function, so `say` can \
             only be called by its name. Repairs: call `say` by its name where it is used; \
             move the reads and pushes out of `say` and pass the values in or out; or run the \
             program with `zedc run`, which has no such limit\n",
            src.display()
        )
    );
    assert!(!out.exists());
}
