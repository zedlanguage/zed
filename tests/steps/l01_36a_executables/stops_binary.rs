//! What a run writes before it stops, under `zedc run` and the executable `zedc build` makes,
//! compared byte for byte (plan row EXE-stdout-before-error): each engine in a child process of
//! its own under `timeout 60`, as a user runs it. DESIGN.md sec:ports: "The writes are
//! committed when the wave ends, `m.stdout` before `m.stderr`, and an error before then writes
//! nothing; ... the first `#ioError` aborts the wave, so the later ports are not written." Each
//! stop path either engine reaches is here: a failure of the body (status 1), a fault (status
//! 3), a nonzero result of `main` after both streams are written, and a failed write of
//! standard output, to a full device and to a pipe whose reader has closed it.
//! `crates/zed-native/Cargo.toml` names this test, since only a test of that package can name
//! the zedc executable.
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
    let d = scratch::process_tmpdir().join("stops_binary");
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

/// `zedc` with `args` under `timeout 60`, its standard output given by `stdout`.
fn zedc(args: &[&str], stdout: Stdio) -> Output {
    Command::new("timeout")
        .arg("60")
        .arg(env!("CARGO_BIN_EXE_zedc"))
        .args(args)
        .env("ZED_RUNTIME", runtime())
        .env("CC", "cc")
        .stdout(stdout)
        .output()
        .unwrap()
}

/// A program built by `zedc build`: its source file, its executable, and the warnings the
/// build wrote to standard error, which `zedc run` writes before its run's own output, since
/// it checks the program each time it runs it.
struct Built {
    file: String,
    exe: String,
    warnings: Vec<u8>,
}

/// The program `src` written to `<name>.zed` and built into the executable `<name>`.
fn program(name: &str, src: &str) -> Built {
    let d = dir();
    let (file, exe) = (d.join(format!("{name}.zed")), d.join(name));
    std::fs::write(&file, src).unwrap();
    let (file, exe) = (file.display().to_string(), exe.display().to_string());
    let built = zedc(&["build", &file, "-o", &exe], Stdio::piped());
    assert_eq!(built.status.code(), Some(0), "building {name}: {built:?}");
    Built {
        file,
        exe,
        warnings: built.stderr,
    }
}

/// A run's status, standard output and standard error, as bytes.
type Ran = (Option<i32>, Vec<u8>, Vec<u8>);

/// What `zedc run` and the executable each give with standard output given by `stdout` (made
/// anew for each), and standard error and, where `stdout` is piped, standard output read apart.
fn both(p: &Built, stdout: impl Fn() -> Stdio) -> [Ran; 2] {
    both_with(p, stdout, &[])
}

/// [`both`], with the variables `env` added to each engine's environment.
fn both_with(p: &Built, stdout: impl Fn() -> Stdio, env: &[(&str, &str)]) -> [Ran; 2] {
    let run = Command::new("timeout")
        .arg("60")
        .arg(env!("CARGO_BIN_EXE_zedc"))
        .args(["run", &p.file])
        .envs(env.iter().copied())
        .stdout(stdout())
        .output()
        .unwrap();
    let native = Command::new("timeout")
        .args(["60", &p.exe])
        .envs(env.iter().copied())
        .stdout(stdout())
        .output()
        .unwrap();
    [run, native].map(|o| (o.status.code(), o.stdout, o.stderr))
}

/// Both engines with standard output and standard error on one pipe, as `2>&1` gives them: the
/// status, and the bytes in the order the run wrote them.
fn merged(p: &Built) -> [(Option<i32>, Vec<u8>); 2] {
    let one = |cmd: &mut Command| {
        let (reader, writer) = std::io::pipe().unwrap();
        cmd.stdout(writer.try_clone().unwrap()).stderr(writer);
        let mut child = cmd.spawn().unwrap();
        // `cmd` holds the parent's copies of the write end; replacing them closes those, so
        // the read ends when the child's last copy closes.
        cmd.stdout(Stdio::null()).stderr(Stdio::null());
        let mut bytes = Vec::new();
        std::io::Read::read_to_end(&mut &reader, &mut bytes).unwrap();
        (child.wait().unwrap().code(), bytes)
    };
    [
        one(Command::new("timeout")
            .arg("60")
            .arg(env!("CARGO_BIN_EXE_zedc"))
            .args(["run", &p.file])),
        one(Command::new("timeout").args(["60", &p.exe])),
    ]
}

/// The two engines' runs are the same byte for byte, but for the build's warnings, which
/// `zedc run` writes first; and the executable's status and standard output are `expected`'s,
/// its standard error holding `expected.2`.
fn agree(name: &str, p: &Built, [run, native]: [Ran; 2], expected: (Option<i32>, &str, &str)) {
    let text = |b: &[u8]| String::from_utf8_lossy(b).into_owned();
    let warned = [p.warnings.as_slice(), &native.2].concat();
    assert_eq!(
        (run.0, text(&run.1), text(&run.2)),
        (native.0, text(&native.1), text(&warned)),
        "{name}: zedc run against the executable after the build's warnings"
    );
    let (code, out, err) = (native.0, text(&native.1), text(&native.2));
    assert_eq!(
        (code, out.as_str()),
        (expected.0, expected.1),
        "{name}: {err}"
    );
    assert!(err.contains(expected.2), "{name}: {err}");
}

/// `main` writing `first line` to standard output, then `rest` (statements, each on a line of
/// its own).
fn writes_then(rest: &str) -> String {
    format!("main(m: MainArgs) {{\n    m.stdout <- \"first line\";\n{rest}}}\n")
}

#[test]
fn a_failure_after_a_write_writes_the_same_on_both_engines() {
    // A failure of the body, status 1: a string of 2^63 bytes joined to itself, too long for a
    // string. `d0` comes from the arguments, so the checker cannot fold it.
    let mut rest = "    d0 = \"a\" ++ String(m.args);\n".to_string();
    for k in 1..=63 {
        rest += &format!("    d{k} = d{} ++ d{};\n", k - 1, k - 1);
    }
    rest += "    m.stderr <- String(len(d63));\n";
    let p = program("failure", &writes_then(&rest));
    agree(
        "failure",
        &p,
        both(&p, Stdio::piped),
        (Some(1), "", "String too long: `d62 ++ d62`"),
    );
}

#[test]
fn a_fault_after_a_write_writes_the_same_on_both_engines() {
    // A fault, status 3: `b ^ k`, a number of more than 2^70 bits, its exponent from the
    // arguments, so the checker cannot fold it.
    let rest = "    b = 2^64 + 13;\n    k = 2^64 + (int(m.args[0] else #outOfBounds -> \"\") else #invalid -> 0);\n    \
                m.stderr <- if k >= 0 { String(b ^ k) } else { \"\" };\n";
    let p = program("fault", &writes_then(rest));
    agree(
        "fault",
        &p,
        both(&p, Stdio::piped),
        (Some(3), "", "Number too large for memory: `b ^ k`"),
    );
}

#[test]
fn a_bug_of_zedc_in_the_run_stops_both_engines_alike() {
    // A bug of zedc, which no program reaches on purpose: a debug build's run stops at a panic
    // where `ZEDC_TEST_BUG` is set (plan row EXE-panic-status). `zedc run` panics in its own
    // code; the executable inside a runtime hook its machine code called, where an unwinding
    // panic would abort the process (status 134), and under a memory limit the limit's
    // SIGABRT handler would report a memory fault. Both are a fault of the run (DESIGN.md
    // sec:ports: "a fault of the run exits with 3"; sec:ffi: "3 for a fault or a limit"),
    // with one report, and the wave commits nothing.
    for (name, limit) in [
        ("bug", ""),
        ("bug_limited", "@limits(memory: 1073741824)\n"),
    ] {
        let rest = "    m.stderr <- String(m.args);\n";
        let p = program(name, &format!("{limit}{}", writes_then(rest)));
        // The switch exists only where debug assertions are on (crates/zedc/src/run.rs), so a
        // release build of the tests checks the second half only.
        if cfg!(debug_assertions) {
            agree(
                name,
                &p,
                both_with(&p, Stdio::piped, &[("ZEDC_TEST_BUG", "1")]),
                (
                    Some(3),
                    "",
                    "the run stopped because of a bug in zedc, not in your program",
                ),
            );
        }
        // Without the variable the same build runs to its end.
        agree(
            name,
            &p,
            both(&p, Stdio::piped),
            (Some(0), "first line\n", "{}\n"),
        );
    }
}

/// The report of a bug in zedc (plan row MSG-bug-report-plain, author 2026-11-09 and
/// 2026-11-15) says in plain words what happened and which declaration zedc was at work on,
/// asks for the report, and then puts what zedc's developers need in a details block: zedc's
/// version as `zedc` with no arguments prints it, the stage, the declaration, what zedc
/// expected (the panic's text) and zedc's own file and line. Both engines mark the run of
/// `main` (`zedc::run`), so both name `main` and the stage `run`, and neither names a unit:
/// the program's content address names the program.
#[test]
fn a_bug_report_names_the_declaration_and_puts_the_version_in_a_details_block() {
    // The switch exists only where debug assertions are on (crates/zedc/src/run.rs).
    if !cfg!(debug_assertions) {
        return;
    }
    let p = program(
        "bug_details",
        &writes_then("    m.stderr <- String(m.args);\n"),
    );
    let version = zedc(&[], Stdio::piped());
    let version = String::from_utf8(version.stdout).unwrap();
    let version = version
        .trim()
        .strip_prefix("zedc ")
        .expect("`zedc` prints its version");
    let ran = both_with(&p, Stdio::piped, &[("ZEDC_TEST_BUG", "1")]);
    for (engine, (status, _, err)) in ["zedc run", "executable"].into_iter().zip(ran) {
        let err = String::from_utf8_lossy(&err).into_owned();
        assert_eq!(status, Some(3), "{engine}: {err}");
        let (message, details) = err
            .split_once("\nDetails for the report:\n")
            .unwrap_or_else(|| panic!("{engine}: no details block: {err}"));
        // The message is plain: no zedc file, no panic text, no version.
        assert!(
            message.starts_with("the run stopped because of a bug in zedc, not in your program.")
                && message.contains("\nPlease report it at ")
                && !message.contains(".rs")
                && !message.contains(version),
            "{engine}: {err}"
        );
        let lines: Vec<&str> = details.lines().collect();
        assert_eq!(
            lines.first().copied(),
            Some(&*format!("  zedc version: {version}")),
            "{engine}: {err}"
        );
        assert!(
            lines.iter().any(|l| l.starts_with("  expected: "))
                && lines
                    .iter()
                    .any(|l| l.starts_with("  in zedc at: ") && l.contains(".rs, line ")),
            "{engine}: {err}"
        );
        assert!(
            message.contains("while it was at work on the declaration `main`.")
                && lines.contains(&"  stage: run")
                && lines.contains(&"  declaration: main"),
            "{engine}: {err}"
        );
    }
}

#[test]
fn a_bug_of_zedc_in_the_run_stops_the_run_not_the_build_stage_before_it() {
    // `k` calls `sq` inside `map`, a family operation, so the build stage runs it as written
    // under the program's definitions (zedc-stage's `Mixer::run_under`, which calls the
    // kernel's `Evaluator::run_under`; seen with a probe printed there, 2026-11-15). That run
    // is the build's, not the program's, and `ZEDC_TEST_BUG` stops only the program's run
    // (plan row PROOF-run-under-test-bug): `zedc run`, which stages the program in the same
    // process, reports the bug at the run of `main`, as the executable does, and not the
    // kernel's check that a run under the definitions is never asked to stop. A stage that
    // gave that run an evaluator set to stop made `zedc run` exit with 101 there, which this
    // test caught.
    let src = "sq(positional n: int) = n * n;\nk = [1, 2, 3].map(x -> sq(x));\n";
    let rest = "    m.stderr <- String(k[0]);\n";
    let p = program("bug_staged", &format!("{src}{}", writes_then(rest)));
    // The switch exists only where debug assertions are on (crates/zedc/src/run.rs).
    if cfg!(debug_assertions) {
        let ran = both_with(&p, Stdio::piped, &[("ZEDC_TEST_BUG", "1")]);
        let stderr = String::from_utf8_lossy(&ran[0].2).into_owned();
        assert!(!stderr.contains("run under globals"), "{stderr}");
        agree(
            "bug_staged",
            &p,
            ran,
            (
                Some(3),
                "",
                "the run stopped because of a bug in zedc, not in your program",
            ),
        );
    }
    agree(
        "bug_staged",
        &p,
        both(&p, Stdio::piped),
        (Some(0), "first line\n", "1\n"),
    );
}

/// The program address the record of a run names, the run made by `cmd` (`zedc run …` or an
/// executable) with `--record <rec>` added; the run writes `first line` and exits with 0.
fn recorded(cmd: &[&str], rec: &Path) -> String {
    let ran = Command::new("timeout")
        .arg("60")
        .args(cmd)
        .args(["--record", rec.to_str().unwrap()])
        .output()
        .unwrap();
    assert_eq!(ran.status.code(), Some(0), "{cmd:?}: {ran:?}");
    let record = zedc::run::Record::from_bytes(&std::fs::read(rec).unwrap()).unwrap();
    record
        .program
        .expect("a record names its program")
        .to_string()
}

#[test]
fn a_bug_of_zedc_in_the_run_names_the_program_on_both_engines() {
    // DESIGN.md sec:checking_in_zed: "the run reports it as a compiler bug with the build's
    // content address" (plan row EXE-bug-report-address). The address is the program's, which
    // a record of the run names: each read of the build's target or an option is replaced by
    // its literal before the address is taken, so an option the program reads gives the build
    // another address, and the target is the host's.
    let d = dir().join("bug_address");
    std::fs::create_dir_all(&d).unwrap();
    std::fs::write(d.join("zed.manifest"), "options = \"fast, slow\";\n").unwrap();
    let file = d.join("main.zed");
    std::fs::write(
        &file,
        writes_then(
            "    m.stderr <- if build.options.fast { \"fast\" } else { String(m.args) };\n",
        ),
    )
    .unwrap();
    let file = file.to_str().unwrap();
    let zedc_exe = env!("CARGO_BIN_EXE_zedc");
    let rec = d.join("run.rec");
    let mut seen = Vec::new();
    for on in [&[][..], &["--option", "fast"], &["--option", "slow"]] {
        let exe = d.join(format!("main{}", on.join("")));
        let exe = exe.to_str().unwrap();
        let built = zedc(
            &[&["build", file, "-o", exe][..], on].concat(),
            Stdio::piped(),
        );
        assert_eq!(built.status.code(), Some(0), "building {on:?}: {built:?}");
        let run = [&[zedc_exe, "run", file][..], on].concat();
        let address = recorded(&run, &rec);
        // The executable's record names the address `zedc run`'s does.
        assert_eq!(recorded(&[exe], &rec), address, "{on:?}");
        seen.push(address.clone());
        // The switch exists only where debug assertions are on (crates/zedc/src/run.rs).
        if cfg!(debug_assertions) {
            for (engine, cmd) in [("zedc run", run), ("executable", vec![exe])] {
                let ran = Command::new("timeout")
                    .arg("60")
                    .args(&cmd)
                    .env("ZEDC_TEST_BUG", "1")
                    .output()
                    .unwrap();
                let err = String::from_utf8_lossy(&ran.stderr);
                assert_eq!(ran.status.code(), Some(3), "{engine} {on:?}: {err}");
                assert!(
                    err.contains(&format!(
                        "The run was of the program whose content address is {address}, the \
                         address a record of its run names."
                    )),
                    "{engine} {on:?}: {err}"
                );
            }
        }
    }
    // `fast`, which the program reads, changes the address; `slow`, which it does not, does not.
    assert_ne!(seen[0], seen[1]);
    assert_eq!(seen[0], seen[2]);
}

#[test]
fn a_nonzero_result_keeps_both_streams_in_order_on_both_engines() {
    let src = "main(m: MainArgs) -> int {\n    m.stdout <- \"first line\";\n    \
               m.stderr <- \"err line\";\n    7\n}\n";
    let p = program("result", src);
    assert_eq!(
        String::from_utf8_lossy(&p.warnings),
        "",
        "result: the build warned"
    );
    agree(
        "result",
        &p,
        both(&p, Stdio::piped),
        (Some(7), "first line\n", "err line\n"),
    );
    // One pipe for both streams: standard output's line comes first, as committed.
    for (engine, got) in ["zedc run", "executable"].iter().zip(merged(&p)) {
        assert_eq!(
            (got.0, String::from_utf8_lossy(&got.1).into_owned()),
            (Some(7), "first line\nerr line\n".into()),
            "{engine}"
        );
    }
}

#[test]
fn a_failed_write_of_standard_output_is_reported_the_same_on_both_engines() {
    let src =
        "main(m: MainArgs) {\n    m.stdout <- \"first line\";\n    m.stderr <- \"after\";\n}\n";
    let p = program("write_failed", src);
    // A full device: the write fails with ENOSPC, and standard error is not written.
    let full = || Stdio::from(std::fs::File::create("/dev/full").unwrap());
    let [run, native] = both(&p, full);
    assert!(
        !String::from_utf8_lossy(&native.2).contains("after"),
        "full: {native:?}"
    );
    agree(
        "full",
        &p,
        [run, native],
        (Some(1), "", "No space left on device"),
    );
    // A pipe whose reader has closed it: the write fails with EPIPE, reported as any failed
    // write is. Before EXE-stdout-before-error the executable was killed by SIGPIPE, with no
    // status and nothing on standard error.
    let closed = || {
        let (reader, writer) = std::io::pipe().unwrap();
        drop(reader);
        Stdio::from(writer)
    };
    let [run, native] = both(&p, closed);
    assert!(
        !String::from_utf8_lossy(&native.2).contains("after"),
        "closed pipe: {native:?}"
    );
    agree(
        "closed pipe",
        &p,
        [run, native],
        (Some(1), "", "Broken pipe"),
    );
}
