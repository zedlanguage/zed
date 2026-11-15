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
    let run = zedc(&["run", &p.file], stdout());
    let native = Command::new("timeout")
        .args(["60", &p.exe])
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
    let rest = "    b = 2^64 + 13;\n    k = 2^64 + (int(m.args[0] else \"\") else 0);\n    \
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
