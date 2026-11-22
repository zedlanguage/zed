//! The run's own close of standard output and standard error (step L7.3p, plan row
//! PORT-stdout-close-status; DESIGN.md sec:ports, "A port's close that fails"), run as a user
//! runs a program: `zedc run` and the executable `zedc build` makes, each in a child process.
//! A close that fails is made by a seccomp filter the child installs before `exec`, which
//! answers `close` of the descriptors a test names with `EIO` and runs every other system call
//! (seccomp(2), `SECCOMP_RET_ERRNO`). The filter is installed in the child itself, never around
//! `timeout`, since coreutils' `timeout` closes its own standard output at exit (gnulib
//! `close_stdout`) and would exit with 125 under the filter; the 60 s limit is kept by a thread
//! of the test instead. `crates/zed-native/Cargo.toml` names this test, since only a test of
//! that package can name the zedc executable.
#![cfg(all(target_os = "linux", target_arch = "x86_64"))]

/// This process's scratch directory, as the step tests have it. A test target of zed-native
/// cannot depend on zed-tests, so the module is compiled in; a target may use part of it.
#[allow(dead_code)]
#[path = "../../src/scratch.rs"]
mod scratch;

use std::os::unix::process::CommandExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::mpsc;
use std::time::Duration;

/// A directory of its own for this test, under the test target's scratch directory; files in
/// it are overwritten by each run, never deleted.
fn dir() -> PathBuf {
    let d = scratch::process_tmpdir().join("close_binary");
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

/// The program `src` written to `<name>.zed` and built into the executable `<name>`, with no
/// filter; the paths of both.
fn program(name: &str, src: &str) -> (String, String) {
    let d = dir();
    let (file, exe) = (d.join(format!("{name}.zed")), d.join(name));
    std::fs::write(&file, src).unwrap();
    let (file, exe) = (file.display().to_string(), exe.display().to_string());
    let built = Command::new("timeout")
        .arg("60")
        .arg(env!("CARGO_BIN_EXE_zedc"))
        .args(["build", &file, "-o", &exe])
        .env("ZED_RUNTIME", runtime())
        .env("CC", "cc")
        .output()
        .unwrap();
    assert_eq!(built.status.code(), Some(0), "building {name}: {built:?}");
    (file, exe)
}

/// `AUDIT_ARCH_X86_64` of linux/audit.h, the architecture the filter accepts: `EM_X86_64` (62)
/// with `__AUDIT_ARCH_64BIT` and `__AUDIT_ARCH_LE`. The libc crate does not define it.
const AUDIT_ARCH_X86_64: u32 = 0xC000_003E;

/// Offsets in `struct seccomp_data` (linux/seccomp.h): the system call's number, the
/// architecture, and the low 32 bits of its first argument on a little-endian machine.
const NR: u32 = 0;
const ARCH: u32 = 4;
const ARG0: u32 = 16;

/// The filter program: `close(fd)` of a descriptor in `fds` gives `EIO`, every other call runs.
fn filter(fds: &[u32]) -> Vec<libc::sock_filter> {
    let stmt = |code: u32, k: u32| libc::sock_filter {
        code: code as u16,
        jt: 0,
        jf: 0,
        k,
    };
    let jeq = |k: u32, jt: u8, jf: u8| libc::sock_filter {
        code: (libc::BPF_JMP | libc::BPF_JEQ | libc::BPF_K) as u16,
        jt,
        jf,
        k,
    };
    let load = |at: u32| stmt(libc::BPF_LD | libc::BPF_W | libc::BPF_ABS, at);
    let n = u8::try_from(fds.len()).unwrap();
    // Layout, for n descriptors: 0 load arch; 1 arch?; 2 load nr; 3 close?; 4 load fd; 5 to
    // 4 + n one test per descriptor; 5 + n the jump past the refusal; 6 + n the refusal; 7 + n
    // the allow. A jump at i of offset k lands at i + 1 + k.
    let mut f = vec![
        load(ARCH),
        jeq(AUDIT_ARCH_X86_64, 0, n + 5),
        load(NR),
        jeq(libc::SYS_close as u32, 0, n + 3),
        load(ARG0),
    ];
    for (i, &fd) in fds.iter().enumerate() {
        // At 5 + i, to the refusal at 6 + n.
        f.push(jeq(fd, n - i as u8, 0));
    }
    // No descriptor matched: past the refusal to the allow.
    f.push(stmt(libc::BPF_JMP | libc::BPF_JA, 1));
    f.push(stmt(
        libc::BPF_RET | libc::BPF_K,
        libc::SECCOMP_RET_ERRNO | libc::EIO as u32,
    ));
    f.push(stmt(libc::BPF_RET | libc::BPF_K, libc::SECCOMP_RET_ALLOW));
    f
}

/// How a run ended: its status, standard output (written to a file) and standard error.
type Ran = (Option<i32>, String, String);

/// Runs `cmd` with `close` failing with `EIO` on the descriptors `fds` (none: no filter), its
/// standard output the file `<dir>/<name>.out`, standard error a pipe, killed after 60 s.
fn run(name: &str, mut cmd: Command, fds: &'static [u32]) -> Ran {
    let out_path = dir().join(format!("{name}.out"));
    let out = std::fs::File::create(&out_path).unwrap();
    cmd.stdin(Stdio::null())
        .stdout(Stdio::from(out))
        .stderr(Stdio::piped());
    if !fds.is_empty() {
        let program = filter(fds);
        #[expect(
            unsafe_code,
            reason = "the filter is installed between fork and exec, by prctl"
        )]
        // SAFETY: the closure runs in the child after `fork`, where only async-signal-safe
        // calls are allowed: it calls `prctl` twice and reads `program`, which was built before
        // the fork, so it allocates nothing.
        unsafe {
            cmd.pre_exec(move || {
                let prog = libc::sock_fprog {
                    len: program.len() as u16,
                    filter: program.as_ptr().cast_mut(),
                };
                if libc::prctl(libc::PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) != 0
                    || libc::prctl(
                        libc::PR_SET_SECCOMP,
                        libc::SECCOMP_MODE_FILTER,
                        &prog as *const libc::sock_fprog,
                    ) != 0
                {
                    return Err(std::io::Error::last_os_error());
                }
                Ok(())
            });
        }
    }
    let child = cmd.spawn().unwrap();
    let pid = child.id() as libc::pid_t;
    let (done, ended) = mpsc::channel::<()>();
    let watchdog = std::thread::spawn(move || {
        if ended.recv_timeout(Duration::from_secs(60)).is_err() {
            #[expect(unsafe_code, reason = "kill is a libc call")]
            // SAFETY: `kill` takes a number and touches no memory; the child is not yet
            // waited for, so its pid is not reused.
            unsafe {
                libc::kill(pid, libc::SIGKILL);
            }
        }
    });
    let output = child.wait_with_output().unwrap();
    let _ = done.send(());
    watchdog.join().unwrap();
    (
        output.status.code(),
        std::fs::read_to_string(&out_path).unwrap(),
        String::from_utf8(output.stderr).unwrap(),
    )
}

/// What `zedc run` and the executable give with `close` failing on `fds`, the words `args`
/// after `--`; each run's standard output is the file `<name>.<engine>.out`.
fn both(name: &str, p: &(String, String), args: &[&str], fds: &'static [u32]) -> [Ran; 2] {
    both_with(name, p, args, fds, &[])
}

/// [`both`] with the environment variables `env` set.
fn both_with(
    name: &str,
    (file, exe): &(String, String),
    args: &[&str],
    fds: &'static [u32],
    env: &[(&str, &str)],
) -> [Ran; 2] {
    let mut zedc = Command::new(env!("CARGO_BIN_EXE_zedc"));
    zedc.args(["run", file, "--"])
        .args(args)
        .envs(env.iter().copied());
    let mut native = Command::new(exe);
    native.arg("--").args(args).envs(env.iter().copied());
    [
        run(&format!("{name}.run"), zedc, fds),
        run(&format!("{name}.exe"), native, fds),
    ]
}

/// The row's headline for `EIO`.
const HEADLINE: &str = "Standard output failed when the run closed it: `close(1)` gave EIO, the \
                        device reported an input or output error; output written before it may \
                        be lost.\n";

/// `main` writing "hi" and giving `status`.
fn hi(status: u8) -> String {
    format!("main(m: MainArgs) -> int {{\n  m.stdout <- \"hi\";\n  {status}\n}}\n")
}

/// The whole message on standard error for a failed close of descriptor 1 that was the file
/// `<name>.<engine>.out`.
fn message(name: &str, engine: &str) -> String {
    let path = dir().join(format!("{name}.{engine}.out"));
    format!(
        "{HEADLINE}The run closed standard output, descriptor 1, which was the file `{}`, and \
         the system gave EIO (\"Input/output error\").\nCheck the device or the server that \
         holds the file, and run again. To see the failure in the program and act on it, write \
         the output as a file and read the acknowledgment:\n    ack = main::files[\"out.txt\"] \
         <- text;\n    match ack {{ #ok -> 0, #ioError(op:, path:, why:, text:) -> {{ m.stderr \
         <- \"cannot ${{op}} ${{path}}: ${{text}}\"; 1 }} }}\n",
        path.display()
    )
}

const ENGINES: [&str; 2] = ["run", "exe"];

#[test]
fn a_failed_close_of_standard_output_turns_status_0_into_1_with_the_row() {
    let p = program("hi0", &hi(0));
    for (engine, got) in ENGINES.iter().zip(both("hi0", &p, &[], &[1])) {
        assert_eq!(
            got,
            (Some(1), "hi\n".into(), message("hi0", engine)),
            "{engine}"
        );
    }
}

#[test]
fn a_failed_close_of_standard_output_keeps_the_status_main_gave() {
    let p = program("hi2", &hi(2));
    for (engine, got) in ENGINES.iter().zip(both("hi2", &p, &[], &[1])) {
        assert_eq!(
            got,
            (Some(2), "hi\n".into(), message("hi2", engine)),
            "{engine}"
        );
    }
}

#[test]
fn a_failed_close_of_standard_error_turns_status_0_into_1_and_writes_nothing() {
    let p = program("hi0e", &hi(0));
    for (engine, got) in ENGINES.iter().zip(both("hi0e", &p, &[], &[2])) {
        assert_eq!(got, (Some(1), "hi\n".into(), String::new()), "{engine}");
    }
    // Both failing: the row for descriptor 1, and the status 1 once.
    for (engine, got) in ENGINES.iter().zip(both("hi0e", &p, &[], &[1, 2])) {
        assert_eq!(
            got,
            (Some(1), "hi\n".into(), message("hi0e", engine)),
            "{engine}"
        );
    }
}

#[test]
fn with_no_failed_close_a_run_exits_with_its_status_and_no_message() {
    for (name, status) in [("ok0", 0), ("ok2", 2)] {
        let p = program(name, &hi(status));
        for (engine, got) in ENGINES.iter().zip(both(name, &p, &[], &[])) {
            assert_eq!(
                got,
                (Some(i32::from(status)), "hi\n".into(), String::new()),
                "{engine}"
            );
        }
    }
    // A filter on another descriptor changes nothing: the filter fails only what it names.
    let p = program("ok0f", &hi(0));
    for (engine, got) in ENGINES.iter().zip(both("ok0f", &p, &[], &[7])) {
        assert_eq!(got, (Some(0), "hi\n".into(), String::new()), "{engine}");
    }
}

/// `main` under `limit`, writing `String(<b> ^ k)` for the `int` `k` of its first argument, as
/// in `limits_binary.rs`.
fn power_program(limit: &str, b: u128) -> String {
    format!(
        "{limit}\nmain(m: MainArgs) {{\n    k = int(m.args[0] else #outOfBounds -> \"\") else #invalid -> 0;\n    \
         m.stdout <- String(if k >= 0 {{ {b} ^ k }} else {{ 0 }});\n}}\n"
    )
}

#[test]
fn a_run_stopped_by_its_memory_limit_keeps_status_3_and_the_row_follows_the_limits_message() {
    let p = program("memory", &power_program("@limits(memory: 16777216)", 2));
    // 2^(10^9): a number of 10^9 bits, past the 16 MiB limit.
    for (engine, (code, out, err)) in ENGINES
        .iter()
        .zip(both("memory", &p, &["1000000000"], &[1]))
    {
        assert_eq!((code, out.as_str()), (Some(3), ""), "{engine}: {err}");
        let row = message("memory", engine);
        let limit = err.find("Memory limit of `main` passed");
        assert!(
            err.ends_with(&row) && limit.is_some_and(|at| at < err.len() - row.len()),
            "{engine}: {err}"
        );
    }
}

#[test]
fn a_run_stopped_by_its_deadline_keeps_status_3_and_the_row_follows_the_deadlines_message() {
    // The deadline stops the run from a thread of the runtime, through the stop that closes
    // the streams with no allocation (`zed_rt::limits::fault_exit`).
    let p = program("deadline", &power_program("@timeout(1r/2r)", 3));
    for (engine, got) in ENGINES
        .iter()
        .zip(both("deadline", &p, &["100000000"], &[1]))
    {
        assert_eq!(
            got,
            (
                Some(3),
                String::new(),
                format!(
                    "Deadline of `main` passed: 0.5 s.\n{}",
                    message("deadline", engine)
                )
            ),
            "{engine}"
        );
    }
}

#[test]
fn a_full_device_fails_the_write_and_the_close_then_succeeds() {
    // `/dev/full` fails the write with ENOSPC, reported as a failed write with status 1; its
    // close has no `flush` and succeeds, so no row follows.
    let src = "main(m: MainArgs) {\n    m.stdout <- \"first line\";\n}\n";
    let (file, exe) = program("full", src);
    let mut zedc = Command::new(env!("CARGO_BIN_EXE_zedc"));
    zedc.args(["run", &file]);
    for (engine, mut cmd) in [("run", zedc), ("exe", Command::new(&exe))] {
        let out = cmd
            .stdout(Stdio::from(std::fs::File::create("/dev/full").unwrap()))
            .stderr(Stdio::piped())
            .output()
            .unwrap();
        let err = String::from_utf8(out.stderr).unwrap();
        assert_eq!(out.status.code(), Some(1), "{engine}: {err}");
        assert!(
            err.contains("No space left on device") && !err.contains("closed it"),
            "{engine}: {err}"
        );
    }
}

#[test]
fn a_bug_of_zedc_in_the_run_keeps_status_3_and_the_row_follows_the_report() {
    // A debug build's run stops at a panic where `ZEDC_TEST_BUG` is set (plan row
    // EXE-panic-status); the switch does not exist in a release build.
    if !cfg!(debug_assertions) {
        return;
    }
    let p = program("bug", &hi(0));
    for (engine, (code, out, err)) in
        ENGINES
            .iter()
            .zip(both_with("bug", &p, &[], &[1], &[("ZEDC_TEST_BUG", "1")]))
    {
        assert_eq!((code, out.as_str()), (Some(3), ""), "{engine}: {err}");
        let row = message("bug", engine);
        let report = err.find("the run stopped because of a bug in zedc, not in your program");
        assert!(
            err.ends_with(&row) && report.is_some_and(|at| at < err.len() - row.len()),
            "{engine}: {err}"
        );
    }
}
