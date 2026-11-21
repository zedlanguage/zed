//! The messages of a run that stops, as a user meets them (plan row MSG-kinds-e2e-tests,
//! DESIGN.md sec:diagnostics): each kind of stop reached by a small program through `zedc run`
//! and through the executable `zedc build` makes, each in a child process under `timeout 60`,
//! and its message checked in full. Each stops with status 3, as every fault of a run does,
//! except a replay that stops at a read its record lacks, which, as every record `zedc replay`
//! cannot use, is a usage error with status 2 (DESIGN.md L1.19).
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
/// in "this machine has 126 GiB of memory", in "the run holds 25 MiB of 32 MiB", and in the
/// limit a run out of memory is offered, a power of two below the machine's memory:
/// "repair: `@limits(memory: 68719476736)` before `main`, 64 GiB, so the run stops".
fn masked(text: &str) -> String {
    let mut out = text.to_string();
    for (before, after) in [
        ("this machine has ", " of memory"),
        ("the run holds ", " of "),
        ("repair: `@limits(memory: ", ", so the run stops"),
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
        "{limit}\nmain(m: MainArgs) {{\n    k = int(m.args[0] else #outOfBounds -> \"\") else #invalid -> 0;\n    \
         j = int(m.args[1] else #outOfBounds -> \"\") else #invalid -> 0;\n{body}}}\n"
    )
}

#[test]
fn a_text_too_large_for_memory_stops_the_run() {
    // `a70` is a tuple of 2^70 copies of the argument, held as 71 shared pairs; its text,
    // two bytes and more for each copy, is past any machine's memory.
    let mut src =
        "main(m: MainArgs) {\n    a0 = m.args[0] else #outOfBounds -> \"\";\n".to_string();
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
             |                 ^^^^^^^^^^^\n  \
             [2] 73:17: repair: `@limits(memory: _, so the run stops with a message before it \
             holds more than that, on any machine with that much memory free\n  \
             [3] 73:17: repair: give the run a smaller input\n  \
             [4] 73:17: repair: bound the input that sets the size where it is read, as `k: \
             int[0..=30]`, so a larger input is refused where it is read\n  \
             [5] 73:17: repair: build the program in the `preallocated` mode, which proves a \
             bound on what the run holds\n"
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
             |                        ^^^^^\n  \
             [2] 7:24: repair: `@limits(memory: 67108864)` before `main`, the limit doubled to \
             64 MiB\n  \
             [3] 7:24: repair: give the run a smaller input\n"
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
             |                        ^^^^^^\n  \
             [2] 7:24: repair: `@limits(memory: 134217728)` before `main`, the limit doubled \
             to 128 MiB\n  \
             [3] 7:24: repair: give the run a smaller input\n"
        )
    });
}

#[test]
fn a_number_too_close_to_a_rounding_boundary_stops_the_run_past_its_memory_limit() {
    // (2^k + 2^(k-53) - 1) / 2^k lies just below the midpoint of two neighboring `f64`s.
    let src = with_args(
        "@limits(memory: 67108864)",
        "    q = if k >= 53 { (2r ^ k + 2r ^ (k - 53) - 1) / 2r ^ k } else { 0r };\n    \
         m.stdout <- String(f64(q));\n",
    );
    stops("round", &src, &["16777216"], |file| {
        format!(
            "{file}:6:24: Memory limit of `main` passed: `f64(q)` must round a number so close \
             to a rounding boundary that it needs about 1.4 × 10^7 digits of it (5.6 MiB), and \
             about 89 MiB of memory to compute it; the run holds _ of 64 MiB.\n  \
             [1] 6:24: the run stopped here\n      \
             6 |     m.stdout <- String(f64(q));\n        \
             |                        ^^^^^^\n  \
             [2] 6:24: repair: `@limits(memory: 134217728)` before `main`, the limit doubled \
             to 128 MiB\n  \
             [3] 6:24: repair: give the run a smaller input\n"
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
         m.stdout <- fs[\"{}\"] else #ioError -> \"none\" else #notFound -> \"none\";\n}}\n",
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
    // The record is at fault, not the program or the machine: a usage error (DESIGN.md L1.19).
    assert_eq!(
        replayed,
        (
            Some(2),
            String::new(),
            format!(
                "{file}:3:17: the port `main::files` could not answer a read: the program reads \
                 \"{at}\" here, and the record holds no read of it, so the replay cannot go on: \
                 a replay reads nothing from outside, only what the record holds. The run that \
                 wrote the record did not read \"{at}\", so its inputs differed from these, or \
                 the record has been changed. Replay with the inputs of the recorded run, or \
                 make a new record with `zedc run <file> --record <out>`.\n  \
                 [1] 3:17: the run stopped here\n      \
                 3 |     m.stdout <- fs[\"{at}\"] else #ioError -> \"none\" else #notFound -> \"none\";\n        \
                 |                 {marks}\n"
            )
        )
    );
}

/// The text every message about a record `zedc replay` cannot read ends with.
const REMAKE: &str = "make it again with `zedc run <file> --record <out>`.";

#[test]
fn a_record_zedc_replay_cannot_use_is_a_usage_error() {
    // Each kind of damage the reader tells apart, made from a whole record of a program that
    // reads standard input: each exits with status 2, writes nothing to standard output, and
    // names the record's file and the line where the entry that cannot be read starts.
    let d = dir();
    let src = "main(m: MainArgs) {\n    m.stdout <- m.stdin[0] else #ioError -> \"none\" else #outOfBounds -> \"none\";\n}\n";
    let file = file("damaged", src);
    let rec = d.join("damaged.rec").display().to_string();
    let recorded = zedc(&["run", &file, "--record", &rec]);
    assert_eq!(recorded, (Some(0), "none\n".into(), String::new()));
    let whole = std::fs::read_to_string(&rec).unwrap();
    let hex = whole.lines().nth(2).unwrap();
    // Lines 1 to 3 are the first line and the program's address; the entry of standard
    // input, the empty input, starts on line 4.
    assert_eq!(
        whole,
        format!("zed record 1\nprogram 64\n{hex}\nlines 7 0\nm.stdin\n")
    );
    let replay = |name: &str, text: &str| {
        let path = d.join(name).display().to_string();
        std::fs::write(&path, text).unwrap();
        let (code, out, err) = zedc(&["replay", &file, &path]);
        assert_eq!((code, out.as_str()), (Some(2), ""), "{name}: {err}");
        (path, err)
    };
    let head = format!("zed record 1\nprogram 64\n{hex}\n");
    // Not a record.
    let (path, err) = replay("header.rec", &whole.replace("record 1", "record 2"));
    assert_eq!(
        err,
        format!(
            "{path}:1: this file is not a record that `zedc run --record` writes: such a record \
             starts with the line `zed record 1`, and this file does not. Name the file \
             `--record` wrote, or make a record with `zedc run <file> --record <out>`.\n"
        )
    );
    // Cut inside its first line.
    let (path, err) = replay("first.rec", "zed rec");
    assert_eq!(
        err,
        format!(
            "{path}:1: the record is cut short: it ends before the end of its first line, `zed \
             record 1`, so the file was cut after it was written. A replay reads only a whole \
             record; {REMAKE}\n"
        )
    );
    // Cut inside the entry of standard input.
    let (path, err) = replay("short.rec", &format!("{head}lines 7 0\nm.st"));
    assert_eq!(
        err,
        format!(
            "{path}:4: the record is cut short: the file ends inside the entry that starts on \
             this line, so the file was cut after it was written, or a length on this line has \
             been changed. A replay reads only a whole record; {REMAKE}\n"
        )
    );
    // A kind of entry `--record` does not write.
    let (path, err) = replay("kind.rec", &format!("{head}socket 7 0\nm.stdin\n"));
    assert_eq!(
        err,
        format!(
            "{path}:4: the record has been changed: `socket` is not a kind of entry that `zedc \
             run --record` writes, which are `program`, `lines`, `text`, `missing`, `error` and \
             `arg`. A replay reads a record only as `zedc run --record` wrote it; {REMAKE}\n"
        )
    );
    // A malformed line where an entry starts.
    let (path, err) = replay("words.rec", &format!("{head}lines seven 0\nm.stdin\n"));
    assert_eq!(
        err,
        format!(
            "{path}:4: the record has been changed: this line should begin an entry, with a kind \
             such as `lines` or `text` and then the length in bytes of each of the entry's \
             fields, and it does not. A replay reads a record only as `zedc run --record` wrote \
             it; {REMAKE}\n"
        )
    );
    // Fields that do not end where their lengths say.
    let (path, err) = replay("length.rec", &format!("{head}lines 6 0\nm.stdin\n"));
    assert_eq!(
        err,
        format!(
            "{path}:4: the record has been changed: the entry that starts on this line does not \
             end where the lengths on the line say: the byte after its fields is not a line \
             end. A replay reads a record only as `zedc run --record` wrote it; {REMAKE}\n"
        )
    );
    // Cut cleanly after the address: whole entries, but no input for standard input.
    let (path, err) = replay("no_input.rec", &head);
    assert_eq!(
        err,
        format!(
            "{path}: the record holds no input for the port `m.stdin`, which the program reads, \
             so the replay cannot go on: a replay reads nothing from outside, only what the \
             record holds. Every run records the input of each port it reads, so the record has \
             been changed since it was written. Replay with the record as it was written, or \
             make a new record with `zedc run <file> --record <out>`.\n"
        )
    );
    // The whole record replays.
    assert_eq!(
        zedc(&["replay", &file, &rec]),
        (Some(0), "none\n".into(), String::new())
    );
}

#[test]
fn the_run_holds_its_values_not_the_memory_it_freed() {
    // `a` holds 2^23592961 + 1, 23592962 bits (2.8 MiB), when `a < b` is refused. The message
    // names what the run holds when the system refuses the step, not what it holds once the
    // run has freed its values (19 KiB before MSG-run-stop-repairs), nor the system's count,
    // which holds memory freed and kept for reuse. The figure is not exact
    // (`zed_kernel::limits::held`), so the test asks for at least 2 MiB and less than the limit.
    let src = with_args(
        "@limits(memory: 33554432)",
        "    a = if k >= 0 { 2 ^ k + 1 } else { 0 };\n    \
         b = if k >= 0 { 2 ^ k } else { 0 };\n    m.stdout <- String(a < b);\n",
    );
    let (_, runs) = both("order_held", &src, &["23592961"]);
    for (engine, (code, _, err)) in ["zedc run", "executable"].iter().zip(runs) {
        assert_eq!(code, Some(3), "{engine}");
        let held = err
            .split_once("the run holds ")
            .and_then(|(_, rest)| rest.split_once(" MiB of 32 MiB"))
            .and_then(|(n, _)| n.parse::<f64>().ok());
        assert!(
            held.is_some_and(|h| (2.0..32.0).contains(&h)),
            "{engine}: {err}"
        );
    }
}

#[test]
fn a_run_out_of_memory_offers_a_limit_a_bound_and_the_preallocated_mode() {
    let mut src =
        "main(m: MainArgs) {\n    a0 = m.args[0] else #outOfBounds -> \"\";\n".to_string();
    for i in 1..=70 {
        src += &format!("    a{i} = (a{}, a{});\n", i - 1, i - 1);
    }
    src += "    m.stdout <- String(a70);\n}\n";
    let (_, runs) = both("text_repair", &src, &["x"]);
    for (engine, (code, _, err)) in ["zedc run", "executable"].iter().zip(runs) {
        assert_eq!(code, Some(3), "{engine}");
        assert!(err.contains("repair: `@limits(memory: "), "{engine}: {err}");
        assert!(err.contains("preallocated"), "{engine}: {err}");
    }
}
