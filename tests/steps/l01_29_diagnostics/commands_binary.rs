//! Every command of the zedc executable that reads a program prints a rejection of it in full,
//! as a user runs it (item FIX-fmt-parse-notes, DESIGN.md sec:diagnostics): the message at its
//! line and column, each step of its derivation with the source line it stands on, and each
//! repair. `zedc run`, `zedc replay`, `zedc build` and `zedc fmt` print it alike on standard
//! error; `zedc test` prints it in its report on standard output, followed by the count of
//! passed and failed checks. `zedc fmt` reads the syntax of a file only, so a program whose
//! syntax is accepted and whose types are not is printed in layout by `zedc fmt` and rejected by
//! the others. `crates/zed-native/Cargo.toml` names this test, since only a test of that package
//! can name the executable.
#![cfg(target_os = "linux")]

use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

/// A loop whose boundary item has neither `initial` nor an index: a parse error with two
/// steps, its statement and its repair.
const BARE: &str = "f(n) = loop t {\n  while t < n;\n  x' = x + 1 with x = 0;\n};\n";

/// What every command prints for [`BARE`] in the file `file`, without the final line break.
fn bare_rejection(file: &Path) -> String {
    format!(
        "{}:3:19: `with x = 0` gives `x` no sentinel value: a boundary item is written \
         `initial x = 0`, which gives the sentinel value, or with an index, as `x[k] = 0`. \
         Without `initial`, `with x = 0` reads as though `x` took the value `0` anew on every \
         step, while a boundary item gives `x` one value, below its first step or index, once.\n  \
         [1] 3:3: the statement whose boundary clause holds the item\n      \
         3 |   x' = x + 1 with x = 0;\n        \
         |   ^^^^^^^^^^^^^^^^^^^^^^ [1]\n        \
         |                   ^^^^^ [2]\n  \
         [2] 3:19: repair: `with initial x = 0`, the sentinel value",
        file.display()
    )
}

/// The file `name` in this test's directory under the test target's scratch directory, holding
/// `text`; it is overwritten by each run, never deleted.
fn file(name: &str, text: &str) -> PathBuf {
    let d = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("l01_29_commands_binary");
    std::fs::create_dir_all(&d).unwrap();
    let f = d.join(name);
    std::fs::write(&f, text).unwrap();
    f
}

/// The runtime library built with `zedc`, which `zedc build` checks before it reads the
/// program, as `tests/steps/l01_36a_executables/binary.rs` finds it.
fn runtime() -> PathBuf {
    let exe = std::env::current_exe().unwrap();
    zed_native::link::runtime_of(Path::new(env!("CARGO_BIN_EXE_zedc")), exe.parent().unwrap())
        .unwrap_or_else(|e| panic!("{e}"))
}

/// `zedc <command> <file> <after>` with no input, the runtime library and linker of `zedc build`
/// named: status, stdout and stderr.
fn zedc(command: &str, file: &Path, after: &[&str]) -> (Option<i32>, String, String) {
    let out = Command::new(env!("CARGO_BIN_EXE_zedc"))
        .arg(command)
        .arg(file)
        .args(after)
        .env("ZED_RUNTIME", runtime())
        .env("CC", "cc")
        .stdin(Stdio::null())
        .output()
        .unwrap();
    (
        out.status.code(),
        String::from_utf8(out.stdout).unwrap(),
        String::from_utf8(out.stderr).unwrap(),
    )
}

/// The words after the file that `command` needs to reach the program: `zedc replay` names a
/// record, which it reads only after the program is accepted, and `zedc build` an output.
fn after(command: &str, out: &Path) -> Vec<String> {
    match command {
        "replay" => vec![out.with_extension("record").display().to_string()],
        "build" => vec!["-o".into(), out.display().to_string()],
        _ => Vec::new(),
    }
}

/// What `command` prints for the file `f` when it rejects it: standard error with status 1 and
/// nothing on standard output, or, for `zedc test`, its report on standard output.
fn rejection(command: &str, f: &Path) -> String {
    let words = after(command, &f.with_extension(format!("{command}.out")));
    let words: Vec<&str> = words.iter().map(String::as_str).collect();
    let (status, out, err) = zedc(command, f, &words);
    assert_eq!(
        status,
        Some(1),
        "zedc {command} {}: {out}{err}",
        f.display()
    );
    if command == "test" {
        assert_eq!(err, "", "zedc test {}", f.display());
        return out;
    }
    assert_eq!(out, "", "zedc {command} {}: {err}", f.display());
    err
}

#[test]
fn zedc_fmt_prints_a_parse_error_with_its_steps_and_repairs() {
    let f = file("fmt.zed", BARE);
    assert_eq!(rejection("fmt", &f), format!("{}\n", bare_rejection(&f)));
}

#[test]
fn zedc_run_prints_a_parse_error_with_its_steps_and_repairs() {
    let f = file("run.zed", BARE);
    assert_eq!(rejection("run", &f), format!("{}\n", bare_rejection(&f)));
}

#[test]
fn zedc_replay_prints_a_parse_error_with_its_steps_and_repairs() {
    let f = file("replay.zed", BARE);
    assert_eq!(rejection("replay", &f), format!("{}\n", bare_rejection(&f)));
}

#[test]
fn zedc_build_prints_a_parse_error_with_its_steps_and_repairs() {
    let f = file("build.zed", BARE);
    assert_eq!(rejection("build", &f), format!("{}\n", bare_rejection(&f)));
}

#[test]
fn zedc_test_prints_a_parse_error_with_its_steps_and_repairs() {
    let f = file("test.zed", BARE);
    assert_eq!(
        rejection("test", &f),
        format!(
            "{}\n0 passed, 1 failed, 0 rejection units\n",
            bare_rejection(&f)
        )
    );
}

/// Units rejected by their syntax, most with a derivation: each phase of the syntax (a
/// character no token starts with, a parse error, and an item that cannot be built), errors of
/// the syntax with steps, and a unit with two errors, both printed.
const SYNTAX: [(&str, &str); 12] = [
    ("bare", BARE),
    (
        "bare_indexed",
        "f(n) = {\n  d[i in 3..<n] = d[i - 1] + 1 with d = 0;\n  d[n - 1]\n};\n",
    ),
    ("character", "x = 1 # 2;\n"),
    ("parse", "f(x) = x +;\n"),
    ("named_first", "g(a, b: int) = a;\ny = g(b: 1, 2);\n"),
    ("argument_twice", "g(a: int) = a;\ny = g(a: 1, a: 2);\n"),
    ("minus_chain", "y = -3.max(1);\n"),
    ("set_and_map", "y = {1, 2 -> 3};\n"),
    ("two_exports", "f(x) = {\n  return x;\n  return 1;\n};\n"),
    (
        "two_initials",
        "f(n) = loop t {\n  while t < n;\n  x' = x + 1 with initial x = 0;\n  \
         y' = x with initial x = 1;\n};\n",
    ),
    ("field_twice", "s = {a: 1};\nt = s with { a = 2, a = 3 };\n"),
    ("two_errors", "y = {1, 2 -> 3};\nz = {1 -> 2, 3};\n"),
];

#[test]
fn every_command_prints_a_syntax_error_as_zedc_run_does() {
    for (name, text) in SYNTAX {
        let f = file(&format!("syntax_{name}.zed"), text);
        let run = rejection("run", &f);
        assert!(
            run.starts_with(&format!("{}:", f.display())),
            "{name}: {run}"
        );
        // Each has its steps but the lexical and the plain parse error, and the last unit has
        // two errors, each after the file's name.
        let steps = run.contains("\n  [1] ");
        assert_eq!(
            steps,
            !matches!(name, "character" | "parse"),
            "{name}: {run}"
        );
        let errors = run.matches(&format!("{}:", f.display())).count();
        assert_eq!(
            errors,
            if name == "two_errors" { 2 } else { 1 },
            "{name}: {run}"
        );
        for command in ["fmt", "replay", "build"] {
            assert_eq!(rejection(command, &f), run, "zedc {command} on {name}");
        }
        // `zedc test` counts each error of the unit as one failed check.
        assert_eq!(
            rejection("test", &f),
            format!("{run}0 passed, {errors} failed, 0 rejection units\n"),
            "zedc test on {name}"
        );
    }
}

/// A unit whose syntax is accepted and whose call is rejected by the checker, with a step and
/// two repairs.
const CHECKED: &str =
    "g(a: int, b: int) = a + b;\nmain(m: MainArgs) {\n  m.stdout <- \"${g(1)}\";\n}\n";

#[test]
fn a_rejection_by_the_checker_prints_alike_and_zedc_fmt_lays_the_unit_out() {
    let f = file("checked.zed", CHECKED);
    let run = rejection("run", &f);
    assert_eq!(
        run,
        format!(
            "{}:3:20: this argument is passed by position, and the parameter it reaches, `a` of \
             `g`, is a named parameter, which a call passes only by name, as `a: …`\n  \
             [1] 1:1: `g` is declared here with no type written for its result; the type the \
             checker found for `g` is `(a: int, b: int) -> int`\n      \
             1 | g(a: int, b: int) = a + b;\n        \
             | ^^^^^^^^^^^^^^^^^^^^^^^^^^\n  \
             [2] 3:20: repair: pass `a` by name, as `a: …`\n      \
             3 |   m.stdout <- \"${{g(1)}}\";\n        \
             |                    ^\n  \
             [3] 3:20: repair: declare `a` `positional` in `g`\n",
            f.display()
        )
    );
    for command in ["replay", "build"] {
        assert_eq!(rejection(command, &f), run, "zedc {command}");
    }
    assert_eq!(
        rejection("test", &f),
        format!("{run}0 passed, 1 failed, 0 rejection units\n")
    );
    let (status, out, err) = zedc("fmt", &f, &[]);
    assert_eq!((status, out.as_str(), err.as_str()), (Some(0), CHECKED, ""));
}

/// A manifest is read with the syntax of a unit, and its parse error prints its steps too.
#[test]
fn a_parse_error_in_a_manifest_prints_its_steps_and_repairs() {
    let d = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("l01_29_commands_binary_package");
    std::fs::create_dir_all(&d).unwrap();
    let manifest = d.join("zed.manifest");
    std::fs::write(&manifest, "prelude = \"std.prelude\" with y = 0;\n").unwrap();
    let f = d.join("a.zed");
    std::fs::write(&f, "main(m: MainArgs) {\n  m.stdout <- \"hi\";\n}\n").unwrap();
    assert_eq!(
        rejection("run", &f),
        format!(
            "{}:1:30: `with y = 0` gives `y` no sentinel value: a boundary item is written \
             `initial y = 0`, which gives the sentinel value, or with an index, as `y[k] = 0`. \
             Without `initial`, `with y = 0` reads as though `y` took the value `0` anew on \
             every step, while a boundary item gives `y` one value, below its first step or \
             index, once.\n  \
             [1] 1:1: the statement whose boundary clause holds the item\n      \
             1 | prelude = \"std.prelude\" with y = 0;\n        \
             | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ [1]\n        \
             |                              ^^^^^ [2]\n  \
             [2] 1:30: repair: `with initial y = 0`, the sentinel value\n",
            manifest.display()
        )
    );
}
