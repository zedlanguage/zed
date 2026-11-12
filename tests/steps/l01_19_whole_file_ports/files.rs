//! `Files` ports: `fs[path]` is `String | #ioError(op:, path:, why:) | #notFound`, and each path
//! is read from the world at most once per wave.| #ioError | #notFound`, and each path is read from
//! the world at most once per wave.

use std::collections::BTreeMap;
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

use zed_kernel::{Lookup, Value};
use zedc::run::load;

use zed_tests::main_param_message;

use super::{dir, run};

#[test]
fn a_config_file_is_read_and_a_missing_one_falls_back() {
    let d = dir("config");
    let cfg = d.join("app.conf");
    std::fs::write(&cfg, "  verbose  \n").unwrap();
    let src = format!(
        "main(m: MainArgs) {{\n  fs = files();\n  \
         mode = trim(fs[\"{}\"]) else \"quiet\";\n  \
         extra = (fs[\"{}\"] else #notFound -> \"(no overrides)\") else \"(unreadable)\";\n  \
         m.stdout <- \"mode=${{mode}} ${{extra}}\";\n}}\n",
        cfg.display(),
        d.join("absent.conf").display()
    );
    let out = run("config", &src, "", &[]);
    assert_eq!(
        (out.status, out.stdout.as_str()),
        (0, "mode=verbose (no overrides)\n")
    );
}

#[test]
fn a_file_that_is_not_utf8_is_an_io_error() {
    let d = dir("binary");
    let bin = d.join("blob.bin");
    std::fs::write(&bin, [0xffu8, 0x00, 0xfe]).unwrap();
    let src = format!(
        "main(m: MainArgs) {{\n  fs = files();\n  \
         m.stdout <- (fs[\"{}\"] else #ioError -> \"unreadable\") else \"missing\";\n}}\n",
        bin.display()
    );
    assert_eq!(run("binary", &src, "", &[]).stdout, "unreadable\n");
    let v = zedc::run::Disk
        .get(&Value::str(bin.to_str().unwrap()))
        .unwrap();
    assert_eq!(
        v,
        Value::io_error("read", bin.to_str().unwrap(), "the file is not UTF-8")
    );
    assert_eq!(
        zedc::run::Disk.get(&Value::Int(3)),
        Err(
            "a `Files` port reads a file by its path, which is a string, and the program read it \
             with 3, which is not one. Write the path as a string, such as `\"data.txt\"`, or \
             convert the value with `String(…)`."
                .to_string()
        )
    );
}

/// A `Files` port that counts the reads the world answers.
#[derive(Debug, Default)]
struct Counting(AtomicUsize);

impl Lookup for Counting {
    fn get(&self, key: &Value) -> Result<Value, String> {
        self.0.fetch_add(1, Ordering::SeqCst);
        Ok(Value::str(&format!("contents of {key}")))
    }
}

#[test]
fn each_path_is_read_once_so_the_wave_sees_one_value() {
    let src = "main(m: MainArgs) {\n  fs = files();\n  \
               a = fs[\"notes.txt\"];\n  b = fs[\"notes.txt\"];\n  c = fs[\"todo.txt\"];\n  \
               m.stdout <- \"${a == b} ${c else \"none\"}\";\n}\n";
    let p = load(src.as_bytes()).unwrap();
    let port = Arc::new(Counting::default());
    let wave = p.run(&BTreeMap::new(), |_| port.clone()).unwrap();
    assert_eq!(
        port.0.load(Ordering::SeqCst),
        2,
        "notes.txt once, todo.txt once"
    );
    assert_eq!(wave.writes[0].1, b"true contents of \"todo.txt\"\n");
    let paths: Vec<String> = wave.record.files["files()"]
        .keys()
        .map(|k| k.to_string())
        .collect();
    assert_eq!(paths, ["\"notes.txt\"", "\"todo.txt\""]);
}

#[test]
fn main_takes_one_main_args() {
    // The headline, then the notes: what `main` takes and where the input is read now.
    let e = load(b"main(n: int) {\n  m.stdout <- \"x\";\n}\n")
        .err()
        .unwrap_or_default();
    assert_eq!(
        e.lines().next(),
        Some(format!("1:6: {}", main_param_message("n", "int")).as_str())
    );
    assert!(
        e.contains("`main` takes one argument, of type `MainArgs`"),
        "{e}"
    );
    // The old header's output ports are a result type, and `main` gives an `int`.
    let e = load(b"main(m: MainArgs) -> (out: Files) {\n  out <- \"x\";\n}\n").err();
    let e = e.unwrap_or_default();
    assert_eq!(
        e.lines().next(),
        Some("1:22: Result of `main` that is not an `int`: `(out: Files)`. Try `int` instead.")
    );
    assert!(
        e.contains("`main` gives an `int`, the program's exit status"),
        "{e}"
    );
    // `main()` and `main(m)` need no type: only `MainArgs` fits.
    assert!(load(b"main() {\n}\n").is_ok());
    assert!(load(b"main(m) {\n  m.stdout <- \"x\";\n}\n").is_ok());
    let e = load(b"helper = 1;\n").err();
    assert_eq!(
        e.as_deref(),
        Some(
            "1:1: This file declares no `main` to start the program at. Try adding \
             `main(m: MainArgs) { m.stdout <- \"hello\"; }`.\n  \
             [1] 1:1: `zedc run` runs a program, which starts at the function `main`; a file of \
             definitions to test runs with `zedc test`\n      \
             1 | helper = 1;\n        \
             | ^"
        )
    );
}

/// A function other than `main` takes a port as an argument (DESIGN.md step L1.19), so an
/// output port declared in a helper's result, the old form, is a later form at L1, whether or
/// not the function is called. A `main` nested in a block has the header rules of `main`, so its
/// result type is rejected as the result of `main` is.
#[test]
fn a_helper_output_port_is_a_later_form_at_l1() {
    let later = |at: &str, written: &str| {
        format!(
            "{at}: the declared result type `-> {written}` is part of the Zed language, and this \
             version of zedc does not compile it yet. Write the program without it, with the \
             forms this zedc compiles."
        )
    };
    let e = load(b"log(positional s) -> (out: Files) {\n  out <- s;\n}\nmain() = 0;\n").err();
    assert_eq!(e, Some(later("1:19", "(out: Files)")));
    let e = load(
        b"say(positional s) -> (stdout: Lines) {\n  stdout <- s;\n}\n\
          main(m: MainArgs) {\n  a = say(\"one\");\n}\n",
    )
    .err();
    assert_eq!(e, Some(later("1:19", "(stdout: Lines)")));
    let e = load(
        b"g() = {\n  main() -> (out: Files) { 0 }\n  1\n};\n\
          main(m: MainArgs) {\n  m.stdout <- \"x\";\n}\n",
    )
    .err();
    let e = e.unwrap_or_default();
    assert_eq!(
        e.lines().next(),
        Some("2:13: Result of `main` that is not an `int`: `(out: Files)`. Try `int` instead.")
    );
    assert!(
        e.contains("`main` gives an `int`, the program's exit status"),
        "{e}"
    );
}

#[test]
fn a_failed_read_says_what_failed_where_and_why() {
    // A directory is no file: reading it fails with the operating system's reason.
    let d = dir("failed-read");
    let src = format!(
        "main(m: MainArgs) {{\n  fs = files();\n  \
         m.stdout <- (fs[\"{}\"] else #ioError(op:, path:, why:) -> \"${{op}} ${{path}}: ${{why}}\") \
         else \"missing\";\n}}\n",
        d.display()
    );
    let out = run("failed-read", &src, "", &[]);
    assert_eq!(
        (out.status, out.stdout),
        (
            0,
            format!("read {}: Is a directory (os error 21)\n", d.display())
        )
    );
    assert_eq!(
        zedc::run::Disk.get(&Value::str(d.to_str().unwrap())),
        Ok(Value::io_error(
            "read",
            d.to_str().unwrap(),
            "Is a directory (os error 21)"
        ))
    );
    // A bare `#ioError` still matches it, by the atom alone.
    let src = format!(
        "main(m: MainArgs) {{\n  fs = files();\n  \
         m.stdout <- (fs[\"{}\"] else #ioError -> \"unreadable\") else \"missing\";\n}}\n",
        d.display()
    );
    assert_eq!(run("failed-read", &src, "", &[]).stdout, "unreadable\n");
}

#[test]
fn a_bare_io_error_pattern_narrows_the_payload_away() {
    // After `else #ioError -> …` and `else #notFound -> …` only a `String` is left, so the
    // push type-checks.
    let src = "main(m: MainArgs) {\n  fs = files();\n  \
               m.stdout <- (fs[\"app.conf\"] else #ioError -> \"unreadable\") \
               else #notFound -> \"missing\";\n}\n";
    assert!(load(src.as_bytes()).is_ok());
    let src = "main(m: MainArgs) {\n  fs = files();\n  \
               m.stdout <- fs[\"app.conf\"] else #notFound -> \"missing\";\n}\n";
    let e = load(src.as_bytes()).err().unwrap();
    assert!(
        e.contains("#ioError(op: String, path: String, why: String)"),
        "{e}"
    );
}
