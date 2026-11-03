//! `Files` ports: `fs[path]` is `String | #ioError(op:, path:, why:) | #notFound`, and each path
//! is read from the world at most once per wave.| #ioError | #notFound`, and each path is read from
//! the world at most once per wave.

use std::collections::BTreeMap;
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

use zed_kernel::{Lookup, Value};
use zedc::run::load;

use super::{dir, run};

#[test]
fn a_config_file_is_read_and_a_missing_one_falls_back() {
    let d = dir("config");
    let cfg = d.join("app.conf");
    std::fs::write(&cfg, "  verbose  \n").unwrap();
    let src = format!(
        "main(fs: Files) -> (stdout: Lines) {{\n  \
         mode = trim(fs[\"{}\"]) else \"quiet\";\n  \
         extra = (fs[\"{}\"] else #notFound -> \"(no overrides)\") else \"(unreadable)\";\n  \
         stdout <- \"mode=${{mode}} ${{extra}}\";\n}}\n",
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
        "main(fs: Files) -> (stdout: Lines) {{\n  \
         stdout <- (fs[\"{}\"] else #ioError -> \"unreadable\") else \"missing\";\n}}\n",
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
        Err("a path is a String, not 3".to_string())
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
    let src = "main(fs: Files) -> (stdout: Lines) {\n  \
               a = fs[\"notes.txt\"];\n  b = fs[\"notes.txt\"];\n  c = fs[\"todo.txt\"];\n  \
               stdout <- \"${a == b} ${c else \"none\"}\";\n}\n";
    let p = load(src.as_bytes()).unwrap();
    let port = Arc::new(Counting::default());
    let wave = p.run(&BTreeMap::new(), |_| port.clone()).unwrap();
    assert_eq!(
        port.0.load(Ordering::SeqCst),
        2,
        "notes.txt once, todo.txt once"
    );
    assert_eq!(wave.writes[0].1, b"true contents of \"todo.txt\"\n");
    let paths: Vec<String> = wave.record.files["fs"]
        .keys()
        .map(|k| k.to_string())
        .collect();
    assert_eq!(paths, ["\"notes.txt\"", "\"todo.txt\""]);
}

#[test]
fn ports_are_lines_or_files_at_l1() {
    let e = load(b"main(n: int) -> (stdout: Lines) {\n  stdout <- \"x\";\n}\n").err();
    assert_eq!(
        e.as_deref(),
        Some("port `n` of `main` is `Lines` or `Files` at layer L1")
    );
    let e = load(b"main(fs: Files) -> (out: Files) {\n  out <- fs;\n}\n").err();
    assert_eq!(
        e.as_deref(),
        Some("output port `out` of `main` is `Lines` at layer L1")
    );
    let e = load(b"helper = 1;\n").err();
    assert_eq!(
        e.as_deref(),
        Some("a program declares one `main` function; this one declares 0")
    );
}

#[test]
fn a_failed_read_says_what_failed_where_and_why() {
    // A directory is no file: reading it fails with the operating system's reason.
    let d = dir("failed-read");
    let src = format!(
        "main(fs: Files) -> (stdout: Lines) {{\n  \
         stdout <- (fs[\"{}\"] else #ioError(op:, path:, why:) -> \"${{op}} ${{path}}: ${{why}}\") \
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
        "main(fs: Files) -> (stdout: Lines) {{\n  \
         stdout <- (fs[\"{}\"] else #ioError -> \"unreadable\") else \"missing\";\n}}\n",
        d.display()
    );
    assert_eq!(run("failed-read", &src, "", &[]).stdout, "unreadable\n");
}

#[test]
fn a_bare_io_error_pattern_narrows_the_payload_away() {
    // After `else #ioError -> …` and `else #notFound -> …` only a `String` is left, so the
    // push type-checks.
    let src = "main(fs: Files) -> (stdout: Lines) {\n  \
               stdout <- (fs[\"app.conf\"] else #ioError -> \"unreadable\") \
               else #notFound -> \"missing\";\n}\n";
    assert!(load(src.as_bytes()).is_ok());
    let src = "main(fs: Files) -> (stdout: Lines) {\n  \
               stdout <- fs[\"app.conf\"] else #notFound -> \"missing\";\n}\n";
    let e = load(src.as_bytes()).err().unwrap();
    assert!(
        e.contains("#ioError(op: String, path: String, why: String)"),
        "{e}"
    );
}
