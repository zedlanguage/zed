//! `Files` ports: `fs[path]` is `String | #ioError | #notFound`, and each path is read from
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
         extra = fs[\"{}\"] else #notFound -> \"(no overrides)\";\n  \
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
         stdout <- fs[\"{}\"] else #ioError -> \"unreadable\";\n}}\n",
        bin.display()
    );
    assert_eq!(run("binary", &src, "", &[]).stdout, "unreadable\n");
    let v = zedc::run::Disk
        .get(&Value::str(bin.to_str().unwrap()))
        .unwrap();
    assert_eq!(v, Value::atom("ioError"));
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
               stdout <- \"${a == b} ${c}\";\n}\n";
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
