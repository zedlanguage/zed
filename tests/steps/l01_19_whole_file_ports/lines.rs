//! `Lines` ports: standard input as the family of its lines, keyed from 0, and a pushed
//! string or family written as lines.

use zed_kernel::Value;
use zedc::run::{join_lines, split_lines};

use super::run;

#[test]
fn a_family_of_lines_is_written_one_line_per_entry() {
    let cat = |input: &[u8]| {
        String::from_utf8(join_lines("stdout", &split_lines("stdin", input)).unwrap()).unwrap()
    };
    assert_eq!(cat(b"first\nsecond\n"), "first\nsecond\n");
    // A last line without `\n` is still a line, and is written with one.
    assert_eq!(cat(b"only"), "only\n");
    // An empty input has no lines, so nothing is written.
    assert_eq!(cat(b""), "");
    // A line that is not UTF-8 is `#ioError`, so a program cannot push the family of its
    // input's lines as they are: the push would fail the wave (sec:failure).
    let src = "main(m: MainArgs) {\n  m.stdout <- m.stdin;\n}\n";
    let out = run("cat", src, "first\n", &[]);
    assert_eq!(out.status, 1);
    assert!(
        out.stderr.contains("a `Lines` port takes a `String` or a family of strings, not (int) -> String | #notFound | #ioError(op: String, path: String, why: String)"),
        "{}",
        out.stderr
    );
}

#[test]
fn lines_are_keyed_from_zero_and_crlf_is_one_line_end() {
    let src = "main(m: MainArgs) {\n  \
               m.stdout <- \"${m.stdin[0] else \"\"}|${m.stdin[1] else \"\"}|${m.stdin[2] else \"none\"}\";\n}\n";
    let out = run("numbers", src, "name: Ada\r\nrole: admin\r\n", &[]);
    assert_eq!(out.stdout, "name: Ada|role: admin|none\n");
    assert_eq!(
        split_lines("stdin", b"a\r\n\nb").to_string(),
        "{0 -> \"a\", 1 -> \"\", 2 -> \"b\"}",
        "an empty line in the middle is kept"
    );
}

#[test]
fn every_cr_right_before_a_line_end_is_dropped() {
    // DESIGN step L1.19: a line ends at `\n`, every `\r` right before its end is dropped, and
    // a last line needs no `\n`; a `\r` inside a line is kept.
    for input in [&b"a"[..], b"a\n", b"a\r\n", b"a\r\r\n", b"a\r", b"a\r\r"] {
        assert_eq!(
            split_lines("stdin", input).to_string(),
            "{0 -> \"a\"}",
            "{input:?}"
        );
    }
    assert_eq!(
        split_lines("stdin", b"a\rb\r\n\r\nc").to_string(),
        "{0 -> \"a\\rb\", 1 -> \"\", 2 -> \"c\"}"
    );
    // A run of `\r` costs one step each: 100000 of them before one `\n` leave one empty line.
    let mut many = vec![b'\r'; 100_000];
    many.push(b'\n');
    assert_eq!(split_lines("stdin", &many).to_string(), "{0 -> \"\"}");
}

#[test]
fn a_line_that_is_not_utf8_is_an_io_error_at_its_key() {
    let lines = split_lines("stdin", b"ok\n\xff\xfe\nfine\n");
    let Value::Family(f) = &lines else {
        panic!("{lines}")
    };
    assert_eq!(f.get(&Value::Int(0)), Some(&Value::str("ok")));
    assert_eq!(
        f.get(&Value::Int(1)),
        Some(&Value::io_error(
            "read",
            "stdin",
            "the line at key 1 is not UTF-8"
        ))
    );
    assert_eq!(f.get(&Value::Int(2)), Some(&Value::str("fine")));
}

#[test]
fn a_greeting_reads_one_line_and_writes_one() {
    let src = "main(m: MainArgs) {\n  \
               name = trim(m.stdin[0]) else \"stranger\";\n  \
               m.stdout <- \"Hello, ${name}!\";\n}\n";
    assert_eq!(
        run("greet", src, "  Grace \n", &[]).stdout,
        "Hello, Grace!\n"
    );
    assert_eq!(run("greet", src, "", &[]).stdout, "Hello, stranger!\n");
}

#[test]
fn a_computed_line_number_reads_that_line() {
    // The first line, key 0, says which line to print; a key that is not a literal reads the
    // family by value, as a literal one does.
    let src = "main(m: MainArgs) {\n  \
               pick = int(m.stdin[0]) else 0;\n  \
               m.stdout <- m.stdin[pick] else \"no such line\";\n}\n";
    assert_eq!(
        run("pick", src, "2\nred\ngreen\nblue\n", &[]).stdout,
        "green\n"
    );
    assert_eq!(run("pick", src, "9\nred\n", &[]).stdout, "no such line\n");
}

/// A program that writes the line of standard input at the key its first argument names, or
/// says the read missed (DESIGN step L1.19: the keys are `0..<n`, and a read outside them is
/// `#outOfBounds`).
const LINE_AT: &str = "main(m: MainArgs) {\n  \
     k = int(m.args[0] else \"\") else 0;\n  \
     m.stdout <- m.stdin[k] else #outOfBounds -> \"out of bounds\" else #ioError -> \"unreadable\";\n}\n";

/// What `LINE_AT` writes for the key `k` over the input `input`. Each run has its own directory,
/// since the tests run at once and a shared one would be rewritten under a running program.
fn line_at(input: &str, k: &str) -> String {
    static RUNS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let n = RUNS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let out = run(&format!("line_at_{n}"), LINE_AT, input, &["--", k]);
    assert_eq!((out.status, out.stderr.as_str()), (0, ""), "{input:?} {k}");
    out.stdout
}

#[test]
fn the_keys_of_n_lines_are_0_to_n_minus_1() {
    let input = "first\nmiddle\nlast\n";
    assert_eq!(line_at(input, "0"), "first\n");
    assert_eq!(line_at(input, "2"), "last\n");
    // Key n, one past the last line, and key -1, one before the first, are outside.
    assert_eq!(line_at(input, "3"), "out of bounds\n");
    assert_eq!(line_at(input, "-1"), "out of bounds\n");
    // One line is key 0 alone, with or without its `\n`.
    assert_eq!(line_at("only", "0"), "only\n");
    assert_eq!(line_at("only", "1"), "out of bounds\n");
}

#[test]
fn an_empty_input_has_no_keys() {
    assert_eq!(split_lines("stdin", b"").to_string(), "{}");
    assert_eq!(line_at("", "0"), "out of bounds\n");
    assert_eq!(line_at("", "-1"), "out of bounds\n");
}

#[test]
fn the_runtime_keys_the_lines_as_the_interpreter_does() {
    // zed-rt's port runtime and the interpreter's split are written apart; both key from 0.
    for input in [
        &b""[..],
        b"\n",
        b"a",
        b"a\r\n\nb",
        b"ok\n\xff\xfe\nfine\n",
        b"x\ny\nz\n",
    ] {
        assert_eq!(
            zed_rt::ports::lines("stdin", input),
            split_lines("stdin", input),
            "{input:?}"
        );
    }
    assert_eq!(
        zed_rt::ports::lines("stdin", b"x\ny\nz\n").to_string(),
        "{0 -> \"x\", 1 -> \"y\", 2 -> \"z\"}"
    );
}
