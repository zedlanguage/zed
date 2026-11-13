//! Line ends and bytes in port input (DESIGN step L1.19 and sec:codecs): a `Lines` input
//! ends a line at `\n`, at `\r\n` and at a lone `\r`, the line breaks of source text (author,
//! 2026-11-13, QUESTIONS A90); a `Files` read is `utf8Text()` over the file's bytes, so a byte
//! order mark is the character U+FEFF and each `\r\n` stays; and a record holds the bytes of
//! each `Lines` input, so a replay gives a line that is not UTF-8 the same `#ioError` the
//! recorded run gave it.

use zed_kernel::{Lookup, Value};
use zedc::run::{Record, split_lines};

use zed_tests::step_helpers::l01_19_whole_file_ports::run_bytes;

use super::{dir, run, zedc};

/// Writes lines 0, 1 and 2 of standard input between `|`, with `none` for a missing key.
const THREE_LINES: &str = "main(m: MainArgs) {\n  \
     m.stdout <- \"${m.stdin[0] else \"none\"}|${m.stdin[1] else \"none\"}|${m.stdin[2] else \"none\"}\";\n}\n";

#[test]
fn a_lone_cr_ends_a_line() {
    // A meter that writes `\r` between readings: each reading is a line.
    let out = run("lone-cr", THREE_LINES, "12\r13\r14\nend\n", &[]);
    assert_eq!((out.status, out.stdout.as_str()), (0, "12|13|14\n"));
    // `\r\n` is one line end, and a `\r` before another line end ends a line of its own.
    let out = run("lone-cr", THREE_LINES, "a\rb\r\nc\r\r\n", &[]);
    assert_eq!(out.stdout, "a|b|c\n");
    assert_eq!(
        split_lines("stdin", b"c\r\r\n").to_string(),
        "{0 -> \"c\", 1 -> \"\"}"
    );
    // Old Mac text, which ends its lines with `\r` alone, is three lines.
    let out = run("lone-cr", THREE_LINES, "one\rtwo\rthree\r", &[]);
    assert_eq!(out.stdout, "one|two|three\n");
    // `\r` alone and `\r\n` alone are each one empty line; `\n\r` is two.
    assert_eq!(split_lines("stdin", b"\r").to_string(), "{0 -> \"\"}");
    assert_eq!(split_lines("stdin", b"\r\n").to_string(), "{0 -> \"\"}");
    assert_eq!(
        split_lines("stdin", b"\n\r").to_string(),
        "{0 -> \"\", 1 -> \"\"}"
    );
    assert_eq!(
        split_lines("stdin", b"a\n\rb").to_string(),
        "{0 -> \"a\", 1 -> \"\", 2 -> \"b\"}"
    );
}

#[test]
fn a_byte_order_mark_is_the_first_character_of_the_first_line() {
    // `utf8Text()` reads each well-formed sequence as its character, and `EF BB BF` is U+FEFF;
    // only source text refuses it (sec:lexical).
    let src = "main(m: MainArgs) {\n  \
               m.stdout <- \"${m.stdin[0] == \"\\u{FEFF}name\"} ${m.stdin[0] == \"name\"} ${m.stdin[1] else \"none\"}\";\n}\n";
    let out = run("bom-lines", src, "\u{FEFF}name\r\nAda\r\n", &[]);
    assert_eq!(
        (out.status, out.stdout.as_str(), out.stderr.as_str()),
        (0, "true false Ada\n", "")
    );
    // A byte order mark after the start is a character like any other.
    assert_eq!(
        split_lines("stdin", "a\n\u{FEFF}b\n".as_bytes()).to_string(),
        "{0 -> \"a\", 1 -> \"\\u{FEFF}b\"}"
    );
}

/// A file written by a Windows editor: a byte order mark, then two lines each ended by `\r\n`.
const WINDOWS_TEXT: &str = "\u{FEFF}name = Ada\r\nrole = admin\r\n";

/// The program that reads the file at `path` whole and writes, on one line, whether the text
/// is `WINDOWS_TEXT` as written, then the text itself.
fn echo_file(path: &std::path::Path) -> String {
    format!(
        "main(m: MainArgs) {{\n  fs = main::files;\n  text = fs[\"{}\"] else \"(no text)\";\n  \
         m.stdout <- \"${{text == \"\\u{{FEFF}}name = Ada\\r\\nrole = admin\\r\\n\"}} [${{text}}]\";\n}}\n",
        path.display()
    )
}

#[test]
fn a_files_read_keeps_the_byte_order_mark_and_each_crlf() {
    let d = dir("bom-crlf");
    let path = d.join("people.ini");
    std::fs::write(&path, WINDOWS_TEXT).unwrap();
    let out = run("bom-crlf", &echo_file(&path), "", &[]);
    assert_eq!(
        (out.status, out.stdout, out.stderr.as_str()),
        (0, format!("true [{WINDOWS_TEXT}]\n"), "")
    );
    // The port gives the file's text exactly: nothing is stripped and no line end is changed.
    let at = |text: &[u8]| {
        std::fs::write(&path, text).unwrap();
        zedc::run::Disk.get(&Value::str(path.to_str().unwrap()))
    };
    assert_eq!(at(WINDOWS_TEXT.as_bytes()), Ok(Value::str(WINDOWS_TEXT)));
    assert_eq!(at(b"\xef\xbb\xbf"), Ok(Value::str("\u{FEFF}")));
    assert_eq!(at(b"a\rb\r\n"), Ok(Value::str("a\rb\r\n")));
    // A file that is UTF-8 only after its first byte is still not UTF-8.
    assert_eq!(
        at(b"\xbb\xbfok\r\n"),
        Ok(Value::io_error(
            "read",
            path.to_str().unwrap(),
            "the file is not UTF-8"
        ))
    );
}

#[test]
fn a_replay_gives_the_recorded_bytes_their_recorded_lines() {
    let d = dir("replay-bytes");
    let (path, rec) = (d.join("people.ini"), d.join("wave.rec"));
    std::fs::write(&path, WINDOWS_TEXT).unwrap();
    let src = format!(
        "main(m: MainArgs) {{\n  fs = main::files;\n  \
         a = m.stdin[0] else \"none\";\n  \
         b = m.stdin[1] else \"none\";\n  \
         c = m.stdin[2] else #ioError(op:, path:, why:) -> \"${{op}} ${{path}}: ${{why}}\" else \"none\";\n  \
         d = m.stdin[3] else \"none\";\n  \
         text = fs[\"{}\"] else \"(no text)\";\n  \
         m.stdout <- \"${{a}}|${{b}}|${{c}}|${{d}}|${{text}}\";\n}}\n",
        path.display()
    );
    // Lines 0 and 1 end with a lone `\r` and a `\n`, line 2 is not UTF-8, and line 3 ends with
    // `\r\n`.
    let input = b"12\r13\n\xff\xfe\r\nfine\r\n";
    let rec_s = rec.to_str().unwrap();
    let out = run_bytes("replay-bytes", &src, input, &["--record", rec_s]);
    let expected =
        format!("12|13|read m.stdin: the line at key 2 is not UTF-8|fine|{WINDOWS_TEXT}\n");
    assert_eq!(
        (out.status, out.stdout.as_str(), out.stderr.as_str()),
        (0, expected.as_str(), "")
    );
    // The record holds the input's bytes as they were read, the `\xff` and each `\r` included.
    let record = Record::from_bytes(&std::fs::read(&rec).unwrap()).unwrap();
    assert_eq!(&*record.lines["m.stdin"], &input[..]);
    // The world changes; the replay reads the record alone and gives the same lines.
    std::fs::write(&path, "changed\n").unwrap();
    let prog = d.join("prog.zed");
    let out = zedc(&["replay", prog.to_str().unwrap(), rec_s], "other\n");
    assert_eq!(
        (out.status, out.stdout.as_str(), out.stderr.as_str()),
        (0, expected.as_str(), "")
    );
}
