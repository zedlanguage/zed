//! Completeness tests of the port runtime (row TEST-complete-crates, author P189): each line
//! end and each shape a `Lines` port reads or writes (DESIGN.md sec:ports). The case list is
//! `crates/zed-rt/COMPLETENESS.md`.

use super::*;
use zed_kernel::Text;

/// The entries of the family `lines` gives, with their keys.
fn entries(port: &str, b: &[u8]) -> Vec<(Value, Value)> {
    match lines(port, b) {
        Value::Family(f) => f
            .leaves()
            .into_iter()
            .map(|(mut k, v)| {
                assert_eq!(k.len(), 1, "one level");
                (k.remove(0), v)
            })
            .collect(),
        v => panic!("not a family: {v:?}"),
    }
}

#[test]
fn lines_are_keyed_from_0_in_order_and_each_line_end_ends_one_line() {
    let cases: [(&[u8], &[&str]); 9] = [
        (b"a", &["a"]),
        (b"a\n", &["a"]),
        (b"a\r\n", &["a"]),
        (b"a\r", &["a"]),
        (b"\n\n", &["", ""]),
        (b"\r\r", &["", ""]),
        (b"\r\n\r\n", &["", ""]),
        (b"x\ny\r\nz\rw", &["x", "y", "z", "w"]),
        (b"\0 \t\n\xc3\xa9", &["\0 \t", "é"]),
    ];
    for (b, want) in cases {
        let got = entries("p", b);
        let want: Vec<(Value, Value)> = want
            .iter()
            .enumerate()
            .map(|(k, s)| (Value::Int(k as i64), Value::str(s)))
            .collect();
        assert_eq!(got, want, "{:?}", String::from_utf8_lossy(b));
    }
}

#[test]
fn a_line_that_is_not_utf8_is_an_io_error_at_its_key_and_the_rest_are_read() {
    let got = entries("in", b"\xc3\nok\r\xff\xfe");
    assert_eq!(
        got,
        vec![
            (
                Value::Int(0),
                Value::io_error("read", "in", "the line at key 0 is not UTF-8")
            ),
            (Value::Int(1), Value::str("ok")),
            (
                Value::Int(2),
                Value::io_error("read", "in", "the line at key 2 is not UTF-8")
            ),
        ]
    );
}

#[test]
fn a_push_writes_each_string_of_a_family_in_key_order_and_skips_empty_levels() {
    let f = |entries: Vec<(Value, Value)>| Value::Family(Family::of(entries));
    let s = Value::str;
    assert_eq!(write("o", &s("")).unwrap(), b"\n");
    assert_eq!(write("o", &f(vec![])).unwrap(), b"");
    // Keys given out of order are written in key order.
    let flat = f(vec![
        (Value::Int(2), s("c")),
        (Value::Int(0), s("a")),
        (Value::Int(1), s("b")),
    ]);
    assert_eq!(write("o", &flat).unwrap(), b"a\nb\nc\n");
    // Nested levels are written leaf by leaf in keypath order; an empty level holds no line.
    let nested = f(vec![
        (
            Value::Int(1),
            f(vec![(Value::Int(0), s("b0")), (Value::Int(1), s("b1"))]),
        ),
        (Value::Int(0), s("a")),
        (Value::Int(2), f(vec![])),
        (Value::Int(3), s("d")),
    ]);
    assert_eq!(write("o", &nested).unwrap(), b"a\nb0\nb1\nd\n");
    // What a port reads, ended by `\n`, is written back as it was.
    let text = b"one\ntwo\n\nfour\n";
    assert_eq!(write("o", &lines("i", text)).unwrap(), text);
}

#[test]
fn a_string_held_in_several_blocks_is_written_whole_in_order() {
    let a = "a".repeat(300);
    let b = "b".repeat(300);
    let joined = Text::join(&Text::from(a.as_str()), &Text::from(b.as_str())).unwrap();
    assert!(
        joined.chunks().count() > 1,
        "the test needs more than one block"
    );
    let want: Vec<u8> = [a.as_bytes(), b.as_bytes(), b"\n"].concat();
    assert_eq!(write("o", &Value::Str(joined)).unwrap(), want);
}

#[test]
fn a_push_of_a_value_that_is_no_string_is_refused_naming_the_port_and_the_value() {
    let refused = |v: &Value| write("out", v).unwrap_err();
    let lone = refused(&Value::Bool(true));
    assert!(
        lone.starts_with("port `out` writes lines of text, and the program pushed true to it"),
        "{lone}"
    );
    // A family with one entry that is no string is refused whole: nothing is written.
    let mixed = Value::Family(Family::of(vec![
        (Value::Int(0), Value::str("ok")),
        (Value::Int(1), Value::Int(7)),
    ]));
    let e = refused(&mixed);
    assert!(e.contains("pushed 7 to it"), "{e}");
    assert!(e.ends_with("Repair: push the value's text in its place, made with `Utf8String(…)`"));
}
