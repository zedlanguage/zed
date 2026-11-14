//! Completeness of source loading (TEST-complete-lex, author P189): each kind of input the
//! loader takes, each rejection with its span and message, and what the loaded text gives the
//! lexer. The case list is `COMPLETENESS.md`.

use zedc::lex::lex;
use zedc::source::{Reject, Span, io_reason, load, unreadable};

/// The rejection of `bytes` as `(kind, start, end)`.
fn rejected(bytes: &[u8]) -> (&'static str, usize, usize) {
    let r = load(bytes).expect_err("rejected");
    let kind = match r {
        Reject::NotUtf8 { .. } => "not UTF-8",
        Reject::ByteOrderMark { .. } => "byte order mark",
        Reject::NotNfc { .. } => "not NFC",
    };
    let Span { start, end } = r.span();
    (kind, start, end)
}

#[test]
fn each_line_ending_and_each_mix_of_them_is_one_break() {
    let cases: [(&[u8], &str); 11] = [
        (b"", ""),
        (b"\r", "\n"),
        (b"\n", "\n"),
        (b"\r\n", "\n"),
        (b"\r\r", "\n\n"),
        (b"\n\n", "\n\n"),
        (b"\r\n\r\n", "\n\n"),
        (b"\n\r\n", "\n\n"),
        (b"\r\r\n", "\n\n"),
        (b"a\r", "a\n"),
        (b"\ra", "\na"),
    ];
    for (bytes, want) in cases {
        assert_eq!(load(bytes).unwrap(), want, "{bytes:?}");
    }
}

/// A case of bytes that are not UTF-8: what they are, the bytes, the span rejected, and the bad
/// bytes in hexadecimal as the message names them.
type BadBytes = (&'static str, &'static [u8], (usize, usize), &'static str);

#[test]
fn each_kind_of_bytes_that_are_not_utf8_is_rejected_at_its_first_bad_sequence() {
    let cases: [BadBytes; 9] = [
        ("a continuation byte alone", b"a = \x80;", (4, 5), "80"),
        ("a byte no UTF-8 uses", b"\xff", (0, 1), "FF"),
        ("a byte no UTF-8 uses, after text", b"x\xfe", (1, 2), "FE"),
        ("a lead byte cut off by text", b"\xe2\x82a", (0, 2), "E2 82"),
        (
            "a four-byte sequence cut off at the end",
            b"x = \xf0\x9f\x98",
            (4, 7),
            "F0 9F 98",
        ),
        ("a two-byte lead byte at the end", b"\xc3", (0, 1), "C3"),
        (
            "a code point above U+10FFFF",
            b"\xf4\x90\x80\x80",
            (0, 1),
            "F4",
        ),
        (
            "a byte order mark cut off at the end",
            b"\xef\xbb",
            (0, 2),
            "EF BB",
        ),
        (
            "the first of two bad sequences",
            b"ok \xc0\xaf and \xff",
            (3, 4),
            "C0",
        ),
    ];
    for (case, bytes, (start, end), hex) in cases {
        let r = load(bytes).expect_err(case);
        assert_eq!(rejected(bytes), ("not UTF-8", start, end), "{case}");
        assert!(
            r.message(bytes)
                .contains(&format!("the bytes here, {hex} in hexadecimal,")),
            "{case}: {}",
            r.message(bytes)
        );
    }
}

#[test]
fn a_rejection_is_placed_in_the_file_as_read_before_its_line_endings_normalize() {
    // The span counts the `\r` bytes, and each `\r\n` or lone `\r` ends a line.
    let bytes = b"a\r\nb\rc\xff";
    assert_eq!(rejected(bytes), ("not UTF-8", 6, 7));
    assert!(
        load(bytes).unwrap_err().render(bytes).starts_with("3:2: "),
        "{}",
        load(bytes).unwrap_err().render(bytes)
    );
    // The column counts characters, not bytes: `é` and `€` are one column each.
    let bytes = "é€".bytes().chain([0xff]).collect::<Vec<u8>>();
    assert!(
        load(&bytes)
            .unwrap_err()
            .render(&bytes)
            .starts_with("1:3: "),
        "{}",
        load(&bytes).unwrap_err().render(&bytes)
    );
}

#[test]
fn a_byte_order_mark_is_rejected_alone_and_before_any_other_text() {
    for bytes in [
        "\u{feff}".as_bytes(),
        "\u{feff}\n".as_bytes(),
        "\u{feff}\u{feff}".as_bytes(),
        "\u{feff}// comment".as_bytes(),
    ] {
        assert_eq!(rejected(bytes), ("byte order mark", 0, 3), "{bytes:?}");
        let r = load(bytes).unwrap_err();
        assert_eq!(r.render(bytes), format!("1:1: {r}"));
    }
}

#[test]
fn the_messages_without_a_place_are_the_rejections_in_words() {
    // The UTF-8 message names the bytes only when it has the file to read them from.
    let bytes = b"\xff";
    let r = load(bytes).unwrap_err();
    assert!(!r.to_string().contains("FF"), "{r}");
    assert!(r.message(bytes).contains("FF"));
    for bytes in ["\u{feff}x".as_bytes(), "e\u{301}".as_bytes()] {
        let r = load(bytes).unwrap_err();
        assert_eq!(r.message(bytes), r.to_string());
    }
}

#[test]
fn a_file_with_two_problems_is_rejected_once_with_a_span_in_the_file() {
    // DESIGN.md sec:lexical names no order among the rejections; a file is rejected with one of
    // them, whose span lies in the file.
    for bytes in [
        "\u{feff}e\u{301}".as_bytes().to_vec(),
        [&b"e\xcc\x81 "[..], b"\xff"].concat(),
        [&b"\xef\xbb\xbf"[..], b"\xff"].concat(),
    ] {
        let (_, start, end) = rejected(&bytes);
        assert!(start < end && end <= bytes.len(), "{bytes:?}");
    }
}

#[test]
fn the_first_of_two_places_nfc_changes_is_the_one_named() {
    let text = "a = \"A\u{30a}\"; b = \"\u{212b}\";";
    let r = load(text.as_bytes()).unwrap_err();
    assert_eq!(
        r,
        Reject::NotNfc {
            span: Span { start: 5, end: 8 },
            nfc: "\u{c5}".into()
        }
    );
}

#[test]
fn a_mark_at_the_start_of_the_file_is_nfc_and_left_to_the_lexer() {
    // Nothing comes before the mark for NFC to compose it with.
    assert_eq!(load("\u{301}a".as_bytes()).unwrap(), "\u{301}a");
}

#[test]
fn line_endings_in_a_loaded_string_are_one_break_each() {
    // A `"""` string written on Windows strips as the one written on Linux.
    let text = load(b"s = \"\"\"\r\n    a\r\n      b\r\n    \"\"\";").unwrap();
    let toks = lex(&text).unwrap();
    assert_eq!(format!("{:?}", toks[2].tok), r#"Str([Text("a\n  b")])"#);
    // A lone `\r` in a `"` string ends its line, so the string is not closed on it.
    let text = load(b"s = \"a\rb\";").unwrap();
    assert!(lex(&text).is_err());
}

#[test]
fn the_compilers_whole_file_path_reports_a_rejection_with_its_place() {
    // `zedc::run::load` is the path a file named on the command line takes.
    for bytes in [&b"x = 1;\n\xff"[..], "\u{feff}x = 1;".as_bytes()] {
        let r = load(bytes).unwrap_err();
        let Err(e) = zedc::run::load(bytes) else {
            panic!("{bytes:?} loaded")
        };
        assert!(e.contains(&r.render(bytes)), "{e}");
    }
}

#[test]
fn a_file_that_cannot_be_read_is_named_with_the_reason_in_words() {
    let e = std::io::Error::from_raw_os_error(2);
    assert_eq!(io_reason(&e), "No such file or directory");
    assert_eq!(
        unreadable("orders.zed", &e),
        "orders.zed: zedc could not read this file: No such file or directory. Check the path and \
         that you may read the file."
    );
    // An error the system did not number keeps its text.
    let e = std::io::Error::other("the disk went away");
    assert_eq!(io_reason(&e), "the disk went away");
    // A real file that is not there.
    let e = std::fs::read("/nonexistent/orders.zed").unwrap_err();
    assert_eq!(io_reason(&e), "No such file or directory");
}
