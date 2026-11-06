//! Loading is of order n log n in the bytes of the file, NFC or not, and so is placing every
//! offset of it (DESIGN.md Part G).

use zed_tests::scaling::{check, check_instructions_only, inputs};
use zedc::source::{Lines, Reject, load};

#[test]
fn nfc_text_with_line_breaks_of_every_kind_scales() {
    // A name with a dot above, a string with an accent and a Hangul syllable, a comment with a
    // letter carrying two marks; `\r\n`, `\n` and `\r` line ends.
    let line = "q\u{307}me = \"Jos\u{e9} \u{d55c}\";\r\n// \u{1ea1}\u{301}\r";
    let files = inputs(4_000, |n| line.repeat(n).into_bytes());
    check("loading n lines of NFC text", 4_000, |n| {
        let text = load(&files[&n]).unwrap();
        assert_eq!(text.lines().count(), 2 * n);
    });
}

#[test]
fn one_base_with_a_long_run_of_marks_of_mixed_classes_scales() {
    // NFC sorts the run by combining class (230 for U+0301, 220 for U+0323), so the first piece
    // that is not NFC is the whole run, and its NFC spelling is the run sorted.
    let files = inputs(4_000, |n| {
        let marks = (0..n).map(|i| if i % 2 == 0 { '\u{301}' } else { '\u{323}' });
        std::iter::once('x')
            .chain(marks)
            .collect::<String>()
            .into_bytes()
    });
    check("loading one base with n marks", 4_000, |n| {
        let Err(Reject::NotNfc { span, nfc }) = load(&files[&n]) else {
            panic!("a run of marks out of order is not NFC")
        };
        assert_eq!((span.start, span.end), (0, files[&n].len()));
        assert!(
            nfc.starts_with("x\u{323}"),
            "{:?}",
            nfc.chars().take(4).collect::<String>()
        );
    });
}

#[test]
fn a_rejection_late_in_a_long_file_scales() {
    let files = inputs(4_000, |n| {
        let mut bytes = "a\u{303} = 1;\n".repeat(n).into_bytes();
        bytes.push(0xff);
        bytes
    });
    // The rejection allocates nothing: std finds the bad byte, and the span is two numbers.
    check_instructions_only(
        "loading n lines and a byte that is not UTF-8",
        4_000,
        1,
        |n| {
            let bytes = &files[&n];
            let Err(Reject::NotUtf8 { span }) = load(bytes) else {
                panic!("0xff is not UTF-8")
            };
            assert_eq!(span.start, bytes.len() - 1);
        },
    );
}

#[test]
fn placing_every_offset_scales() {
    let files = inputs(4_000, |n| "ab\u{e9}\r\n".repeat(n).into_bytes());
    check("placing every offset of n lines", 4_000, |n| {
        let bytes = &files[&n];
        let lines = Lines::new(bytes);
        let sum: usize = (0..bytes.len()).map(|i| lines.line_start(i).1).sum();
        // Line k holds the five bytes before its `\n`, and the `\n` starts line k + 1 as the
        // `\r` before it ends line k.
        assert_eq!(sum, 3 * n * (n + 1) + n);
    });
}
